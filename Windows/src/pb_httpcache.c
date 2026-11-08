#include "pb_internal.h"
#include <ctype.h>

// HTTP inspection for proxied TCP connections: an optional response cache and an optional full request log.
//
// Both features are off by default. While both are off connection_handler hands every connection straight to the
// IOCP relay and nothing here runs. While either is on, a proxied connection whose application speaks first with an
// HTTP/1.x request line is driven here, one request/response exchange at a time:
//
//   request  : head (+ body) read from the application, written to the request log, then either answered from the
//              cache (GET only) or forwarded to the proxy
//   response : head + body read from the proxy and forwarded to the application; a cacheable response is kept
//
// Anything else is handed to the normal relay with every byte already read forwarded first, so the stream is never
// altered: TLS (HTTPS - encrypted, so it can be neither cached nor read; the request log records its SNI), protocols
// where the server speaks first, CONNECT, protocol upgrades (WebSocket), "Expect: 100-continue" uploads and malformed
// or oversized heads.
//
// Cache: an in-memory LRU of plain-HTTP responses that have a Content-Length, keyed by method + absolute URL +
// Accept-Encoding. It follows the usual shared-cache rules: no Authorization / Range requests, no no-store / no-cache /
// private / Set-Cookie / Vary (other than Accept-Encoding) responses; freshness from s-maxage / max-age / Expires,
// otherwise RESP_CACHE_DEFAULT_TTL_S. Turning the cache off empties it.
//
// Request log: %ProgramData%\ProxyBridge\Logs\requests.log, one entry per request with the process, destination,
// the complete head and the body (up to REQ_LOG_BODY_MAX bytes; binary bodies as a hex dump), plus one line per
// response. The file rotates to requests.log.1 at REQ_LOG_ROTATE_BYTES. It holds everything the applications send
// (cookies, tokens, form data) in clear text: it is meant for debugging and is off by default.

#define RESP_CACHE_MAX_BYTES     (64u * 1024u * 1024u)   // whole cache
#define RESP_CACHE_MAX_ENTRY     (8u * 1024u * 1024u)    // one response (head + body)
#define RESP_CACHE_DEFAULT_TTL_S 300                     // freshness of a response that states none
#define RESP_CACHE_MAX_TTL_S     86400
#define RESP_CACHE_BUCKETS       1024

#define REQ_LOG_BODY_MAX         (1024u * 1024u)         // request body bytes written to the log per request
#define REQ_LOG_HEX_MAX          (64u * 1024u)           // binary bodies: bytes shown as hex
#define REQ_LOG_ROTATE_BYTES     (50ull * 1024ull * 1024ull)

#define HTTP_HEAD_MAX            (64u * 1024u)
#define HTTP_IO_CHUNK            65536
#define HTTP_IDLE_KEEPALIVE_MS   120000                  // waiting for the next request on a kept-alive connection
#define HTTP_IDLE_RESPONSE_MS    300000                  // waiting for the server's response
#define HTTP_IDLE_BODY_MS        120000                  // waiting for more body bytes

volatile BOOL g_resp_cache_enabled = FALSE;
volatile BOOL g_req_log_enabled = FALSE;
volatile BOOL g_https_intercept_enabled = FALSE;

// ============================================================================================
// growable byte buffer
// ============================================================================================
typedef struct { char *p; size_t len, cap; } HBUF;

static BOOL hb_reserve(HBUF *b, size_t extra)
{
    if (b->len + extra <= b->cap) return TRUE;
    size_t nc = b->cap ? b->cap : 4096;
    while (nc < b->len + extra) nc *= 2;
    char *np = (char *)realloc(b->p, nc);
    if (np == NULL) return FALSE;
    b->p = np; b->cap = nc;
    return TRUE;
}
static BOOL hb_append(HBUF *b, const void *d, size_t n)
{
    if (n == 0) return TRUE;
    if (!hb_reserve(b, n)) return FALSE;
    memcpy(b->p + b->len, d, n); b->len += n;
    return TRUE;
}
static BOOL hb_puts(HBUF *b, const char *s) { return hb_append(b, s, strlen(s)); }
static void hb_consume(HBUF *b, size_t n)
{
    if (n >= b->len) { b->len = 0; return; }
    memmove(b->p, b->p + n, b->len - n); b->len -= n;
}
static void hb_free(HBUF *b) { free(b->p); b->p = NULL; b->len = b->cap = 0; }

// ============================================================================================
// small string helpers
// ============================================================================================
static BOOL ci_prefix(const char *s, size_t slen, const char *pre)
{
    size_t n = strlen(pre);
    return slen >= n && _strnicmp(s, pre, n) == 0;
}

static const char *find_crlfcrlf(const char *p, size_t len)
{
    for (size_t i = 0; i + 3 < len; i++)
        if (p[i] == '\r' && p[i + 1] == '\n' && p[i + 2] == '\r' && p[i + 3] == '\n') return p + i;
    return NULL;
}

static const char *find_crlf(const char *p, size_t len)
{
    for (size_t i = 0; i + 1 < len; i++)
        if (p[i] == '\r' && p[i + 1] == '\n') return p + i;
    return NULL;
}

// Value of header `name` in a head (request/status line + header lines, CRLF separated). Repeated headers are joined
// with ", ". Returns FALSE if the header is absent.
static BOOL hdr_get(const char *head, size_t len, const char *name, char *out, size_t outsz)
{
    size_t nlen = strlen(name), o = 0;
    BOOL found = FALSE;
    if (outsz == 0) return FALSE;
    out[0] = '\0';
    const char *end = head + len;
    const char *line = find_crlf(head, len);
    if (line == NULL) return FALSE;
    line += 2;
    while (line < end)
    {
        const char *eol = find_crlf(line, (size_t)(end - line));
        if (eol == NULL) eol = end;
        if (eol == line) break;
        if ((size_t)(eol - line) > nlen && line[nlen] == ':' && _strnicmp(line, name, nlen) == 0)
        {
            const char *v = line + nlen + 1, *ve = eol;
            while (v < ve && (*v == ' ' || *v == '\t')) v++;
            while (ve > v && (ve[-1] == ' ' || ve[-1] == '\t')) ve--;
            if (found && o + 2 < outsz) { out[o++] = ','; out[o++] = ' '; }
            for (; v < ve && o + 1 < outsz; v++) out[o++] = *v;
            out[o] = '\0';
            found = TRUE;
        }
        line = eol + 2;
    }
    return found;
}

// Does the comma-separated value contain `token` (case-insensitive; "max-age" also matches "max-age=60")?
// If `arg` is given it receives the part after '='.
static BOOL tok_has(const char *value, const char *token, char *arg, size_t argsz)
{
    size_t tl = strlen(token);
    const char *p = value;
    while (*p)
    {
        while (*p == ' ' || *p == '\t' || *p == ',') p++;
        const char *s = p;
        while (*p && *p != ',') p++;
        const char *e = p;
        while (e > s && (e[-1] == ' ' || e[-1] == '\t')) e--;
        if ((size_t)(e - s) >= tl && _strnicmp(s, token, tl) == 0 && (s + tl == e || s[tl] == '=' || s[tl] == ' '))
        {
            if (arg && argsz)
            {
                const char *a = s + tl;
                while (a < e && (*a == ' ' || *a == '=')) a++;
                if (a < e && *a == '"') a++;
                size_t n = 0;
                while (a < e && *a != '"' && n + 1 < argsz) arg[n++] = *a++;
                arg[n] = '\0';
            }
            return TRUE;
        }
    }
    return FALSE;
}

static BOOL hdr_has_token(const char *head, size_t len, const char *name, const char *token)
{
    char v[1024];
    return hdr_get(head, len, name, v, sizeof(v)) && tok_has(v, token, NULL, 0);
}

// "Sun, 06 Nov 1994 08:49:37 GMT" (also without the weekday) -> seconds since 1970. 0 if not parseable.
static ULONGLONG http_date_parse(const char *s)
{
    static const char *mon[12] = { "Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec" };
    const char *c = strchr(s, ',');
    c = c ? c + 1 : s;
    int d = 0, y = 0, hh = 0, mm = 0, ss = 0, m = -1;
    char ms[4] = {0};
    if (sscanf(c, " %d %3s %d %d:%d:%d", &d, ms, &y, &hh, &mm, &ss) != 6) return 0;
    for (int i = 0; i < 12; i++) if (_stricmp(ms, mon[i]) == 0) m = i;
    if (m < 0 || y < 1970 || d < 1 || d > 31) return 0;
    SYSTEMTIME st; ZeroMemory(&st, sizeof(st));
    st.wYear = (WORD)y; st.wMonth = (WORD)(m + 1); st.wDay = (WORD)d;
    st.wHour = (WORD)hh; st.wMinute = (WORD)mm; st.wSecond = (WORD)ss;
    FILETIME ft;
    if (!SystemTimeToFileTime(&st, &ft)) return 0;
    ULONGLONG t = ((ULONGLONG)ft.dwHighDateTime << 32) | ft.dwLowDateTime;
    return t / 10000000ull - 11644473600ull;
}

static ULONGLONG unix_now(void)
{
    FILETIME ft; GetSystemTimeAsFileTime(&ft);
    ULONGLONG t = ((ULONGLONG)ft.dwHighDateTime << 32) | ft.dwLowDateTime;
    return t / 10000000ull - 11644473600ull;
}

// ============================================================================================
// response cache
// ============================================================================================
typedef struct CACHE_ENTRY {
    char      *key;
    UINT32     hash;
    char      *head;          // status line + headers, without Connection / Keep-Alive / Age and without the blank line
    size_t     head_len;
    char      *body;
    size_t     body_len;
    ULONGLONG  stored;        // unix seconds
    ULONGLONG  expires;       // GetTickCount64() deadline
    struct CACHE_ENTRY *hnext;
    struct CACHE_ENTRY *prev, *next;   // LRU, most recently used first
} CACHE_ENTRY;

static CACHE_ENTRY *g_cache_buckets[RESP_CACHE_BUCKETS];
static CACHE_ENTRY *g_cache_lru_head = NULL, *g_cache_lru_tail = NULL;
static size_t       g_cache_bytes = 0;
static UINT32       g_cache_count = 0;
static SRWLOCK      g_cache_lock = SRWLOCK_INIT;

static UINT32 key_hash(const char *s)
{
    UINT32 h = 2166136261u;
    for (; *s; s++) { h ^= (unsigned char)*s; h *= 16777619u; }
    return h;
}

static size_t entry_size(const CACHE_ENTRY *e) { return e->head_len + e->body_len + strlen(e->key) + sizeof(*e); }

// caller holds g_cache_lock exclusively
static void cache_unlink(CACHE_ENTRY *e)
{
    CACHE_ENTRY **pp = &g_cache_buckets[e->hash % RESP_CACHE_BUCKETS];
    while (*pp && *pp != e) pp = &(*pp)->hnext;
    if (*pp) *pp = e->hnext;
    if (e->prev) e->prev->next = e->next; else g_cache_lru_head = e->next;
    if (e->next) e->next->prev = e->prev; else g_cache_lru_tail = e->prev;
    g_cache_bytes -= entry_size(e);
    g_cache_count--;
    free(e->key); free(e->head); free(e->body); free(e);
}

static void cache_lru_front(CACHE_ENTRY *e)
{
    if (g_cache_lru_head == e) return;
    if (e->prev) e->prev->next = e->next;
    if (e->next) e->next->prev = e->prev; else g_cache_lru_tail = e->prev;
    e->prev = NULL; e->next = g_cache_lru_head;
    if (g_cache_lru_head) g_cache_lru_head->prev = e;
    g_cache_lru_head = e;
    if (g_cache_lru_tail == NULL) g_cache_lru_tail = e;
}

static CACHE_ENTRY *cache_find_locked(const char *key, UINT32 h)
{
    for (CACHE_ENTRY *e = g_cache_buckets[h % RESP_CACHE_BUCKETS]; e; e = e->hnext)
        if (e->hash == h && strcmp(e->key, key) == 0) return e;
    return NULL;
}

void resp_cache_clear(void)
{
    AcquireSRWLockExclusive(&g_cache_lock);
    while (g_cache_lru_head) cache_unlink(g_cache_lru_head);
    ReleaseSRWLockExclusive(&g_cache_lock);
}

// On a hit, *head / *body are malloc'ed copies (caller frees) and *age is the entry's age in seconds.
static BOOL cache_lookup(const char *key, char **head, size_t *head_len, char **body, size_t *body_len, ULONGLONG *age)
{
    UINT32 h = key_hash(key);
    BOOL hit = FALSE;
    AcquireSRWLockExclusive(&g_cache_lock);
    CACHE_ENTRY *e = cache_find_locked(key, h);
    if (e != NULL && GetTickCount64() >= e->expires) { cache_unlink(e); e = NULL; }
    if (e != NULL)
    {
        *head = (char *)malloc(e->head_len + 1);
        *body = (char *)malloc(e->body_len + 1);
        if (*head && *body)
        {
            memcpy(*head, e->head, e->head_len); *head_len = e->head_len;
            memcpy(*body, e->body, e->body_len); *body_len = e->body_len;
            ULONGLONG now = unix_now();
            *age = now > e->stored ? now - e->stored : 0;
            cache_lru_front(e);
            hit = TRUE;
        }
        else { free(*head); free(*body); *head = *body = NULL; }
    }
    ReleaseSRWLockExclusive(&g_cache_lock);
    return hit;
}

// Takes ownership of head / body.
static void cache_store(const char *key, char *head, size_t head_len, char *body, size_t body_len, UINT32 ttl_s)
{
    CACHE_ENTRY *e = (CACHE_ENTRY *)calloc(1, sizeof(*e));
    char *k = _strdup(key);
    if (e == NULL || k == NULL) { free(e); free(k); free(head); free(body); return; }
    e->key = k; e->hash = key_hash(key);
    e->head = head; e->head_len = head_len; e->body = body; e->body_len = body_len;
    e->stored = unix_now();
    e->expires = GetTickCount64() + (ULONGLONG)ttl_s * 1000ull;
    size_t sz = entry_size(e);

    AcquireSRWLockExclusive(&g_cache_lock);
    if (!g_resp_cache_enabled) { ReleaseSRWLockExclusive(&g_cache_lock); free(k); free(head); free(body); free(e); return; }
    CACHE_ENTRY *old = cache_find_locked(key, e->hash);
    if (old) cache_unlink(old);
    while (g_cache_lru_tail && g_cache_bytes + sz > RESP_CACHE_MAX_BYTES) cache_unlink(g_cache_lru_tail);
    CACHE_ENTRY **b = &g_cache_buckets[e->hash % RESP_CACHE_BUCKETS];
    e->hnext = *b; *b = e;
    e->next = g_cache_lru_head;
    if (g_cache_lru_head) g_cache_lru_head->prev = e;
    g_cache_lru_head = e;
    if (g_cache_lru_tail == NULL) g_cache_lru_tail = e;
    g_cache_bytes += sz;
    g_cache_count++;
    ReleaseSRWLockExclusive(&g_cache_lock);
}

// Freshness lifetime of a response in seconds, 0 = must not be cached.
static UINT32 response_ttl(const char *head, size_t len, int status)
{
    char cc[1024], v[256], arg[64];
    if (!(status == 200 || status == 203 || status == 300 || status == 301 || status == 308)) return 0;
    if (hdr_get(head, len, "Set-Cookie", v, sizeof(v))) return 0;
    if (hdr_get(head, len, "Vary", v, sizeof(v)))
    {
        // only "Accept-Encoding" (part of the key) is understood
        char tmp[256]; size_t o = 0;
        for (const char *p = v; *p && o + 1 < sizeof(tmp); p++) if (*p != ' ' && *p != '\t') tmp[o++] = *p;
        tmp[o] = '\0';
        if (_stricmp(tmp, "Accept-Encoding") != 0) return 0;
    }
    if (hdr_get(head, len, "Cache-Control", cc, sizeof(cc)))
    {
        if (tok_has(cc, "no-store", NULL, 0) || tok_has(cc, "no-cache", NULL, 0) || tok_has(cc, "private", NULL, 0)) return 0;
        if (tok_has(cc, "s-maxage", arg, sizeof(arg)) || tok_has(cc, "max-age", arg, sizeof(arg)))
        {
            long long s = _atoi64(arg);
            if (s <= 0) return 0;
            if (hdr_get(head, len, "Age", v, sizeof(v))) { s -= _atoi64(v); if (s <= 0) return 0; }
            return (UINT32)(s > RESP_CACHE_MAX_TTL_S ? RESP_CACHE_MAX_TTL_S : s);
        }
    }
    if (hdr_has_token(head, len, "Pragma", "no-cache")) return 0;
    if (hdr_get(head, len, "Expires", v, sizeof(v)))
    {
        ULONGLONG exp = http_date_parse(v), base = 0;
        char d[128];
        if (hdr_get(head, len, "Date", d, sizeof(d))) base = http_date_parse(d);
        if (base == 0) base = unix_now();
        if (exp <= base) return 0;                      // "0", "-1", invalid or in the past: already stale
        ULONGLONG s = exp - base;
        return (UINT32)(s > RESP_CACHE_MAX_TTL_S ? RESP_CACHE_MAX_TTL_S : s);
    }
    return RESP_CACHE_DEFAULT_TTL_S;
}

// Copy of a response head without the hop-by-hop / per-delivery headers and without the final blank line.
static char *head_for_cache(const char *head, size_t len, size_t *out_len)
{
    HBUF b = {0};
    const char *end = head + len;
    const char *eol = find_crlf(head, len);
    if (eol == NULL) return NULL;
    hb_append(&b, head, (size_t)(eol - head) + 2);
    const char *line = eol + 2;
    while (line < end)
    {
        const char *e = find_crlf(line, (size_t)(end - line));
        if (e == NULL) e = end;
        if (e == line) break;
        size_t ll = (size_t)(e - line);
        if (!ci_prefix(line, ll, "Connection:") && !ci_prefix(line, ll, "Keep-Alive:") && !ci_prefix(line, ll, "Age:") &&
            !ci_prefix(line, ll, "Proxy-Connection:") && !ci_prefix(line, ll, "X-ProxyBridge-Cache:"))
        {
            hb_append(&b, line, ll);
            hb_append(&b, "\r\n", 2);
        }
        line = e + 2;
    }
    if (b.p == NULL) return NULL;
    *out_len = b.len;
    return b.p;
}

// ============================================================================================
// request log file
// ============================================================================================
static SRWLOCK  g_reqlog_lock = SRWLOCK_INIT;
static HANDLE   g_reqlog_file = INVALID_HANDLE_VALUE;
static volatile LONG g_reqlog_seq = 0;

static void reqlog_path_w(wchar_t *out, size_t n, BOOL dir_only)
{
    wchar_t base[MAX_PATH];
    DWORD k = GetEnvironmentVariableW(L"ProgramData", base, MAX_PATH);
    if (k == 0 || k >= MAX_PATH) lstrcpynW(base, L"C:\\ProgramData", MAX_PATH);
    _snwprintf_s(out, n, _TRUNCATE, dir_only ? L"%s\\ProxyBridge\\Logs" : L"%s\\ProxyBridge\\Logs\\requests.log", base);
}

// caller holds g_reqlog_lock exclusively
static BOOL reqlog_open_locked(void)
{
    if (g_reqlog_file != INVALID_HANDLE_VALUE) return TRUE;
    wchar_t dir[MAX_PATH + 64], path[MAX_PATH + 64], base[MAX_PATH + 32];
    reqlog_path_w(dir, MAX_PATH + 64, TRUE);
    reqlog_path_w(path, MAX_PATH + 64, FALSE);
    lstrcpynW(base, dir, MAX_PATH + 32);
    wchar_t *slash = wcsrchr(base, L'\\');
    if (slash) { *slash = 0; CreateDirectoryW(base, NULL); }   // ...\ProxyBridge
    CreateDirectoryW(dir, NULL);                                // ...\ProxyBridge\Logs
    g_reqlog_file = CreateFileW(path, FILE_APPEND_DATA, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, NULL,
                                OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    return g_reqlog_file != INVALID_HANDLE_VALUE;
}

static void reqlog_close(void)
{
    AcquireSRWLockExclusive(&g_reqlog_lock);
    if (g_reqlog_file != INVALID_HANDLE_VALUE) { CloseHandle(g_reqlog_file); g_reqlog_file = INVALID_HANDLE_VALUE; }
    ReleaseSRWLockExclusive(&g_reqlog_lock);
}

// Appends one complete entry (written in one call so entries from parallel connections never interleave).
static void reqlog_write(const char *data, size_t len)
{
    if (!g_req_log_enabled || len == 0) return;
    AcquireSRWLockExclusive(&g_reqlog_lock);
    if (reqlog_open_locked())
    {
        LARGE_INTEGER sz;
        if (GetFileSizeEx(g_reqlog_file, &sz) && (ULONGLONG)sz.QuadPart > REQ_LOG_ROTATE_BYTES)
        {
            wchar_t path[MAX_PATH + 64], old[MAX_PATH + 72];
            reqlog_path_w(path, MAX_PATH + 64, FALSE);
            _snwprintf_s(old, MAX_PATH + 72, _TRUNCATE, L"%s.1", path);
            CloseHandle(g_reqlog_file); g_reqlog_file = INVALID_HANDLE_VALUE;
            MoveFileExW(path, old, MOVEFILE_REPLACE_EXISTING);
            reqlog_open_locked();
        }
        if (g_reqlog_file != INVALID_HANDLE_VALUE)
        {
            while (len > 0)
            {
                DWORD w = 0, part = len > 0x40000000u ? 0x40000000u : (DWORD)len;
                if (!WriteFile(g_reqlog_file, data, part, &w, NULL) || w == 0) break;
                data += w; len -= w;
            }
        }
    }
    ReleaseSRWLockExclusive(&g_reqlog_lock);
}

static void fmt_now(char *out, size_t n)
{
    SYSTEMTIME st; GetLocalTime(&st);
    snprintf(out, n, "%04u-%02u-%02u %02u:%02u:%02u.%03u", st.wYear, st.wMonth, st.wDay, st.wHour, st.wMinute, st.wSecond, st.wMilliseconds);
}

// Per-connection description used by the log: "chrome.exe (PID 1234) -> 93.184.216.34:80 (example.com) via proxy #1"
typedef struct {
    UINT32 id;
    char   proc[64];
    char   dest[160];
    FLOW_META meta;
} HSESS;

static void sess_describe(HSESS *s, const FLOW_META *meta)
{
    s->meta = *meta;
    s->id = (UINT32)InterlockedIncrement(&g_reqlog_seq);
    char full[MAX_PROCESS_NAME];
    if (meta->pid != 0 && get_process_name_from_pid(meta->pid, full, sizeof(full)))
        snprintf(s->proc, sizeof(s->proc), "%s", extract_filename(full));
    else
        snprintf(s->proc, sizeof(s->proc), "%s", meta->pid == 4 ? "System" : "unknown");
    char ip[64], dom[256]; dom[0] = '\0';
    if (meta->v6)
    {
        struct in6_addr a6; memcpy(&a6, meta->dest, 16);
        char t[48]; if (!inet_ntop(AF_INET6, &a6, t, sizeof(t))) t[0] = '\0';
        snprintf(ip, sizeof(ip), "[%s]", t);
        dns_cache_lookup_v6(meta->dest, dom, sizeof(dom));
    }
    else
    {
        UINT32 v4; memcpy(&v4, meta->dest, 4);
        format_ip_address(v4, ip, sizeof(ip));
        dns_cache_lookup(v4, dom, sizeof(dom));
    }
    if (dom[0]) snprintf(s->dest, sizeof(s->dest), "%s:%u (%s)", ip, (unsigned)meta->port, dom);
    else        snprintf(s->dest, sizeof(s->dest), "%s:%u", ip, (unsigned)meta->port);
}

static void entry_header(HBUF *b, const HSESS *s, const char *what)
{
    char ts[40], line[512];
    fmt_now(ts, sizeof(ts));
    snprintf(line, sizeof(line), "\r\n===== %s | #%u | %s (PID %lu) -> %s | proxy #%u | %s =====\r\n",
             ts, s->id, s->proc, (unsigned long)s->meta.pid, s->dest, s->meta.proxy_id, what);
    hb_puts(b, line);
}

static BOOL looks_text(const char *p, size_t n)
{
    size_t bad = 0;
    for (size_t i = 0; i < n; i++)
    {
        unsigned char c = (unsigned char)p[i];
        if (c == 0) return FALSE;
        if (c < 0x20 && c != '\r' && c != '\n' && c != '\t') bad++;
    }
    return bad * 20 <= n;
}

static void hex_dump(HBUF *b, const unsigned char *p, size_t n)
{
    char line[96];
    for (size_t off = 0; off < n; off += 16)
    {
        int o = snprintf(line, sizeof(line), "%08zx  ", off);
        for (size_t i = 0; i < 16; i++)
            o += (off + i < n) ? snprintf(line + o, sizeof(line) - o, "%02x ", p[off + i]) : snprintf(line + o, sizeof(line) - o, "   ");
        o += snprintf(line + o, sizeof(line) - o, " ");
        for (size_t i = 0; i < 16 && off + i < n; i++) line[o++] = (p[off + i] >= 0x20 && p[off + i] < 0x7f) ? (char)p[off + i] : '.';
        line[o++] = '\r'; line[o++] = '\n';
        hb_append(b, line, (size_t)o);
    }
}

static void append_body(HBUF *b, const char *body, size_t shown, unsigned long long total)
{
    char line[160];
    if (total == 0) { hb_puts(b, "[no body]\r\n"); return; }
    if (looks_text(body, shown))
    {
        hb_append(b, body, shown);
        hb_puts(b, "\r\n");
        if (total > shown) { snprintf(line, sizeof(line), "[body truncated: %zu of %llu bytes shown]\r\n", shown, total); hb_puts(b, line); }
    }
    else
    {
        size_t h = shown > REQ_LOG_HEX_MAX ? REQ_LOG_HEX_MAX : shown;
        snprintf(line, sizeof(line), "[binary body: %llu bytes, hex dump of the first %zu]\r\n", total, h);
        hb_puts(b, line);
        hex_dump(b, (const unsigned char *)body, h);
    }
}

// TLS ClientHello -> server_name, best effort and bounds-checked.
static BOOL tls_sni(const unsigned char *p, size_t n, char *out, size_t outsz)
{
    size_t i = 5;                                         // record header
    if (n < 5 + 4 || p[0] != 0x16 || p[5] != 0x01) return FALSE;
    i += 4 + 2 + 32;                                      // handshake header, version, random
    if (i + 1 > n) return FALSE;
    i += 1 + p[i];                                        // session id
    if (i + 2 > n) return FALSE;
    i += 2 + ((size_t)p[i] << 8 | p[i + 1]);              // cipher suites
    if (i + 1 > n) return FALSE;
    i += 1 + p[i];                                        // compression methods
    if (i + 2 > n) return FALSE;
    size_t ext_end = i + 2 + ((size_t)p[i] << 8 | p[i + 1]);
    i += 2;
    if (ext_end > n) ext_end = n;
    while (i + 4 <= ext_end)
    {
        size_t type = (size_t)p[i] << 8 | p[i + 1], len = (size_t)p[i + 2] << 8 | p[i + 3];
        i += 4;
        if (i + len > ext_end) return FALSE;
        if (type == 0 && len >= 5)
        {
            size_t nl = (size_t)p[i + 3] << 8 | p[i + 4];
            if (p[i + 2] != 0 || 5 + nl > len || nl + 1 > outsz) return FALSE;
            memcpy(out, p + i + 5, nl); out[nl] = '\0';
            return TRUE;
        }
        i += len;
    }
    return FALSE;
}

// Non-HTTP connection: one entry describing what could be seen.
static void reqlog_non_http(const HSESS *s, const char *first, size_t n, BOOL server_first)
{
    if (!g_req_log_enabled) return;
    HBUF b = {0};
    char sni[256], line[400];
    if (server_first)
    {
        entry_header(&b, s, "TCP (server spoke first)");
        hb_puts(&b, "[not HTTP: the server sent the first bytes; the stream is relayed unchanged]\r\n");
    }
    else if (n >= 6 && (unsigned char)first[0] == 0x16 && (unsigned char)first[1] == 0x03)
    {
        entry_header(&b, s, "TLS");
        if (tls_sni((const unsigned char *)first, n, sni, sizeof(sni)))
            snprintf(line, sizeof(line), "TLS ClientHello, server name (SNI): %s\r\n", sni);
        else
            snprintf(line, sizeof(line), "TLS ClientHello (no server name)\r\n");
        hb_puts(&b, line);
        hb_puts(&b, "[encrypted (HTTPS/TLS): the request content cannot be read and is not logged]\r\n");
    }
    else
    {
        entry_header(&b, s, "TCP");
        size_t h = n > 1024 ? 1024 : n;
        snprintf(line, sizeof(line), "[not HTTP: first %zu bytes sent by the application]\r\n", h);
        hb_puts(&b, line);
        hex_dump(&b, (const unsigned char *)first, h);
    }
    reqlog_write(b.p, b.len);
    hb_free(&b);
}

// ============================================================================================
// PBIO backends and stream helpers (every wait wakes once a second so ProxyBridge_Stop is never held up)
// ============================================================================================
// Raw socket backend: the HTTP engine runs over this when the connection is plain (not decrypted TLS).
typedef struct { PBIO io; SOCKET s; BOOL owns; } RAWIO;

static int raw_read(PBIO *io, char *buf, int cap, DWORD idle_ms)
{
    RAWIO *r = (RAWIO *)io;
    ULONGLONG start = GetTickCount64();
    while (running)
    {
        fd_set rf; FD_ZERO(&rf); FD_SET(r->s, &rf);
        struct timeval tv = { 1, 0 };
        int sr = select(0, &rf, NULL, NULL, &tv);
        if (sr == SOCKET_ERROR) return -1;
        if (sr > 0) { int n = recv(r->s, buf, cap, 0); return n == SOCKET_ERROR ? -1 : n; }   // 0 = peer closed
        if (GetTickCount64() - start >= idle_ms) return -1;
    }
    return -1;
}
static int raw_write(PBIO *io, const char *buf, int len) { RAWIO *r = (RAWIO *)io; return send_all(r->s, buf, len) == SOCKET_ERROR ? -1 : 0; }
static BOOL raw_pending(PBIO *io) { (void)io; return FALSE; }
static void raw_destroy(PBIO *io, BOOL sh)
{
    RAWIO *r = (RAWIO *)io;
    if (r->owns && r->s != INVALID_SOCKET) { if (sh) shutdown(r->s, SD_SEND); closesocket(r->s); }
    free(r);
}
static PBIO *pbio_socket(SOCKET s)
{
    RAWIO *r = (RAWIO *)calloc(1, sizeof(*r));
    if (r == NULL) return NULL;
    r->io.read = raw_read; r->io.write = raw_write; r->io.pending = raw_pending; r->io.destroy = raw_destroy;
    r->io.sock = s; r->io.is_tls = FALSE; r->s = s; r->owns = TRUE;
    return &r->io;
}
// Hands the socket back so it can go to the IOCP relay; the wrapper no longer owns or closes it.
static SOCKET pbio_release_socket(PBIO *io) { RAWIO *r = (RAWIO *)io; SOCKET s = r->s; r->s = INVALID_SOCKET; r->owns = FALSE; return s; }

// Plaintext bidirectional pump used when a TLS-terminated connection turns out not to be a plain exchange
// (it cannot go to the raw relay - the relay would copy ciphertext; here we re-encrypt on each write).
typedef struct { PBIO *src, *dst; } PUMP;
static DWORD WINAPI pump_dir(LPVOID arg)
{
    PUMP *pm = (PUMP *)arg;
    char *buf = (char *)malloc(HTTP_IO_CHUNK);
    if (buf)
    {
        int n;
        while ((n = pm->src->read(pm->src, buf, HTTP_IO_CHUNK, HTTP_IDLE_KEEPALIVE_MS)) > 0)
            if (pm->dst->write(pm->dst, buf, n) != 0) break;
        free(buf);
    }
    shutdown(pm->src->sock, SD_BOTH);   // wake the sibling direction's blocked recv
    shutdown(pm->dst->sock, SD_BOTH);
    return 0;
}
static void pbio_pump(PBIO *a, PBIO *b)
{
    PUMP up = { a, b }, dn = { b, a };
    HANDLE th = CreateThread(NULL, 0, pump_dir, &up, 0, NULL);
    pump_dir(&dn);
    if (th) { WaitForSingleObject(th, INFINITE); CloseHandle(th); }
}

// bit 1 = a readable, bit 2 = b readable; 0 = idle timeout; -1 = stopping / error.
static int wait_readable(PBIO *a, PBIO *b, DWORD idle_ms)
{
    if (a->pending(a)) return 1;
    if (b && b->pending(b)) return 2;
    ULONGLONG start = GetTickCount64();
    while (running)
    {
        fd_set rf; FD_ZERO(&rf);
        FD_SET(a->sock, &rf);
        if (b) FD_SET(b->sock, &rf);
        struct timeval tv = { 1, 0 };
        int r = select(0, &rf, NULL, NULL, &tv);
        if (r == SOCKET_ERROR) return -1;
        if (r > 0) return (FD_ISSET(a->sock, &rf) ? 1 : 0) | ((b && FD_ISSET(b->sock, &rf)) ? 2 : 0);
        if (GetTickCount64() - start >= idle_ms) return 0;
        if (a->pending(a)) return 1;
        if (b && b->pending(b)) return 2;
    }
    return -1;
}

// Reads what is available from `io` into b. >0 bytes read, 0 = peer closed, -1 = error / timeout / stopping.
static int fill(PBIO *io, HBUF *b, DWORD idle_ms)
{
    if (!hb_reserve(b, HTTP_IO_CHUNK)) return -1;
    int n = io->read(io, b->p + b->len, HTTP_IO_CHUNK, idle_ms);
    if (n > 0) b->len += (size_t)n;
    return n;
}

// Reads until `in` holds a complete head. Returns the head length (including the blank line), 0 = peer closed before
// any byte of a head, -1 = error, -2 = head too large / peer closed mid-head.
static long read_head(PBIO *io, HBUF *in, DWORD idle_ms)
{
    for (;;)
    {
        const char *e = find_crlfcrlf(in->p ? in->p : "", in->len);
        if (e) return (long)(e - in->p) + 4;
        if (in->len >= HTTP_HEAD_MAX) return -2;
        int n = fill(io, in, idle_ms);
        if (n == 0) return in->len == 0 ? 0 : -2;
        if (n < 0) return -1;
    }
}

// Moves exactly `n` bytes from src (buffered bytes in `in` first) to dst. Bytes are also appended to `copy`
// (if given) while it stays under copy_max; *copy_total counts all of them.
static BOOL move_exact(PBIO *src, PBIO *dst, HBUF *in, unsigned long long n, HBUF *copy, size_t copy_max, unsigned long long *copy_total)
{
    while (n > 0)
    {
        if (in->len == 0)
        {
            int r = fill(src, in, HTTP_IDLE_BODY_MS);
            if (r <= 0) return FALSE;
        }
        size_t k = in->len < n ? in->len : (size_t)n;
        if (dst->write(dst, in->p, (int)k) != 0) return FALSE;
        if (copy && copy->len < copy_max) hb_append(copy, in->p, (copy_max - copy->len) < k ? (copy_max - copy->len) : k);
        if (copy_total) *copy_total += k;
        hb_consume(in, k);
        n -= k;
    }
    return TRUE;
}

// Reads one CRLF-terminated line into `in` (not consumed). Returns its length including CRLF, or -1.
static long need_line(PBIO *src, HBUF *in)
{
    for (;;)
    {
        const char *e = find_crlf(in->p ? in->p : "", in->len);
        if (e) return (long)(e - in->p) + 2;
        if (in->len > 8192) return -1;
        if (fill(src, in, HTTP_IDLE_BODY_MS) <= 0) return -1;
    }
}

// Moves a chunked body (chunks, last chunk, trailers) verbatim.
static BOOL move_chunked(PBIO *src, PBIO *dst, HBUF *in, HBUF *copy, size_t copy_max, unsigned long long *copy_total)
{
    for (;;)
    {
        long ll = need_line(src, in);
        if (ll < 0) return FALSE;
        char szs[32]; size_t k = 0;
        while (k < (size_t)ll && k + 1 < sizeof(szs) && isxdigit((unsigned char)in->p[k])) { szs[k] = in->p[k]; k++; }
        szs[k] = '\0';
        if (k == 0) return FALSE;
        unsigned long long size = _strtoui64(szs, NULL, 16);
        if (!move_exact(src, dst, in, (unsigned long long)ll, copy, copy_max, copy_total)) return FALSE;
        if (size == 0)
        {
            for (;;)                                       // trailers up to the empty line
            {
                ll = need_line(src, in);
                if (ll < 0) return FALSE;
                BOOL last = (ll == 2);
                if (!move_exact(src, dst, in, (unsigned long long)ll, copy, copy_max, copy_total)) return FALSE;
                if (last) return TRUE;
            }
        }
        if (!move_exact(src, dst, in, size + 2, copy, copy_max, copy_total)) return FALSE;
    }
}

// Everything until src closes.
static BOOL move_until_close(PBIO *src, PBIO *dst, HBUF *in, HBUF *copy, size_t copy_max, unsigned long long *copy_total)
{
    for (;;)
    {
        if (in->len > 0)
        {
            if (dst->write(dst, in->p, (int)in->len) != 0) return FALSE;
            if (copy && copy->len < copy_max) hb_append(copy, in->p, (copy_max - copy->len) < in->len ? (copy_max - copy->len) : in->len);
            if (copy_total) *copy_total += in->len;
            in->len = 0;
        }
        int r = fill(src, in, HTTP_IDLE_BODY_MS);
        if (r == 0) return TRUE;
        if (r < 0) return FALSE;
    }
}

static BOOL is_http_method_prefix(const char *p, size_t n, BOOL *complete)
{
    static const char *methods[] = { "GET ", "POST ", "HEAD ", "PUT ", "DELETE ", "OPTIONS ", "PATCH ", "TRACE ", "CONNECT ",
                                     "PROPFIND ", "PROPPATCH ", "MKCOL ", "COPY ", "MOVE ", "LOCK ", "UNLOCK ", "REPORT ", "SEARCH " };
    for (size_t i = 0; i < sizeof(methods) / sizeof(methods[0]); i++)
    {
        size_t ml = strlen(methods[i]);
        size_t k = n < ml ? n : ml;
        if (memcmp(p, methods[i], k) == 0) { *complete = n >= ml; return TRUE; }
    }
    return FALSE;
}

// Flushes whatever was buffered from each side, then hands the two streams on: raw streams go to the fast IOCP relay;
// TLS streams are pumped here as plaintext (re-encrypted per write). Destroys both PBIOs.
static void hand_off(PBIO *client, PBIO *proxy, HBUF *from_client, HBUF *from_proxy, const FLOW_META *meta)
{
    BOOL ok = TRUE;
    if (from_client && from_client->len > 0) ok = proxy->write(proxy, from_client->p, (int)from_client->len) == 0;
    if (ok && from_proxy && from_proxy->len > 0) ok = client->write(client, from_proxy->p, (int)from_proxy->len) == 0;
    if (!ok) { client->destroy(client, FALSE); proxy->destroy(proxy, FALSE); return; }
    if (!client->is_tls && !proxy->is_tls)
    {
        SOCKET cs = pbio_release_socket(client), ps = pbio_release_socket(proxy);
        client->destroy(client, FALSE); proxy->destroy(proxy, FALSE);
        DWORD zero = 0;
        setsockopt(cs, SOL_SOCKET, SO_SNDTIMEO, (char *)&zero, sizeof(zero));
        setsockopt(ps, SOL_SOCKET, SO_SNDTIMEO, (char *)&zero, sizeof(zero));
        relay_or_block(cs, ps, meta);
    }
    else
    {
        pbio_pump(client, proxy);
        client->destroy(client, TRUE); proxy->destroy(proxy, TRUE);
    }
}

static void close_both(PBIO *client, PBIO *proxy)
{
    client->destroy(client, TRUE);
    proxy->destroy(proxy, TRUE);
}

// ============================================================================================
// the HTTP session
// ============================================================================================
typedef struct {
    char   method[16];
    char   target[2048];
    char   version[16];
    int    minor;             // HTTP/1.<minor>
} REQLINE;

static BOOL parse_request_line(const char *head, size_t len, REQLINE *rl)
{
    const char *eol = find_crlf(head, len);
    if (eol == NULL) return FALSE;
    const char *sp1 = memchr(head, ' ', (size_t)(eol - head));
    if (sp1 == NULL || sp1 == head || (size_t)(sp1 - head) >= sizeof(rl->method)) return FALSE;
    const char *sp2 = sp1 + 1;
    while (sp2 < eol && *sp2 != ' ') sp2++;
    if (sp2 >= eol || (size_t)(sp2 - sp1 - 1) >= sizeof(rl->target) || sp2 == sp1 + 1) return FALSE;
    size_t vl = (size_t)(eol - sp2 - 1);
    if (vl >= sizeof(rl->version) || vl < 8 || memcmp(sp2 + 1, "HTTP/1.", 7) != 0) return FALSE;
    memcpy(rl->method, head, (size_t)(sp1 - head)); rl->method[sp1 - head] = '\0';
    memcpy(rl->target, sp1 + 1, (size_t)(sp2 - sp1 - 1)); rl->target[sp2 - sp1 - 1] = '\0';
    memcpy(rl->version, sp2 + 1, vl); rl->version[vl] = '\0';
    rl->minor = rl->version[7] - '0';
    return TRUE;
}

static BOOL wants_close(const char *head, size_t len, int minor)
{
    if (hdr_has_token(head, len, "Connection", "close")) return TRUE;
    if (minor == 0 && !hdr_has_token(head, len, "Connection", "keep-alive")) return TRUE;
    return FALSE;
}

typedef enum { BODY_NONE, BODY_LENGTH, BODY_CHUNKED, BODY_CLOSE, BODY_BAD } BODY_KIND;

static BODY_KIND body_kind(const char *head, size_t len, BOOL is_request, unsigned long long *clen)
{
    char v[256];
    *clen = 0;
    if (hdr_get(head, len, "Transfer-Encoding", v, sizeof(v)))
    {
        if (tok_has(v, "chunked", NULL, 0)) return BODY_CHUNKED;
        return is_request ? BODY_BAD : BODY_CLOSE;
    }
    if (hdr_get(head, len, "Content-Length", v, sizeof(v)))
    {
        char *end = NULL;
        if (strchr(v, ',') != NULL) return BODY_BAD;        // repeated Content-Length: not handled here
        if (v[0] < '0' || v[0] > '9') return BODY_BAD;
        *clen = _strtoui64(v, &end, 10);
        if (end == NULL || *end != '\0') return BODY_BAD;
        return *clen ? BODY_LENGTH : BODY_NONE;
    }
    return is_request ? BODY_NONE : BODY_CLOSE;
}

// Builds the cache key; FALSE if the request must bypass the cache entirely.
static BOOL cache_key_for(const char *head, size_t len, const REQLINE *rl, const HSESS *s, char *key, size_t keysz, BOOL *may_lookup)
{
    char v[1024], host[512], ae[256];
    *may_lookup = TRUE;
    if (strcmp(rl->method, "GET") != 0) return FALSE;
    if (hdr_get(head, len, "Authorization", v, sizeof(v)) || hdr_get(head, len, "Range", v, sizeof(v))) return FALSE;
    if (hdr_get(head, len, "Cache-Control", v, sizeof(v)))
    {
        if (tok_has(v, "no-store", NULL, 0)) return FALSE;
        if (tok_has(v, "no-cache", NULL, 0) || tok_has(v, "max-age=0", NULL, 0)) *may_lookup = FALSE;
    }
    if (hdr_has_token(head, len, "Pragma", "no-cache")) *may_lookup = FALSE;
    if (!hdr_get(head, len, "Accept-Encoding", ae, sizeof(ae))) ae[0] = '\0';
    if (_strnicmp(rl->target, "http://", 7) == 0)
        snprintf(key, keysz, "GET %s\n%s", rl->target, ae);
    else
    {
        if (!hdr_get(head, len, "Host", host, sizeof(host)) || host[0] == '\0')
            snprintf(host, sizeof(host), "%s", s->dest);
        for (char *p = host; *p; p++) *p = (char)tolower((unsigned char)*p);
        snprintf(key, keysz, "GET http://%s%s\n%s", host, rl->target, ae);
    }
    return TRUE;
}

static void request_url(const char *head, size_t len, const REQLINE *rl, const HSESS *s, char *out, size_t n)
{
    char host[512];
    if (rl->target[0] != '/') { snprintf(out, n, "%s", rl->target); return; }
    if (!hdr_get(head, len, "Host", host, sizeof(host)) || host[0] == '\0') snprintf(host, sizeof(host), "%s", s->dest);
    snprintf(out, n, "http://%s%s", host, rl->target);
}

static void log_request(const HSESS *s, const char *head, size_t head_len, const HBUF *body, unsigned long long body_total, const char *note)
{
    if (!g_req_log_enabled) return;
    HBUF b = {0};
    entry_header(&b, s, "HTTP request");
    hb_append(&b, head, head_len);
    append_body(&b, body->p ? body->p : "", body->len, body_total);
    if (note) { hb_puts(&b, note); hb_puts(&b, "\r\n"); }
    reqlog_write(b.p, b.len);
    hb_free(&b);
}

static void log_response(const HSESS *s, const char *status_line, size_t sl_len, const char *cache, unsigned long long body_len, BOOL body_known)
{
    if (!g_req_log_enabled) return;
    char line[700], st[400];
    size_t k = sl_len < sizeof(st) - 1 ? sl_len : sizeof(st) - 1;
    memcpy(st, status_line, k); st[k] = '\0';
    if (body_known)
        snprintf(line, sizeof(line), "<<<<< #%u response: %s | cache: %s | body %llu bytes\r\n", s->id, st, cache, body_len);
    else
        snprintf(line, sizeof(line), "<<<<< #%u response: %s | cache: %s\r\n", s->id, st, cache);
    reqlog_write(line, strlen(line));
}

// Runs the request/response engine over two plaintext streams (raw sockets or decrypted TLS). Owns both PBIOs.
// `cin_init`, if given, holds bytes already read from the application (the start of its first request); it is moved in.
static void run_http(PBIO *client, PBIO *proxy, const FLOW_META *meta, HBUF *cin_init)
{
    HSESS s; ZeroMemory(&s, sizeof(s));
    HBUF cin = {0}, pin = {0};               // plaintext read from the application / from the proxy, not yet forwarded
    if (cin_init && cin_init->len) { cin = *cin_init; cin_init->p = NULL; cin_init->len = cin_init->cap = 0; }

    sess_describe(&s, meta);
    BOOL first = TRUE;
    for (;;)
    {
        // ---------------- request ----------------
        if (!first && cin.len == 0)
        {
            // Between requests: watch the proxy too, so a server-side close is passed on promptly.
            int r = wait_readable(client, proxy, HTTP_IDLE_KEEPALIVE_MS);
            if (r <= 0) break;
            if (r & 2)
            {
                int n = fill(proxy, &pin, 1000);
                if (n <= 0) break;                          // server closed the kept-alive connection
                hand_off(client, proxy, &cin, &pin, meta);  // unsolicited bytes: not a plain exchange any more
                goto done;
            }
        }
        first = FALSE;
        long hl = read_head(client, &cin, HTTP_IDLE_KEEPALIVE_MS);
        if (hl == 0) break;                                  // application closed between requests
        if (hl < 0) { hand_off(client, proxy, &cin, NULL, meta); goto done; }

        REQLINE rl;
        char *head = cin.p;
        if (!parse_request_line(head, (size_t)hl, &rl)) { hand_off(client, proxy, &cin, NULL, meta); goto done; }

        unsigned long long clen = 0;
        BODY_KIND bk = body_kind(head, (size_t)hl, TRUE, &clen);
        char upg[64];
        BOOL tunnel = _stricmp(rl.method, "CONNECT") == 0 || hdr_get(head, (size_t)hl, "Upgrade", upg, sizeof(upg)) ||
                      (bk != BODY_NONE && hdr_has_token(head, (size_t)hl, "Expect", "100-continue")) || bk == BODY_BAD;
        if (tunnel)
        {
            HBUF none = {0};
            log_request(&s, head, (size_t)hl, &none, 0,
                        "[protocol switch / tunnel / 100-continue: the rest of this connection is relayed unchanged and not logged]");
            hand_off(client, proxy, &cin, NULL, meta);
            goto done;
        }
        BOOL req_close = wants_close(head, (size_t)hl, rl.minor);
        BOOL is_head = _stricmp(rl.method, "HEAD") == 0;

        // Cache lookup (GET without a body only).
        char key[3072]; BOOL may_lookup = FALSE;
        BOOL cacheable_req = g_resp_cache_enabled && bk == BODY_NONE &&
                             cache_key_for(head, (size_t)hl, &rl, &s, key, sizeof(key), &may_lookup);
        if (cacheable_req && may_lookup)
        {
            char *ch = NULL, *cb = NULL; size_t chl = 0, cbl = 0; ULONGLONG age = 0;
            if (cache_lookup(key, &ch, &chl, &cb, &cbl, &age))
            {
                HBUF none = {0};
                log_request(&s, head, (size_t)hl, &none, 0, NULL);
                char extra[160];
                snprintf(extra, sizeof(extra), "Age: %llu\r\nX-ProxyBridge-Cache: HIT\r\nConnection: %s\r\n\r\n",
                         (unsigned long long)age, req_close ? "close" : "keep-alive");
                HBUF out = {0};
                BOOL ok = hb_append(&out, ch, chl) && hb_puts(&out, extra) && hb_append(&out, cb, cbl);
                const char *sle = find_crlf(ch, chl);
                log_response(&s, ch, sle ? (size_t)(sle - ch) : chl, "HIT", cbl, TRUE);
                char url[2200];
                request_url(head, (size_t)hl, &rl, &s, url, sizeof(url));
                log_message("[CACHE] HIT %s %s (%zu bytes) for %s", rl.method, url, cbl, s.proc);
                hb_consume(&cin, (size_t)hl);
                ok = ok && client->write(client, out.p, (int)out.len) == 0;
                hb_free(&out); free(ch); free(cb);
                if (!ok || req_close) break;
                continue;
            }
        }

        // Forward the head, then stream the body (a copy goes to the log).
        if (proxy->write(proxy, head, (int)hl) != 0) break;
        HBUF reqhead = {0};
        if (g_req_log_enabled) hb_append(&reqhead, head, (size_t)hl);
        hb_consume(&cin, (size_t)hl);
        HBUF reqbody = {0}; unsigned long long reqtotal = 0;
        BOOL ok = TRUE;
        HBUF *copy = g_req_log_enabled ? &reqbody : NULL;
        if (bk == BODY_LENGTH)       ok = move_exact(client, proxy, &cin, clen, copy, REQ_LOG_BODY_MAX, &reqtotal);
        else if (bk == BODY_CHUNKED) ok = move_chunked(client, proxy, &cin, copy, REQ_LOG_BODY_MAX, &reqtotal);
        if (g_req_log_enabled) log_request(&s, reqhead.p ? reqhead.p : "", reqhead.len, &reqbody, reqtotal, ok ? NULL : "[request body incomplete: connection failed]");
        hb_free(&reqhead); hb_free(&reqbody);
        if (!ok) break;

        // ---------------- response ----------------
        long rhl;
        int status = 0;
        for (;;)
        {
            rhl = read_head(proxy, &pin, HTTP_IDLE_RESPONSE_MS);
            if (rhl <= 0) break;
            if (rhl < 12 || memcmp(pin.p, "HTTP/1.", 7) != 0) { rhl = -2; break; }
            status = atoi(pin.p + 9);
            if (status >= 100 && status < 200 && status != 101)
            {
                if (client->write(client, pin.p, (int)rhl) != 0) { rhl = -1; break; }
                hb_consume(&pin, (size_t)rhl);
                continue;                                    // interim response: the final one follows
            }
            break;
        }
        if (rhl == 0) break;                                 // proxy closed without answering
        if (rhl < 0) { hand_off(client, proxy, &cin, &pin, meta); goto done; }

        const char *rh = pin.p;
        const char *sle = find_crlf(rh, (size_t)rhl);
        size_t sl_len = sle ? (size_t)(sle - rh) : (size_t)rhl;
        int rminor = rh[7] - '0';
        if (status == 101)
        {
            log_response(&s, rh, sl_len, "-", 0, FALSE);
            hand_off(client, proxy, &cin, &pin, meta);
            goto done;
        }

        unsigned long long rlen = 0;
        BODY_KIND rbk = (is_head || status == 204 || status == 304) ? BODY_NONE : body_kind(rh, (size_t)rhl, FALSE, &rlen);
        if (rbk == BODY_BAD) { hand_off(client, proxy, &cin, &pin, meta); goto done; }
        BOOL resp_close = wants_close(rh, (size_t)rhl, rminor) || rbk == BODY_CLOSE;

        UINT32 ttl = 0;
        if (cacheable_req && (rbk == BODY_LENGTH || (rbk == BODY_NONE && !is_head && status != 304 && status != 204)) &&
            rlen + (unsigned long long)rhl <= RESP_CACHE_MAX_ENTRY)
            ttl = response_ttl(rh, (size_t)rhl, status);

        char *cache_head = NULL; size_t cache_head_len = 0;
        if (ttl) cache_head = head_for_cache(rh, (size_t)rhl - 2, &cache_head_len);
        char statusline[400];
        size_t sk = sl_len < sizeof(statusline) - 1 ? sl_len : sizeof(statusline) - 1;
        memcpy(statusline, rh, sk); statusline[sk] = '\0';

        if (client->write(client, rh, (int)rhl) != 0) { free(cache_head); break; }
        hb_consume(&pin, (size_t)rhl);

        HBUF rbody = {0}; unsigned long long rtotal = 0;
        HBUF *rcopy = cache_head ? &rbody : NULL;
        if (rbk == BODY_LENGTH)       ok = move_exact(proxy, client, &pin, rlen, rcopy, RESP_CACHE_MAX_ENTRY, &rtotal);
        else if (rbk == BODY_CHUNKED) ok = move_chunked(proxy, client, &pin, NULL, 0, &rtotal);
        else if (rbk == BODY_CLOSE)   ok = move_until_close(proxy, client, &pin, NULL, 0, &rtotal);

        const char *cstate = !cacheable_req ? "BYPASS" : (cache_head && ok) ? "MISS, stored" : "MISS";
        log_response(&s, statusline, strlen(statusline), g_resp_cache_enabled ? cstate : "off", rtotal, TRUE);
        if (cache_head && ok && rtotal == rlen)
        {
            char *body = rbody.p ? rbody.p : (char *)malloc(1);
            size_t blen = rbody.len;
            rbody.p = NULL;
            cache_store(key, cache_head, cache_head_len, body, blen, ttl);
            cache_head = NULL;
        }
        free(cache_head);
        hb_free(&rbody);
        if (!ok || req_close || resp_close) break;
    }
    close_both(client, proxy);
done:
    hb_free(&cin); hb_free(&pin);
}

// Reads the first bytes the application sends on a raw socket (no PBIO yet), then either intercepts TLS (HTTPS),
// runs the plain-HTTP engine, or hands the connection to the relay unchanged. Takes ownership of both sockets.
static int raw_wait_two(SOCKET a, SOCKET b, DWORD idle_ms)   // 1=a, 2=b, 3=both, 0=timeout, -1=stop/error
{
    ULONGLONG start = GetTickCount64();
    while (running)
    {
        fd_set rf; FD_ZERO(&rf); FD_SET(a, &rf); if (b != INVALID_SOCKET) FD_SET(b, &rf);
        struct timeval tv = { 1, 0 };
        int r = select(0, &rf, NULL, NULL, &tv);
        if (r == SOCKET_ERROR) return -1;
        if (r > 0) return (FD_ISSET(a, &rf) ? 1 : 0) | ((b != INVALID_SOCKET && FD_ISSET(b, &rf)) ? 2 : 0);
        if (GetTickCount64() - start >= idle_ms) return 0;
    }
    return -1;
}

void http_inspect_session(SOCKET client, SOCKET proxy, const FLOW_META *meta)
{
    DWORD snd = 30000;                       // a stuck peer must not hold this thread forever
    setsockopt(client, SOL_SOCKET, SO_SNDTIMEO, (char *)&snd, sizeof(snd));
    setsockopt(proxy, SOL_SOCKET, SO_SNDTIMEO, (char *)&snd, sizeof(snd));

    // Who speaks first? Only an application that opens the connection is inspected.
    int w = raw_wait_two(client, proxy, HTTP_IDLE_KEEPALIVE_MS);
    if (w <= 0) { relay_or_block(client, proxy, meta); return; }
    if (w & 2)
    {
        if (g_req_log_enabled) { HSESS s; sess_describe(&s, meta); reqlog_non_http(&s, NULL, 0, TRUE); }
        relay_or_block(client, proxy, meta);
        return;
    }

    // Peek the application's opening bytes to classify the connection (HTTP / TLS / other).
    HBUF cin = {0};
    for (;;)
    {
        if (raw_wait_two(client, INVALID_SOCKET, 5000) != 1) break;
        if (!hb_reserve(&cin, HTTP_IO_CHUNK)) break;
        int n = recv(client, cin.p + cin.len, HTTP_IO_CHUNK, 0);
        if (n <= 0) break;
        cin.len += (size_t)n;
        if (cin.len >= 3 && (unsigned char)cin.p[0] == 0x16 && (unsigned char)cin.p[1] == 0x03) break;   // TLS record
        BOOL complete = FALSE;
        if (!is_http_method_prefix(cin.p, cin.len, &complete) || complete) break;
    }

    BOOL is_tls = cin.len >= 3 && (unsigned char)cin.p[0] == 0x16 && (unsigned char)cin.p[1] == 0x03;

    // HTTPS interception: terminate the app's TLS with a minted cert, open our own TLS to the origin.
    if (is_tls && g_https_intercept_enabled)
    {
        char sni[256];
        if (!tls_sni((const unsigned char *)cin.p, cin.len, sni, sizeof(sni)))
        {
            sni[0] = '\0';                   // no SNI: fall back to the destination domain, else leave empty (cert CN = IP)
            if (meta->v6) dns_cache_lookup_v6(meta->dest, sni, sizeof(sni));
            else { UINT32 v4; memcpy(&v4, meta->dest, 4); dns_cache_lookup(v4, sni, sizeof(sni)); }
        }
        PBIO *cio = pb_tls_accept(client, sni, cin.p, (int)cin.len);   // consumes `client` and the ClientHello
        hb_free(&cin);
        if (cio == NULL) { closesocket(proxy); return; }
        PBIO *pio = pb_tls_connect(proxy, sni);
        if (pio == NULL) { cio->destroy(cio, TRUE); return; }
        run_http(cio, pio, meta, NULL);
        return;
    }

    // Not interceptable HTTP: log what can be seen (TLS SNI, or a hex dump) and relay the raw stream unchanged.
    BOOL complete = FALSE;
    if (is_tls || cin.len == 0 || !is_http_method_prefix(cin.p, cin.len, &complete) || !complete)
    {
        if (g_req_log_enabled && cin.len > 0) { HSESS s; sess_describe(&s, meta); reqlog_non_http(&s, cin.p, cin.len, FALSE); }
        if (cin.len > 0 && send_all(proxy, cin.p, (int)cin.len) == SOCKET_ERROR) { hb_free(&cin); closesocket(client); closesocket(proxy); return; }
        hb_free(&cin);
        relay_or_block(client, proxy, meta);
        return;
    }

    // Plain HTTP: run the engine over raw-socket PBIOs (fast IOCP relay still available for hand-off).
    PBIO *cio = pbio_socket(client);
    PBIO *pio = cio ? pbio_socket(proxy) : NULL;
    if (cio == NULL || pio == NULL)
    {
        if (cio) cio->destroy(cio, FALSE); else closesocket(client);
        if (pio) pio->destroy(pio, FALSE); else closesocket(proxy);
        hb_free(&cin);
        return;
    }
    run_http(cio, pio, meta, &cin);
    hb_free(&cin);
}

// ============================================================================================
// public API
// ============================================================================================
PROXYBRIDGE_API void ProxyBridge_SetResponseCacheEnabled(BOOL enable)
{
    BOOL was = g_resp_cache_enabled;
    g_resp_cache_enabled = enable ? TRUE : FALSE;
    if (!enable) resp_cache_clear();
    if (was != g_resp_cache_enabled)
        log_message(enable ? "Response cache on: cacheable plain-HTTP responses are kept in memory (HTTPS cannot be cached)"
                           : "Response cache off (cache emptied)");
}

PROXYBRIDGE_API void ProxyBridge_ClearResponseCache(void)
{
    resp_cache_clear();
}

PROXYBRIDGE_API void ProxyBridge_GetResponseCacheStats(UINT32 *entries, UINT64 *bytes)
{
    AcquireSRWLockShared(&g_cache_lock);
    if (entries) *entries = g_cache_count;
    if (bytes) *bytes = (UINT64)g_cache_bytes;
    ReleaseSRWLockShared(&g_cache_lock);
}

PROXYBRIDGE_API void ProxyBridge_SetRequestLoggingEnabled(BOOL enable)
{
    BOOL was = g_req_log_enabled;
    g_req_log_enabled = enable ? TRUE : FALSE;
    if (!enable) reqlog_close();
    if (was != g_req_log_enabled)
    {
        if (enable)
        {
            char path[MAX_PATH * 3];
            ProxyBridge_GetRequestLogPath(path, sizeof(path));
            log_message("Request logging on: every request is written in full to %s", path);
        }
        else log_message("Request logging off");
    }
}

PROXYBRIDGE_API BOOL ProxyBridge_GetRequestLogPath(char *buffer, size_t size)
{
    if (buffer == NULL || size == 0) return FALSE;
    wchar_t w[MAX_PATH + 64];
    reqlog_path_w(w, MAX_PATH + 64, FALSE);
    int n = WideCharToMultiByte(CP_UTF8, 0, w, -1, buffer, (int)(size > 0x7fffffff ? 0x7fffffff : size), NULL, NULL);
    if (n <= 0) { buffer[0] = '\0'; return FALSE; }
    return TRUE;
}

PROXYBRIDGE_API void ProxyBridge_SetHttpsInterceptEnabled(BOOL enable)
{
    BOOL was = g_https_intercept_enabled;
    if (enable && !pb_tls_ensure_ca())
    {
        g_https_intercept_enabled = FALSE;
        log_message("HTTPS interception: could not set up the ProxyBridge CA; proxied HTTPS stays encrypted");
        return;
    }
    g_https_intercept_enabled = enable ? TRUE : FALSE;
    if (was != g_https_intercept_enabled)
        log_message(enable ? "HTTPS interception on: proxied HTTPS is decrypted for the cache / request log (applications must trust the ProxyBridge CA)"
                           : "HTTPS interception off: proxied HTTPS passes through encrypted");
}

PROXYBRIDGE_API int ProxyBridge_InstallTlsCertificate(void)
{
    return pb_tls_install_ca();
}

PROXYBRIDGE_API BOOL ProxyBridge_GetTlsCertificatePath(char *buffer, size_t size)
{
    if (pb_tls_ensure_ca()) pb_tls_ensure_exported();
    return pb_tls_ca_cert_path(buffer, size);
}
