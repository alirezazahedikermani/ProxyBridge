// test_httpcache.c - the response cache and the full request log (pb_httpcache.c), linked from the real core sources.
// A fake origin server stands in for the proxy tunnel; each "intercepted connection" is a real loopback socket pair
// driven by http_inspect_session(), and non-HTTP connections go to the real IOCP relay.
//   - GET responses are cached (per Accept-Encoding) and served with X-ProxyBridge-Cache: HIT, across connections
//   - no-store responses / no-cache requests / POST bypass the cache; turning the cache off empties it
//   - bodies (Content-Length, chunked + trailers, close-delimited), 1xx, HEAD keep the exchange in sync
//   - Connection: close is honoured; non-HTTP (TLS) streams are relayed unchanged
//   - the request log holds the complete request (head + body), the response status and the cache state
#include "pb_internal.h"
#include "pbtest.h"

static int g_head_req = 0;
static char r[200000];
// ---------------- fake origin ----------------
static SOCKET g_origin_l; static int g_origin_port; volatile LONG g_hits = 0;
static int rd_head(SOCKET s, char *buf, int cap)
{
    int len = 0;
    while (len < cap - 1) { int n = recv(s, buf + len, 1, 0); if (n <= 0) return -1; len += n; buf[len] = 0; if (len >= 4 && !memcmp(buf + len - 4, "\r\n\r\n", 4)) return len; }
    return -1;
}
static DWORD WINAPI origin_conn(LPVOID p)
{
    SOCKET s = (SOCKET)(ULONG_PTR)p; char h[8192], r[8192], body[100000];
    while (rd_head(s, h, sizeof h) > 0)
    {
        LONG n = InterlockedIncrement(&g_hits);
        char *cl = strstr(h, "Content-Length: "); int blen = cl ? atoi(cl + 16) : 0;
        for (int got = 0; got < blen; ) { int k = recv(s, body + got, blen - got, 0); if (k <= 0) return 0; got += k; }
        if (strstr(h, "Transfer-Encoding: chunked")) {   // read chunked request
            char line[64]; int L;
            for (;;) { L = 0; while (recv(s, line + L, 1, 0) == 1 && !(L > 0 && line[L] == '\n')) L++; int sz = strtol(line, NULL, 16);
                       char tmp[4096]; int need = sz + 2; while (need > 0) { int k = recv(s, tmp, need > 4096 ? 4096 : need, 0); if (k <= 0) return 0; need -= k; }
                       if (sz == 0) break; }
            blen = -1;
        }
        char b[256];
        if (!strncmp(h, "GET /c ", 7)) { snprintf(b, sizeof b, "hello-%ld", n);
            snprintf(r, sizeof r, "HTTP/1.1 200 OK\r\nCache-Control: max-age=60\r\nContent-Length: %d\r\nConnection: keep-alive\r\n\r\n%s", (int)strlen(b), b); }
        else if (!strncmp(h, "GET /nc ", 8)) { snprintf(b, sizeof b, "nc-%ld", n);
            snprintf(r, sizeof r, "HTTP/1.1 200 OK\r\nCache-Control: no-store\r\nContent-Length: %d\r\n\r\n%s", (int)strlen(b), b); }
        else if (!strncmp(h, "GET /chunk ", 11)) {
            snprintf(r, sizeof r, "HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nabcde\r\n3\r\nfgh\r\n0\r\nX-T: 1\r\n\r\n"); }
        else if (!strncmp(h, "HEAD ", 5)) snprintf(r, sizeof r, "HTTP/1.1 200 OK\r\nContent-Length: 999\r\n\r\n");
        else if (!strncmp(h, "POST ", 5)) { snprintf(b, sizeof b, "posted-%d", blen);
            snprintf(r, sizeof r, "HTTP/1.1 201 Created\r\nContent-Length: %d\r\n\r\n%s", (int)strlen(b), b); }
        else if (!strncmp(h, "GET /close ", 11)) { snprintf(r, sizeof r, "HTTP/1.0 200 OK\r\n\r\nuntil-close-body"); send_all(s, r, (int)strlen(r)); closesocket(s); return 0; }
        else snprintf(r, sizeof r, "HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n");
        send_all(s, r, (int)strlen(r));
    }
    closesocket(s); return 0;
}
static DWORD WINAPI origin_accept(LPVOID p)
{
    for (;;) { SOCKET s = accept(g_origin_l, NULL, NULL); if (s == INVALID_SOCKET) return 0; CloseHandle(CreateThread(NULL, 0, origin_conn, (LPVOID)(ULONG_PTR)s, 0, NULL)); }
}
static SOCKET listen_any(int *port)
{
    SOCKET l = socket(AF_INET, SOCK_STREAM, 0); struct sockaddr_in a = {0}; a.sin_family = AF_INET; a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    bind(l, (struct sockaddr*)&a, sizeof a); listen(l, 16); int al = sizeof a; getsockname(l, (struct sockaddr*)&a, &al); *port = ntohs(a.sin_port); return l;
}
static SOCKET dial(int port) { SOCKET s = socket(AF_INET, SOCK_STREAM, 0); struct sockaddr_in a = {0}; a.sin_family = AF_INET; a.sin_addr.s_addr = htonl(INADDR_LOOPBACK); a.sin_port = htons(port); if (connect(s, (struct sockaddr*)&a, sizeof a)) return INVALID_SOCKET; return s; }

// One "intercepted connection": app <-> [session] <-> origin
typedef struct { SOCKET c, p; } SESS;
static DWORD WINAPI sess_thread(LPVOID x) { SESS *s = x; FLOW_META m; ZeroMemory(&m, sizeof(m)); m.pid = GetCurrentProcessId(); m.proxy_id = 1; m.port = 80; m.dest[0] = 10; m.dest[3] = 1; http_inspect_session(s->c, s->p, &m); free(s); return 0; }
static SOCKET open_app_conn(void)
{
    static SOCKET l = INVALID_SOCKET; static int lp;
    if (l == INVALID_SOCKET) l = listen_any(&lp);
    SOCKET app = dial(lp); SOCKET c = accept(l, NULL, NULL);
    SESS *s = malloc(sizeof *s); s->c = c; s->p = dial(g_origin_port);
    CloseHandle(CreateThread(NULL, 0, sess_thread, s, 0, NULL));
    DWORD to = 5000; setsockopt(app, SOL_SOCKET, SO_RCVTIMEO, (char*)&to, sizeof to);
    return app;
}
// reads one response: head + Content-Length body (or chunked till 0\r\n...\r\n\r\n, or until close)
static int read_resp(SOCKET s, char *out, int cap)
{
    int len = 0;
    for (;;) {
        char *e = len >= 4 ? strstr(out, "\r\n\r\n") : NULL;
        if (e) {
            while (!strncmp(out, "HTTP/1.1 100", 12)) { int hl = (int)(e - out) + 4; memmove(out, out + hl, len - hl + 1); len -= hl; e = strstr(out, "\r\n\r\n"); if (!e) break; }
            if (e) {
            int hl = (int)(e - out) + 4; char *cl = strstr(out, "Content-Length: ");
            if (cl && cl < e) { int need = hl + atoi(cl + 16); if (g_head_req) need = hl; if (len >= need) return need; }
            else if (strstr(out, "chunked")) { if (strstr(e + 4, "0\r\nX-T: 1\r\n\r\n")) return len; }
            }
        }
        int n = recv(s, out + len, cap - 1 - len, 0);
        if (n <= 0) return len;
        len += n; out[len] = 0;
    }
}
static void req(SOCKET s, const char *q, char *resp) { send_all(s, q, (int)strlen(q)); int n = read_resp(s, resp, 200000); resp[n] = 0; }
#define EXPECT(c, msg) do { CHECK(c); if (!(c)) printf("    (%s)\n%s\n", msg, r); } while (0)

int main(void)
{
    WSADATA w; WSAStartup(MAKEWORD(2, 2), &w);
    running = TRUE;
    CHECK(relay_pool_start());
    dns_cache_init();
    { struct in_addr ia; inet_pton(AF_INET, "10.0.0.1", &ia); dns_cache_store(ia.S_un.S_addr, "example.test"); }
    char path[600]; ProxyBridge_GetRequestLogPath(path, sizeof path);
    { wchar_t wp[600]; MultiByteToWideChar(CP_UTF8, 0, path, -1, wp, 600); DeleteFileW(wp); }
    g_origin_l = listen_any(&g_origin_port);
    CloseHandle(CreateThread(NULL, 0, origin_accept, NULL, 0, NULL));
    ProxyBridge_SetResponseCacheEnabled(TRUE);
    ProxyBridge_SetRequestLoggingEnabled(TRUE);

    SOCKET a = open_app_conn();
    req(a, "GET /c HTTP/1.1\r\nHost: Example.Test\r\nAccept-Encoding: gzip\r\n\r\n", r);
    EXPECT(strstr(r, "hello-1") && !strstr(r, "X-ProxyBridge-Cache"), "first GET goes to origin");
    req(a, "GET /c HTTP/1.1\r\nHost: example.test\r\nAccept-Encoding: gzip\r\n\r\n", r);
    EXPECT(strstr(r, "hello-1") && strstr(r, "X-ProxyBridge-Cache: HIT") && strstr(r, "Content-Length: 7"), "second GET on same keep-alive connection is a cache HIT");
    req(a, "GET /c HTTP/1.1\r\nHost: example.test\r\nAccept-Encoding: br\r\n\r\n", r);
    EXPECT(strstr(r, "hello-2") && !strstr(r, "HIT"), "different Accept-Encoding is a separate entry");
    req(a, "GET /c HTTP/1.1\r\nHost: example.test\r\nAccept-Encoding: gzip\r\nCache-Control: no-cache\r\n\r\n", r);
    EXPECT(strstr(r, "hello-3") && !strstr(r, "HIT"), "request no-cache bypasses lookup");
    req(a, "GET /nc HTTP/1.1\r\nHost: example.test\r\n\r\n", r);
    req(a, "GET /nc HTTP/1.1\r\nHost: example.test\r\n\r\n", r);
    EXPECT(strstr(r, "nc-5") && !strstr(r, "HIT"), "no-store response is not cached");
    req(a, "POST /p HTTP/1.1\r\nHost: example.test\r\nContent-Length: 11\r\n\r\nhello=world", r);
    EXPECT(strstr(r, "posted-11"), "POST with body is forwarded");
    req(a, "POST /p HTTP/1.1\r\nHost: example.test\r\nTransfer-Encoding: chunked\r\n\r\n4\r\nabcd\r\n0\r\n\r\n", r);
    EXPECT(strstr(r, "posted--1"), "chunked POST is forwarded");
    req(a, "GET /chunk HTTP/1.1\r\nHost: example.test\r\n\r\n", r);
    EXPECT(strstr(r, "5\r\nabcde\r\n3\r\nfgh\r\n0\r\nX-T: 1\r\n\r\n"), "1xx + chunked response with trailers relayed verbatim");
    g_head_req = 1; req(a, "HEAD /h HTTP/1.1\r\nHost: example.test\r\nX-Mark: HEAD-REQ\r\n\r\n", r);
    EXPECT(strstr(r, "Content-Length: 999"), "HEAD response (no body) handled"); g_head_req = 0;
    req(a, "GET /c HTTP/1.1\r\nHost: example.test\r\nAccept-Encoding: gzip\r\n\r\n", r);
    EXPECT(strstr(r, "HIT"), "connection still in sync after HEAD");
    closesocket(a);

    SOCKET b = open_app_conn();
    req(b, "GET http://example.test/c HTTP/1.1\r\nHost: example.test\r\nAccept-Encoding: gzip\r\nConnection: close\r\n\r\n", r);
    EXPECT(strstr(r, "hello-3") && strstr(r, "HIT") && strstr(r, "Connection: close"), "new connection, absolute-form URL: HIT");
    char x[10]; int n = recv(b, x, sizeof x, 0);
    EXPECT(n == 0, "Connection: close honoured on HIT");
    closesocket(b);

    SOCKET c = open_app_conn();
    req(c, "GET /close HTTP/1.0\r\nHost: example.test\r\n\r\n", r);
    EXPECT(strstr(r, "until-close-body"), "close-delimited response");
    closesocket(c);

    /* non-HTTP: relayed unchanged by the real relay (the origin answers garbage with nothing and closes) */
    SOCKET d = open_app_conn();
    const char tls[] = "\x16\x03\x01\x00\x10" "not really tls!!\r\n\r\n";
    send_all(d, tls, sizeof(tls) - 1);
    r[0] = 0; int dn = recv(d, r, 100, 0);
    EXPECT(dn >= 0 && strstr(r, "404") != NULL, "non-HTTP stream reaches the server unchanged");
    closesocket(d);

    ProxyBridge_SetResponseCacheEnabled(FALSE);
    SOCKET e = open_app_conn();
    req(e, "GET /c HTTP/1.1\r\nHost: example.test\r\nAccept-Encoding: gzip\r\n\r\n", r);
    EXPECT(!strstr(r, "HIT"), "cache off: emptied and not used");
    closesocket(e);

    Sleep(300);
    ProxyBridge_SetRequestLoggingEnabled(FALSE);
    FILE *f = fopen(path, "rb"); static char logb[400000]; size_t ln = f ? fread(logb, 1, sizeof logb - 1, f) : 0; if (f) fclose(f); logb[ln] = 0;
    EXPECT(strstr(logb, "hello=world") && strstr(logb, "POST /p HTTP/1.1") && strstr(logb, "test_httpcache.exe (PID "), "request log has full POST with body");
    EXPECT(strstr(logb, "cache: HIT") && strstr(logb, "MISS, stored") && strstr(logb, "TLS ClientHello"), "request log has cache states and TLS entry");
    running = FALSE;
    relay_pool_stop();
    return pbtest_done("test_httpcache");
}
