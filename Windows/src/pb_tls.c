#include "pb_internal.h"
#define SECURITY_WIN32
#include <security.h>
#include <schannel.h>

// ============================================================================================
// HTTPS interception (TLS man-in-the-middle) for the response cache and the full request log.
//
// When HTTPS interception is on, a proxied TLS connection is split in two by http_inspect_session:
//   application  <--TLS-->  ProxyBridge  <--TLS-->  (proxy)  -->  origin server
// ProxyBridge terminates the application's TLS using a certificate it mints on the fly for the
// requested host, signed by a local ProxyBridge root CA, and opens its own real TLS connection to
// the origin (through the same proxy tunnel), validating the origin's certificate normally. The
// decrypted bytes in the middle are the plain HTTP that the cache and the request log already
// understand, so the exact same engine runs over a PBIO backed by SChannel instead of a raw socket.
//
// For any of this to work the user must trust the ProxyBridge root CA (Settings -> Decrypt HTTPS ->
// Install Certificate, or import the exported .crt). Without that, applications reject the minted
// certificate - exactly as they should for traffic they have not been told to trust.
//
// The CA private key and one shared leaf key live in the machine key set; the CA certificate is kept
// in a persistent "ProxyBridge" system store and exported to %ProgramData%\ProxyBridge\ca so it can
// be installed. Everything here is Win32 only (SChannel + CryptoAPI); there is no external dependency.
// ============================================================================================

#pragma comment(lib, "secur32.lib")
#pragma comment(lib, "crypt32.lib")

#define TLS_CA_CONTAINER   L"ProxyBridge CA Key"
#define TLS_LEAF_CONTAINER L"ProxyBridge Leaf Key"
#define TLS_STORE_NAME     L"ProxyBridge"
#define TLS_CA_CN          "ProxyBridge Local Root CA"
#define TLS_IO_CHUNK       16384
#define TLS_LEAF_CACHE_MAX 2048

static const int g_asc_req = ASC_REQ_SEQUENCE_DETECT | ASC_REQ_REPLAY_DETECT | ASC_REQ_CONFIDENTIALITY |
                             ASC_REQ_EXTENDED_ERROR | ASC_REQ_ALLOCATE_MEMORY | ASC_REQ_STREAM;
static const int g_isc_req = ISC_REQ_SEQUENCE_DETECT | ISC_REQ_REPLAY_DETECT | ISC_REQ_CONFIDENTIALITY |
                             ISC_REQ_EXTENDED_ERROR | ISC_REQ_ALLOCATE_MEMORY | ISC_REQ_STREAM;

// ============================================================================================
// certificate authority + per-host leaf minting
// ============================================================================================
static SRWLOCK          g_ca_lock = SRWLOCK_INIT;
static BOOL             g_ca_ready = FALSE;
static PCCERT_CONTEXT   g_ca_cert = NULL;          // the root CA (with its private key, via key-prov-info)
static HCERTSTORE       g_ca_store = NULL;         // persistent machine store that holds g_ca_cert

// host -> minted leaf certificate (kept for the life of the process; a server credential references it)
typedef struct LEAF_ENTRY { char host[256]; PCCERT_CONTEXT cert; struct LEAF_ENTRY *next; } LEAF_ENTRY;
static LEAF_ENTRY      *g_leaf_cache = NULL;
static UINT32           g_leaf_count = 0;
static SRWLOCK          g_leaf_lock = SRWLOCK_INIT;

static void tls_log(const char *fmt, ...)
{
    char buf[512];
    va_list a; va_start(a, fmt); vsnprintf(buf, sizeof(buf), fmt, a); va_end(a);
    log_message("%s", buf);
}

// Opens (creating if needed) an RSA provider bound to a named machine-key-set container.
static BOOL open_container(const wchar_t *name, HCRYPTPROV *out)
{
    if (CryptAcquireContextW(out, name, MS_ENH_RSA_AES_PROV_W, PROV_RSA_AES, CRYPT_MACHINE_KEYSET))
        return TRUE;
    if (CryptAcquireContextW(out, name, MS_ENH_RSA_AES_PROV_W, PROV_RSA_AES, CRYPT_MACHINE_KEYSET | CRYPT_NEWKEYSET))
        return TRUE;
    return FALSE;
}

// Ensures the container holds a key pair of the given spec (AT_SIGNATURE for the CA, AT_KEYEXCHANGE for leaves).
static BOOL ensure_key(HCRYPTPROV prov, DWORD keyspec)
{
    HCRYPTKEY k = 0;
    if (CryptGetUserKey(prov, keyspec, &k)) { CryptDestroyKey(k); return TRUE; }
    if (CryptGenKey(prov, keyspec, (2048u << 16) | CRYPT_EXPORTABLE, &k)) { CryptDestroyKey(k); return TRUE; }
    return FALSE;
}

// Encodes one X.509 extension into `ext` (its pbData must be freed with LocalFree via CryptEncodeObjectEx alloc flag).
static BOOL encode_ext(LPCSTR oid, BOOL crit, LPCSTR struct_type, const void *info, CERT_EXTENSION *ext)
{
    DWORD cb = 0;
    BYTE *enc = NULL;
    if (!CryptEncodeObjectEx(X509_ASN_ENCODING, struct_type, info, CRYPT_ENCODE_ALLOC_FLAG, NULL, &enc, &cb))
        return FALSE;
    ext->pszObjId = (LPSTR)oid;
    ext->fCritical = crit;
    ext->Value.cbData = cb;
    ext->Value.pbData = enc;
    return TRUE;
}

// caller holds g_ca_lock exclusively
static BOOL ca_create(void)
{
    HCRYPTPROV prov = 0;
    if (!open_container(TLS_CA_CONTAINER, &prov)) { tls_log("[TLS] CA key container failed (%lu)", GetLastError()); return FALSE; }
    if (!ensure_key(prov, AT_SIGNATURE)) { CryptReleaseContext(prov, 0); tls_log("[TLS] CA key generation failed (%lu)", GetLastError()); return FALSE; }

    // Subject / issuer name "CN=ProxyBridge Local Root CA"
    CERT_NAME_BLOB subject = {0};
    char nameStr[128]; snprintf(nameStr, sizeof(nameStr), "CN=%s", TLS_CA_CN);
    DWORD cbName = 0;
    CertStrToNameA(X509_ASN_ENCODING, nameStr, CERT_X500_NAME_STR, NULL, NULL, &cbName, NULL);
    subject.pbData = (BYTE *)malloc(cbName);
    if (subject.pbData == NULL || !CertStrToNameA(X509_ASN_ENCODING, nameStr, CERT_X500_NAME_STR, NULL, subject.pbData, &cbName, NULL))
    { free(subject.pbData); CryptReleaseContext(prov, 0); return FALSE; }
    subject.cbData = cbName;

    // Extensions: basicConstraints CA=TRUE, keyUsage certSign+crlSign.
    CERT_EXTENSION exts[2]; ZeroMemory(exts, sizeof(exts)); DWORD nExt = 0;
    CERT_BASIC_CONSTRAINTS2_INFO bc = {0}; bc.fCA = TRUE; bc.fPathLenConstraint = FALSE;
    if (encode_ext(szOID_BASIC_CONSTRAINTS2, TRUE, X509_BASIC_CONSTRAINTS2, &bc, &exts[nExt])) nExt++;
    BYTE kuBits = CERT_KEY_CERT_SIGN_KEY_USAGE | CERT_CRL_SIGN_KEY_USAGE;
    CRYPT_BIT_BLOB ku = {0}; ku.cbData = 1; ku.pbData = &kuBits; ku.cUnusedBits = 0;
    if (encode_ext(szOID_KEY_USAGE, TRUE, X509_KEY_USAGE, &ku, &exts[nExt])) nExt++;
    CERT_EXTENSIONS ce = {0}; ce.cExtension = nExt; ce.rgExtension = exts;

    CRYPT_KEY_PROV_INFO kpi = {0};
    kpi.pwszContainerName = (LPWSTR)TLS_CA_CONTAINER;
    kpi.pwszProvName = (LPWSTR)MS_ENH_RSA_AES_PROV_W;
    kpi.dwProvType = PROV_RSA_AES;
    kpi.dwFlags = CRYPT_MACHINE_KEYSET;
    kpi.dwKeySpec = AT_SIGNATURE;

    CRYPT_ALGORITHM_IDENTIFIER sig = {0}; sig.pszObjId = (LPSTR)szOID_RSA_SHA256RSA;

    SYSTEMTIME stStart; GetSystemTime(&stStart);
    SYSTEMTIME stEnd = stStart; stEnd.wYear += 10;

    PCCERT_CONTEXT caCtx = CertCreateSelfSignCertificate(prov, &subject, 0, &kpi, &sig, &stStart, &stEnd, &ce);
    for (DWORD i = 0; i < nExt; i++) LocalFree(exts[i].Value.pbData);
    free(subject.pbData);
    CryptReleaseContext(prov, 0);
    if (caCtx == NULL) { tls_log("[TLS] CA self-sign failed (%lu)", GetLastError()); return FALSE; }

    if (!CertAddCertificateContextToStore(g_ca_store, caCtx, CERT_STORE_ADD_REPLACE_EXISTING, &g_ca_cert))
    { CertFreeCertificateContext(caCtx); tls_log("[TLS] storing CA failed (%lu)", GetLastError()); return FALSE; }
    CertFreeCertificateContext(caCtx);
    return TRUE;
}

BOOL pb_tls_ensure_ca(void)
{
    BOOL ok;
    AcquireSRWLockExclusive(&g_ca_lock);
    if (g_ca_ready) { AcquireSRWLockExclusive(&g_leaf_lock); ReleaseSRWLockExclusive(&g_leaf_lock); ReleaseSRWLockExclusive(&g_ca_lock); return TRUE; }

    if (g_ca_store == NULL)
        g_ca_store = CertOpenStore(CERT_STORE_PROV_SYSTEM_W, 0, 0,
                                   CERT_SYSTEM_STORE_LOCAL_MACHINE | CERT_STORE_OPEN_EXISTING_FLAG, TLS_STORE_NAME);
    if (g_ca_store == NULL)
        g_ca_store = CertOpenStore(CERT_STORE_PROV_SYSTEM_W, 0, 0, CERT_SYSTEM_STORE_LOCAL_MACHINE, TLS_STORE_NAME);
    if (g_ca_store == NULL) { ReleaseSRWLockExclusive(&g_ca_lock); tls_log("[TLS] cannot open CA store (%lu)", GetLastError()); return FALSE; }

    // Reuse an existing CA from the store, else mint one.
    g_ca_cert = CertFindCertificateInStore(g_ca_store, X509_ASN_ENCODING, 0, CERT_FIND_ANY, NULL, NULL);
    ok = (g_ca_cert != NULL) ? TRUE : ca_create();

    // Make sure the shared leaf key exists.
    if (ok)
    {
        HCRYPTPROV lp = 0;
        if (!open_container(TLS_LEAF_CONTAINER, &lp) || !ensure_key(lp, AT_KEYEXCHANGE)) { ok = FALSE; tls_log("[TLS] leaf key setup failed (%lu)", GetLastError()); }
        if (lp) CryptReleaseContext(lp, 0);
    }
    g_ca_ready = ok;
    ReleaseSRWLockExclusive(&g_ca_lock);
    if (ok) pb_tls_ensure_exported();   // best-effort export of the .crt for the user to install
    return ok;
}

// Mints (and caches) a leaf certificate for `host`, signed by the CA, with the shared leaf key.
static PCCERT_CONTEXT leaf_for_host(const char *host)
{
    char h[256];
    snprintf(h, sizeof(h), "%s", (host && host[0]) ? host : "localhost");

    AcquireSRWLockShared(&g_leaf_lock);
    for (LEAF_ENTRY *e = g_leaf_cache; e; e = e->next)
        if (_stricmp(e->host, h) == 0) { PCCERT_CONTEXT c = e->cert; ReleaseSRWLockShared(&g_leaf_lock); return c; }
    ReleaseSRWLockShared(&g_leaf_lock);

    HCRYPTPROV leafProv = 0, caProv = 0;
    if (!open_container(TLS_LEAF_CONTAINER, &leafProv)) return NULL;

    // Public key of the shared leaf key.
    DWORD cbPub = 0;
    CryptExportPublicKeyInfo(leafProv, AT_KEYEXCHANGE, X509_ASN_ENCODING, NULL, &cbPub);
    CERT_PUBLIC_KEY_INFO *pub = (CERT_PUBLIC_KEY_INFO *)malloc(cbPub);
    if (pub == NULL || !CryptExportPublicKeyInfo(leafProv, AT_KEYEXCHANGE, X509_ASN_ENCODING, pub, &cbPub))
    { free(pub); CryptReleaseContext(leafProv, 0); return NULL; }
    CryptReleaseContext(leafProv, 0);

    // Subject CN=host
    CERT_NAME_BLOB subject = {0};
    char nameStr[320]; snprintf(nameStr, sizeof(nameStr), "CN=%s", h);
    DWORD cbName = 0;
    CertStrToNameA(X509_ASN_ENCODING, nameStr, CERT_X500_NAME_STR, NULL, NULL, &cbName, NULL);
    subject.pbData = (BYTE *)malloc(cbName);
    if (subject.pbData == NULL || !CertStrToNameA(X509_ASN_ENCODING, nameStr, CERT_X500_NAME_STR, NULL, subject.pbData, &cbName, NULL))
    { free(subject.pbData); free(pub); return NULL; }
    subject.cbData = cbName;

    // Extensions: SAN dNSName=host, EKU serverAuth, basicConstraints CA=FALSE, keyUsage.
    wchar_t hostW[256]; MultiByteToWideChar(CP_UTF8, 0, h, -1, hostW, 256);
    CERT_ALT_NAME_ENTRY altEntry = {0}; altEntry.dwAltNameChoice = CERT_ALT_NAME_DNS_NAME; altEntry.pwszDNSName = hostW;
    CERT_ALT_NAME_INFO altInfo = {0}; altInfo.cAltEntry = 1; altInfo.rgAltEntry = &altEntry;
    LPSTR ekuOids[1] = { (LPSTR)szOID_PKIX_KP_SERVER_AUTH };
    CERT_ENHKEY_USAGE eku = {0}; eku.cUsageIdentifier = 1; eku.rgpszUsageIdentifier = ekuOids;
    CERT_BASIC_CONSTRAINTS2_INFO bc = {0}; bc.fCA = FALSE;
    BYTE kuBits = CERT_DIGITAL_SIGNATURE_KEY_USAGE | CERT_KEY_ENCIPHERMENT_KEY_USAGE;
    CRYPT_BIT_BLOB ku = {0}; ku.cbData = 1; ku.pbData = &kuBits;

    CERT_EXTENSION exts[4]; ZeroMemory(exts, sizeof(exts)); DWORD nExt = 0;
    if (encode_ext(szOID_SUBJECT_ALT_NAME2, FALSE, X509_ALTERNATE_NAME, &altInfo, &exts[nExt])) nExt++;
    if (encode_ext(szOID_ENHANCED_KEY_USAGE, FALSE, X509_ENHANCED_KEY_USAGE, &eku, &exts[nExt])) nExt++;
    if (encode_ext(szOID_BASIC_CONSTRAINTS2, TRUE, X509_BASIC_CONSTRAINTS2, &bc, &exts[nExt])) nExt++;
    if (encode_ext(szOID_KEY_USAGE, FALSE, X509_KEY_USAGE, &ku, &exts[nExt])) nExt++;

    BYTE serial[16]; for (int i = 0; i < 16; i++) serial[i] = (BYTE)(GetTickCount() >> (i % 4 * 8)) ^ (BYTE)(rand() & 0xFF);
    serial[0] &= 0x7F;

    PCCERT_CONTEXT leaf = NULL;
    AcquireSRWLockShared(&g_ca_lock);
    if (g_ca_ready && g_ca_cert != NULL &&
        open_container(TLS_CA_CONTAINER, &caProv))
    {
        CERT_INFO ci; ZeroMemory(&ci, sizeof(ci));
        ci.dwVersion = CERT_V3;
        ci.SerialNumber.cbData = sizeof(serial); ci.SerialNumber.pbData = serial;
        ci.SignatureAlgorithm.pszObjId = (LPSTR)szOID_RSA_SHA256RSA;
        ci.Issuer = g_ca_cert->pCertInfo->Subject;
        SYSTEMTIME st; GetSystemTime(&st); FILETIME ft0; SystemTimeToFileTime(&st, &ft0);
        st.wYear += 2; FILETIME ft1; SystemTimeToFileTime(&st, &ft1);
        ci.NotBefore = ft0; ci.NotAfter = ft1;
        ci.Subject = subject;
        ci.SubjectPublicKeyInfo = *pub;
        ci.cExtension = nExt; ci.rgExtension = exts;

        CRYPT_ALGORITHM_IDENTIFIER sig = {0}; sig.pszObjId = (LPSTR)szOID_RSA_SHA256RSA;
        DWORD cbEnc = 0;
        if (CryptSignAndEncodeCertificate(caProv, AT_SIGNATURE, X509_ASN_ENCODING, X509_CERT_TO_BE_SIGNED,
                                          &ci, &sig, NULL, NULL, &cbEnc))
        {
            BYTE *enc = (BYTE *)malloc(cbEnc);
            if (enc != NULL && CryptSignAndEncodeCertificate(caProv, AT_SIGNATURE, X509_ASN_ENCODING, X509_CERT_TO_BE_SIGNED,
                                                            &ci, &sig, NULL, enc, &cbEnc))
            {
                leaf = CertCreateCertificateContext(X509_ASN_ENCODING, enc, cbEnc);
                if (leaf != NULL)
                {
                    CRYPT_KEY_PROV_INFO kpi = {0};
                    kpi.pwszContainerName = (LPWSTR)TLS_LEAF_CONTAINER;
                    kpi.pwszProvName = (LPWSTR)MS_ENH_RSA_AES_PROV_W;
                    kpi.dwProvType = PROV_RSA_AES;
                    kpi.dwFlags = CRYPT_MACHINE_KEYSET;
                    kpi.dwKeySpec = AT_KEYEXCHANGE;
                    CertSetCertificateContextProperty(leaf, CERT_KEY_PROV_INFO_PROP_ID, 0, &kpi);
                }
            }
            free(enc);
        }
        CryptReleaseContext(caProv, 0);
    }
    ReleaseSRWLockShared(&g_ca_lock);

    for (DWORD i = 0; i < nExt; i++) LocalFree(exts[i].Value.pbData);
    free(subject.pbData);
    free(pub);
    if (leaf == NULL) return NULL;

    AcquireSRWLockExclusive(&g_leaf_lock);
    LEAF_ENTRY *dup = NULL;                                 // another thread may have raced us
    for (LEAF_ENTRY *e = g_leaf_cache; e; e = e->next) if (_stricmp(e->host, h) == 0) { dup = e; break; }
    if (dup) { PCCERT_CONTEXT c = dup->cert; ReleaseSRWLockExclusive(&g_leaf_lock); CertFreeCertificateContext(leaf); return c; }
    if (g_leaf_count >= TLS_LEAF_CACHE_MAX)                 // crude cap: drop the whole cache
    {
        while (g_leaf_cache) { LEAF_ENTRY *n = g_leaf_cache->next; CertFreeCertificateContext(g_leaf_cache->cert); free(g_leaf_cache); g_leaf_cache = n; }
        g_leaf_count = 0;
    }
    LEAF_ENTRY *le = (LEAF_ENTRY *)calloc(1, sizeof(*le));
    if (le == NULL) { ReleaseSRWLockExclusive(&g_leaf_lock); return leaf; }   // uncached but usable
    snprintf(le->host, sizeof(le->host), "%s", h);
    le->cert = leaf; le->next = g_leaf_cache; g_leaf_cache = le; g_leaf_count++;
    ReleaseSRWLockExclusive(&g_leaf_lock);
    return leaf;
}

// ============================================================================================
// CA export / install
// ============================================================================================
static void ca_dir_w(wchar_t *out, size_t n, BOOL file)
{
    wchar_t base[MAX_PATH];
    DWORD k = GetEnvironmentVariableW(L"ProgramData", base, MAX_PATH);
    if (k == 0 || k >= MAX_PATH) lstrcpynW(base, L"C:\\ProgramData", MAX_PATH);
    _snwprintf_s(out, n, _TRUNCATE, file ? L"%s\\ProxyBridge\\ca\\ProxyBridge-CA.crt" : L"%s\\ProxyBridge\\ca", base);
}

// Writes the CA certificate (DER .crt) to %ProgramData%\ProxyBridge\ca. Best effort; safe to call repeatedly.
void pb_tls_ensure_exported(void)
{
    AcquireSRWLockShared(&g_ca_lock);
    PCCERT_CONTEXT ca = g_ca_cert;
    BOOL have = g_ca_ready && ca != NULL;
    wchar_t dir[MAX_PATH + 32], path[MAX_PATH + 48];
    ca_dir_w(dir, MAX_PATH + 32, FALSE);
    ca_dir_w(path, MAX_PATH + 48, TRUE);
    if (have)
    {
        wchar_t parent[MAX_PATH + 32]; lstrcpynW(parent, dir, MAX_PATH + 32);
        wchar_t *slash = wcsrchr(parent, L'\\'); if (slash) { *slash = 0; CreateDirectoryW(parent, NULL); }
        CreateDirectoryW(dir, NULL);
        HANDLE f = CreateFileW(path, GENERIC_WRITE, FILE_SHARE_READ, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
        if (f != INVALID_HANDLE_VALUE)
        {
            DWORD w = 0;
            WriteFile(f, ca->pbCertEncoded, ca->cbCertEncoded, &w, NULL);
            CloseHandle(f);
        }
    }
    ReleaseSRWLockShared(&g_ca_lock);
}

BOOL pb_tls_ca_cert_path(char *buf, size_t size)
{
    if (buf == NULL || size == 0) return FALSE;
    wchar_t w[MAX_PATH + 48];
    ca_dir_w(w, MAX_PATH + 48, TRUE);
    int n = WideCharToMultiByte(CP_UTF8, 0, w, -1, buf, (int)(size > 0x7fffffff ? 0x7fffffff : size), NULL, NULL);
    if (n <= 0) { buf[0] = '\0'; return FALSE; }
    return TRUE;
}

int pb_tls_install_ca(void)
{
    if (!pb_tls_ensure_ca()) return -1;
    HCERTSTORE root = CertOpenStore(CERT_STORE_PROV_SYSTEM_W, 0, 0, CERT_SYSTEM_STORE_LOCAL_MACHINE, L"ROOT");
    if (root == NULL) return -2;
    int rc = 0;
    AcquireSRWLockShared(&g_ca_lock);
    if (g_ca_cert == NULL || !CertAddCertificateContextToStore(root, g_ca_cert, CERT_STORE_ADD_REPLACE_EXISTING, NULL))
        rc = -3;
    ReleaseSRWLockShared(&g_ca_lock);
    CertCloseStore(root, 0);
    if (rc == 0) tls_log("[TLS] ProxyBridge CA installed in the machine Trusted Root store");
    return rc;
}

// ============================================================================================
// SChannel PBIO backend
// ============================================================================================
typedef struct {
    PBIO       io;
    SOCKET     sock;
    BOOL       server;
    CredHandle cred;  BOOL have_cred;
    CtxtHandle ctx;   BOOL have_ctx;
    SecPkgContext_StreamSizes sizes;
    char      *enc;   size_t enc_len, enc_cap;      // ciphertext received, not yet decrypted
    char      *dec;   size_t dec_off, dec_len, dec_cap;   // decrypted plaintext not yet delivered
    char      *obuf;  size_t ocap;                   // scratch for one outgoing record
    BOOL       eof;
    CRITICAL_SECTION lock;                           // one context op (encrypt / decrypt / shutdown) at a time
} TLSIO;

static BOOL enc_reserve(TLSIO *t, size_t extra)
{
    if (t->enc_len + extra <= t->enc_cap) return TRUE;
    size_t nc = t->enc_cap ? t->enc_cap : 16384;
    while (nc < t->enc_len + extra) nc *= 2;
    char *p = (char *)realloc(t->enc, nc);
    if (p == NULL) return FALSE;
    t->enc = p; t->enc_cap = nc;
    return TRUE;
}

static BOOL dec_store(TLSIO *t, const char *p, size_t n)
{
    if (t->dec_off == t->dec_len) t->dec_off = t->dec_len = 0;
    if (t->dec_len + n > t->dec_cap)
    {
        size_t nc = t->dec_cap ? t->dec_cap : 16384;
        while (nc < t->dec_len + n) nc *= 2;
        char *np = (char *)realloc(t->dec, nc);
        if (np == NULL) return FALSE;
        t->dec = np; t->dec_cap = nc;
    }
    memcpy(t->dec + t->dec_len, p, n); t->dec_len += n;
    return TRUE;
}

// Waits up to idle_ms for the socket to be readable; 1 = readable, 0 = timeout, -1 = error / stopping.
static int sock_wait(SOCKET s, DWORD idle_ms)
{
    ULONGLONG start = GetTickCount64();
    while (running)
    {
        fd_set rf; FD_ZERO(&rf); FD_SET(s, &rf);
        struct timeval tv = { 1, 0 };
        int r = select(0, &rf, NULL, NULL, &tv);
        if (r == SOCKET_ERROR) return -1;
        if (r > 0) return 1;
        if (GetTickCount64() - start >= idle_ms) return 0;
    }
    return -1;
}

static int tls_send_all(SOCKET s, const char *p, size_t n)
{
    while (n > 0)
    {
        int k = send(s, p, (int)(n > 0x40000000u ? 0x40000000u : n), 0);
        if (k == SOCKET_ERROR) return -1;
        p += k; n -= (size_t)k;
    }
    return 0;
}

static int tls_read(PBIO *io, char *buf, int cap, DWORD idle_ms)
{
    TLSIO *t = (TLSIO *)io;
    EnterCriticalSection(&t->lock);
    for (;;)
    {
        if (t->dec_len > t->dec_off)
        {
            size_t k = t->dec_len - t->dec_off;
            if (k > (size_t)cap) k = (size_t)cap;
            memcpy(buf, t->dec + t->dec_off, k);
            t->dec_off += k;
            LeaveCriticalSection(&t->lock);
            return (int)k;
        }
        if (t->eof) { LeaveCriticalSection(&t->lock); return 0; }

        if (t->enc_len > 0)
        {
            SecBuffer sb[4];
            sb[0].BufferType = SECBUFFER_DATA;  sb[0].pvBuffer = t->enc; sb[0].cbBuffer = (unsigned long)t->enc_len;
            sb[1].BufferType = SECBUFFER_EMPTY; sb[1].pvBuffer = NULL;   sb[1].cbBuffer = 0;
            sb[2].BufferType = SECBUFFER_EMPTY; sb[2].pvBuffer = NULL;   sb[2].cbBuffer = 0;
            sb[3].BufferType = SECBUFFER_EMPTY; sb[3].pvBuffer = NULL;   sb[3].cbBuffer = 0;
            SecBufferDesc msg = { SECBUFFER_VERSION, 4, sb };
            SECURITY_STATUS ss = DecryptMessage(&t->ctx, &msg, 0, NULL);
            if (ss == SEC_E_OK)
            {
                SecBuffer *data = NULL, *extra = NULL;
                for (int i = 1; i < 4; i++)
                {
                    if (sb[i].BufferType == SECBUFFER_DATA && data == NULL) data = &sb[i];
                    if (sb[i].BufferType == SECBUFFER_EXTRA) extra = &sb[i];
                }
                if (data && data->cbBuffer > 0 && !dec_store(t, (char *)data->pvBuffer, data->cbBuffer))
                { LeaveCriticalSection(&t->lock); return -1; }
                if (extra && extra->cbBuffer > 0)
                { memmove(t->enc, extra->pvBuffer, extra->cbBuffer); t->enc_len = extra->cbBuffer; }
                else t->enc_len = 0;
                continue;                                  // deliver what we just decrypted (or decrypt the next record)
            }
            if (ss == SEC_I_CONTEXT_EXPIRED) { t->eof = TRUE; continue; }     // peer sent close_notify
            if (ss == SEC_I_RENEGOTIATE) { t->eof = TRUE; LeaveCriticalSection(&t->lock); return -1; }  // not supported mid-stream
            if (ss != SEC_E_INCOMPLETE_MESSAGE) { LeaveCriticalSection(&t->lock); return -1; }
            // incomplete record: fall through and read more ciphertext
        }

        int w = sock_wait(t->sock, idle_ms);
        if (w <= 0) { LeaveCriticalSection(&t->lock); return -1; }
        if (!enc_reserve(t, TLS_IO_CHUNK)) { LeaveCriticalSection(&t->lock); return -1; }
        int n = recv(t->sock, t->enc + t->enc_len, TLS_IO_CHUNK, 0);
        if (n == 0) { t->eof = TRUE; continue; }           // socket closed: deliver buffered, then EOF
        if (n == SOCKET_ERROR) { LeaveCriticalSection(&t->lock); return -1; }
        t->enc_len += (size_t)n;
    }
}

static int tls_write(PBIO *io, const char *buf, int len)
{
    TLSIO *t = (TLSIO *)io;
    EnterCriticalSection(&t->lock);
    int rc = 0;
    size_t remaining = (size_t)len;
    while (remaining > 0)
    {
        size_t k = remaining < t->sizes.cbMaximumMessage ? remaining : t->sizes.cbMaximumMessage;
        memcpy(t->obuf + t->sizes.cbHeader, buf, k);
        SecBuffer sb[4];
        sb[0].BufferType = SECBUFFER_STREAM_HEADER;  sb[0].pvBuffer = t->obuf;                               sb[0].cbBuffer = t->sizes.cbHeader;
        sb[1].BufferType = SECBUFFER_DATA;           sb[1].pvBuffer = t->obuf + t->sizes.cbHeader;           sb[1].cbBuffer = (unsigned long)k;
        sb[2].BufferType = SECBUFFER_STREAM_TRAILER; sb[2].pvBuffer = t->obuf + t->sizes.cbHeader + k;       sb[2].cbBuffer = t->sizes.cbTrailer;
        sb[3].BufferType = SECBUFFER_EMPTY;          sb[3].pvBuffer = NULL;                                  sb[3].cbBuffer = 0;
        SecBufferDesc msg = { SECBUFFER_VERSION, 4, sb };
        if (EncryptMessage(&t->ctx, 0, &msg, 0) != SEC_E_OK) { rc = -1; break; }
        size_t total = sb[0].cbBuffer + sb[1].cbBuffer + sb[2].cbBuffer;
        if (tls_send_all(t->sock, t->obuf, total) != 0) { rc = -1; break; }
        buf += k; remaining -= k;
    }
    LeaveCriticalSection(&t->lock);
    return rc;
}

static BOOL tls_pending(PBIO *io)
{
    TLSIO *t = (TLSIO *)io;
    return (t->dec_len > t->dec_off) || (t->enc_len > 0);
}

static void tls_shutdown_notify(TLSIO *t)
{
    DWORD dwType = SCHANNEL_SHUTDOWN;
    SecBuffer ib = { sizeof(dwType), SECBUFFER_TOKEN, &dwType };
    SecBufferDesc id = { SECBUFFER_VERSION, 1, &ib };
    if (ApplyControlToken(&t->ctx, &id) != SEC_E_OK) return;

    SecBuffer ob = { 0, SECBUFFER_TOKEN, NULL };
    SecBufferDesc od = { SECBUFFER_VERSION, 1, &ob };
    DWORD attr = 0;
    SECURITY_STATUS ss;
    if (t->server)
        ss = AcceptSecurityContext(&t->cred, &t->ctx, NULL, g_asc_req, 0, &t->ctx, &od, &attr, NULL);
    else
        ss = InitializeSecurityContextW(&t->cred, &t->ctx, NULL, g_isc_req, 0, 0, NULL, 0, &t->ctx, &od, &attr, NULL);
    if ((ss == SEC_E_OK || ss == SEC_I_CONTEXT_EXPIRED) && ob.pvBuffer && ob.cbBuffer)
        tls_send_all(t->sock, (char *)ob.pvBuffer, ob.cbBuffer);
    if (ob.pvBuffer) FreeContextBuffer(ob.pvBuffer);
}

static void tls_destroy(PBIO *io, BOOL send_shutdown)
{
    TLSIO *t = (TLSIO *)io;
    if (t->have_ctx)
    {
        if (send_shutdown) { EnterCriticalSection(&t->lock); tls_shutdown_notify(t); LeaveCriticalSection(&t->lock); }
        DeleteSecurityContext(&t->ctx);
    }
    if (t->have_cred) FreeCredentialsHandle(&t->cred);
    if (t->sock != INVALID_SOCKET) { if (send_shutdown) shutdown(t->sock, SD_SEND); closesocket(t->sock); }
    DeleteCriticalSection(&t->lock);
    free(t->enc); free(t->dec); free(t->obuf);
    free(t);
}

static TLSIO *tls_new(SOCKET s, BOOL server)
{
    TLSIO *t = (TLSIO *)calloc(1, sizeof(*t));
    if (t == NULL) return NULL;
    t->io.read = tls_read; t->io.write = tls_write; t->io.pending = tls_pending; t->io.destroy = tls_destroy;
    t->io.sock = s; t->io.is_tls = TRUE;
    t->sock = s; t->server = server;
    InitializeCriticalSection(&t->lock);
    return t;
}

// Finishes a handshake: sets up stream sizes and the outgoing scratch buffer.
static BOOL tls_finish(TLSIO *t)
{
    if (QueryContextAttributesW(&t->ctx, SECPKG_ATTR_STREAM_SIZES, &t->sizes) != SEC_E_OK) return FALSE;
    t->ocap = (size_t)t->sizes.cbHeader + t->sizes.cbMaximumMessage + t->sizes.cbTrailer;
    t->obuf = (char *)malloc(t->ocap);
    return t->obuf != NULL;
}

PBIO *pb_tls_accept(SOCKET client, const char *host, const char *initial, int initial_len)
{
    if (!pb_tls_ensure_ca()) { closesocket(client); return NULL; }
    PCCERT_CONTEXT leaf = leaf_for_host(host);
    if (leaf == NULL) { tls_log("[TLS] no leaf certificate for %s", host ? host : "?"); closesocket(client); return NULL; }

    TLSIO *t = tls_new(client, TRUE);
    if (t == NULL) { closesocket(client); return NULL; }

    SCHANNEL_CRED sc; ZeroMemory(&sc, sizeof(sc));
    sc.dwVersion = SCHANNEL_CRED_VERSION;
    sc.cCreds = 1; sc.paCred = &leaf;
    // The leaf key is a legacy CSP key, which SChannel can serve for TLS 1.0-1.2 but not TLS 1.3 (1.3 server keys
    // must be CNG). Cap the application-facing side at 1.2 so the handshake uses a protocol this key supports.
    sc.grbitEnabledProtocols = SP_PROT_TLS1_0_SERVER | SP_PROT_TLS1_1_SERVER | SP_PROT_TLS1_2_SERVER;
    if (AcquireCredentialsHandleW(NULL, (LPWSTR)UNISP_NAME_W, SECPKG_CRED_INBOUND, NULL, &sc, NULL, NULL, &t->cred, NULL) != SEC_E_OK)
    { tls_log("[TLS] server credentials failed (%lu)", GetLastError()); t->sock = INVALID_SOCKET; tls_destroy(&t->io, FALSE); closesocket(client); return NULL; }
    t->have_cred = TRUE;

    if (initial_len > 0 && initial != NULL)
    {
        if (!enc_reserve(t, (size_t)initial_len)) { tls_destroy(&t->io, FALSE); return NULL; }
        memcpy(t->enc, initial, (size_t)initial_len); t->enc_len = (size_t)initial_len;
    }

    for (;;)
    {
        if (t->enc_len == 0)
        {
            int w = sock_wait(t->sock, 30000);
            if (w <= 0) { tls_destroy(&t->io, FALSE); return NULL; }
            if (!enc_reserve(t, TLS_IO_CHUNK)) { tls_destroy(&t->io, FALSE); return NULL; }
            int n = recv(t->sock, t->enc + t->enc_len, TLS_IO_CHUNK, 0);
            if (n <= 0) { tls_destroy(&t->io, FALSE); return NULL; }
            t->enc_len += (size_t)n;
        }

        SecBuffer ib[2];
        ib[0].BufferType = SECBUFFER_TOKEN; ib[0].pvBuffer = t->enc; ib[0].cbBuffer = (unsigned long)t->enc_len;
        ib[1].BufferType = SECBUFFER_EMPTY; ib[1].pvBuffer = NULL;   ib[1].cbBuffer = 0;
        SecBufferDesc in = { SECBUFFER_VERSION, 2, ib };
        SecBuffer ob[1];
        ob[0].BufferType = SECBUFFER_TOKEN; ob[0].pvBuffer = NULL; ob[0].cbBuffer = 0;
        SecBufferDesc out = { SECBUFFER_VERSION, 1, ob };
        DWORD attr = 0;
        SECURITY_STATUS ss = AcceptSecurityContext(&t->cred, t->have_ctx ? &t->ctx : NULL, &in, g_asc_req, 0,
                                                   &t->ctx, &out, &attr, NULL);
        t->have_ctx = TRUE;
        if (ob[0].pvBuffer && ob[0].cbBuffer)
        {
            int sr = tls_send_all(t->sock, (char *)ob[0].pvBuffer, ob[0].cbBuffer);
            FreeContextBuffer(ob[0].pvBuffer);
            if (sr != 0) { tls_destroy(&t->io, FALSE); return NULL; }
        }

        if (ss == SEC_E_INCOMPLETE_MESSAGE) continue;      // need more ClientHello / handshake bytes
        if (ss == SEC_I_CONTINUE_NEEDED || ss == SEC_E_OK)
        {
            if (ib[1].BufferType == SECBUFFER_EXTRA && ib[1].cbBuffer > 0)
            { memmove(t->enc, t->enc + (t->enc_len - ib[1].cbBuffer), ib[1].cbBuffer); t->enc_len = ib[1].cbBuffer; }
            else t->enc_len = 0;
            if (ss == SEC_E_OK) { if (!tls_finish(t)) { tls_destroy(&t->io, FALSE); return NULL; } return &t->io; }
            continue;
        }
        tls_log("[TLS] server handshake with app failed (0x%lx) for %s", (unsigned long)ss, host ? host : "?");
        tls_destroy(&t->io, FALSE);
        return NULL;
    }
}

PBIO *pb_tls_connect(SOCKET upstream, const char *host)
{
    TLSIO *t = tls_new(upstream, FALSE);
    if (t == NULL) { closesocket(upstream); return NULL; }

    SCHANNEL_CRED sc; ZeroMemory(&sc, sizeof(sc));
    sc.dwVersion = SCHANNEL_CRED_VERSION;
    sc.dwFlags = SCH_CRED_AUTO_CRED_VALIDATION | SCH_CRED_NO_DEFAULT_CREDS;
    sc.grbitEnabledProtocols = 0;
    if (AcquireCredentialsHandleW(NULL, (LPWSTR)UNISP_NAME_W, SECPKG_CRED_OUTBOUND, NULL, &sc, NULL, NULL, &t->cred, NULL) != SEC_E_OK)
    { t->sock = INVALID_SOCKET; tls_destroy(&t->io, FALSE); closesocket(upstream); return NULL; }
    t->have_cred = TRUE;

    wchar_t targetW[256];
    MultiByteToWideChar(CP_UTF8, 0, (host && host[0]) ? host : "localhost", -1, targetW, 256);

    BOOL first = TRUE;
    for (;;)
    {
        SecBuffer ib[2];
        ib[0].BufferType = SECBUFFER_TOKEN; ib[0].pvBuffer = t->enc; ib[0].cbBuffer = (unsigned long)t->enc_len;
        ib[1].BufferType = SECBUFFER_EMPTY; ib[1].pvBuffer = NULL;   ib[1].cbBuffer = 0;
        SecBufferDesc in = { SECBUFFER_VERSION, 2, ib };
        SecBuffer ob[1];
        ob[0].BufferType = SECBUFFER_TOKEN; ob[0].pvBuffer = NULL; ob[0].cbBuffer = 0;
        SecBufferDesc out = { SECBUFFER_VERSION, 1, ob };
        DWORD attr = 0;
        SECURITY_STATUS ss = InitializeSecurityContextW(&t->cred, first ? NULL : &t->ctx, targetW, g_isc_req, 0, 0,
                                                        first ? NULL : &in, 0, &t->ctx, &out, &attr, NULL);
        first = FALSE;
        t->have_ctx = TRUE;
        if (ob[0].pvBuffer && ob[0].cbBuffer)
        {
            int sr = tls_send_all(t->sock, (char *)ob[0].pvBuffer, ob[0].cbBuffer);
            FreeContextBuffer(ob[0].pvBuffer);
            if (sr != 0) { tls_destroy(&t->io, FALSE); return NULL; }
        }

        if (ss == SEC_E_OK)
        {
            if (ib[1].BufferType == SECBUFFER_EXTRA && ib[1].cbBuffer > 0)
            { memmove(t->enc, t->enc + (t->enc_len - ib[1].cbBuffer), ib[1].cbBuffer); t->enc_len = ib[1].cbBuffer; }
            else t->enc_len = 0;
            if (!tls_finish(t)) { tls_destroy(&t->io, FALSE); return NULL; }
            return &t->io;
        }
        if (ss == SEC_I_CONTINUE_NEEDED || ss == SEC_E_INCOMPLETE_MESSAGE)
        {
            if (ss == SEC_I_CONTINUE_NEEDED && ib[1].BufferType == SECBUFFER_EXTRA && ib[1].cbBuffer > 0)
                { memmove(t->enc, t->enc + (t->enc_len - ib[1].cbBuffer), ib[1].cbBuffer); t->enc_len = ib[1].cbBuffer; }
            else if (ss == SEC_I_CONTINUE_NEEDED)
                t->enc_len = 0;
            int w = sock_wait(t->sock, 30000);
            if (w <= 0) { tls_destroy(&t->io, FALSE); return NULL; }
            if (!enc_reserve(t, TLS_IO_CHUNK)) { tls_destroy(&t->io, FALSE); return NULL; }
            int n = recv(t->sock, t->enc + t->enc_len, TLS_IO_CHUNK, 0);
            if (n <= 0) { tls_destroy(&t->io, FALSE); return NULL; }
            t->enc_len += (size_t)n;
            continue;
        }
        tls_log("[TLS] client handshake to origin %s failed (0x%lx)", host ? host : "?", (unsigned long)ss);
        tls_destroy(&t->io, FALSE);
        return NULL;
    }
}

void pb_tls_cleanup(void)
{
    AcquireSRWLockExclusive(&g_leaf_lock);
    while (g_leaf_cache) { LEAF_ENTRY *n = g_leaf_cache->next; CertFreeCertificateContext(g_leaf_cache->cert); free(g_leaf_cache); g_leaf_cache = n; }
    g_leaf_count = 0;
    ReleaseSRWLockExclusive(&g_leaf_lock);
    AcquireSRWLockExclusive(&g_ca_lock);
    if (g_ca_cert) { CertFreeCertificateContext(g_ca_cert); g_ca_cert = NULL; }
    if (g_ca_store) { CertCloseStore(g_ca_store, 0); g_ca_store = NULL; }
    g_ca_ready = FALSE;
    ReleaseSRWLockExclusive(&g_ca_lock);
}
