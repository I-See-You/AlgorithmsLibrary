/**
Zubayet Zaman Zico

codeforces : I_See_You
hackerrank : I_See_You
codechef   : xico
spoj       : xico
email      : hhoho07@gmail.com
**/

//#include <stdio.h>
//#include <iostream>
//#include <cstring>
//#include <cmath>
//#include <algorithm>
//#include <string>
//#include <vector>
//#include <map>
//#include <set>
//#include <queue>
//#include <cstdlib>
//#include <limits>
//#include <iostream>
//#include <sstream>
//#include <unordered_set>
//#include <unordered_map>
//#include <random>
#include <bits/stdc++.h>
//#include <ext/pb_ds/assoc_container.hpp>
//using namespace __gnu_pbds;
using namespace std;


#define gc getchar unlocked
#ifndef ONLINE JUDGE
#define gc getchar
#endif // ONLINE JUDGE

#define pc putchar_unlocked
#ifndef ONLINE JUDGE
#define pc putchar
#endif // ONLINE JUDGE

#define fRead           freopen("input.txt","r",stdin)
#define fWrite          freopen("output.txt","w",stdout)

#define eps             1e-9
#define inf             0x3f3f3f3f
#define INF             2e18
#define LL              long long
#define ULL             unsigned long long
#define PI              acos(-1.0)
#define pb              push_back
#define mk              make_pair
#define pii             pair<int,int>
#define pLL             pair<LL,LL>
#define ff              first
#define ss              second
#define all(a)          a.begin(),a.end()
#define rall(a)         a.rbegin(),a.rend()
#define SQR(a)          ((a)*(a))
#define Unique(a)       sort(all(a)),a.erase(unique(all(a)),a.end())
#define min3(a,b,c)     min(a,min(b,c))
#define max3(a,b,c)     max(a,max(b,c))
#define min4(a,b,c,d)   min(min(a,b),min(c,d))
#define max4(a,b,c,d)   max(max(a,b),max(c,d))
#define max5(a,b,c,d,e) max(max3(a,b,c),max(d,e))
#define min5(a,b,c,d,e) min(min3(a,b,c),min(d,e))
#define Iterator(a)     __typeof__(a.begin())
#define rIterator(a)    __typeof__(a.rbegin())
#define FOR(a,it)       for(Iterator(a) it = a.begin();it != a.end(); it++)
#define rFOR(a,it)      for(rIterator(a) it = a.rbegin();it != a.rend(); it++)
#define FastRead        ios_base::sync_with_stdio(0);cin.tie(0)
#define CasePrint       pc('C'); pc('a'); pc('s'); pc('e'); pc(' '); write(qq++,false); pc(':'); pc(' ')
#define vi              vector <int>
#define vL              vector <LL>
#define For(I,A,B)      for(int I = (A); I  < (B); ++I)
#define rFor(I,A,B)     for(int I = (A); I >= (B); --I)
#define Rep(I,N)        For(I,0,N)
#define REP(I,N)        For(I, 1, N + 1)
#define gti             int, vi, greater<int>
#define gtL             LL, vL, greater<LL>
#define Found(a, b)     a.find(b) != a.end()
#define y0              y00

const int MOD = 1e9 + 7;
int fx[] = {-1,+0,+1,+0,+1,+1,-1,-1,+0};
int fy[] = {+0,-1,+0,+1,+1,-1,+1,-1,+0};
int day[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
//template <typename T> using orderset = tree <T, null_type, less<T>, rb_tree_tag,tree_order_statistics_node_update>; // find_by_order, order_of_key
template <typename T> inline bool isLeap(T y) {return (y % 400 == 0) || (y % 100 ? y % 4 == 0 : false); }
template <typename T> inline T GCD (T a,T b ) {a = abs(a);b = abs(b); if(a < b) swap(a, b); while ( b ) { a = a % b; swap ( a, b ); } return a;}
template <typename T> inline T EGCD(T a,T b,T &x,T &y){if(a == 0) {x = 0;y = 1;return b;}T x1, y1;T d = EGCD(b % a, a, x1, y1);x = y1 - (b / a) * x1;y = x1;return d;}
template <typename T> inline T LCM(T x,T y){T tp = GCD(x,y);if( (x / tp) * 1. * y > 9e18) return 9e18;return (x / tp) * y;}
template <typename T> inline T BigMod(T A,T B,T M = MOD){A %= M;T ret = 1;while(B){if(B & 1) ret = (ret * A) % M;A = (A * A) % M;B = B >> 1;}return ret;}
template <typename T> inline T InvMod (T A,T M = MOD){return BigMod(A,M-2,M);}
template <typename T> void Compress(T * in, int n, int f = 0){vector <T> vv;for(int i = f; i < n + f; i++) vv.pb(in[i]);Unique(vv);for(int i = f; i < n + f; i++) in[i] = lower_bound(all(vv), in[i]) - vv.begin();}
//template <typename T> void Compress(vector <T> &in){vector <T> vv;for(T x : in) vv.pb(x);Unique(vv);for(int i = 0; i < in.size(); i++) in[i] = lower_bound(all(vv), in[i]) - vv.begin();}
/*---------------------------fast I/O------------------------------------*/
#define scani2(a,b) scani(a) , scani(b)
#define scani3(a,b,c) scani(a), scani(b), scani(c)
#define scani4(a,b,c,d) scani(a), scani(b), scani(c), scani(d)
#define scani5(a,b,c,d,e) scani(a), scani(b), scani(c), scani(d) , scani(e)
template <typename T> T scani(T &n){n = 0;bool negative = false;char c = gc();while( c < '0' || c > '9'){if(c == '-') negative = true;c = gc();}while(c >= '0' && c <= '9'){n = n*10 + c-48;c = gc();}if(negative) n = ~(n-1);return n;}
template <typename T> void write(T n,int type = true){if(n<0) {pc('-');n = -n;}if(!n) {pc('0');if(type==32) pc(' '); else if(type) pc('\n'); return;}char buff[22];int len = 0;while(n) buff[len++] = n%10+48,n/=10;for(int i=len-1;i>=0;i--) pc(buff[i]);if(type==32) pc(' '); else if(type) pc('\n');}
int scans(char *a){int i=0;char c = 0;while(c < 33) c = gc();while(c > 33){a[i++] = c;c = gc();}a[i] = 0;return i;}
/*********************************************** End of template *********************************************/
#define Sieve

#ifdef Sieve
const int pSz = 2000006;
bool np[pSz + 10]; vi prime; int prime_size;void sieve(){np[0] = np[1] = 1;prime.pb(2);for(LL i = 4; i <= pSz; i+=2) np[i] = 1;for(LL i = 3; i <= pSz; i+=2){if(!np[i]){prime.pb(i);for(LL j = i * i; j <= pSz; j += (i << 1)) np[j] = 1;}}prime_size = prime.size();}
#endif

#ifdef Combi
const int nSz = 2000006;
LL F[nSz + 1], tMod = MOD;
void Factorial(){ F[0] = 1; for(int i = 1; i <= nSz; i++) F[i] = (F[i - 1] * i) % tMod; }
inline LL nCr(int n, int r) { return (F[n] * InvMod((F[n - r] * F[r]) % tMod, tMod)) % tMod; }
#endif

#ifdef Z_Algo
void zAlgo(char *s, int *z){
    int L, R, sz; sz = strlen(s); z[0] = L = R = 0;
    For(i, 1, sz) { z[i] = 0; if(i <= R) z[i] = min(z[i - L], R - i + 1); while(i + z[i] < sz && s[i + z[i]] == s[z[i]]) z[i]++; if(i + z[i] - 1 > R) L = i, R = i + z[i] - 1; }
}void zAlgo(string &s, int *z){
    int L, R, sz; sz = s.size(); z[0] = L = R = 0;
    For(i, 1, sz) { z[i] = 0; if(i <= R) z[i] = min(z[i - L], R - i + 1); while(i + z[i] < sz && s[i + z[i]] == s[z[i]]) z[i]++; if(i + z[i] - 1 > R) L = i, R = i + z[i] - 1; }
}void zAlgo(int *s, int *z, int n){
    int L, R, sz; sz = n; z[0] = L = R = 0;
    For(i, 1, sz) { z[i] = 0; if(i <= R) z[i] = min(z[i - L], R - i + 1); while(i + z[i] < sz && s[i + z[i]] == s[z[i]]) z[i]++; if(i + z[i] - 1 > R) L = i, R = i + z[i] - 1; }
}
#endif // Z_Algo


/********************************************* define Template *************************************************/

template <typename T> inline T SqrDis(T x1, T y1, T x2, T y2){return SQR(x1 - x2) + SQR(y1 - y2);}
template <typename T> inline T Area2(T Ax, T Ay, T Bx, T By, T Cx, T Cy){T ret = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By);
    if(ret < 0) return ret = -ret;
    return ret;
}
/**************************************************** GEO ******************************************************/
const int N = 200005; /** need to update this **/
const int M = 200005;
const ULL hs = 3797;
/** use data types carefully try to take 'long long' **/

#define MAX 4194404

struct complx{
    long double real, img;

    inline complx(){
        real = img = 0.0;
    }

    inline complx(long double x){
        real = x, img = 0.0;
    }

    inline complx(long double x, long double y){
        real = x, img = y;
    }

    inline void operator += (complx &other){
        real += other.real, img += other.img;
    }

    inline void operator -= (complx &other){
        real -= other.real, img -= other.img;
    }

    inline complx operator + (complx &other){
        return complx(real + other.real, img + other.img);
    }

    inline complx operator - (complx &other){
        return complx(real - other.real, img - other.img);
    }

    inline complx operator * (complx& other){
        return complx((real * other.real) - (img * other.img), (real * other.img) + (img * other.real));
    }
};
;

void FFT(vector <complx> &ar, int n, int inv){
    int i, j, l, len, len2;
    const long double p = 4.0 * inv * acos(0.0);

    for (i = 1, j = 0; i < n; i++){
        for (l = n >> 1; j >= l; l >>= 1) j -= l;
        j += l;
        if (i < j) swap(ar[i], ar[j]);
    }

    for(len = 2; len <= n; len <<= 1) {
        long double ang = 2 * PI / len * inv;
        complx wlen(cos(ang), sin(ang));
        for(i = 0; i < n; i += len) {
            complx w(1);
            for(j = 0; j < len / 2; j++) {
                complx u = ar[i + j];
                complx v = ar[i + j + len / 2] * w;
                ar[i + j] = u + v;
                ar[i + j + len / 2] = u - v;
                w = w * wlen;
            }
        }
    }

    if (inv == -1){
        long double tmp = 1.0 / n;
        for (i = 0; i < n; i++) ar[i].real *= tmp;
    }
}


vector <complx> Mul(const vector <complx> &x, const vector <complx> &y) {
    int n = 1;
    while(n <= x.size() + y.size()) n = n * 2;
    vector <complx> A(n), B(n);
    Rep(i, x.size()) A[i] = x[i];
    Rep(i, y.size()) B[i] = y[i];
    FFT(A, n, 1);
    FFT(B, n, 1);
    Rep(i, n) A[i] = A[i] * B[i];
    FFT(A, n, -1);
    return A;
}

int in[N];
LL res[N];
string num;
vL numBs;
LL maxPower3, base;

vL bruteForceMul(vL &A, vL &B, LL bs = 10) {
    vL a = A, b = B; if(a.size() > b.size()) swap(a, b);
    vL r;
    LL carry = 0;
    LL m = a[0];
    for(int i = b.size() - 1, j = 0; i >= 0; i--) {
        LL cur = (carry + b[i] * m);
        r.pb(cur % bs);
        carry = cur / bs;
    }
    if(carry) r.pb(carry);
    reverse(all(r));
    return r;
}

vL bigNumMul(vL &a, vL &b, LL bs = 10) {
    if(min(b.size(), a.size()) == 1) return bruteForceMul(a, b, bs);
    string r;
    int na = a.size();
    int nb = b.size();
    vector <complx> A(na), B(nb);
    for(int i = 0; i < na; i++) A[i] = complx(a[na - i - 1]);
    for(int i = 0; i < nb; i++) B[i] = complx(b[nb - i - 1]);

    int n = na + nb - 1;
    vector <complx> R = Mul(A, B);
    vector <LL> rs(n + 1, 0);
    for(int i = 0; i < n; i++) rs[i] = round(R[i].real);
    for(int i = 0; i < n; i++) {
        rs[i + 1] += rs[i] / bs;
        rs[i] %= bs;
    }
    while(n > 0 && rs[n] == 0) n--; n++;
    rs.resize(n);
    reverse(all(rs));
    return rs;
}

char bigNumCompare(vL &a, vL &b) {
    if(a.size() == b.size()) {
        for(int i = 0; i < a.size(); i++) {
            if(a[i] < b[i]) return '<';
            if(a[i] > b[i]) return '>';
        }
        return '=';
    }
    return (a.size() < b.size()) ? '<' : '>';
}


vL bigPow(vL R, vL a, int b) {
    while(b) {
        if(b & 1) R = bigNumMul(R, a, base);
        a = bigNumMul(a, a, base);
        b = b / 2;
    }
    return R;
}

int ans_me() {
    int L = numBs.size();
    int P = (num.size() - 1) * log(10) / log(3);
    P = max(0, P - 1);
    int sum = 3 * P;
    int ret = inf;
    vL temp;
    vL b = vL {3};
    vL b2 = vL {2};
    vL b4 = vL {4};
    vL threePowP = bigPow(vL {1}, b, P);

    while(bigNumCompare(threePowP, numBs) == '<') {
        if(bigNumCompare(temp = bigNumMul(threePowP, b2, base), numBs) != '<') ret = min(ret, sum + 2);
        if(bigNumCompare(temp = bigNumMul(threePowP, b4, base), numBs) != '<') ret = min(ret, sum + 4);

        threePowP = bigNumMul(threePowP, b, base);
        sum += 3;
    }
    ret = min(ret, sum);

    return ret;
}


vL convertBase(string nc, LL bs) {
    LL pw = 0, sv = bs;
    vL ret;
    while(sv % 10 == 0) pw++, sv /= 10;
    LL r = nc.size() % pw; r = (pw - r) % pw;
    while(r--) nc = '0' + nc;
    for(int i = 0; i < nc.size() / pw; i++) {
        int c = 0;
        for(int j = 0; j < pw; j++) c = c * 10 + nc[i * pw + j] - '0';
        ret.pb(c);
    }
    return ret;
}

int main()
{
    base = 1000;
    maxPower3 = 1500000 * log(10) / log(3); maxPower3++;
    cerr << maxPower3 << "\n";

    cin >> num;
    numBs = convertBase(num, base);

    int res = ans_me();
    res = max(res, 1);

    cout << res << "\n";
    return 0;
}
