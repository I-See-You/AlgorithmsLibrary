#include <bits/stdc++.h>


#define gc getchar unlocked
#ifndef ONLINE JUDGE
#define gc getchar
#endif // ONLINE JUDGE

#define pc putchar_unlocked
#ifndef ONLINE JUDGE
#define pc putchar
#endif // ONLINE JUDGE

#define fRead           freopen("input.txt","r",stdin)
#define fWrite          freopen ("output.txt","w",stdout)

#define eps             1e-8
#define inf             0x3f3f3f3f
#define INF             2e18
#define LL              long long
#define ULL             unsigned long long
#define PI              acos(-1.0)
#define pb              push_back
#define mk              make_pair
#define pii             pair<int,int>
#define pLL             pair<LL,LL>
#define vi              vector <int>
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

using namespace std;

const int MOD = 1e9 + 7;
int fx[] = {+0,+1,+0,-1,+1,+1,-1,-1,+0};
int fy[] = {+1,+0,-1,+0,+1,-1,+1,-1,+0};
template <typename T> inline T GCD (T a,T b ) {a = abs(a);b = abs(b); if(a < b) swap(a, b); while ( b ) { a = a % b; swap ( a, b ); } return a;}
template <typename T> inline T EGCD(T a,T b,T &x,T &y){if(a == 0) {x = 0;y = 1;return b;}T x1, y1;T d = EGCD(b % a, a, x1, y1);x = y1 - (b / a) * x1;y = x1;return d;}
template <typename T> inline T LCM(T x,T y){T tp = GCD(x,y);if( (x / tp) * 1. * y > 9e18) return 9e18;return (x / tp) * y;}
template <typename T> inline T BigMod(T A,T B,T M = MOD){T ret = 1;while(B){if(B & 1) ret = (ret * A) % M;A = (A * A) % M;B = B >> 1;}return ret;}
template <typename T> inline T InvMod (T A,T M = MOD){return BigMod(A,M-2,M);}
/*---------------------------fast I/O------------------------------------*/
#define scani2(a,b) scani(a) , scani(b)
#define scani3(a,b,c) scani(a), scani(b), scani(c)
#define scani4(a,b,c,d) scani(a), scani(b), scani(c), scani(d)
#define scani5(a,b,c,d,e) scani(a), scani(b), scani(c), scani(d) , scani(e)
template <typename T> T scani(T &n){n = 0;bool negative = false;char c = gc();while( c < '0' || c > '9'){if(c == '-') negative = true;c = gc();}while(c >= '0' && c <= '9'){n = n*10 + c-48;c = gc();}if(negative) n = ~(n-1);return n;}
template <typename T> void write(T n,int type = true){if(n<0) {pc('-');n = -n;}if(!n) {pc('0');if(type==32) pc(' '); else if(type) pc('\n'); return;}char buff[22];int len = 0;while(n) buff[len++] = n%10+48,n/=10;for(int i=len-1;i>=0;i--) pc(buff[i]);if(type==32) pc(' '); else if(type) pc('\n');}
int scans(char *a){int i=0;char c = 0;while(c < 33) c = gc();while(c > 33){a[i++] = c;c = gc();}a[i] = 0;return i;}
/*********************************************** End of template *********************************************/
const int N = 100005;

ULL Hash[N];
int type[N], del[N];
pii F1[N], F2[N], qr[N], P[N];
int n, m, mX, mY;

struct treeY{
    treeY *L, *R;
    ULL H;
    treeY(){
        L = R = NULL;
        H = 0;
    }
};

struct treeX{
    treeY *SegY;
    treeX *L, *R;
    treeX(){
        SegY = NULL;
        L = R = NULL;
    }
}*root = NULL;


void updateY(treeY *&node, int b, int e, int id)
{
    if(b > F2[id].ss || e < F1[id].ss) return ;
    if(node == NULL) {
        node = new treeY();
    }
    if(F1[id].ss <= b && e <= F2[id].ss){
        node->H ^= Hash[id];
        return ;
    }
    int mid = (b + e) >> 1;
    updateY(node->L, b, mid, id);
    updateY(node->R, mid + 1, e, id);
}


void updateX(treeX *&node, int b, int e, int id)
{
    if(b > F2[id].ff || e < F1[id].ff) return ;
    if(node == NULL) {
        node = new treeX();
    }
    if(F1[id].ff <= b && e <= F2[id].ff){
        updateY(node->SegY, 0, mY, id);
        return ;
    }
    int mid = (b + e) >> 1;
    updateX(node->L, b, mid, id);
    updateX(node->R, mid + 1, e, id);
}


ULL queryY(treeY *node, int b, int e, int id)
{
    if(b > P[id].ss || e < P[id].ss) return 0ULL;
    if(node == NULL) {
        return 0ULL;
    }
    if(P[id].ss <= b && e <= P[id].ss){
        return node->H;
    }
    int mid = (b + e) >> 1;
    return (node->H) ^ queryY(node->L, b, mid, id) ^ queryY(node->R, mid + 1, e, id);
}


ULL queryX(treeX *node, int b, int e, int id)
{
    if(b > P[id].ff || e < P[id].ff) return 0ULL;
    if(node == NULL) {
        return 0ULL;
    }
    if(P[id].ff <= b && e <= P[id].ff){
        return queryY(node->SegY, 0, mY, id);
    }
    int mid = (b + e) >> 1;
    return queryY(node->SegY, 0, mY, id) ^ queryX(node->L, b , mid, id) ^ queryX(node->R, mid + 1, e, id);
}


void compress()
{
    mX = -1;
    mY = -1;
    set <int> st;
    map <int, int> Mp;
    for(int i=1;i<=n;i++) st.insert(P[i].ff);
    for(int i=1;i<=m;i++) {
        if(type[i] == 1){
            st.insert(F1[i].ff);
            st.insert(F2[i].ff);
        }
    }
    FOR(st, it) Mp[*it] = ++mX;
    for(int i=1;i<=n;i++) P[i].ff = Mp[P[i].ff];
    for(int i=1;i<=m;i++){
        if(type[i] == 1){
            F1[i].ff = Mp[F1[i].ff];
            F2[i].ff = Mp[F2[i].ff];
        }
    }
    st.clear();
    Mp.clear();
    for(int i=1;i<=n;i++) st.insert(P[i].ss);
    for(int i=1;i<=m;i++){
        if(type[i] == 1){
            st.insert(F1[i].ss);
            st.insert(F2[i].ss);
        }
    }
    FOR(st, it) Mp[*it] = ++mY;
    for(int i=1;i<=n;i++) P[i].ss = Mp[P[i].ss];
    for(int i=1;i<=m;i++){
        if(type[i] == 1){
            F1[i].ss = Mp[F1[i].ss];
            F2[i].ss = Mp[F2[i].ss];
        }
    }
    st.clear();
    Mp.clear();
}



int main()
{
    root = new treeX();
    scani2(n, m);
    for(int i=1;i<=n;i++) scani2(P[i].ff, P[i].ss);
    for(int i=1;i<=m;i++){
        char ck[11];
        scanf("%s",ck);
        if(ck[0] == 'a'){
            type[i] = 1;
            scani4(F1[i].ff, F1[i].ss, F2[i].ff, F2[i].ss);
            Hash[i] = 1ULL * (i + 420) * (i * 13) * (i - 7) + 6;
        }
        else if(ck[0] == 'd'){
            type[i] = 2;
            scani(del[i]);
        }
        else {
            type[i] = 3;
            scani2(qr[i].ff, qr[i].ss);
        }
    }

    compress();

    for(int i=1;i<=m;i++){
        if(type[i] == 1){
            updateX(root, 0, mX, i);
        }
        else if(type[i] == 2){
            updateX(root, 0, mX, del[i]);
        }
        else {
            ULL y = queryX(root, 0, mX, qr[i].ss);
            ULL x = queryX(root, 0, mX, qr[i].ff);
            if(x == y) printf("YES\n");
            else printf("NO\n");
        }
    }
    return 0;
}
