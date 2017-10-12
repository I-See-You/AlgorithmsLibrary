// http://codeforces.com/contest/819/problem/C

#include <cstdio>
#include <cstring>
#include <cmath>
#include <algorithm>
#include <vector>
#include <string>
#include <map>
#include <set>
#include <cassert>
using namespace std;
#define rep(i,a,n) for (int i=a;i<n;i++)
#define per(i,a,n) for (int i=n-1;i>=a;i--)
#define pb push_back
#define mp make_pair
#define all(x) (x).begin(),(x).end()
#define fi first
#define se second
#define SZ(x) ((int)(x).size())
typedef vector<int> VI;
typedef long long ll;
typedef pair<int,int> PII;
const ll mod=1000000007;
ll powmod(ll a,ll b) {ll res=1;a%=mod; assert(b>=0); for(;b;b>>=1){if(b&1)res=res*a%mod;a=a*a%mod;}return res;}
// head

typedef pair<ll,ll> PLL;
namespace Factor {
	const int N=2010000;
	ll C,fac[10010],n,mut,a[1001000];
	int T,cnt,i,l,prime[N],p[N],psize,_cnt;
	ll _e[100],_pr[100];
	vector<ll> d;
	inline ll mul(ll a,ll b,ll p) {
		if (p<=1000000000) return a*b%p;
		else if (p<=1000000000000ll) return (((a*(b>>20)%p)<<20)+(a*(b&((1<<20)-1))))%p;
		else {
			ll d=(ll)floor(a*(long double)b/p+0.5);
			ll ret=(a*b-d*p)%p;
			if (ret<0) ret+=p;
			return ret;
		}
	}
	void prime_table(){
		int i,j,tot,t1;
		for (i=1;i<=psize;i++) p[i]=i;
		for (i=2,tot=0;i<=psize;i++){
			if (p[i]==i) prime[++tot]=i;
			for (j=1;j<=tot && (t1=prime[j]*i)<=psize;j++){
				p[t1]=prime[j];
				if (i%prime[j]==0) break;
			}
		}
	}
	void init(int ps) {
		psize=ps;
		prime_table();
	}
	ll powl(ll a,ll n,ll p) {
		ll ans=1;
		for (;n;n>>=1) {
			if (n&1) ans=mul(ans,a,p);
			a=mul(a,a,p);
		}
		return ans;
	}
	bool witness(ll a,ll n) {
		int t=0;
		ll u=n-1;
		for (;~u&1;u>>=1) t++;
		ll x=powl(a,u,n),_x=0;
		for (;t;t--) {
			_x=mul(x,x,n);
			if (_x==1 && x!=1 && x!=n-1) return 1;
			x=_x;
		}
		return _x!=1;
	}
	bool miller(ll n) {
		if (n<2) return 0;
		if (n<=psize) return p[n]==n;
		if (~n&1) return 0;
		for (int j=0;j<=7;j++) if (witness(rand()%(n-1)+1,n)) return 0;
		return 1;
	}
	ll gcd(ll a,ll b) {
		ll ret=1;
		while (a!=0) {
			if ((~a&1) && (~b&1)) ret<<=1,a>>=1,b>>=1;
			else if (~a&1) a>>=1; else if (~b&1) b>>=1;
			else {
				if (a<b) swap(a,b);
				a-=b;
			}
		}
		return ret*b;
	}
	ll rho(ll n) {
		for (;;) {
			ll X=rand()%n,Y,Z,T=1,*lY=a,*lX=lY;
			int tmp=20;
			C=rand()%10+3;
			X=mul(X,X,n)+C;*(lY++)=X;lX++;
			Y=mul(X,X,n)+C;*(lY++)=Y;
			for(;X!=Y;) {
				ll t=X-Y+n;
				Z=mul(T,t,n);
				if(Z==0) return gcd(T,n);
				tmp--;
				if (tmp==0) {
					tmp=20;
					Z=gcd(Z,n);
					if (Z!=1 && Z!=n) return Z;
				}
				T=Z;
				Y=*(lY++)=mul(Y,Y,n)+C;
				Y=*(lY++)=mul(Y,Y,n)+C;
				X=*(lX++);
			}
		}
	}
	void _factor(ll n) {
		for (int i=0;i<cnt;i++) {
			if (n%fac[i]==0) n/=fac[i],fac[cnt++]=fac[i];}
		if (n<=psize) {
			for (;n!=1;n/=p[n]) fac[cnt++]=p[n];
			return;
		}
		if (miller(n)) fac[cnt++]=n;
		else {
			ll x=rho(n);
			_factor(x);_factor(n/x);
		}
	}
	void dfs(ll x,int dep) {
		if (dep==_cnt) d.pb(x);
		else {
			dfs(x,dep+1);
			for (int i=1;i<=_e[dep];i++) dfs(x*=_pr[dep],dep+1);
		}
	}
	void norm() {
		sort(fac,fac+cnt);
		_cnt=0;
		rep(i,0,cnt) if (i==0||fac[i]!=fac[i-1]) _pr[_cnt]=fac[i],_e[_cnt++]=1;
			else _e[_cnt-1]++;
	}
	vector<ll> getd() {
		d.clear();
		dfs(1,0);
		return d;
	}
	vector<ll> factor(ll n) {
		cnt=0;
		_factor(n);
		norm();
		return getd();
	}
	vector<PLL> factorG(ll n) {
		cnt=0;
		_factor(n);
		norm();
		vector<PLL> d;
		rep(i,0,_cnt) d.pb(mp(_pr[i],_e[i]));
		return d;
	}
	bool is_primitive(ll a,ll p) {
		assert(miller(p));
		vector<PLL> D=factorG(p-1);
		rep(i,0,SZ(D)) if (powl(a,(p-1)/D[i].fi,p)==1) return 0;
		return 1;
	}
}

int pre[110][110],_;
ll n[10],m[10],s[10],ans;
int ppr[110],ff[110],ee[110],cntt;
map<ll,int> mn,mm,ms;
vector<ll> d;
void gao(ll *a,map<ll,int> &hs) {
	hs.clear();
	a[0]=a[1]*a[2]*a[3];
	rep(i,1,4) {
		vector<PLL> d=Factor::factorG(a[i]);
		for (auto v:d) hs[v.fi]+=v.se;
	}
}
void dfs(ll x,int dep) {
	if (dep==cntt) {
		d.pb(x);
//		printf("ff %lld\n",x);
	} else {
		dfs(x,dep+1);
		for (int i=1;i<=ee[dep];i++) dfs(x*=ppr[dep],dep+1);
	}
}
void dfs2(ll x,int dep,int sign) {
	if (sign==0) return;
	if (dep==cntt) {
		ans+=sign*(m[0]/x);
	} else {
		dfs2(x,dep+1,sign*pre[0][ff[dep]]);
		for (int i=1;i<=ee[dep];i++) dfs2(x*=ppr[dep],dep+1,sign*pre[i][ff[dep]]);
	}
}
void gen(map<ll,int> hs) {
	d.clear();
	cntt=0;
	for (auto p:hs) ppr[cntt]=p.fi,ee[cntt]=p.se,cntt++;
//	printf("gg %d\n",cntt);
	dfs(1,0);
}
int main() {
	rep(i,0,66) rep(j,0,66) rep(k,0,i+1) {
		if (i-k>j) continue;
		if (k==1) pre[i][j]--; else if (k==0) pre[i][j]++;
	}
	Factor::init(2000000);
	for (scanf("%d",&_);_;_--) {
		rep(i,1,4) scanf("%lld",n+i);
		gao(n,mn);
		rep(i,1,4) scanf("%lld",m+i);
		gao(m,mm);
		rep(i,1,4) scanf("%lld",s+i);
		s[1]*=2;
		gao(s,ms); gen(ms);
		ans=0;
		for (auto v:d) if (v<=n[0]) ans++;
		cntt=0;
		for (auto p:mn) {
			ppr[cntt]=p.fi;
			ff[cntt]=ms[p.fi];
			ee[cntt]=p.se;
			cntt++;
		}
		dfs2(1,0,1);
		printf("%lld\n",ans);
	}
}



//
//#include <bits/stdc++.h>
////#include <ext/pb_ds/assoc_container.hpp>
////using namespace __gnu_pbds;
//using namespace std;
//
//
//#define gc getchar unlocked
//#ifndef ONLINE JUDGE
//#define gc getchar
//#endif // ONLINE JUDGE
//
//#define pc putchar_unlocked
//#ifndef ONLINE JUDGE
//#define pc putchar
//#endif // ONLINE JUDGE
//
//#define fRead           freopen("input.txt","r",stdin)
//#define fWrite          freopen("output.txt","w",stdout)
//
//#define eps             1e-9
//#define inf             0x3f3f3f3f
//#define INF             2e18
//#define LL              long long
//#define ULL             unsigned long long
//#define PI              acos(-1.0)
//#define pb              push_back
//#define mk              make_pair
//#define pii             pair<int,int>
//#define pLL             pair<LL,LL>
//#define ff              first
//#define ss              second
//#define all(a)          a.begin(),a.end()
//#define rall(a)         a.rbegin(),a.rend()
//#define SQR(a)          ((a)*(a))
//#define Unique(a)       sort(all(a)),a.erase(unique(all(a)),a.end())
//#define min3(a,b,c)     min(a,min(b,c))
//#define max3(a,b,c)     max(a,max(b,c))
//#define min4(a,b,c,d)   min(min(a,b),min(c,d))
//#define max4(a,b,c,d)   max(max(a,b),max(c,d))
//#define max5(a,b,c,d,e) max(max3(a,b,c),max(d,e))
//#define min5(a,b,c,d,e) min(min3(a,b,c),min(d,e))
//#define Iterator(a)     __typeof__(a.begin())
//#define rIterator(a)    __typeof__(a.rbegin())
//#define FOR(a,it)       for(Iterator(a) it = a.begin();it != a.end(); it++)
//#define rFOR(a,it)      for(rIterator(a) it = a.rbegin();it != a.rend(); it++)
//#define FastRead        ios_base::sync_with_stdio(0);cin.tie(0)
//#define CasePrint       pc('C'); pc('a'); pc('s'); pc('e'); pc(' '); write(qq++,false); pc(':'); pc(' ')
//#define vi              vector <int>
//#define vL              vector <LL>
//#define For(I,A,B)      for(int I = (A); I  < (B); ++I)
//#define rFor(I,A,B)     for(int I = (A); I >= (B); --I)
//#define Rep(I,N)        For(I,0,N)
//#define REP(I,N)        For(I, 1, N + 1)
//#define gti             int, vi, greater<int>
//#define gtL             LL, vL, greater<LL>
//#define Found(a, b)     a.find(b) != a.end()
//
//const int MOD = 1e9 + 7;
//int fx[] = {-1,+0,+1,+0,+1,+1,-1,-1,+0};
//int fy[] = {+0,-1,+0,+1,+1,-1,+1,-1,+0};
//int day[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
////template <typename T> using orderset = tree <T, null_type, less<T>, rb_tree_tag,tree_order_statistics_node_update>; // find_by_order, order_of_key
//template <typename T> inline bool isLeap(T y) {return (y % 400 == 0) || (y % 100 ? y % 4 == 0 : false); }
//template <typename T> inline T GCD (T a,T b ) {a = abs(a);b = abs(b); if(a < b) swap(a, b); while ( b ) { a = a % b; swap ( a, b ); } return a;}
//template <typename T> inline T EGCD(T a,T b,T &x,T &y){if(a == 0) {x = 0;y = 1;return b;}T x1, y1;T d = EGCD(b % a, a, x1, y1);x = y1 - (b / a) * x1;y = x1;return d;}
//template <typename T> inline T LCM(T x,T y){T tp = GCD(x,y);if( (x / tp) * 1. * y > 9e18) return 9e18;return (x / tp) * y;}
//template <typename T> inline T BigMod(T A,T B,T M = MOD){T ret = 1;while(B){if(B & 1) ret = (ret * A) % M;A = (A * A) % M;B = B >> 1;}return ret;}
//template <typename T> inline T InvMod (T A,T M = MOD){return BigMod(A,M-2,M);}
////template <typename T> void Compress(T * in, int n){vector <T> vv;for(int i = 0; i < n; i++) vv.pb(in[i]);Unique(vv);for(int i = 0; i < n; i++) in[i] = lower_bound(all(vv), in[i]) - vv.begin();}
////template <typename T> void Compress(vector <T> &in){vector <T> vv;for(T x : in) vv.pb(x);Unique(vv);for(int i = 0; i < in.size(); i++) in[i] = lower_bound(all(vv), in[i]) - vv.begin();}
///*---------------------------fast I/O------------------------------------*/
//#define scani2(a,b) scani(a) , scani(b)
//#define scani3(a,b,c) scani(a), scani(b), scani(c)
//#define scani4(a,b,c,d) scani(a), scani(b), scani(c), scani(d)
//#define scani5(a,b,c,d,e) scani(a), scani(b), scani(c), scani(d) , scani(e)
//template <typename T> T scani(T &n){n = 0;bool negative = false;char c = gc();while( c < '0' || c > '9'){if(c == '-') negative = true;c = gc();}while(c >= '0' && c <= '9'){n = n*10 + c-48;c = gc();}if(negative) n = ~(n-1);return n;}
//template <typename T> void write(T n,int type = true){if(n<0) {pc('-');n = -n;}if(!n) {pc('0');if(type==32) pc(' '); else if(type) pc('\n'); return;}char buff[22];int len = 0;while(n) buff[len++] = n%10+48,n/=10;for(int i=len-1;i>=0;i--) pc(buff[i]);if(type==32) pc(' '); else if(type) pc('\n');}
//int scans(char *a){int i=0;char c = 0;while(c < 33) c = gc();while(c > 33){a[i++] = c;c = gc();}a[i] = 0;return i;}
///*********************************************** End of template *********************************************/
//#define Sieve
//
//#ifdef Sieve
//const int pSz = 2000006;
//bool np[pSz + 10]; vi prime; int prime_size;void sieve(){np[0] = np[1] = 1;prime.pb(2);for(LL i = 4; i <= pSz; i+=2) np[i] = 1;for(LL i = 3; i <= pSz; i+=2){if(!np[i]){prime.pb(i);for(LL j = i * i; j <= pSz; j += (i << 1)) np[j] = 1;}}prime_size = prime.size();}
//#endif
//
//#ifdef Combi
//const int nSz = 2000006;
//LL F[nSz + 1], tMod = MOD;
//void Factorial(){ F[0] = 1; for(int i = 1; i <= nSz; i++) F[i] = (F[i - 1] * i) % tMod; }
//inline LL nCr(int n, int r) { return (F[n] * InvMod((F[n - r] * F[r]) % tMod, tMod)) % tMod; }
//#endif
//
//#ifdef Z_Algo
//void zAlgo(char *s, int *z){
//    int L, R, sz; sz = strlen(s); z[0] = L = R = 0;
//    For(i, 1, sz) { z[i] = 0; if(i <= R) z[i] = min(z[i - L], R - i + 1); while(i + z[i] < sz && s[i + z[i]] == s[z[i]]) z[i]++; if(i + z[i] - 1 > R) L = i, R = i + z[i] - 1; }
//}void zAlgo(string &s, int *z){
//    int L, R, sz; sz = s.size(); z[0] = L = R = 0;
//    For(i, 1, sz) { z[i] = 0; if(i <= R) z[i] = min(z[i - L], R - i + 1); while(i + z[i] < sz && s[i + z[i]] == s[z[i]]) z[i]++; if(i + z[i] - 1 > R) L = i, R = i + z[i] - 1; }
//}void zAlgo(int *s, int *z, int n){
//    int L, R, sz; sz = n; z[0] = L = R = 0;
//    For(i, 1, sz) { z[i] = 0; if(i <= R) z[i] = min(z[i - L], R - i + 1); while(i + z[i] < sz && s[i + z[i]] == s[z[i]]) z[i]++; if(i + z[i] - 1 > R) L = i, R = i + z[i] - 1; }
//}
//#endif // Z_Algo
//
//
///********************************************* define Template *************************************************/
//
//template <typename T> inline T SqrDis(T x1, T y1, T x2, T y2){return SQR(x1 - x2) + SQR(y1 - y2);}
//template <typename T> inline T Area2(T Ax, T Ay, T Bx, T By, T Cx, T Cy){T ret = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By);
//    if(ret < 0) return ret = -ret;
//    return ret;
//}
///**************************************************** GEO ******************************************************/
//const int N = 2000006;
//const int M = 44444;
//const ULL hs = 3797;
//
//namespace Factor {
//	const int N=2010000;
//	LL C,fac[10010],n,mut,a[1001000];
//	int T,cnt,i,l,prime[N],p[N],psize,_cnt;
//	LL _e[100],_pr[100];
//	vector<LL> d;
//	inline LL mul(LL a,LL b,LL p) {
//		if (p<=1000000000) return a*b%p;
//		else if (p<=1000000000000ll) return (((a*(b>>20)%p)<<20)+(a*(b&((1<<20)-1))))%p;
//		else {
//			LL d=(LL)floor(a*(long double)b/p+0.5);
//			LL ret=(a*b-d*p)%p;
//			if (ret<0) ret+=p;
//			return ret;
//		}
//	}
//	void prime_table(){
//		int i,j,tot,t1;
//		for (i=1;i<=psize;i++) p[i]=i;
//		for (i=2,tot=0;i<=psize;i++){
//			if (p[i]==i) prime[++tot]=i;
//			for (j=1;j<=tot && (t1=prime[j]*i)<=psize;j++){
//				p[t1]=prime[j];
//				if (i%prime[j]==0) break;
//			}
//		}
//	}
//	void init(int ps) {
//		psize=ps;
//		prime_table();
//	}
//	LL powl(LL a,LL n,LL p) {
//		LL ans=1;
//		for (;n;n>>=1) {
//			if (n&1) ans=mul(ans,a,p);
//			a=mul(a,a,p);
//		}
//		return ans;
//	}
//	bool witness(LL a,LL n) {
//		int t=0;
//		LL u=n-1;
//		for (;~u&1;u>>=1) t++;
//		LL x=powl(a,u,n),_x=0;
//		for (;t;t--) {
//			_x=mul(x,x,n);
//			if (_x==1 && x!=1 && x!=n-1) return 1;
//			x=_x;
//		}
//		return _x!=1;
//	}
//	bool miller(LL n) {
//		if (n<2) return 0;
//		if (n<=psize) return p[n]==n;
//		if (~n&1) return 0;
//		for (int j=0;j<=7;j++) if (witness(rand()%(n-1)+1,n)) return 0;
//		return 1;
//	}
//	LL gcd(LL a,LL b) {
//		LL ret=1;
//		while (a!=0) {
//			if ((~a&1) && (~b&1)) ret<<=1,a>>=1,b>>=1;
//			else if (~a&1) a>>=1; else if (~b&1) b>>=1;
//			else {
//				if (a<b) swap(a,b);
//				a-=b;
//			}
//		}
//		return ret*b;
//	}
//	LL rho(LL n) {
//		for (;;) {
//			LL X=rand()%n,Y,Z,T=1,*lY=a,*lX=lY;
//			int tmp=20;
//			C=rand()%10+3;
//			X=mul(X,X,n)+C;*(lY++)=X;lX++;
//			Y=mul(X,X,n)+C;*(lY++)=Y;
//			for(;X!=Y;) {
//				LL t=X-Y+n;
//				Z=mul(T,t,n);
//				if(Z==0) return gcd(T,n);
//				tmp--;
//				if (tmp==0) {
//					tmp=20;
//					Z=gcd(Z,n);
//					if (Z!=1 && Z!=n) return Z;
//				}
//				T=Z;
//				Y=*(lY++)=mul(Y,Y,n)+C;
//				Y=*(lY++)=mul(Y,Y,n)+C;
//				X=*(lX++);
//			}
//		}
//	}
//	void _factor(LL n) {
//		for (int i=0;i<cnt;i++) {
//			if (n%fac[i]==0) n/=fac[i],fac[cnt++]=fac[i];}
//		if (n<=psize) {
//			for (;n!=1;n/=p[n]) fac[cnt++]=p[n];
//			return;
//		}
//		if (miller(n)) fac[cnt++]=n;
//		else {
//			LL x=rho(n);
//			_factor(x);_factor(n/x);
//		}
//	}
//	void dfs(LL x,int dep) {
//		if (dep==_cnt) d.pb(x);
//		else {
//			dfs(x,dep+1);
//			for (int i=1;i<=_e[dep];i++) dfs(x*=_pr[dep],dep+1);
//		}
//	}
//	void norm() {
//		sort(fac,fac+cnt);
//		_cnt=0;
//		For(i,0,cnt) if (i==0||fac[i]!=fac[i-1]) _pr[_cnt]=fac[i],_e[_cnt++]=1;
//			else _e[_cnt-1]++;
//	}
//	vector<LL> getd() {
//		d.clear();
//		dfs(1,0);
//		return d;
//	}
//	vector<LL> factor(LL n) {
//		cnt=0;
//		_factor(n);
//		norm();
//		return getd();
//	}
//	vector<pLL> factorG(LL n) {
//		cnt=0;
//		_factor(n);
//		norm();
//		vector<pLL> d;
//		For(i,0,_cnt) d.pb(mk(_pr[i],_e[i]));
//		return d;
//	}
//	bool is_primitive(LL a,LL p) {
//		assert(miller(p));
//		vector<pLL> D=factorG(p-1);
//		For(i,0,D.size()) if (powl(a,(p-1)/D[i].ff,p)==1) return 0;
//		return 1;
//	}
//}
//
//
//int main()
//{
//    int t; scani(t);
//    while(t--) {
//        LL n; scani(n);
//
//    }
//    return 0;
//}
//
