#include <bits/stdc++.h>
using namespace std;

struct data {
    int id, f, s;
    data(){}
    data(int a, int b, int c) {
        id = a;
        f = b;
        s = c;
    }
    bool operator <(const data &yoo) const{
        if(f == yoo.f) return s < yoo.s;
        return f < yoo.f;
    }
}sfx[N];

int Rank[22][N], stp, n, Mc[N][22], lcp[N], rnk[N];
int dp[33][N], na, nb, k;
char a[N], b[N], in[N];

void suffixArray() {
    stp = 1; Rep(i, n) Rank[0][i] = in[i];
    for(int sz = 1; sz < n; sz *= 2, stp++) {
        Rep(i, n) {
            sfx[i].id = i;
            sfx[i].f = Rank[stp - 1][i];
            sfx[i].s = i + sz < n ? Rank[stp - 1][i + sz] : -1;
        } sort(sfx, sfx + n);
        int rk = 0; Rank[stp][ sfx[0].id ] = 0;
        For(i, 1, n) {
            if(sfx[i].f != sfx[i - 1].f || sfx[i].s != sfx[i - 1].s) rk++;
            Rank[stp][ sfx[i].id ] = rk;
        }
    }stp--;
    if(n == 1) Rank[0][0] = sfx[0].id = 0;
//    Rep(i, n) { For(j, sfx[i].id, n) printf("%c", in[j]); pc('\n'); }
}

void kasai() {
    Rep(i, n) rnk[ sfx[i].id ] = i;
    for(int i = 0, k = 0; i < n; i++, k ? k-- : 0) {
        if(rnk[i] == n - 1) {
            k = 0;
            continue;
        }
        int j = sfx[ rnk[i] + 1 ].id;
        while(i + k < n && j + k < n && in[i + k] == in[j + k]) k++;
        lcp[ rnk[i] ] = k;
    }
}

void sparsTable() {
    for(int i = 0; i < n; i++) Mc[i][0] = lcp[i];
    for(int j = 1; (1 << j) <= n; j++) for(int i = 0; i + (1 << j) <= n; i++) Mc[i][j] = min( Mc[i][j - 1], Mc[i + (1 << (j - 1))][j - 1] );
}

int lcpMatch(int x, int y) {
    x = Rank[stp][x];
    y = Rank[stp][y];
    if(x == y) return n - sfx[x].id;
    if(x > y) swap(x, y);
    int k = log2(y - x);
    return min( Mc[x][k], Mc[y - (1 << k)][k] );
}

int lcpMatchSlow(int x, int y) {
    if(x == y) return n - x;
    int ret = 0;
    for(int i = stp; i >= 0 && x < n && y < n; i--) {
        if(Rank[i][x] == Rank[i][y]) {
            x += (1 << i);
            y += (1 << i);
            ret += (1 << i);
        }
    }
    return ret;
}


int main()
{
    n = scani(in);
    SuffixArray();
    Rep(i, n) {
        For(j, sfx[i].id, n) printf("%c", in[j]);
        pc('\n');
    }
    For(i, 1, n) write(lcp[i]);

    return 0;
}
