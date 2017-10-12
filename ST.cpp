#include <bits/stdc++.h>
using namespace std;

int M[100000][20];

int main()
{
    int n;
    cin >> n;
    for(int i=0;i<n;i++) cin >> M[i][0];

    for(int j=1;(1<<j) <= n;j++)
        for(int i=0;i + (1<<j) <= n;i++)
            M[i][j] = min(M[i][j-1], M[i + (1<<(j-1))][j-1]);
    int qr;
    cin >> qr;
    while(qr--)
    {
        int x,y;
        cin >> x >> y;
        int k = log2(y-x+1);
        int ans = min(M[x][k] , M[y - (1<<k) + 1][k]);
        cout << ans << endl;
    }
    return 0;
}
