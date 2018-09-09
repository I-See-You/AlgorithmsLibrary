#include <bits/stdtr1c++.h>

#define LET 26
#define MAX 300010
#define clr(ar) memset(ar, 0, sizeof(ar))
#define read() freopen("lol.txt", "r", stdin)
#define dbg(x) cout << #x << " = " << x << endl

using namespace std;


long long solve(long long a, long long b, long long n) {
    if (a > b) {
        swap(a, b);
    }
    if (a == b){
        return n / a;
    }
    long long k = min((b - 1) / (b - a), n / a);
    long long res = ((2 * (a - 1) - (b - a) * (k - 1)) * k) >> 1;
    if (a * (k + 1) > n && k * b < n) {
        res += (n - k * b);
    }
    return n + 1 - res;
}

int main()
{
    long long A, B, N;
    while(cin >> A >> B >> N) {
        cout << solve(A, B, N) << '\n';
    }
    return 0;
}
