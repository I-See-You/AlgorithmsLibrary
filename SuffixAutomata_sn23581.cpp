//http://codeforces.com/contest/427/problem/D

// Suffix Automata
#include<stdio.h>
#include<iostream>
#include<string.h>
#include<stdlib.h>
#include<math.h>
#include<algorithm>
#include<set>
#include<map>
#include<utility>
#include<vector>
#include<string>
#include<stack>
#include<queue>
using namespace std;               //REMEMBER TO TAKE DOUBLE SIZED ARRAY
#define MAXLEN 20000
struct State
{
    int len, link;
    map < char , int > nxtc;
} SA[2*MAXLEN];
int NumOcc[2*MAXLEN];
char str[MAXLEN];
vector < pair < int , int > > lenState;
class SuffixAutomata
{
    int sz, last, lm;
    int fnl;
    void init(int idx)
    {
        SA[idx].len = 0, SA[idx].link = -1;
        SA[idx].nxtc.clear();
    }
public:
    SuffixAutomata()
    {
        sz = last = 0;
        init(0);
        lenState.clear();
        lm = 0;
        ++sz;
    }
    int size() {return sz;}
    void extend(char ch, bool *mark)
    {
        int p, q, clone, cur = sz++;
        lm = fnl = cur;
        init(cur);
        SA[cur].len = SA[last].len + 1;
        lenState.push_back(make_pair(SA[cur].len, cur));
        for (p = last; p != -1 && SA[p].nxtc.count(ch) == 0; p = SA[p].link) SA[p].nxtc[ch] = cur;
        if (p == -1) SA[cur].link = 0;
        else
        {
            q = SA[p].nxtc[ch];
            if (SA[p].len + 1 == SA[q].len) SA[cur].link = q;
            else
            {
                clone = sz++;
                init(clone);
                SA[clone] = SA[q];
                mark[clone] = mark[q];
                SA[clone].len = SA[p].len + 1;
                for (; p != -1 && SA[p].nxtc[ch] == q; p = SA[p].link) SA[p].nxtc[ch] = clone;
                SA[cur].link = SA[q].link = clone;
                lenState.push_back(make_pair(SA[clone].len, clone));
            }
        }
        last = cur;
    }
    void numOcc(bool *mark, bool t)
    {
        int i,p,q;
        map < char, int > :: iterator im;
        memset(NumOcc, 0, sizeof(NumOcc));
        NumOcc[lm] = 1;
        sort(lenState.begin(), lenState.end());
        for (i=lenState.size()-1; i>=0; --i)
        {
            p = lenState[i].second;
            if (p < 1) continue;
            map < char , int > &M = SA[p].nxtc;
            for (im = M.begin(); im != M.end(); ++im)
            {
                q = im -> second;
                NumOcc[p] += NumOcc[q];
            }
        }
        if (!t) return;
        for (q=1; q<sz; ++q)
        {
            if (NumOcc[q] == 1) mark[q] = true;
        }
    }
    int calc(bool *mark)
    {
        int i,p,q;
        int ret = -1,temp;
        for (q=1; q<sz; ++q)
        {
            if (NumOcc[q] == 2 && mark[q])
            {
                p = SA[q].link;
                temp = SA[p].len + 1;
                if (ret == -1 || ret > temp) ret = temp;
            }
        }
        return ret;
    }
};
bool mark[MAXLEN];
int main()
{
    int i;
    while(scanf("%s", str) != EOF)
    {
        SuffixAutomata temp;
        memset(mark, 0, sizeof(mark));
        for (i=0; str[i]; ++i) temp.extend(str[i],mark);
        temp.extend('$',mark);
        temp.numOcc(mark,1);
        scanf("%s", str);
        for (i=0; str[i]; ++i) temp.extend(str[i],mark);
        temp.extend('#',mark);
        temp.numOcc(mark,0);
        printf("%d\n", temp.calc(mark));
    }
    return 0;
}
