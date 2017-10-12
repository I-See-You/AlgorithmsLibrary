
#include<bits/stdc++.h>
using namespace std;
#define RANGE 20006
bool sieve[RANGE];
int fprime[RANGE];
vector < pair < int , int > > ppf;
vector < int > divset;
void primeTable()
{
    int i,j;
    int lim = sqrt((double) RANGE)+6;
    memset(fprime, -1, sizeof(fprime));
    fprime[2] = 2;
    for (i=4; i<RANGE; i+=2) sieve[i] = true, fprime[i] = 2;
    for (i=3; i<lim; i+=2)
    {
        if (!sieve[i])
        {
            fprime[i] = i;
            for (j=i*i; j<RANGE; j += (i<<1))
            {
                sieve[j] = true;
                if (fprime[j] == -1) fprime[j] = i;
            }
        }
    }
    for (; i<RANGE; i+=2)
    {
        if (!sieve[i]) fprime[i] = i;
    }
}

/**
 *   //////////////////
 *   // MAXIMUM FLOW //
 *   //////////////////
 *
 * This file is part of my library of algorithms found here:
 *      http://shygypsy.com/tools/
 * LICENSE:
 *      http://shygypsy.com/tools/LICENSE.html
 * Copyright (c) 2006
 * Contact author:
 *      abednego at gmail.c0m
 **/

/****************
 * Maximum flow * (Dinic's on an adjacency list + matrix)
 ****************
 * Takes a weighted directed graph of edge capacities as an adjacency
 * matrix 'cap' and returns the maximum flow from s to t.
 *
 * PARAMETERS:
 *      - cap (global): adjacency matrix where cap[u][v] is the capacity
 *          of the edge u->v. cap[u][v] is 0 for non-existent edges.
 *      - n: the number of vertices ([0, n-1] are considered as vertices).
 *      - s: source vertex.
 *      - t: sink.
 * RETURNS:
 *      - the flow
 *      - prev contains the minimum cut. If prev[v] == -1, then v is not
 *          reachable from s; otherwise, it is reachable.
 * RUNNING TIME:
 *      - O(n^3)
 * FIELD TESTING:
 *      - Valladolid 10330: Power Transmission (Gives WA, but it's probably my graph building that's wrong)
 *      - Valladolid 563:   Crimewave
 *      - Valladolid 753:   A Plug for UNIX
 *      - Valladolid 10511: Councilling
 *      - Valladolid 820:   Internet Bandwidth
 *      - Valladolid 10779: Collector's Problem
 * #include <string.h>
 **/

#include <string.h>
#include <stdio.h>

// the maximum number of vertices
#define NN 206

// adjacency matrix (fill this up)
// If you fill adj[][] yourself, make sure to include both u->v and v->u.
int cap[NN][NN], deg[NN], adj[NN][NN];

// BFS stuff
int q[NN], prev[NN];

int dinic( int n, int s, int t )
{
    int flow = 0;

    while( true )
    {
        // find an augmenting path
        memset( prev, -1, sizeof( prev ) );
        int qf = 0, qb = 0;
        prev[q[qb++] = s] = -2;
        while( qb > qf && prev[t] == -1 )
            for( int u = q[qf++], i = 0, v; i < deg[u]; i++ )
                if( prev[v = adj[u][i]] == -1 && cap[u][v] )
                    prev[q[qb++] = v] = u;

        // see if we're done
        if( prev[t] == -1 ) break;

        // try finding more paths
        for( int z = 0; z < n; z++ ) if( cap[z][t] && prev[z] != -1 )
        {
            int bot = cap[z][t];
            for( int v = z, u = prev[v]; u >= 0; v = u, u = prev[v] )
                //bot <?= cap[u][v];
                if (cap[u][v] < bot) bot = cap[u][v];
            if( !bot ) continue;

            cap[z][t] -= bot;
            cap[t][z] += bot;
            for( int v = z, u = prev[v]; u >= 0; v = u, u = prev[v] )
            {
                cap[u][v] -= bot;
                cap[v][u] += bot;
            }
            flow += bot;
        }
    }

        return flow;
}

//----------------- EXAMPLE USAGE -----------------
int incap[206][206];
pair < int , int > arr[206];
bool cmp(pair < int , int > pa, pair < int , int > pb)
{
    int a = pa.first, b = pb.first;
    return (a&1) < (b&1);
}
int build()
{
    int N,i,j;
    scanf("%d", &N);
    for (i=1; i<=N; ++i) scanf("%d", &arr[i].first), arr[i].second = i;
    /// read a graph into cap[][]
    memset(cap, 0, sizeof(cap));
    for (i=1; i<=N; ++i)
    {
        if (arr[i].first&1) cap[0][i] = 2;
        else cap[i][N+1] = 2;
    }
    for (i=1; i<=N; ++i)
    {
        for (j=i+1; j<=N; ++j)
        {
            if (sieve[arr[i].first+arr[j].first]) continue;
            if (arr[i].first&1) cap[i][j] = incap[i][j] = 1;//, printf("edge %d %d\n", i,j);
            else cap[j][i] = incap[j][i] = 1;//, printf("edge %d %d\n", j,i);
        }
    }
    return N+2;
}
vector < int > Edges[206];
vector < vector < int > > ans;
vector < int > cur;
int vis[206];
void dfs(int node)
{
    vis[node] = true;
    cur.push_back(node);
    int i,now;
    for (i=0; i<Edges[node].size(); ++i)
    {
        now = Edges[node][i];
        if (vis[now]) continue;
        dfs(now);
        break;
    }
}
int main()
{
    primeTable();
    int n = build(), s, t, m;
    s = 0, t = n-1;

    // init the adjacency list adj[][] from cap[][]
    memset( deg, 0, sizeof( deg ) );
    for( int u = 0; u < n; u++ )
        for( int v = 0; v < n; v++ ) if( cap[u][v] || cap[v][u] )
            adj[u][deg[u]++] = v;

    int fl = dinic( n, s, t );
    int N = n-2;
    if (fl != N)
    {
        puts("Impossible");
        return 0;
    }
    int i,j;
    for (i=1; i<=N; ++i)
    {
        for (j=1; j<=N; ++j)
        {
            if (incap[i][j] != cap[i][j])
            {
                //printf("-- %d %d\n", i,j);
                Edges[i].push_back(j);
                Edges[j].push_back(i);
            }
        }
    }
    ans.clear();
    for (i=1; i<=N; ++i)
    {
        if (vis[i]) continue;
        cur.clear();
        dfs(i);
        ans.push_back(cur);
    }
    printf("%d\n", ans.size());
    for (i=0; i<ans.size(); ++i)
    {
        cur = ans[i];
        printf("%d", cur.size());
        for (j=0; j<cur.size(); ++j) printf(" %d", cur[j]);
        puts("");
    }
    return 0;
}
