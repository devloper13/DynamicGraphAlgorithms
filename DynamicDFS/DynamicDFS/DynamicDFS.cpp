//
//  main.cpp
//  Dynamic Graph DFS
//
//  Created by rishabh on 11/3/18.
//  Copyright © 2018 rishabh. All rights reserved.
//

#include <iostream>
#include <vector>
#include <set>
#include <utility>
#include <typeinfo>
#include <chrono>

using namespace std;
using namespace std::chrono;

#define root 0
#define INF 10100           //should change this and try
#define LgINF 14             //should change this and try

struct Cmp
{
    bool operator ()(const pair<int, int> &a, const pair< int, int> &b)
    {
        if (a.second == b.second)
            return a.first < b.first;
        return a.second < b.second;
    }
};
vector <int> gradjlist[INF],edgelist[INF],dfsadjlist[INF],hldadjlist[INF];
int visit[INF],subvisit[INF];
multiset<pair<int, int>,Cmp> baseArray[INF];
int ptr,segsize;
int chainNo, chainof[INF], chainHead[INF], posInBase[INF],lastchildofchain[INF];
int depth[INF], index_parent[LgINF][INF], otherEnd[INF], subtreesize[INF];

multiset<pair<int, int>,Cmp> segtree[INF*6], qt[INF*6],subtree,path;
multiset<pair<int, int> >::iterator itr;
pair<multiset<pair<int, int> >::iterator,bool> verify;
/***************** Utility ******************/
void print_adj(int v,vector <int> dfsadjlist[INF])
{
    for(int i=1;i <= v;i++)
    {
        printf("(%d %d)-> ",i,subtreesize[i]);
        for (int j =0; j < dfsadjlist[i].size() ; j++) {
            int temp = dfsadjlist[i].at(j);
            printf(" (%d %d)",temp,subtreesize[temp]);
        }
        printf("\n");
    }
}

void print_edgelist(multiset<pair<int, int>,Cmp> args)
{
    multiset<pair<int, int> >::iterator itr;
    for(int i =0;i<=segsize;i++)
    {
        printf("nodeId %d \n",i);
        for (itr = subtree.begin(); itr != subtree.end();itr++) {
            //printf("%d -> (%d %d)",i,&itr->first,&itr->second);
            cout<<itr->first<<" "<<itr->second<<endl;
        }
        printf("\n");
    }
}

void print_segtree()
{
    multiset<pair<int, int> >::iterator itr;
    for(int i =0;i<=segsize;i++)
    {
        printf("nodeId %d \n",i);
        for (itr = segtree[i].begin(); itr != segtree[i].end();itr++) {
            //printf("%d -> (%d %d)",i,&itr->first,&itr->second);
            cout<<itr->first<<" "<<itr->second<<endl;
        }
        printf("\n");
    }
}

pair<int, int> reverse_pair(pair<int, int> ri)
{
    return make_pair(ri.second, ri.first);
}

void print_dfs(int a,int b)
{
    int i=0;
    for(i=a;i<=b;i++)
        printf(" %d ",baseArray[i].begin()->first);
}
/***************** Dynamic Approach *******************/

void make_seg_tree(int u,int s,int e)
{
    if(s == e)
    {
            segtree[u].insert(baseArray[s].begin(),baseArray[s].end());
        if(segsize < u)
            segsize = u;
        return;
    }
    int child1 =u*2;
    int child2 =u*2 + 1;
    int mid = (s + e)/2;
    make_seg_tree(child1, s, mid);
    make_seg_tree(child2, mid+1, e);
    /* for each node in baseArray (constructed in HLD DFS) we have subgraph inside seg tree */

     segtree[u].insert(segtree[child1].begin(),segtree[child1].end());
     segtree[u].insert(segtree[child2].begin(),segtree[child2].end());
}


/* Updates will be applied to segment tree*/
int update_seg_tree(int u,int s,int e,int w,int v,int choice)
{
    int prev_first=0;
    set<pair<int, int> >::iterator itr;
    if(s == e && s == w)            //single cell update in Base array and segtree
    {
        if(choice == 1)
        {
            segtree[u].erase(make_pair(baseArray[s].begin()->first, v));
            baseArray[s].erase(make_pair(baseArray[s].begin()->first, v));
            return baseArray[s].begin()->first;
        }
        else if(choice == 2)
        {
            segtree[u].insert(make_pair(baseArray[s].begin()->first, v));
            baseArray[s].insert(make_pair(baseArray[s].begin()->first, v));
            return baseArray[s].begin()->first;
        }
    }
    int child1 =u*2;
    int child2 =u*2 + 1;
    int mid = (s + e)/2;
    if(w>=s && w<=mid)
    {
        prev_first = update_seg_tree(child1, s, mid,w,v,choice);
        segtree[u].erase(make_pair(prev_first, v));
        return prev_first;
    }
    else if(w>mid && w<=e)
    {
        prev_first = update_seg_tree(child2, mid+1, e,w,v,choice);
        segtree[u].erase(make_pair(prev_first, v));
        return prev_first;
    }
    /* for each node in baseArray (constructed in HLD DFS) we have subgraph inside seg tree */
    return prev_first;
}

void delete_from_adjlist(vector <int> adjlist[INF],int a,int b)
{
    int i=0;
    vector<int>::iterator itr;
    for(i=0;i<adjlist[a].size();i++)
    {
        if(adjlist[a].at(i) == b)
            break;
    }
    if(i != adjlist[a].size())
    adjlist[a].erase(adjlist[a].begin()+i);
    for(i=0;i<adjlist[b].size();i++)
    {
        if(adjlist[b].at(i) == a)
            break;
    }
    if(i != adjlist[b].size())
    adjlist[b].erase(adjlist[b].begin()+i);
}

void insert_from_adjlist(vector <int> adjlist[INF],int a,int b)
{
    int i=0;
    vector<int>::iterator itr;
    for(i=0;i<adjlist[a].size();i++)
    {
        if(adjlist[a].at(i) == b)
            break;
    }
    if(i != adjlist[a].size())
        adjlist[a].push_back(b);
    
    for(i=0;i<adjlist[b].size();i++)
    {
        if(adjlist[b].at(i) == a)
            break;
    }
    if(i != adjlist[b].size())
        adjlist[b].push_back(a);
}

void delete_query(int u,int v)
{
    update_seg_tree(1, 0, ptr-1, posInBase[u], v, 1);
    update_seg_tree(1, 0, ptr-1, posInBase[v], u, 1);
    //delete_from_adjlist(gradjlist, u, v);
    delete_from_adjlist(hldadjlist, u, v);
    delete_from_adjlist(dfsadjlist, u, v);
}

void insert_query(int u, int v)
{
    update_seg_tree(1, 0, ptr-1, posInBase[u], v, 2);
    update_seg_tree(1, 0, ptr-1, posInBase[v], u, 2);
    //insert_from_adjlist(gradjlist, u, v);
    insert_from_adjlist(dfsadjlist, u, v);
    insert_from_adjlist(hldadjlist, u, v);
}
/*collects all nodes inside Subtree T(w) */
multiset<pair<int, int>,Cmp> query_up_tree(int c,int s,int e,int u, int v)
{
    int i=0;
        if(s > v || e <u)
        {
            return subtree;
        }
        if(s >= u && e <= v){
            for(i=s;i <=e;i++)
            subtree.insert(baseArray[i].begin(),baseArray[i].end());
            return subtree;
        }
    int child1 =c * 2;
    int child2 =c * 2 + 1;
    int mid = (s + e)/2;
    
    query_up_tree(child1, s, mid, u, v);
    query_up_tree(child2, mid+1,e, u, v);
    return subtree;
}

/*collects all nodes inside Path u,v */
int query_up_tree_path(int c,int s,int e,int u, int v)
{
    int i=0;
    if(s > v || e <u)
    {
        return 0;
    }
    if(s >= u && e <= v){
        for(i=s;i <=e;i++)
            path.insert(baseArray[i].begin(),baseArray[i].end());
        return 1;
    }
    int child1 =c * 2;
    int child2 =c * 2 + 1;
    int mid = (s + e)/2;
    
    query_up_tree_path(child1, s, mid, u, v);
    query_up_tree_path(child2, mid+1,e, u, v);
    return 1;
}


/*
 * query_up_path:
 * It takes two nodes u and v, condition is that v is an ancestor of u
 * We query the chain in which u is present till chain head, then move to next chain up
 * We do that way till u and v are in the same chain, we query for that part of chain and break
 */

pair<int, int> query_up_path(int u,int v,multiset<pair<int, int>,Cmp> sbt)
{
//    multiset<pair<int, int>,Cmp> path_edges;
    multiset<pair<int, int> >::iterator itr;
    //print_edgelist(sbt);
    if (u == v)
    {
        path.clear();
        query_up_tree_path(1, 0, ptr-1, posInBase[v], posInBase[u]);
        for (itr=path.begin(); itr!=path.end(); itr++) {
            if(sbt.find(reverse_pair(*itr)) != sbt.end())   //reversed to match entries in subtree
                return *itr;
        }
    }
    int uchain, vchain = chainof[v];
    while (1) {
        uchain = chainof[u];
        if(vchain == uchain)
        {
            path.clear();
            //printf("posInBase[v]-> %d ",posInBase[v]);
            query_up_tree_path(1, 0, ptr-1, posInBase[v], posInBase[u]);
            for (itr=path.begin(); itr!=path.end(); itr++) {
                if(sbt.find(reverse_pair(*itr)) != sbt.end())
                    return *itr;
            }
            break;
        }
        path.clear();
        query_up_tree_path(1, 0, ptr-1, posInBase[chainHead[uchain]], posInBase[u]);
        
        for (itr=path.begin(); itr!=path.end(); itr++) {
            if(sbt.find(reverse_pair(*itr)) != sbt.end())
                return *itr;
        }
        u = chainHead[uchain];  // move u to u's chainHead
        u = index_parent[0][u]; //Then move to its parent, that means we changed chains
    }
    return *itr;
}


pair<int, int> dfs_delete_query(int u,int v)
{
    delete_query(u, v);
    int lastnodeofchain;
    pair<int, int> low_edge;
    if(v == index_parent[0][u])
    {
        if(lastchildofchain[u]==chainNo)
        {
            lastnodeofchain = baseArray[ptr-1].begin()->first;
        }
        else
        {
            lastnodeofchain = baseArray[posInBase[chainHead[lastchildofchain[u]+1]]-1].begin()->first;
        }
            low_edge = query_up_path(v,1,query_up_tree(1,0,ptr-1,posInBase[u],posInBase[lastnodeofchain]));
        printf("low_edge -> %d %d\n",low_edge.first,low_edge.second);
    }
    else
    {
        if(lastchildofchain[v]==chainNo)
        {
            lastnodeofchain = baseArray[ptr-1].begin()->first;
        }
        else{
            lastnodeofchain = baseArray[posInBase[chainHead[lastchildofchain[v]+1]]-1].begin()->first;
        }
        
        low_edge = query_up_path(u,1,query_up_tree(1,0,ptr-1,posInBase[v],posInBase[lastnodeofchain]));
        printf("low_edge -> %d %d\n",low_edge.first,low_edge.second);
        
    }
    subtree.clear();
    return low_edge;
}

/* HLD divides the tree into vertex-disjoint chains
 ( Meaning no two chains has a node in common ) in such a way
 that to move from any node in the tree to the root node,
 we will have to change at most log N chains.*/

void HLD(int u,int v)
{
    hldadjlist[u].push_back(v);
    hldadjlist[v].push_back(u);
    int hc = -1, i;
    printf("%d ", u);
    if(chainHead[chainNo] == -1)
    {
        chainHead[chainNo] = u;
    }
    chainof[u] = chainNo;
    posInBase[u] = ptr;
    for (i = 0; i < gradjlist[u].size(); i++) {
     baseArray[ptr].insert(make_pair(u,gradjlist[u].at(i)));//save subtree T(w) in array where w is part HLD path
    }
    ptr++;
    for(i = 0;i < dfsadjlist[u].size();i++)
    {
        if((hc == -1 ||(subtreesize[hc] < subtreesize[dfsadjlist[u].at(i)])) && dfsadjlist[u].at(i) != v)
        {
            hc = dfsadjlist[u].at(i);
        }
    }
    
    if(hc != -1)
    {
        HLD(hc, u);
    }
    
    for (i = 0; i < dfsadjlist[u].size(); i++) {
        if(dfsadjlist[u].at(i) != hc && dfsadjlist[u].at(i)!= v)
        {
            chainNo++;
            HLD(dfsadjlist[u].at(i), u);
        }
    }
    lastchildofchain[u] = chainNo; //added for find subtree T(w) will store last chaino
}

/*
 * LCA:
 * Takes two nodes u, v and returns Lowest Common Ancestor of u, v
 */
int LCA(int u, int v) {
    if(depth[u] < depth[v]) swap(u,v);
    int diff = depth[u] - depth[v];
    for(int i=0; i<LgINF; i++) if( (diff>>i)&1 ) u = index_parent[i][u];
    if(u == v) return u;
    for(int i=LgINF-1; i>=0; i--) if(index_parent[i][u] != index_parent[i][v]) {
        u = index_parent[i][u];
        v = index_parent[i][v];
    }
    return index_parent[0][u];
}


int dfs_subtree(int u,int v,int depth_)
{
    dfsadjlist[u].push_back(v);
    dfsadjlist[v].push_back(u);
    visit[u] = 1;
    index_parent[0][u] = v;
    depth[u] = depth_;
    subtreesize[u] = 1;
    for (int i = 0; i < gradjlist[u].size(); i++) {
        if(gradjlist[u].at(i) != v && visit[gradjlist[u].at(i)] != 1)
        {
            visit[gradjlist[u].at(i)] = 1;
            subtreesize[gradjlist[u].at(i)] = dfs_subtree(gradjlist[u].at(i), u, depth[u]+1);
            subtreesize[u] += subtreesize[gradjlist[u].at(i)];
        }
    }
    return subtreesize[u];
}

int reroot(int r_new,int r_old)
{
    printf("REROOT %d",r_new);
    int lastnodeofchain = 0;
    if (r_old == r_new)
    {
        
            if(lastchildofchain[r_new]==chainNo)  //last chain
            {
                lastnodeofchain = baseArray[ptr-1].begin()->first;
            }
            else
            {
                lastnodeofchain =baseArray[posInBase[chainHead[lastchildofchain[r_new]+1]]-1].begin()->first;
            }
        print_dfs(posInBase[r_new], lastnodeofchain);
        return 0;
    }
    int r_newchain = chainof[r_new], r_oldchain = chainof[r_old];
    while(1){
        int new_child =r_new;
        int new_parent = r_new;
        pair<int,int> low_edge;
        r_newchain = chainof[r_new];
        
        if(r_newchain == r_oldchain)
        {
            int old_parent = index_parent[0][new_child];
            int flag =1;
            int save_new_child = new_child;
            while(old_parent != r_old)
            {

                path.clear();

                flag = 0;
                new_child = old_parent;    //reversing parent order
                old_parent = index_parent[0][new_child];
                index_parent[0][new_child] = new_parent;    //new parent to dfs
                
                printf(" %d ",new_child);
                for (int i = 0; i < hldadjlist[new_child].size(); i++) {
                    if(hldadjlist[new_child].at(i) != new_parent &&
                       hldadjlist[new_child].at(i) != old_parent && subvisit[hldadjlist[new_child].at(i)] != 1)
                    {

                        subvisit[hldadjlist[new_child].at(i)] = 1;
                        if(lastchildofchain[hldadjlist[new_child].at(i)]==chainNo)  //last chain
                        {
                            lastnodeofchain = baseArray[ptr-1].begin()->first;
                        }
                        else
                        {

    lastnodeofchain =baseArray[posInBase[chainHead[lastchildofchain[hldadjlist[new_child].at(i)]+1]]-1].begin()->first;
                        }
low_edge = query_up_path(new_child,r_old,query_up_tree(1,0,ptr-1,posInBase[hldadjlist[new_child].at(i)],posInBase[lastnodeofchain]));

                        if(low_edge.first !=0 && low_edge.second!=0)
                        {
                            
                            reroot(hldadjlist[new_child].at(i), low_edge.second);
                            index_parent[0][low_edge.second]=low_edge.first;
                        }
                        r_newchain=chainof[new_child];
                    }
                }
                new_parent = new_child; //next loop a,b in r_old to r_new
            }
                if(lastchildofchain[save_new_child]==chainNo)  //last chain
                {
                    lastnodeofchain = baseArray[ptr-1].begin()->first;
                }
                else
                {
                    //printf("lastchildofchain of %d next chainhead pos")
                    lastnodeofchain =baseArray[posInBase[chainHead[lastchildofchain[save_new_child]+1]]-1].begin()->first;
                }
                 print_dfs(posInBase[save_new_child] + 1, posInBase[chainHead[chainof[r_new]]]-1);

            index_parent[0][old_parent] = new_parent;
            printf(" %d ",r_old);
            break;
        }
        else
        {
            int old_parent = index_parent[0][new_child];
            int save_new_child = new_child;
            while(old_parent != index_parent[0][chainHead[r_newchain]])
            {
            path.clear();
               
            new_child = index_parent[0][new_child];
            old_parent = index_parent[0][new_child];
            index_parent[0][new_child] = new_parent;
                printf(" %d ",new_child);
            for (int i = 0; i < hldadjlist[new_child].size(); i++) {
                if(hldadjlist[new_child].at(i) != new_parent &&
                   hldadjlist[new_child].at(i) != old_parent &&subvisit[hldadjlist[new_child].at(i)] != 1)
                {
                    //printf("Inside if condition");
                    subvisit[hldadjlist[new_child].at(i)] = 1;
                    if(lastchildofchain[hldadjlist[new_child].at(i)]==chainNo)  //last chain
                    {
                        lastnodeofchain = baseArray[ptr-1].begin()->first;
                    }
                    else
                    {
    lastnodeofchain =baseArray[posInBase[chainHead[lastchildofchain[hldadjlist[new_child].at(i)]+1]]-1].begin()->first;
                    }
                    low_edge = query_up_path(new_child,r_old,query_up_tree(1,0,ptr-1,posInBase[hldadjlist[new_child].at(i)],posInBase[lastnodeofchain]));
                    printf("low_edge -> %d %d\n",low_edge.first,low_edge.second);
                    if(low_edge.first !=0 && low_edge.second!=0)
                    {
                        reroot(hldadjlist[new_child].at(i), low_edge.second);
                        index_parent[0][low_edge.second]=low_edge.first;
                    }
                }
            }
        }
                if(lastchildofchain[save_new_child]==chainNo)  //last chain
                {
                    lastnodeofchain = baseArray[ptr-1].begin()->first;
                }
                else
                {
                    //printf("lastchildofchain of %d next chainhead pos")
                    lastnodeofchain =baseArray[posInBase[chainHead[lastchildofchain[save_new_child]+1]]-1].begin()->first;
                }
                print_dfs(posInBase[save_new_child]+1, posInBase[lastnodeofchain]);
            //printf("lastchildofchain of %d next chainhead pos\n",lastnodeofchain);
    }
        r_new = chainHead[r_newchain];  // move u to u's chainHead
        r_new = index_parent[0][r_new]; //Then move to its parent, that means we changed chains

  }
    return 1;
}

int main(int argc, const char * argv[]) {
    // insert code here...
    int t,n = 0,i,u,v = 0,j,k,vtx=0;
    
        scanf("%d",&vtx);
        scanf("%d",&n);
        for (j=0; j<=n; j++) {
            chainHead[j] = -1;
            visit[j] = 0;
            subvisit[j] =0;
        }
        for (j=0; j<LgINF; j++) {
            for (k =0; k<=n; k++) {
                index_parent[j][i] = -1;
            }
        }
        
        for (j=0; j<n; j++) {
            scanf("%d",&u);
            scanf("%d",&v);
            gradjlist[u].push_back(v);
            edgelist[u].push_back(j);
            gradjlist[v].push_back(u);
            edgelist[v].push_back(j);
        }
    
    visit[1] = 1;          //before calling DFS
    printf("Original DFS:\n");
    dfs_subtree(1,0,0);    //call dfs for calculating subtree size
    delete_from_adjlist(dfsadjlist, 1, 0);  //removing node 0 from hld
    HLD(1, 0);//call HLD from node 1
    cout<<endl;
    make_seg_tree(1, 0, ptr-1);//call build_segment tree for the path of HLD

    
    //construct array for LCA Note: To be needed for Edge insertion
    index_parent[0][1] = 1;
    for(i=1; i<LgINF; i++)
        for(int j=1; j<=vtx; j++)
            if(index_parent[i-1][j] != -1)
                index_parent[i][j] = index_parent[i-1][index_parent[i-1][j]];
    printf("\nUpdated DFS: \n");
    while(1) {
        int lastnodeofchain;
        char s[100];
        scanf("%s", s);
        if(s[0] =='E') {
            break;
        }
        int a, b;
        //printf("Debug1");
        scanf("%d %d", &a, &b);
        if(s[0]=='D') {
            if(a == index_parent[0][b])
            {
                 pair<int,int> low_edge = dfs_delete_query(a,b);
                
                if(lastchildofchain[a]==chainNo)
                {
                    lastnodeofchain = baseArray[ptr-1].begin()->first;
                }
                else
                {
                    lastnodeofchain = baseArray[posInBase[chainHead[lastchildofchain[b]+1]]-1].begin()->first;
                }
                print_dfs(0,posInBase[a]-1);
                print_dfs(posInBase[lastnodeofchain]+1,vtx-1);
                reroot(low_edge.second, a);
                index_parent[0][low_edge.second]=low_edge.first;
                printf("\n\nDFS Modified please try new graph   \n");
                break;
            }
            else if(b == index_parent[0][a])
            {

                 pair<int,int> low_edge = dfs_delete_query(a,b);
                if(lastchildofchain[a]==chainNo)
                {
                    lastnodeofchain = baseArray[ptr-1].begin()->first;
                }
                else
                {

                    lastnodeofchain = baseArray[posInBase[chainHead[lastchildofchain[a]+1]]-1].begin()->first;
                }
                print_dfs(0,posInBase[a]-1);
                print_dfs(posInBase[lastnodeofchain]+1,vtx-1);
                reroot(low_edge.second, a);
                
                index_parent[0][low_edge.second]=low_edge.first;
                printf("\n\nDFS Modified please try new graph\n");
                break;
            }
            else{
                delete_query(a,b);
                printf("\nNo change in DFS Back edge deletion\n");
                break;
            }

        }else if(s[0] == 'I'){
            int w = LCA(a, b);
            if (w == b || w== a) {
                printf("\nNo change in DFS Back edge added\n");
                insert_query(b, a);
                break;
            }
            else{
                if(chainof[b] < chainof[a])
                {
                    swap(b, a);
                }
                if(chainof[b] > chainof[a]){
                    for(k =0;k<hldadjlist[w].size();k++)
                    {
                        
                        if((lastchildofchain[hldadjlist[w].at(k)] >= lastchildofchain[b]) && (hldadjlist[w].at(k) !=index_parent[0][w]) && chainof[hldadjlist[w].at(k)] <= chainof[b])
                        {
                            break;
                        }
                    }
                   
                    print_dfs(0, posInBase[hldadjlist[w].at(k)]-1);

                    reroot(b,hldadjlist[w].at(k));
                    if(lastchildofchain[b]==chainNo)
                    {
                        lastnodeofchain = baseArray[ptr-1].begin()->first;
                    }
                    else
                    {

                        lastnodeofchain = baseArray[posInBase[chainHead[lastchildofchain[b]+1]]-1].begin()->first;
                    }
                    print_dfs(posInBase[lastnodeofchain]+1, vtx-1);
                    printf("\n DFS Modified please try new graph \n");
                    break;
                }
            }
        }
        else if(s[0]=='R') {
            //for report DFS
        }else if (s[0]=='P') {
            print_segtree();
        }
        printf("\nEnd Of Function\n");
       
    }//update info from user
    /* below code should be inside user update query function
    //update segment tree
    //Identify the path and Component
    //call query get node for reroot in subtree
    //call reroot
     */
    chainNo=0;
    for (j=0; j<n; j++) {
        dfsadjlist[j].clear();
        gradjlist[j].clear();
        edgelist[j].clear();
        chainHead[j] = -1;
        visit[j]=0;
        for (k=0; k<LgINF; k++) {
            index_parent[k][j] = -1;
        }
    }
    return 0;
}


