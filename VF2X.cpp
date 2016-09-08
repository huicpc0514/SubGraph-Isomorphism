#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <assert.h>
#include <ctime>

#include <algorithm>
#include <iterator>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
typedef int VIndex;
typedef int EIndex;
typedef int VLabel;
const VIndex NULL_VIndex=-1;
const EIndex NULL_EIndex=-1;
const set<VIndex> NULL_vertex_SET={};

struct Edge{
    int u,v,label,nxt,pre;//label is cap
    Edge(){}
    Edge(int u,int v,int label,int nxt,int pre):u(u),v(v),label(label),nxt(nxt),pre(pre){}
};
struct Graph{
    int edge_cnt,vertex_cnt;
    vector<VLabel> vertex;
    vector<EIndex> head_edge;
    vector<EIndex> rev_head_edge;
    vector<Edge> edge;
    vector<set<VIndex>> pred;
    vector<set<VIndex>> succ;
    void addVertex(int label){
        vertex.push_back(label);
        head_edge.push_back(NULL_EIndex);
        rev_head_edge.push_back(NULL_EIndex);
        pred.push_back(NULL_vertex_SET);
        succ.push_back(NULL_vertex_SET);
        vertex_cnt++;
    }
    void addEdge(int u,int v,int label){
        edge.push_back(Edge(u,v,label,head_edge[u],rev_head_edge[v]));
        head_edge[u]=edge_cnt;
        rev_head_edge[v]=edge_cnt++;
        pred[v].insert(u); succ[u].insert(v);
    }
    void init(){
        vertex_cnt=edge_cnt=0;
        vertex.clear();
        edge.clear();
        head_edge.clear();
        rev_head_edge.clear();
        pred.clear();
        succ.clear();
    }
    void printGraph(){
        printf("vertex count = %d\n",vertex_cnt);
        printf("vertex label:\n");
        for(auto v: vertex) printf("%d ",v+1);
        printf("\n");
        printf("vertex pred:\n");
        int cnt=0;
        for(auto nodes: pred){
            printf("No.%d:",++cnt);
            for(auto v: nodes) printf(" %d",v+1); printf("\n");
        }
        printf("vertex succ:\n");
        cnt=0;
        for(auto nodes: succ){
            printf("No. %d:",++cnt);
            for(auto v: nodes) printf(" %d",v+1); printf("\n");
        }
        printf("edge count: %d\n",edge_cnt);
    }
};
vector<Graph> database,query;
void readGraph(vector<Graph> &G,int total){
    Graph now_graph;
    now_graph.init();
    int n,m;
    while(1){
        scanf("%d%d",&n,&m);
        if(n==0&&m==0) break;
        //printf("n=%d m=%d tot=%d\n",n,m,total);
        for(int i=0;i<n;i++) now_graph.addVertex(i);
        for(int i=0;i<m;i++){
            int u,v,cap; scanf("%d%d%d",&u,&v,&cap);
            u--; v--;
            now_graph.addEdge(u,v,cap);
        }
        G.push_back(now_graph);
        total--;
        if(total==0) break;
        now_graph.init();
    }
}
bool cmp(pair<int,int> a,pair<int,int> b){
    if(a.first>b.first) return 1;
    else if(a.first==b.first) return a.second>b.second;
    return 0;
}
struct State{
    int vertex_cnt; bool isomorphism;
    set<VIndex> in_1, in_2, out_1, out_2; //当前已经匹配点的源点in，汇点out
    set<VIndex> M1,M2;  //匹配集合
    vector<VIndex> core_1, core_2;//对应点对
    State(){}
    State(int cnt1,int cnt2,bool sub){
        vertex_cnt=cnt1; isomorphism=sub;
        core_1.resize(cnt1);
        fill(core_1.begin(),core_1.end(),NULL_VIndex);
        core_2.resize(cnt2);
        fill(core_2.begin(),core_2.end(),NULL_VIndex);
        in_1.clear(); in_2.clear();
        out_1.clear(); out_2.clear();
        M1.clear(); M2.clear();
    }

    vector<pair<VIndex,VIndex>> candi_sort(vector<pair<VIndex,VIndex>> &P,const Graph &G1,const Graph &G2)const{
        if(P.size()<=3) return P;
        vector<pair<int,int>> node;
        for(int i=0;i<P.size();i++){
            pair<int,int> p=P[i];
            int u=p.first, v=p.second;
            int u_cnt=G1.pred[u].size()+G1.succ[u].size();
            int v_cnt=G2.pred[v].size()+G2.succ[v].size();
            node.push_back(make_pair(v_cnt*1000+u_cnt,i));
        }
        sort(node.begin(),node.end(),cmp);
        vector<pair<VIndex,VIndex>> now_P;
        for(int i=0;i<node.size();i++){
            int id=node[i].second;
            now_P.push_back(P[id]);
        }
        return now_P;
    }
    vector<pair<VIndex,VIndex>> genPairSucc(const Graph &G1,const Graph &G2,const int vid)const{
        vector<pair<VIndex,VIndex>>P;
        vector<VIndex> vis;  vis.resize(G2.vertex_cnt,0);
        int cnt=0;
        for(auto v: G1.succ[vid]){
            if(core_1[v]!=NULL_EIndex){
                int uid=core_1[v]; cnt++;
                for(auto u: G2.pred[uid]){
                    if(core_2[u]==NULL_EIndex) vis[u]++;
                }
            }
        }
        for(int i=0;i<G2.vertex_cnt;i++){
            if(vis[i]==cnt) P.push_back(make_pair(vid,i));
        }
        return P;
    }
    vector<pair<VIndex,VIndex>> genPairPred(const Graph &G1,const Graph &G2,const int vid)const{
        vector<pair<VIndex,VIndex>>P;
        vector<VIndex> vis;  vis.resize(G2.vertex_cnt,0);
        int cnt=0;
        for(auto v: G1.pred[vid]){
            if(core_1[v]!=NULL_EIndex){
                int uid=core_1[v]; cnt++;
                for(auto u: G2.succ[uid]){
                    if(core_2[u]==NULL_EIndex) vis[u]++;
                }
            }
        }
        for(int i=0;i<G2.vertex_cnt;i++){
            if(vis[i]==cnt) P.push_back(make_pair(vid,i));
        }
        return P;
    }
    vector<pair<VIndex,VIndex>> genPairSet(const Graph &G1,const Graph &G2)const{
        vector<pair<VIndex,VIndex>>P;
        if(out_1.size()&&out_2.size()){ //先生成最大的点对,减少搜索空间
            VIndex max_vid1=-1;
            for(auto vid1: out_1) max_vid1=max(max_vid1,vid1);
            int flag=0;
            for(auto v:G1.succ[max_vid1]){
                if(core_1[v]!=NULL_EIndex){flag=1;break;}
            }
            if(flag) P=genPairSucc(G1,G2,max_vid1);
            else{
                for(auto vid2: out_2){
                    P.push_back(make_pair(max_vid1,vid2));
                }
            }
            int cnt=P.size();
            for(int i=0;i<cnt/2;i++) swap(P[i],P[cnt-i-1]);
        }else if(in_1.size()&&in_2.size()){
            VIndex max_vid1=-1;
            for(auto vid1: in_1) max_vid1=max(max_vid1,vid1);
            int flag=0;
            for(auto v:G1.pred[max_vid1]){
                if(core_1[v]!=NULL_EIndex){flag=1;break;}
            }
            if(flag) P=genPairPred(G1,G2,max_vid1);
            else{
                for(auto vid2: in_2){
                    P.push_back(make_pair(max_vid1,vid2));
                }
            }
            int cnt=P.size();
            for(int i=0;i<cnt/2;i++) swap(P[i],P[cnt-i-1]);
        }else{
            VIndex max_vid1=vertex_cnt-1;
            for(;max_vid1>=0&&core_1[max_vid1]!=NULL_VIndex;max_vid1--){}
            int vid=core_2.size()-1;
            for(;vid>=0;vid--){
                if(core_2[vid]==NULL_VIndex){
                    P.push_back(make_pair(max_vid1,vid));
                }
            }
        }
        return P;//candi_sort(P,G1,G2);
    }
    void addNewPair(VIndex n,VIndex m, const set<VIndex> &pred1,const set<VIndex> &pred2,
                    const set<VIndex> &succ1,const set<VIndex> &succ2){
        M1.insert(n); M2.insert(m);
        core_1[n]=m; core_2[m]=n;
        for(auto u: pred1) if(core_1[u]==NULL_VIndex) in_1.insert(u);
        for(auto u: pred2) if(core_2[u]==NULL_VIndex) in_2.insert(u);
        for(auto u: succ1) if(core_1[u]==NULL_VIndex) out_1.insert(u);
        for(auto u: succ2) if(core_2[u]==NULL_VIndex) out_2.insert(u);
        if(in_1.find(n)!=in_1.end()) in_1.erase(n);
        if(in_2.find(m)!=in_2.end()) in_2.erase(m);
        if(out_1.find(n)!=out_1.end()) out_1.erase(n);
        if(out_2.find(m)!=out_2.end()) out_2.erase(m);
    }
    //check 新加入的点对是否能和之前的完全匹配,包括边的容量
    bool checkPredRule(const Graph &G1,const Graph &G2,VIndex n,VIndex m)const{
        for(int eid=G1.head_edge[n];eid!=NULL_EIndex;eid=G1.edge[eid].nxt){
            VIndex vid=G1.edge[eid].v;
            VIndex map_vid=core_1[G1.edge[eid].v];
            if(map_vid==NULL_VIndex) continue;
            int label=G1.edge[eid].label;//cap subgraph
            bool flag=0;
            for(int eid2=G2.head_edge[m];eid2!=NULL_EIndex;eid2=G2.edge[eid2].nxt){
                if(G2.edge[eid2].v==map_vid&&G2.edge[eid2].label>=label){
                    flag=1; break;
                }
            }
            if(!flag) return false;
        }
//        set<VIndex> new_pred;
//        set_intersection(M2.begin(),M2.end(),G2.pred[m].begin(),G2.pred[m].end(),
//                         inserter(new_pred,new_pred.begin()));
//        for(auto v2: new_pred){
//            VIndex v1=core_2[v2];
//            assert(v1!=NULL_VIndex);
//            if(G1.pred[n].find(v1)==G1.pred[n].end()) return false;
//        }
        return true;
    }
    bool checkSuccRule(const Graph &G1,const Graph &G2,VIndex n,VIndex m)const{
        for(int eid=G1.rev_head_edge[n];eid!=NULL_EIndex;eid=G1.edge[eid].pre){
            int vid=G1.edge[eid].u;
            VIndex map_vid=core_1[G1.edge[eid].u];
            if(map_vid==NULL_VIndex) continue;
            int label=G1.edge[eid].label;
            bool flag=0;
            for(int eid2=G2.rev_head_edge[m];eid2!=NULL_EIndex;eid2=G2.edge[eid2].pre){
                if(G2.edge[eid2].u==map_vid&&G2.edge[eid2].label>=label){
                    flag=1; break;
                }
            }
            if(!flag) return false;
        }
//        set<VIndex> new_succ;
//        set_intersection(M2.begin(),M2.end(),G2.succ[m].begin(),G2.succ[m].end(),
//                         inserter(new_succ,new_succ.begin()));
//        for(auto v2: new_succ){
//            int v1=core_2[v2];
//            assert(v1!=NULL_VIndex);
//            if(G1.succ[n].find(v1)==G1.succ[n].end()) return false;
//        }
        return true;
    }
    int set_inter_size(const set<VIndex> &a,const set<VIndex> &b)const{
        int cnt=0;
        for(auto v: a){
            if(b.find(v)!=b.end()) cnt++;
        }
        return cnt;
    }
    bool checkInRule(const Graph &G1,const Graph &G2,VIndex n,VIndex m)const{
        int num1=set_inter_size(in_1,G1.pred[n]);
        int num2=set_inter_size(in_2,G2.pred[m]);
        if(isomorphism&&num1>num2) return false;
        num1=set_inter_size(in_1,G1.succ[n]);
        num2=set_inter_size(in_2,G2.succ[m]);
        if(isomorphism&&num1>num2) return false; //if subgraph nodes is more than G2, false
        return true;
    }
    bool checkOutRule(const Graph &G1,const Graph &G2,VIndex n,VIndex m)const{
        int num1=set_inter_size(out_1,G1.succ[n]);
        int num2=set_inter_size(out_2,G2.succ[m]);
        if(isomorphism&&num1>num2) return false;
        num1=set_inter_size(out_1,G1.pred[n]);
        num2=set_inter_size(out_2,G2.pred[m]);
        if(isomorphism&&num1>num2) return false;
        return true;
    }
    set<VIndex> genCsA(int cnt,const vector<VIndex> &core, //补集
                       const set<VIndex> &in,const set<VIndex> &out)const{
        set<VIndex> ans;
        for(int vid=0;vid<cnt;vid++){//未匹配点且在in和out中不存在
            if(core[vid]==NULL_VIndex&&in.find(vid)==in.end()&&out.find(vid)==out.end()){
                ans.insert(vid);
            }
        }
        return ans;
    }
    bool checkNewRule(const Graph &G1,const Graph &G2,VIndex n,VIndex m)const{
        set<VIndex> _n1=genCsA(G1.vertex_cnt,core_1,in_1,out_1);
        set<VIndex> _n2=genCsA(G2.vertex_cnt,core_2,in_2,out_2);
        int num1=set_inter_size(G1.pred[n],_n1);
        int num2=set_inter_size(G2.pred[m],_n2);
        if(isomorphism&&num1>num2) return false;
        num1=set_inter_size(G1.succ[n],_n1);
        num2=set_inter_size(G2.succ[m],_n2);
//        for(auto x: _n2){
//            printf("%d ",x);
//        }printf("\n");
//        for(auto x: G2.succ[m]){
//            printf("%d ",x);
//        }
//        printf("\n");
        if(isomorphism&&num1>num2) return false;
        return true;
    }
    bool checkSynRules(const Graph &G1,const Graph &G2,VIndex n,VIndex m)const{
//        printf("%d %d %d %d %d\n",checkPredRule(G1,G2,n,m),checkSuccRule(G1,G2,n,m),
//               checkInRule(G1,G2,n,m),checkOutRule(G1,G2,n,m),
//               checkNewRule(G1,G2,n,m));
        return checkPredRule(G1,G2,n,m)&&checkSuccRule(G1,G2,n,m)&&
               checkInRule(G1,G2,n,m)&&checkOutRule(G1,G2,n,m)&&
               checkNewRule(G1,G2,n,m);
    }
    void printMap()const{
        printf("%s mapping found\n",isomorphism?"Subgraph":"Not");
        if(isomorphism)
            for(int i=0;i<vertex_cnt;i++) printf("%d %d\n",i+1,core_1[i]+1);
    }
};
State ans_state;
bool solve(const Graph &G1,const Graph &G2,const State &state){
    if(state.M1.size()==state.vertex_cnt){
        state.printMap();
        ans_state=state;
        return true;
    }
    //printf("now size=%d\n",state.M1.size());
    vector<pair<VIndex,VIndex>> P=state.genPairSet(G1,G2);
    for(auto p: P){
        int n=p.first, m=p.second;
        if(state.checkSynRules(G1,G2,n,m)){
            //printf("n=%d m=%d\n",n+1,m+1);
            State new_state=state;
            new_state.addNewPair(n,m,G1.pred[n],G2.pred[m],G1.succ[n],G2.succ[m]);
            if(solve(G1,G2,new_state)) return true;
        }
    }
    return false;
}
bool subisomorphism(const Graph &G1,Graph &G2){
    if(G1.vertex_cnt>G2.vertex_cnt) return false;
    if(G1.edge_cnt>G2.edge_cnt) return false;
    State state(G1.vertex_cnt,G2.vertex_cnt,1);
    if(solve(G1,G2,state)){
        //将原图中的边的容量减少
        //printf("**\n");
        for(int uid=0;uid<G1.vertex_cnt;uid++){
            int mpu=ans_state.core_1[uid];
            for(int i=G1.head_edge[uid];i!=NULL_EIndex;i=G1.edge[i].nxt){
                int vid=G1.edge[i].v;
                int mpv=ans_state.core_1[vid];
                //printf("u=%d v=%d mpu=%d mpv=%d ",uid+1,vid+1,mpu+1,mpv+1);
                for(int j=G2.head_edge[mpu];j!=NULL_EIndex;j=G2.edge[j].nxt){
                    if(G2.edge[j].v==mpv){
                        //printf("%d %d\n",G2.edge[j].label,G1.edge[i].label);
                        G2.edge[j].label-=G1.edge[i].label; break;
                    }
                }
            }
        }
        return true;
    }
    return false;
}

int main(){
    freopen("in.txt","r",stdin);
    //freopen("out.txt","w",stdout);
    readGraph(database,1);
    readGraph(query,100);
    //database[0].printGraph();
//    for(auto G1: query){
//        G1.printGraph();
//    }
    //subisomorphism(query[0],database[0]);
    for(auto G1:query){
        time_t start_time=0,end_time=0;
        subisomorphism(G1,database[0]);
        printf("end\n");
    }
    return 0;
}
