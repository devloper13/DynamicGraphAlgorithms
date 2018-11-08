//Adjacency List
//priority queue
//Distance vector
//Each edge must maintain at which time it was accessed and processed. This is needed to run dijkstra from the earliest edge.
// -1 to execute and any negative number to delete

#include <bits/stdc++.h>	
#include <time.h>
using namespace std;

# define INF 0x3f3f3f3f 
# define MAXNODE 100000
/***************************/
class priority{
    public:
        priority_queue< pair<int,int>, vector < pair<int,int> > , greater< pair<int,int> > > pq;
        vector<int> dist;
        vector<int> time_order;
        vector<int> already_popped;
        priority(){
        	dist.reserve(MAXNODE);
        	time_order.reserve(MAXNODE);
        	already_popped.reserve(MAXNODE);
        }
};

vector<priority> heapState(MAXNODE);

vector<int> nodetime(MAXNODE);

vector<int> dist(MAXNODE);

vector<int> predecessor(MAXNODE);

vector< vector< pair<int,int> > >Graph(MAXNODE);

vector<int> allVertex(MAXNODE);

vector<int> alreadyPopped(MAXNODE);
/***************************/


void removeEdge(int vertex1,int vertex2){
	int index=0;
	vector< pair<int,int> >::iterator iter;
	if(Graph[vertex1].size()>0){
		for(iter = Graph[vertex1].begin();iter!=Graph[vertex1].end();iter++){
			if(iter->first == vertex2){
				break;
			}
			else{
				index++;
			}
		}
		Graph[vertex1].erase(Graph[vertex1].begin() + index);
		if(predecessor[vertex1] == vertex2){
			dist[vertex1] = INF;
			predecessor[vertex1] = -1;
			nodetime[vertex1] = INF;
		}
	}
	index=0;
	if(Graph[vertex2].size()>0){
		for(iter = Graph[vertex2].begin();iter!=Graph[vertex2].end();iter++){
			if(iter->first == vertex1){
				break;
			}
			else{
				index++;
			}
		}
		Graph[vertex2].erase(Graph[vertex2].begin() + index);
		if(predecessor[vertex2] == vertex1){
			dist[vertex2] = INF;
			predecessor[vertex2] = -1;
			nodetime[vertex2] = INF;
		}
	}
}

void removeVertex(int vertex){
	if(Graph[vertex].size()>0){
		//cout<<"Testing Vertex deletion\n";
		
		int index = 0;
		//cout<<"Before Deletion: "<<Graph[vertex].size();
		Graph[vertex].clear();
		//cout<<"\nAfter Deletion: "<<Graph[vertex].size();
		allVertex[vertex] = -1;
		vector< vector< pair<int,int> > >::iterator iter;
		vector< pair<int,int> >::iterator initer;
		//vector<int>::iterator allVertIter;
		for(iter=Graph.begin();iter!=Graph.end();iter++){
			for(initer = (*iter).begin();initer!=(*iter).end();initer++){
				if(initer->first == vertex){
					break;
				}
				else{
					index++;
				}
			}
			(*iter).erase((*iter).begin() + index);	
			index=0;
		}
		dist[vertex] = INF;
		predecessor[vertex] = -1;
		nodetime[vertex] = INF;
	}
}
void addEdge(int vertex1,int vertex2,int weight){
	if(allVertex[vertex1]==-1){
		allVertex[vertex1] = vertex1;
	}
	if(allVertex[vertex2]==-1){
		allVertex[vertex2] = vertex2;
	}
	//int newFlag=0;
	int gflag=0;
	vector< pair<int,int> >::iterator iter;
	if(Graph[vertex1].size()!=0){
		
		//struct AdjListNode* newNode =  newAdjListNode(vertex1,w); 
		for(iter=Graph[vertex1].begin();iter!=Graph[vertex1].end();iter++){
			if((*iter).first == vertex2){
				gflag=1;
				(*iter).second = weight;
				break;
			}
		}
	}
	if(gflag==0){
		
			Graph[vertex1].push_back( make_pair(vertex2,weight) );
	}
	gflag=0;
	if(Graph[vertex2].size()!=0){
	
		//struct AdjListNode* newNode =  newAdjListNode(vertex1,w); 
		for(iter=Graph[vertex2].begin();iter!=Graph[vertex2].end();iter++){
			if((*iter).first == vertex1){
				gflag=1;
				(*iter).second = weight;
				break;
			}
		}
		
	}
	if(gflag==0){
			Graph[vertex2].push_back( make_pair(vertex1,weight) );
	}
}

void dijkstra(int src,int first){
	//get min
	priority_queue< pair<int,int>, vector < pair<int,int> > , greater< pair<int,int> > > pq;
	//cout<<dist[src]<<".+\n";
	pq.push(make_pair(dist[src], src));
		
	
	vector< pair<int,int> >::iterator iter;
	
	if(first==0){
		//Restoring heap state
		priority newP = heapState[nodetime[src]];
		pq = newP.pq;
		nodetime = newP.time_order;
		dist = newP.dist;
		alreadyPopped = newP.already_popped;
	}
	int time=nodetime[src]-1;
	int prev;
	while(!pq.empty()){
		
		int u = pq.top().second;
		if(alreadyPopped[u] == 0){
			nodetime[u] = time + 1;
		
		
		/* saving heap state*/
		priority p;
		p.pq = pq;
		p.dist = dist;
		p.time_order = nodetime;
		p.already_popped = alreadyPopped;
		heapState[nodetime[u]] = p;
		/* saving heap state end*/
		
		prev = u;
		time = nodetime[prev];
		//nodetime[u] = time + 1;
		//cout<<"Source = "<<u<<endl; 
        pq.pop(); 
        alreadyPopped[u] = 1;
        
		for(iter=Graph[u].begin();iter!=Graph[u].end();iter++){
			//cout<<"Current distance of "<<(*iter).first<<" from source  = "<<dist[(*iter).first]<<endl<<"distance of source  to "<<(*iter).first<<" = "<<dist[u] + (*iter).second<<endl;
			if((dist[(*iter).first] > (dist[u] + (*iter).second))){
				//cout<<"INSIDE IF:\n";	
				//cout<<"Current distance of "<<(*iter).first<<" from source  = "<<dist[(*iter).first]<<endl<<"distance of source  to "<<(*iter).first<<" = "<<dist[u] + (*iter).second<<endl;
				dist[(*iter).first] = dist[u] + (*iter).second;
				predecessor[iter->first] = u;
				pq.push(make_pair(dist[(*iter).first],(*iter).first ));
			}
			
		}
		
		} //alreadyPopped
		else{
			pq.pop();
		}
				
	}
	
	for (int i = 0; i < dist.size(); ++i){
		if(dist[i] != INF){ 
        	printf("%d \t\t %d\n", i, dist[i]); 
        }
    }    
        
    /*for(int i = 0;i<5;i++){
    	cout<<nodetime[i]<<"\n";
    }*/  
	
}
int main(){
	int vertex1,vertex2,cost;
	int min_label=INF;
	int label=0;
	int first=1;
	for(int i=1;i<MAXNODE;i++){
		dist[i] = INF;
		nodetime[i] = INF;
		predecessor[i] = -1;
		allVertex[i] = -1;
	}
	
	nodetime[0] = 1;
	int breakLimit=5;
    
	while(1){
		cin>>vertex1;
		if(nodetime[vertex1]<min_label && vertex1!=-1){
			min_label = nodetime[vertex1];
			label = vertex1;
		}
		if(vertex1<0){
			clock_t t; 
    		t = clock();
    		
			dijkstra(label,first);
			breakLimit--;
			
			t = clock() - t; 
   		 	double time_taken = ((double)t)/CLOCKS_PER_SEC; // in seconds
   		 	cout<<"Time Taken to execute: "<<time_taken<<" seconds. \n";
			first=0;
			min_label=INF;
			label=0;
			cout<<"done\n";
			if(breakLimit == 0){
				break;
			}
		}
		else{
			cin>>vertex2;
			
			if(vertex2<0){
				removeVertex(vertex1);
				//cout<<"hi\n";
				min_label=0;
				first=1;
			}
			else{
				if(nodetime[vertex2]<min_label){
					min_label = nodetime[vertex2];
					label = vertex2;
				}	
				cin>>cost;
				if(cost<0){
					removeEdge(vertex1,vertex2);
				}
				else{
					addEdge(vertex1,vertex2,cost);
				}
			}
			//find min node and store in "min_label
			//minlabel = history[vertex1]->time < history[]
		}	
	}
}
