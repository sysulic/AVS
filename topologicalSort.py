# ==========================================================
# topologicalSort
# ==========================================================
from collections import defaultdict 

class Graph: 
    def __init__(self,vertices): 
        self.graph = defaultdict(list) 
        self.V = vertices

    def add_edge(self,u,v): 
        self.graph[u].append(v) 
        
    def set_keys_station(self):
        keyStation = {}
        key = list(self.graph.keys())
        if len(key) < self.V:
            for i in key:
                for j in self.graph[i]:
                    if j not in key:
                        key.append(j)
        for ele in key:
            keyStation[ele] = False
        return keyStation

    def topological_sort(self):
        queue = []
        station = self.set_keys_station()
        for i in range(self.V):
            for elem in station:
                if not station[elem]:
                    self.topological_sort_util(elem, queue, station)
        return queue   

    def topological_sort_util(self, elem, queue, station):
        station[elem] = True
        for i in station:
            if elem in self.graph[i] and not station[i]:
                station[elem] = False
        if station[elem]:
            queue.append(elem)
        

if __name__ == '__main__':
    g= Graph(6) 
    g.add_edge(5, 2); 
    g.add_edge(5, 0); 
    g.add_edge(4, 0); 
    g.add_edge(4, 1); 
    g.add_edge(2, 3); 
    g.add_edge(3, 1); 
    
    print ("result：")
    print(g.topological_sort())