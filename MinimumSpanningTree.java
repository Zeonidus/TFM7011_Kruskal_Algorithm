import java.util.Collections;
import java.util.List;

/* Modified from:
 * 
 * http://www.keithschwarz.com/interesting/code/?dir=kruskal
 * Keith Schwarz (htiek@cs.stanford.edu)
 */
public class MinimumSpanningTree<K> {
	
	/* This is the method that brings everything in together.
	 * It will accept an initial graph and use it to compute
	 * the initial graph's MST using Kruskal's algorithm.
	 */
	//@ requires g != null;
	//@ ensures \result != null;
	public /*@ pure @*/ UndirectedGraph<K> generateMST(UndirectedGraph<K> g) {
		UndirectedGraph<K> mst = new UndirectedGraph<K>();
		UnionFind<K> uf = new UnionFind<K>();
		
		List<Edge<K>> edges = g.toEdges();
		Collections.sort(edges); //Sort ascending
		
		//For each node, add them into the UndirectedGraph and UnionFind structure
		for(K node : g) {
			uf.add(node);
			mst.addNode(node);
		}
		
		int edgeCount = 0; //edge count in MST variable		
		//adds the edges and also checks for loops
		for(Edge<K> edge : edges) {
			if(uf.find(edge.n1) == uf.find(edge.n2))
				continue; //forms loop; ignore.		
			mst.addEdge(edge);
			uf.union(edge.n1, edge.n2);
			if(++edgeCount == g.size()) break; //reached the amount of edges, n-1
		}
		return mst;
	}
}
