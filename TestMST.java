import java.util.List;
import java.util.Random;

public final class TestMST {
	private TestMST() {};
	
	public /*@ pure @*/ static void main(String[] args) {		
		test1(); 
		test2();
	}

	/* Used in test1()
	 * Generates a complete graph with the specified number of nodes 
	 * where each edge is generated with a random weight specified by 
	 * the minWeight and maxWeight parameters 
	 */
	//@ requires count > 0;
	//@ requires minWeight >= 0;
	//@ requires maxWeight >= minWeight;
	private /*@ pure @*/ static UndirectedGraph<Integer> generateRandomGraph(int count, int minWeight, int maxWeight) {
		UndirectedGraph<Integer> g = new UndirectedGraph<Integer>();
		Random rand = new Random();
		for(int i = 0; i < count; i++) {
			g.addNode(i);
		}
		
		for(int i = 0; i < count; i++) {
			for(int j = i + 1; j < count ; j++) {
				//min + rand(max - min + 1)
				int r = minWeight + rand.nextInt(maxWeight - minWeight + 1);
				g.addEdge(i, j, r);
			}
		}
		return g;
	}
	
	/* Test1:
	 * Generates a Minimum Spanning Tree 
	 * from a complete graph with a range of random weights.
	 */
	private /*@ pure @*/ static void test1() {		
		UndirectedGraph<Integer> g = new UndirectedGraph<Integer>();
		UndirectedGraph<Integer> mTree = new UndirectedGraph<Integer>();
		
		final int VERTEXCOUNT = 5;
		final int MINWEIGHT = 1;
		final int MAXWEIGHT = 10;
		System.out.println("Test 1: Fixed vertex count (" + VERTEXCOUNT + 
			"), range of random weights " + "(" + MINWEIGHT + " to " + MAXWEIGHT + ")");
		
		g = generateRandomGraph(VERTEXCOUNT, MINWEIGHT, MAXWEIGHT); //Makes the random graph
		mTree = new MinimumSpanningTree<Integer>().generateMST(g); //generates MST graph
		
		String str = "";
		List<Edge<Integer>> edges = mTree.toEdges();
		for(Edge<Integer> e : edges) {
			str += e.n1 + " " + e.n2 + " " + e.weight + "\n"; 
		}
		System.out.println(str);
	}
	
	/* Test 2:
	 * MST is generated from an initial complete graph
	 * which was constructed manually. 
	 */
	private /*@ pure @*/ static void test2() {
		System.out.println("Test 2: Manually constructed initial graph ran through MST algorithm.");
		UndirectedGraph<Integer> g = new UndirectedGraph<Integer>();
		g.addNode(1);
		g.addNode(2);
		g.addNode(3);
		g.addNode(4);
		
		g.addEdge(1, 2, 2);
		g.addEdge(1, 3, 3);
		g.addEdge(1, 4, 1);
		
		g.addEdge(2, 3, 5);
		g.addEdge(2, 4, 9);
		
		g.addEdge(3, 4, 1);
		
		MinimumSpanningTree<Integer> mst = new MinimumSpanningTree<Integer>();
		UndirectedGraph<Integer> mTree = mst.generateMST(g);
		
		String s = "";
		List<Edge<Integer>> edges = mTree.toEdges();
		for(Edge<Integer> e : edges) {
			s += e.n1 + " " + e.n2 + " " + e.weight + "\n"; 
		}
		System.out.println(s);
	}

}
