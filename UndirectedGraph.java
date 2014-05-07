import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;


/* Modified from:
 * 
 * http://www.keithschwarz.com/interesting/code/kruskal/UndirectedGraph.java.html
 * Keith Schwarz (htiek@cs.stanford.edu)
 */

public final class UndirectedGraph<K> implements Iterable<K> {
	
	//(Node1, Link(Node2, Weight))
	private /*@ spec_public @*/ HashMap<K, Map<K, Integer>> g = new HashMap<K, Map<K, Integer>>();
	
	//@ public invariant g != null;
	
	//@ requires node != null;
	//@ modifies this.g;
	//@ ensures this.g.containsKey(node);
	public boolean addNode(K node) {
		if(g.containsKey(node)) 
			return false;
		else {
			g.put(node, new HashMap<K, Integer>());
			return true;
		}
	}
	
	//@ requires e != null;
	//@ modifies this.g;
	public void addEdge(Edge<K> e) {
		addEdge(e.n1, e.n2, e.weight);
	}
	
	//@ requires n1 != null && n2 != null && weight > 0;
	//@ modifies this.g;
	//@ ensures this.g.get(n1) == n1;
	//@ ensures this.g.get(n2) == n2;
	public void addEdge(K n1, K n2, int weight) {
		if(!g.containsKey(n1) || !g.containsKey(n2)) {	
			throw new NoSuchElementException("Both nodes must exist.");
		}
		else {
			g.get(n1).put(n2, weight); //n1 --weight--> n2
			g.get(n2).put(n1, weight); //n2 --weight--> n1
		}
	}
	
	public /*@ pure @*/ List<Edge<K>> toEdges() { 
		List<Edge<K>> list = new ArrayList<Edge<K>>();
		List<K> used = new ArrayList<K>();
		for(K node : this) {
			for(Map.Entry<K, Integer> entry : this.edgesFrom(node).entrySet()) {
				if(used.contains(entry.getKey())) 
					continue; //Node already added, ignore this node
				else
					list.add(new Edge<K>(node, entry.getKey(), entry.getValue()));
				used.add(node); //disallow adding node from the other side
			}
		}
		
		return list;
	}
	
	//Unimplemented since kruskal's algorithm doesn't require it.
	//public void removeEdge() {}
	
	//@ requires node != null;
	// ensures g.get(node) == n; //JML error: parser cannot 'see' n.
    public Map<K, Integer> edgesFrom(K node) {
        Map<K, Integer> n = g.get(node);
        if (n == null)
            throw new NoSuchElementException("Source node does not exist.");
        return Collections.unmodifiableMap(n);
    }

	//@ requires key != null;
	//@ ensures \result == g.containsKey(key);
	public /*@ pure @*/ boolean containsNode(K key) { return g.containsKey(key); }
	
	//@ ensures \result == g.size();
	public /*@ pure @*/ int size() { return g.size(); }
	
	//@ ensures \result == g.isEmpty();
	public /*@ pure @*/ boolean isEmpty() { return g.isEmpty(); }
	
	//@ ensures \result == g.keySet().iterator();
	@Override
	public /*@ pure @*/ Iterator<K> iterator() {
		return g.keySet().iterator();
	}
}
