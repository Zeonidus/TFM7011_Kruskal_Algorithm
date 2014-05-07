import java.util.Collection;
import java.util.HashMap;
import java.util.NoSuchElementException;


/* Modified from:
 * 
 * http://www.keithschwarz.com/interesting/code/?dir=union-find
 * Keith Schwarz (htiek@cs.stanford.edu)
 */

/* This is the UnionFind class which supports
 * Kruskal's algorithm by using a Disjoint-set data structure
 */
public class UnionFind<T> {
	
	/* The Link nested class is used link a node to another node,
	 * making the other node it's "parent"
	 */
	private static final class Link<T> {
		public T parent;
		public int rank = 0; //Used for union operation
		
		//@ public invariant parent != null;
		//@ public invariant rank >= 0;
				
		//@ requires parent != null;
		//@ modifies this.parent;
		//@ ensures this.parent == parent;
		Link(T parent) { this.parent = parent; }
	}
	
	private final /*@ spec_public @*/ HashMap<T, Link<T>> g = new HashMap<T, Link<T>>();
	
	//@ public invariant g != null;
	
	public UnionFind() {}
	
	//@ requires elements != null;
	//@ modifies this.g;
	public UnionFind(Collection<T> elements) {
		for(T e : elements) {
			this.add(e);
		}
	}
	
	/* Adds a node into the HashMap */
	//@ modifies this.g;
	public boolean add(T e) {
		if(e == null) 
			throw new NullPointerException("Element cannot be null");
		else if(g.containsKey(e)) 
			return false;
		else {
			g.put(e, new Link<T>(e));
			return true;
		}
	}
	
	/* The Find operation attempts to find the representation
	 * of the disjoint-set by recursively 'climbing' up the
	 * ladder of parents until the highest parent is found
	 * (the node's parent points to itself) 
	 */
	//@ requires e != null;
	public T find(T e) {
		if(!g.containsKey(e)) {
			throw new NoSuchElementException("Element " + e + " does not exist");
		}
		else
			return rFind(e);
	}
	
	//RecursiveFind: Find rep of e recursively;
	//@ requires e != null;
	private T rFind(T e) {
		Link<T> f = g.get(e);
		if(f.parent.equals(e)) {
			return e;
		}
		else {
			f.parent = rFind(f.parent);
			return f.parent;
		}
	}
	
	//Set a node's parent to another node
	//@ requires n1 != null && n2 != null;
	public void union(T n1, T n2) {
		Link<T> l1 = g.get(find(n1));
		Link<T> l2 = g.get(find(n2));
		
		if(l1 == l2) 
			return;
		
		if(l1.rank > l2.rank)
			l2.parent = l1.parent;
		else if(l1.rank < l2.rank)
			l1.parent = l2.parent;
		else {
			l2.parent = l1.parent;
			l1.rank++;		
		}		
	}
}
