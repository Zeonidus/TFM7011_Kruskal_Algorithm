/* Adapted from:
 * 
 * http://www.keithschwarz.com/interesting/code/?dir=kruskal
 * Keith Schwarz (htiek@cs.stanford.edu)
 */
public final class Edge<K> implements Comparable<Edge<K>> {
	/*@ spec_public @*/ K n1, n2;
	/*@ spec_public @*/ int weight;
    private /*@ spec_public @*/ final int tiebreaker; 
    private /*@ spec_public @*/ static int nextTiebreaker = 0;
    
    //@ public invariant weight > 0;
	//@ public invariant tiebreaker > 0;
    //@ public invariant nextTiebreaker > 0;
    
    //@ requires weight > 0;
    //@ modifies this.n1, this.n2, this.weight;
    //@ modifies this.tiebreaker, this.nextTiebreaker;
    //@ ensures this.n1 == n1;
    //@ ensures this.n2 == n2;
    //@ ensures this.weight == weight;
    //@ ensures this.tiebreaker == this.nextTiebreaker + 1;
	public Edge(K n1, K n2, int weight) {
		this.n1 = n1;
		this.n2 = n2;
		this.weight = weight;
		this.tiebreaker = Edge.nextTiebreaker++;
	}

	//@ requires o != null;
	//@ ensures \result >= -1 && \result <= 1;
	@Override
	public /*@ pure @*/ int compareTo(Edge<K> o) {
		if(this.weight > o.weight) return +1;
		if(this.weight < o.weight) return -1;
		
		//Same cost, pick one to be the "larger" 
		return tiebreaker - o.tiebreaker; 
	}
}