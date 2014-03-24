package hola;

import java.util.Set;
import java.util.HashSet;

public class MaxCliqueFinder {    
    
    public static void main(String[] args) {
	int n = 4;
	int[][] g = new int[n][n];	
	g[0][1] = 1;
	g[0][3] = 1;
	g[2][3] = 1;

	System.out.println(MaxCliqueFinder.findMaximumClique(g));
    }
    
    private static Set<Integer> findNeighbours(Integer n, int[][] g){
	Set<Integer> ns = new HashSet<Integer>();
	for (int i=0; i < g.length; i++){
	    for (int j=0; j < g.length; j++){
		if (g[i][j] == 1) {
		    if (i == n) ns.add(j);
		    else if (j == n) ns.add(i);
		}
	    }
	}
	return ns;
    }

    private static void findMaximalCliques(Set<Integer> r, Set<Integer> p, 
					   Set<Integer> x, 
					   int[][] g, 
					   Set<Set<Integer>> cliques){
	if (p.isEmpty() && x.isEmpty()) cliques.add(r);

	for (Object o : p.toArray()){	    
	    Integer n = (Integer)o;
	    Set<Integer> ns = findNeighbours(n, g);
	    Set<Integer> r2 = new HashSet<Integer>(r);
	    Set<Integer> p2 = new HashSet<Integer>(p);
	    Set<Integer> g2 = new HashSet<Integer>(x);
	    r2.add(n);
	    p2.retainAll(ns);
	    g2.retainAll(ns);
	    findMaximalCliques(r2, p2, g2, g, cliques);
	    p.remove(n);
	    x.add(n);
	}
    }

    public static Set<Integer> findMaximumClique(int[][] g){
	System.out.println(g);
	System.out.println(p);	
	Set<Integer> r = new HashSet<Integer>();
	Set<Integer> p = new HashSet<Integer>();
	for (int i=0; i < g.length; i++) p.add(i);
	Set<Integer> x = new HashSet<Integer>();		
	Set<Set<Integer>> cliques = new HashSet<Set<Integer>>();
	
	findMaximalCliques(r, p, x, g, cliques);
	Set<Integer> max = null;
	for (Set<Integer> c : cliques){
	    if (max == null || c.size() > max.size()) max = c;
	}
		
	return max;
    }
    
}