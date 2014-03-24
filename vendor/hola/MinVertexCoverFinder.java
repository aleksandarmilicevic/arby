package hola;

import java.util.Set;
import java.util.HashSet;
import java.util.Arrays;

public class MinVertexCoverFinder {    
    
    public static void main(String[] args) {
	int n = 4;
	int[][] g = new int[n][n];	
	g[0][1] = 1;
	g[1][2] = 1;
	g[2][3] = 1;
		
	System.out.println(MinVertexCoverFinder.findMinVertexCover(g));
    }
    
    private static void printArray(int[][] g){
	for (int i=0; i < g.length; i++){
	    for (int j=0; j < g.length; j++){
		System.out.print(g[i][j] + " ");
	    }
	    System.out.println("");
	}
    }

    private static boolean isVertexCover(Set<Integer> candidate, int[][] g){
	for (int i=0; i < g.length; i++){
	    for (int j=0; j < g.length; j++){
		if (i != j && g[i][j] == 1){
		    if (!(candidate.contains(i) || candidate.contains(j)))
			return false;
		}
	    }
	}	
	return true;
    }

    public static Set<Integer> findMinVertexCover(int[][] g){
	printArray(g);
  	long startTime = System.nanoTime();
	Set<Integer> min = null;
	int pow = (int) Math.pow(2, g.length) - 1;
	for (int i = pow; i >= 1; i--){
	    String bstr = Integer.toBinaryString(i);
	    System.out.println(bstr);
	    for (int j = 0; j < bstr.length(); j++){
		Set<Integer> candidate = new HashSet<Integer>();
		if (bstr.charAt(j) == '1') candidate.add(j);		
		if (isVertexCover(candidate, g)){
		    if (min == null || candidate.size() < min.size())
			min = candidate;
		}
	    }
	}
  	long endTime = System.nanoTime();
	long duration = endTime - startTime;
	System.out.println("Imperative: " + duration/1000000000.0);
	return min;
    }
    
}