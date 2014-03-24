package hola;

import java.util.Set;
import java.util.HashSet;
import java.util.Arrays;
import hola.MaxCliqueFinder;

public class MaxIndependentSetFinder {    
    
    public static void main(String[] args) {
	int n = 4;
	int[][] g = new int[n][n];	
	g[0][1] = 1;
	g[1][2] = 1;
	g[2][3] = 1;
		
	System.out.println(MaxIndependentSetFinder.findMaxIndependentSet(g));
    }

    private static void printArray(int[][] g){
	for (int i=0; i < g.length; i++){
	    for (int j=0; j < g.length; j++){
		System.out.print(g[i][j] + " ");
	    }
	    System.out.println("");
	}
    }

    private static int[][] complementGraph(int[][] g){
	int[][] g2 = new int[g.length][g.length];
	
	for (int i=0; i < g.length; i++){
	    for (int j=0; j < g.length; j++){
		if (j <= i || g[i][j] == 1) g2[i][j] = 0;
		else g2[i][j] = 1;
	    }
	}	
	return g2;
    }

    public static Set<Integer> findMaxIndependentSet(int[][] g){
	return MaxCliqueFinder.findMaximumClique(complementGraph(g));
    }   
}