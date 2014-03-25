package hola;

import java.util.Set;
import java.util.HashSet;
import java.util.Arrays;

public class MaxCutFinder {    
    
    public static void main(String[] args) {
	int n = 4;
	int[][] g = new int[n][n];	
	g[0][1] = 1;
	g[1][2] = 1;
	g[2][3] = 1;
		
	System.out.println(MaxCutFinder.findMaximumCut(g));
    }
     
    private static void printArray(int[][] g){
	for (int i=0; i < g.length; i++){
	    for (int j=0; j < g.length; j++){
		System.out.print(g[i][j] + " ");
	    }
	    System.out.println("");
	}
    }
   
    private static int cutSize(Set<Integer> cut, int[][] g){
	int size = 0;
	for (int i=0; i < g.length; i++){
	    for (int j=0; j < g.length; j++){
		if (i != j && g[i][j] == 1){
		    if ((cut.contains(i) && !cut.contains(j)) ||
			(cut.contains(j) && !cut.contains(i)))
			size++;
		}
	    }
	}
	return size;
    }

    private static String pad(String original, int l){
	String newStr = original;
	while (l > newStr.length()){
	    newStr = "0" + newStr;
	}
	return newStr;
    }

    public static Set<Integer> findMaximumCut(int[][] g){
	printArray(g);
  	long startTime = System.nanoTime();

	Set<Integer> max = null;
	int maxSize = 0;
	int pow = (int) Math.pow(2, g.length) - 1;
	for (int i = pow; i >= 1; i--){
	    String bstr = pad(Integer.toBinaryString(i), g.length);
	    Set<Integer> newCut = new HashSet<Integer>();
	    for (int j = 0; j < bstr.length(); j++){
		if (bstr.charAt(j) == '1') newCut.add(j);		
	    }
	    int s = cutSize(newCut, g);
	    if (max == null || 
		s > maxSize ||
		(s == maxSize && newCut.size() > max.size())) {
		max = newCut;
		maxSize = s;
	    }
	}
  	long endTime = System.nanoTime();
	long duration = endTime - startTime;
	System.out.println("Imperative: " + duration/1000000000.0);
	return max;
    }
    
}