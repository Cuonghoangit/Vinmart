package miners.test;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.URL;


import miners.algorithms.frequentpatterns.efim.AlgoMTimEFIM;
import miners.algorithms.frequentpatterns.efim.Itemsets;

// dEFIM TESTER, OUTPUT TO SCREEN
public class testiMEFIM_mem {

	public static void main(String [] arg) throws IOException{		
		String input = fileToPath("BMS.txt");	// the input and output file paths
		String MMUPath = fileToPath("BMSMMU.txt");
		//int minutil = 12500000;					// the minutil threshold
		//double sumUtil = ;
		int dbSize = Integer.MAX_VALUE;//(1112949 * 100)/100;
		AlgoMTimEFIM algo = new AlgoMTimEFIM();				// Create the dEFIM algorithm object
		
		// execute the algorithm
		algo.runAlgorithm(input,MMUPath, null, true, dbSize, true);
		
		algo.printStats();							// Print statistics
		//itemsets.printItemsets();					// Print the itemsets
	}
	
	public static String fileToPath(String filename) throws UnsupportedEncodingException{
		URL url = testiMEFIM_mem.class.getResource(filename);
		 return java.net.URLDecoder.decode(url.getPath(),"UTF-8");
	}
}
