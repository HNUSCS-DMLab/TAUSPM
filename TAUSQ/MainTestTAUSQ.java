/**
 * Copyright (C), 2015-2020, HNU
 * FileName: MainTestTHUSSpan
 * Author:   K. Cao
 * Date:     2025/6/1 08:00
 * Description: This file is for testing the AlgoTHUSSpan algorithm.
 */
package TAUSQ;

import TAUSQ.AlgoTAUSQ;

import java.io.IOException;

public class MainTestTAUSQ {

    public static void main(String[] arg) throws IOException {
        /**设置数据集和阈值**/
        String dataset = "sign";
        double thresholdratio = 0.005;
        int[][] targetSequence = {
                {356,-1,10,-1,10,-1,10,-1,-2}, //bible
                {8,-1,17,-1,8,-1,-2},  //leviathan
                {1857,4250,-1,-2},            //syn
                {8,-1,9,-1,-2},       //sign
                {11,-1,218,-1,6,-1,148,-1,-2},    //kosarak
        };

        // run the algorithm
        //for (int i=0; i<Target.length; i++) {
            // the input database
            String input = "input/" + dataset + ".txt";
            //for (int j=0; j<utilityRatio.length; j++) {

            AlgoTAUSQ algo = new AlgoTAUSQ();

            // set the maximum pattern length (optional)
            algo.setMaxPatternLength(1000);

            //set target sequence
            algo.setTargetsequence(targetSequence[3]);

            // the path for saving the patterns found
            String output = "output/" + "TAUSQ_" + dataset + "_" + thresholdratio + ".txt";

            algo.runAlgorithm(input, output, thresholdratio);
            // print statistics
            algo.printStatistics();
            //index++;
            //}
        //}
    }
}
