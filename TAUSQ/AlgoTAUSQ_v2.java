/**
 * Copyright (C), 2015-2025, HNU
 * FileName: AlgoTAUSQ
 * Author: K. Cao
 * Date: 2025/6/1 08:00
 * Description: The implementation of TAUSQ algorithm.
 * Pruning strategy: SRAU + TDAU
F * Data structure: Targeted list + q-matrix + LOT
 */
package TAUSQ;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;
//output debug result
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

public class AlgoTAUSQ {

    //the time the algorithm started
    double startTimestamp = 0;
    //the time the algorithm terminated
    double endTimestamp = 0;
    //the number of patterns generated
    int patternCount = 0;

    //writer to write the output file
    BufferedWriter writer = null;

    final int BUFFERS_SIZE = 2000;

    //buffer for storing the current pattern that is mined when performing mining
    private int[] patternBuffer = null;

    //if true, debugging information will be shown in the console
    final int DEBUG = 0; //1:qmatrix,2:UtilityChain,3:Utility and SRAU/SRAU of each 1-sequence,4:Pre-insertion,5:projected UtilityChain,6:search order,7:q-seq包含target seq
    int DEBUG_flag = 0;

    //if true, save result to file in a format that is easier to read by humans
    final boolean SAVE_RESULT_EASIER_TO_READ_FORMAT = false;

    //the minimum average utility threshold
    double minAU = 0;

    //max pattern length
    int maxPatternLength = 1000;

    //the input file path
    String input;

    //Target sequence
    int[] targetSequence;

    //Target sequence length
    int targetSeqLength = 0;

    //Target sequence
    ArrayList<ArrayList<Integer>> targetseq;
    
    //non-high average utility itemset
    Set<Integer> tempSufSet = new HashSet<>();

    // the number of Candidate
    int NumOfCandidate = 0;

    /**
     * Default constructor
     */
    public AlgoTAUSQ() {
    }

    /**
     * @param input the input file path
     * @param output the output file path
     * @param utilityratio the minimum utility threshold ratio
     * @throws IOException exception if error while writing the file
     */
    public void runAlgorithm(String input, String output, double utilityratio) throws IOException {
        // reset maximum
        MemoryLogger.getInstance().reset();

        // input path
        this.input = input;

        // initialize the buffer for storing the current itemset
        patternBuffer = new int[BUFFERS_SIZE];

        // record the start time of the algorithm
        startTimestamp = System.currentTimeMillis();

        // create a writer object to write results to file
        writer = new BufferedWriter(new FileWriter(output));

        // for storing the current sequence number
        int NumberOfSequence = 0;

        // for storing the utility of all sequence
        int totalUtility = 0;

        BufferedReader myInput = null;
        String thisLine;

        //================  First DATABASE SCAN TO CONSTRUCT QMATRIX (DEFULT STORAGE MODE IN THE PAPER)	===================
        //================  CONSTRUCT UTILITYCHAINs OF ALL 1-SEQUENCEs, CALCULATE UTILITY AND SRAU OF THEM =================
        // Read the database to create the QMatrix for each sequence；
        List<QMatrix> database  = new ArrayList<>();
        // for storing an UtilityChain of each 1-sequence；
        Map<Integer,ArrayList<TargetedList>> mapItemUC = new HashMap<>();

        //for storing an Utility and SRAU of each 1-sequence；
        Map<Integer,Integer> mapItemUtility = new HashMap<>();
        Map<Integer,Integer> mapItemSRAU = new HashMap<>();
        Map<Integer, Map<Integer, int[]>> mapRsIUtility = new HashMap<>();

        //LOT；
        ArrayList<ArrayList<Integer>> LOT = new ArrayList<>();

        //convert to List
        targetseq = convertT(targetSequence);
        //scan target sequence length
        for (int item : targetSequence) {
        	if (item != -2 && item != -1)
        		targetSeqLength++;
        }

        try {
            // prepare the object for reading the file
            myInput = new BufferedReader(new InputStreamReader( new FileInputStream(new File(input))));

            // We will read each sequence in buffers.
            // The first buffer will store the items of a sequence and the -1 between them)；itemBuffer存q-seq中所有的item和-1
            int[] itemBuffer = new int[BUFFERS_SIZE];
            // The second buffer will store the utility of items in a sequence and the -1 between them)；utilityBuffer存q-seq中item的效用和-1
            int[] utilityBuffer = new int[BUFFERS_SIZE];
            // The following variable will contain the length of the data stored in the two previous buffer；以上两个数组的长度
            int itemBufferLength;
            // Finally, we create another buffer for storing the items from a sequence without
            // the -1. This is just used so that we can collect the list of items in that sequence
            // efficiently. We will use this information later to create the number of rows in the
            // QMatrix for that sequence.
            int[] itemsSequenceBuffer = new int[BUFFERS_SIZE];
            // The following variable will contain the length of the data stored in the previous buffer；
            int itemsLength;

            int seqnum = 0;
            // for each line (transaction) until the end of file
            while ((thisLine = myInput.readLine()) != null) {
                seqnum++;
                // if the line is  a comment, is  empty or is a kind of metadata
                if (thisLine.isEmpty() == true || thisLine.charAt(0) == '#' || thisLine.charAt(0) == '%' || thisLine.charAt(0) == '@') {
                    continue;
                }

                // for storing an UtilityList of each 1-sequence in the current transaction；
                Map<Integer, TargetedList> mapItemUL = new HashMap<Integer, TargetedList>();

                //for storing utility and remaining utility of each 1-sequence in the current transaction；
                Map<Integer, Integer> mapItemU = new HashMap<Integer, Integer>();
                Map<Integer, Integer> mapItemP = new HashMap<Integer, Integer>();
                Map<Integer, Map<Integer, int[]>> LocalmapRsIUtility = new HashMap<>();

              	// We reset the two following buffer length to zero because we are reading a new sequence.
                itemBufferLength = 0;
                itemsLength = 0;

                // split the sequence according to the " " separator
                String tokens[] = thisLine.split(" ");

                // get the sequence utility (the last token on the line)
                String sequenceUtilityString = tokens[tokens.length - 1];
                int positionColons = sequenceUtilityString.indexOf(':');
                int sequenceUtility = Integer.parseInt(sequenceUtilityString.substring(positionColons + 1));

                // This variable will count the number of itemsets；
                int nbItemsets = 1;

                //recording the remaining utility when constructing UtilityList(For Task 2)；
                int restUtility = sequenceUtility;

                // For each token on the line except the last three tokens (the -1 -2 and sequence utility).
                for (int i = 0; i < tokens.length - 4; i++) {
                    String currentToken = tokens[i];
                    // if empty, continue to next token
                    if (currentToken.length() == 0) {
                        continue;
                    }
                    // if the current token is -1 ,the ending sign of an itemset
                    if (currentToken.equals("-1")) {
                        // It means that it is the end of an itemset.
                        // We store the -1 in the respective buffers
                        itemBuffer[itemBufferLength] = -1;
                        utilityBuffer[itemBufferLength] = -1;
                        // We increase the length of the data stored in the buffers
                        itemBufferLength++;

                        // we update the number of itemsets in that sequence that are not empty
                        nbItemsets++;
                    } else {
                        //We need to finish the following three tasks if the current token is an item

                        /* Task 1: Construct QMtriax */

                        // We will extract the item from the string:
                        int positionLeftBracketString = currentToken.indexOf('[');
                        int positionRightBracketString = currentToken.indexOf(']');
                        String itemString = currentToken.substring(0, positionLeftBracketString);
                        Integer item = Integer.parseInt(itemString);

                        // We also extract the utility from the string:
                        String utilityString = currentToken.substring(positionLeftBracketString + 1, positionRightBracketString);
                        Integer itemUtility = Integer.parseInt(utilityString);

                        // We store the item and its utility in the buffers
                        // for temporarily storing the sequence
                        itemBuffer[itemBufferLength] = item;
                        utilityBuffer[itemBufferLength] = itemUtility;
                        itemBufferLength++;

                        // We also put this item in the buffer for all items of this sequence
                        itemsSequenceBuffer[itemsLength++] = item;
                    }
                }// task1 finish

                //DPP strategy
                if(seqContain(itemBuffer, itemBufferLength,targetSequence)==false) {
                    if(DEBUG==7){
                        System.out.print(seqnum+" 不包含target的 q-seq:");
                        for(int i=0;i<itemBufferLength;i++){
                            System.out.print(itemBuffer[i]+" ");
                        }
                        System.out.println();
                    }
                    continue;
                }

                //totalUtility只统计包含target seq的效用
                totalUtility += sequenceUtility;

                /************************LOT************************/
                fillLOT(LOT,targetseq,itemBuffer,itemBufferLength);
                if(DEBUG==8){
                    System.out.print("sid:"+NumberOfSequence+" ");
                    System.out.println(LOT.get(NumberOfSequence).toString());
                    System.out.println();
                }

                /**********************************以下完成task2和task3******************************************/

                /* Task 2: Construct UtilityList */

                //No. of itemset
                int currentItemset = 0;

                Map<Integer, int[]> mapRsSIU = new HashMap<>();
                //以下构建各个1-seq的utilitylist
                for (int i = 0; i < itemBufferLength; i++) {
                    int item = itemBuffer[i];
                    int itemUtility = utilityBuffer[i];
                    if(item == -1)  currentItemset++;
                    else {
                        restUtility -= itemUtility;

                        int oneseqIIMatch = 0;//item
                        int oneseqIMatch = 0;//itemset
                        if (item == targetSequence[0]) {
                        	oneseqIIMatch = 1;
                        }

                        /*****************CHECK for CONTAIN****************/
                        boolean rsContainsuf;

                        if(oneseqIMatch>=targetseq.size()) rsContainsuf=true;
                        else{
                            int lastpos = LOT.get(NumberOfSequence).get(oneseqIMatch).intValue();
                            if(lastpos<currentItemset){
                                rsContainsuf = false;
                            }else
                                rsContainsuf = true;
                        }

                        // if the item has not appeared in the current transaction
                        if (mapItemUL.get(item) == null) {
                            TargetedList tempUL = new TargetedList();
                            tempUL.set_sid(NumberOfSequence);

                            if (rsContainsuf) {

                                tempUL.set_IIMatch(oneseqIIMatch);
                                tempUL.set_IMatch(oneseqIMatch);

                                tempUL.add( currentItemset, itemUtility, restUtility);
                           }
                            mapItemUL.put(item, tempUL);
                        } else { // has appeared
                            //当剩余序列包含后缀时，才把这个instance放到utilitylist中
                            if (rsContainsuf) {
                                TargetedList tempUL = mapItemUL.get(item);
                                tempUL.add( currentItemset, itemUtility, restUtility);
                                mapItemUL.put(item, tempUL);
                            }
                        } //mapItemUL: for storing an UtilityList of each 1-sequence in the current transaction
                        //task2完成

                        /* Task 3: Calculate  Utility and SRAU */
                        //计算1-seq的效用和SRAU

                        mapRsSIU.clear();
                        int tempSRAU = 0;
                        // if ru==0 then SRAU=0。 序列的最后一个item的ru==0
                        if (i==itemBufferLength-1) {
                            tempSRAU = 0;
                        }else {
                            //因为1-seq的SRAU不是根据utilitylist计算的，所以计算它们的SRAU时，要增加剩余序列是否包含后缀的判断条件
                            if (rsContainsuf) {
                                tempSRAU = itemUtility + restUtility;

                                for (int k = i + 1; k < itemBufferLength; k++) {
                                    int tempItem = itemBuffer[k];
                                    int tempUtility = utilityBuffer[k];
                                    if (tempItem != -1) {
                                        if (mapRsSIU.get(tempItem) == null) {
                                            mapRsSIU.put(tempItem, new int[]{tempUtility,0});
                                        } else {
                                            int[] lastSIU = mapRsSIU.get(tempItem);
                                            if (lastSIU[0] < tempUtility) {
                                                mapRsSIU.put(tempItem, new int[]{tempUtility, lastSIU[1]+ lastSIU[0]});
                                            } else {
                                                mapRsSIU.put(tempItem, new int[]{lastSIU[0], lastSIU[1]+ tempUtility});
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        //if the item has not appeared in the current transaction
                        if (mapItemU.get(item) == null) {
                            mapItemU.put(item, itemUtility);
                            mapItemP.put(item, tempSRAU);
                            mapItemUL.get(item).set_SRAU(tempSRAU);
                            
                            LocalmapRsIUtility.put(item, new HashMap<>(mapRsSIU));
                        } else { //has appeared
                            if (itemUtility > mapItemU.get(item)) {
                                mapItemU.put(item, itemUtility);
                            }
                            //update SRAU
                            if (tempSRAU > mapItemP.get(item)) {
                                mapItemP.put(item, tempSRAU);
                                mapItemUL.get(item).set_SRAU(tempSRAU);
                            }
                        }
                    }
                } //finish task2,3

                //Update global variables mapItemUtility, mapItemSRAU and mapItemUC according to the current transaction
                //update 1-seq utility
                for(Entry<Integer,Integer> entry: mapItemU.entrySet()){
                    int item = entry.getKey();
                    if(mapItemUtility.get(item)==null){
                        mapItemUtility.put(item,entry.getValue());
                    }else{
                        mapItemUtility.put(item,entry.getValue()+ mapItemUtility.get(item));
                    }
                }

                for (Entry<Integer, Map<Integer, int[]>> entry : LocalmapRsIUtility.entrySet()) {
                    int item = entry.getKey();
                    if (mapRsIUtility.get(item) == null) {
                        mapRsIUtility.put(item, new HashMap<>(entry.getValue()));
                    } else {
                        // merge
                        for (Map.Entry<Integer, int[]> entry1 : entry.getValue().entrySet()) {
                            int innerKey = entry1.getKey();
                            int[] values = entry1.getValue();
                            if (mapRsIUtility.get(item).get(innerKey) == null) {
                                mapRsIUtility.get(item).put(innerKey, values.clone());
                            } else {
                                int[] existingValues = mapRsIUtility.get(item).get(innerKey);
                                for (int i = 0; i < values.length; i++) {
                                    existingValues[i] += values[i];
                                }
                            }
                        }
                    }
                }

                //update 1-seq SRAU
                for(Entry<Integer,Integer> entry: mapItemP.entrySet()){
                    int item = entry.getKey();
                    if(mapItemSRAU.get(item)==null){
                        mapItemSRAU.put(item,entry.getValue());
                    }else{
                        mapItemSRAU.put(item,entry.getValue()+ mapItemSRAU.get(item));
                    }
                }
                //update 1-seq utilitychain
                for(Entry<Integer, TargetedList> entry: mapItemUL.entrySet()){
                    int item = entry.getKey();
                    ArrayList<TargetedList> tempChain = new ArrayList<TargetedList>();
                    if(mapItemUC.get(item) != null)
                        tempChain = mapItemUC.get(item);
                    //add utilitylist to utilitychain
                    tempChain.add(entry.getValue());
                    mapItemUC.put(item,tempChain);
                }

                /******************************CONSTRUCT QMATRIX***********************************/
                // Now, we sort the buffer for storing all items from the current sequence in alphabetical order
                Arrays.sort(itemsSequenceBuffer,0, itemsLength);
                // but an item may appear multiple times in that buffer so we will loop over the buffer to remove duplicates
                // This variable remember the last insertion position in the buffer:
                int newItemsPos = 0;
                // This variable remember the last item read in that buffer
                int lastItemSeen = -999;
                // for each position in that buffer
                for(int i=0; i< itemsLength; i++) {
                    // get the item
                    int item = itemsSequenceBuffer[i];
                    // if the item was not seen previously
                    if(item != lastItemSeen) {
                        // we copy it at the current insertion position
                        itemsSequenceBuffer[newItemsPos++] = item;
                        // we remember this item as the last seen item
                        lastItemSeen = item;
                    }
                } // remove repeating items of itemsSequenceBuffer (length: newItemsPos) and sort it in ascending order

                // New we count the number of items in that sequence；
                int nbItems = newItemsPos;

                // And we will create the Qmatrix for that sequence
                QMatrix matrix = new QMatrix(nbItems, nbItemsets, itemsSequenceBuffer, nbItems, sequenceUtility);
                // We add the QMatrix to the initial sequence database.
                database.add(matrix);

                // Next we will fill the matrix column by column
                // This variable will represent the position in the sequence；
                int posBuffer = 0;

                for(int itemset=0; itemset < nbItemsets; itemset++) {
                    // This variable represent the position in the list of items in the QMatrix
                    int posNames = 0;

                    // While we did not reach the end of the sequence；
                    while(posBuffer < itemBufferLength) {
                        // Get the item at the current position in the sequence
                        int item = itemBuffer[posBuffer];

                        // if it is an itemset separator, we move to next position in the sequence
                        if(item == -1) {
                            posBuffer++;
                            break;
                        }
                        // else if it is the item that correspond to the next row in the matrix
                        else if(item == matrix.itemNames[posNames]) {
                            // calculate the utility for this item/itemset cell in the matrix
                            int utility = utilityBuffer[posBuffer];
                            // We update the remaining utility by subtracting the utility of the
                            // current item/itemset
                            sequenceUtility -= utility;
                            // update the cell in the matrix
                            matrix.registerItem(posNames, itemset, utility, sequenceUtility);
                            // move to the next item in the matrix and in the sequence
                            posNames++;
                            posBuffer++;
                        }else if(item > matrix.itemNames[posNames]) {
                            // if the next item in the sequence is larger than the current row in the matrix
                            // it means that the item do not appear in that itemset, so we put a utility of 0
                            // for that item and move to the next row in the matrix.
                            matrix.registerItem(posNames, itemset, 0, sequenceUtility);
                            posNames++;
                        }else {
                            // Otherwise, we put a utility of 0 for the current row in the matrix and move
                            // to the next item in the sequence
                            matrix.registerItem(posNames, itemset, 0, sequenceUtility);
                            posBuffer++;
                        } // By default, the items in reverse order are deleted.
                    }
                } // QMatrix of the current transaction has been built.

                // if in debug mode, we print the q-matrix that we have just built
                if(DEBUG==1) {
                    System.out.println(matrix.toString());
                    System.out.println();
                }
                //System.out.print(NumberOfSequence+"------");System.out.println(thisLine);

                // we update the number of transactions；
                NumberOfSequence++;
            } // finish scaning a transaction each time through the loop

            System.out.println("num of q-seq that contain target sequence:" + NumberOfSequence);

            // if in debug mode, we print the UtilityChain that we have just built
            if(DEBUG==2) {
                for (Entry<Integer,ArrayList<TargetedList>> entry: mapItemUC.entrySet()){
                    System.out.println("item:"+entry.getKey());
                    for(int i=0;i<entry.getValue().size();i++){
                        System.out.println(i+"-th UtilityList:");
                        for(int j=0;j<entry.getValue().get(i).LengthOfUtilityList;j++){
                            System.out.print(j+"-th element: ");
                            System.out.print("sid:"+entry.getValue().get(i).get_sid());
                            System.out.print("  tid:"+entry.getValue().get(i).List.get(j).tid);
                            System.out.print("  acu:"+entry.getValue().get(i).List.get(j).acu);
                            System.out.println("  rru:"+entry.getValue().get(i).List.get(j).rru);
                        }
                        System.out.println("End of a UtilityList");
                    }
                    System.out.println("******");
                }
            }

            // if in debug mode, we print the Utility and SRAU of each 1-sequence that we have just built
            if(DEBUG==3) {
                System.out.println("SRAU:");
                for (Entry<Integer,Integer> entry: mapItemSRAU.entrySet()){
                    System.out.println(entry.getKey()+" : "+entry.getValue());
                }
                System.out.println("******");
                System.out.println("Utility:");
                for (Entry<Integer,Integer> entry: mapItemUtility.entrySet()){
                    System.out.println(entry.getKey()+" : "+entry.getValue());
                }
            }
        } catch (Exception e) {
            // catches exception if error while reading the input file
            e.printStackTrace();
        }finally {
            if(myInput != null){
                // close the input file
                myInput.close();
            }
        }

        // check the memory usage
        MemoryLogger.getInstance().checkMemory();

        //set threshold
        this.minAU = utilityratio * totalUtility;
        System.out.println("total utility: "+totalUtility+" utility ratio:"+utilityratio+" AU_Threshold:"+this.minAU);

        // Mine the database recursively
        for(Entry<Integer, Integer> entry : mapItemSRAU.entrySet()){
        	int item = entry.getKey();
            patternBuffer[0]= item;
            patternBuffer[1] = -1;
            patternBuffer[2] = -2;

            NumOfCandidate++;

            //check 1-seq
            if(mapItemUtility.get(item) >= (minAU * (0 + 1)) && seqContain(patternBuffer,1,targetSequence)){
                //writeOut(patternBuffer,1,mapItemUtility.get(item));
                patternCount++;
            }

            // SRAU pruning strategy
            Set<Integer> tempSLowUList = new HashSet<>();
            int tempLowIUtility = 0;
            int temprrsICount = 0;
            int qSufIUtility =0;
            int rrsMaxLen = 0;

            int oneseqIIMatch = 0;
            if (item == targetSequence[0]) {
            	oneseqIIMatch = 1;
            }

            int sufTCount = 0;
            tempSufSet.clear();
            for (int l = oneseqIIMatch; l <targetSequence.length; l++) {
                if ( targetSequence[l] != -2 && targetSequence[l] != -1) {
                    int tempSufItem = targetSequence[l];
                    tempSufSet.add(tempSufItem);
                	sufTCount++;
                }
            }

            for (Map.Entry<Integer, int[]> entry1 : mapRsIUtility.get(item).entrySet()) {
            	int tempItem = entry1.getKey();
            	int[] tempValue = entry1.getValue();
               if (tempValue[0] < minAU) {
            	   if (!tempSufSet.contains(tempItem)) {
                	tempLowIUtility += (tempValue[0] + tempValue[1]);
                	tempSLowUList.add(tempItem);
            	   } else {
                	   qSufIUtility += (tempValue[0] + tempValue[1]);
                   }
                } else {
                	temprrsICount++;
                }
            }

            rrsMaxLen = Math.max(sufTCount, temprrsICount);
            if (temprrsICount < sufTCount)
            	tempLowIUtility += qSufIUtility;

            if (entry.getValue()-tempLowIUtility >= minAU*(0 + 1 + rrsMaxLen)) {
                TUSQ(patternBuffer, 1, database, mapItemUC.get(item), 1, targetSequence, LOT, tempSLowUList, sufTCount);
            }
        }

        double runtime = System.currentTimeMillis() - startTimestamp;
        StringBuilder buffer = new StringBuilder();
        buffer.append("============= ALGOTUSQ  v1.0 - STATS =============\n");
        buffer.append(" Target sequence:");
        for(int item:targetSequence){
            buffer.append(item+",");
        }
        buffer.append("\n");
        buffer.append(" num of q-seq that contain target sequence :" + NumberOfSequence + " \n");
        buffer.append(" Threshold :"+ this.minAU +" \n");
        buffer.append(" Total time : " + runtime/1000 + " s\n");
        buffer.append(" Max Memory : " + MemoryLogger.getInstance().getMaxMemory() + " MB\n");
        buffer.append(" Number of candidates : " + NumOfCandidate + " \n");
        buffer.append(" High-utility sequential pattern count : " + patternCount);
        writer.write(buffer.toString());
        writer.newLine();

        // check the memory usage again and close the file.
        MemoryLogger.getInstance().checkMemory();
        // close output file
        writer.close();
        // record end time
        endTimestamp = System.currentTimeMillis();
    }

    //This inner class is used to store the information of candidates after concatenating the item.
    public class ItemConcatnation implements Comparable<ItemConcatnation>{
        // utility
        int utility;
        // SRAU
        int SRAU;
        // max(extrarrsICount, sufTCount)
        int rrsMaxLen;
        // projected database UtilityChain；
        ArrayList<TargetedList> UChain;
        // Candidate after concatenating the item
        public int[] candidate;
        // length of Candidate after concatenating the item
        int candidateLength;
        // new part of LowUList
        Set<Integer> extraLowUList;

        int sufTCount;

        // Constructor
        public ItemConcatnation(int utility, int SRAU, int rrsMaxLen, ArrayList<TargetedList> UChain, int[] candidate, int candidateLength, Set<Integer> extraLowUList, int sufTCount){
            this.utility = utility;
            this.SRAU = SRAU;
            this.rrsMaxLen = rrsMaxLen;
            this.UChain = UChain;
            this.candidateLength = candidateLength;
            this.candidate = new int[BUFFERS_SIZE];
            this.extraLowUList = new HashSet<>(extraLowUList);
            this.sufTCount = sufTCount;
            System.arraycopy(candidate, 0, this.candidate, 0, candidateLength);
        }

        // overwrite the compareTo function；
        public int compareTo(ItemConcatnation t){
            if (this.SRAU > t.SRAU)
                return -1;
            else if(this.SRAU < t.SRAU)
                return 1;
            else
                return 0;
        }
    }

    /**
     * construct target chain of candidates
     * @param candidate a sequence t'
     * @param candidateLength length of sequence t'
     * @param database q-matrix of all sequences 
     * @param utilitychain target chain of t which is the prefix of t'
     * @param kind 0:i-Concatenation，1:s-Concatenation
     * @param T target sequence
     * @param LOT last instance table
     * @param extraLowUList set of non-high utility item
     */
    private ItemConcatnation constructUtilityChain(int[] candidate, int candidateLength, List<QMatrix> database, ArrayList<TargetedList> utilitychain, int kind, int[] T, ArrayList<ArrayList<Integer>> LOT, Set<Integer> extraLowUList){
    	
        //store UtilityChain of candidate
        ArrayList<TargetedList> uc = new ArrayList<TargetedList>();
        int item = candidate[candidateLength-1];
        // store utility and SRAU of candidate
        int Utility = 0;
        int SRAU = 0;
        Map<Integer, Integer> mapRrsIU = new HashMap<Integer, Integer>();
      	int tempIIMatch = 0;
      	int tempIMatch = 0;
        Map<Integer, Integer> lastrrsIU = new HashMap<Integer, Integer>();
        Map<Integer, Integer> localmapRrsIU = new HashMap<Integer, Integer>();
        //rrs corresponds to the instance of t'
        Map<Integer, Map<Integer, Integer>> mapmapRrsIU = new HashMap<Integer, Map<Integer, Integer>>();

        //for each UtilityList of candidate's Prefix
        for (TargetedList utilitylist:utilitychain){
            // LocalUtility、LocalSRAU记录t'在此sequence中的utility和SRAU
            int LocalUtility = 0;
            int LocalSRAU = 0;
            localmapRrsIU.clear();
        	mapmapRrsIU.clear();
            
            //check whether instances exist
            if(utilitylist.List.size()==0){
                continue;
            }
            //initialize the variables
            //store serial number of transaction
            int sid = utilitylist.get_sid();

            //utilitylist of t'
            TargetedList ul = new TargetedList();
            ul.set_sid(sid);
            //get qmatrix of the current transaction
            QMatrix qmatrix = database.get(sid);
            //ItemNum: sequence length
            int ItemNum = qmatrix.itemNames.length;
            int row = 0;
            //get row
            while (row!=ItemNum){
                if (item==qmatrix.itemNames[row]){
                    break;
                }
                row++;
            }
            //If the last item of t' does not appear in the current sequence
            if (row==qmatrix.itemNames.length)
                continue;

            /***************************************I-CONCATENATION**********************************************/
            if(kind==0){
                //sequence length
            	int ItemsetNum = qmatrix.matrixItemUtility[0].length;

                //construct UtilityList of candidate in the current transaction
                for (int j = 0; j<utilitylist.LengthOfUtilityList; j++){
                    int column = utilitylist.List.get(j).tid;
                    int ItemUtility = qmatrix.matrixItemUtility[row][column];

                    //If the last item of t' do appear
                    if (ItemUtility!=0){

                    	//flags corresponds to the current element
                    	int IIMatch = utilitylist.get_IIMatch();
                        int IMatch = utilitylist.get_IMatch();
                        
                        //update flags
                        int[] newMatch = updateMatch(item, IIMatch, IMatch, targetseq, 0);
                    	
                        /*****************CHECK SUFFIX MATCH****************/
                        boolean rsContainsuf;

                        if(newMatch[1]>=targetseq.size()) rsContainsuf=true;
                        else{
                            int lastpos = LOT.get(sid).get(newMatch[1]);
                            if(lastpos<column){
                                rsContainsuf = false;
                            }else
                                rsContainsuf = true;
                        }

                        //update utilitylist of t'
                        if(rsContainsuf) {
                        	//update rrs
                            int ItemRsU = qmatrix.matrixItemRemainingUtility[row][column];//如果ItemUtility==0，这么取RemainingUtility可能出错
                            int tempConItem = 0;
                            int tempConItemUtility = 0;

                            if(j==0) {
                                mapRrsIU.clear();
                            	for (int n=column+1; n<ItemsetNum; n++){
                            		for (int m=0; m<ItemNum; m++) {
                            			tempConItem = qmatrix.itemNames[m];
                            			tempConItemUtility = qmatrix.matrixItemUtility[m][n];
                                        if (tempConItemUtility != 0) {
                                            if (!extraLowUList.contains(tempConItem)){
                                				if(mapRrsIU.get(tempConItem)==null) {
                                					mapRrsIU.put(tempConItem, tempConItemUtility);
                                				} else {
                                					if(tempConItemUtility > mapRrsIU.get(tempConItem)) {
                                						mapRrsIU.put(tempConItem, tempConItemUtility);
                                					}
                                				}
                                            } else {
                                            	ItemRsU -= tempConItemUtility;
                                            }
                                        }
                            		}
                            	}
                            	for (int m=row+1; m<ItemNum; m++) {
                            		tempConItem = qmatrix.itemNames[m];
                        			tempConItemUtility = qmatrix.matrixItemUtility[m][column];
                                    if (tempConItemUtility != 0) {
                                        if (!extraLowUList.contains(tempConItem)){
                            				if(mapRrsIU.get(tempConItem)==null) {
                            					mapRrsIU.put(tempConItem, tempConItemUtility);
                            				} else {
                            					if(tempConItemUtility > mapRrsIU.get(tempConItem)) {
                            						mapRrsIU.put(tempConItem, tempConItemUtility);
                            					}
                            				}
                            			} else {
                                        	ItemRsU -= tempConItemUtility;
                                        }
                                    }
                            	}
                        	}//End of update rrs

                            ul.set_IIMatch(newMatch[0]);
                            ul.set_IMatch(newMatch[1]);

                            ul.add(column, utilitylist.List.get(j).acu + ItemUtility, ItemRsU);
                            mapmapRrsIU.put(column, mapRrsIU);
                        }
                    }
                }
                // if the current transaction does not hold candidate
                if (ul.LengthOfUtilityList==0)
                    continue;
            }//finish the construction of the utilitylist of t' after i-extension
            else{
                /******************************************S-CONCATENATION****************************************/
                //sequence length
                int ItemsetNum = qmatrix.matrixItemUtility[0].length;
                //for temporarily storing UtilityElement
                Map<Integer, TargetedList.UtilityElement> mapUE = new HashMap<Integer, TargetedList.UtilityElement>();
                //an instance of UtilityList
                TargetedList l = new TargetedList();

                //construct UtilityList of candidate in the current transaction     
                for (int j = 0; j<utilitylist.LengthOfUtilityList; j++){
                    int column = utilitylist.List.get(j).tid;
                    
                    //flags corresponds to the current element
                    int IIMatch = utilitylist.get_IIMatch();
                    int IMatch = utilitylist.get_IMatch();

                    for (int i=column+1;i<ItemsetNum;i++){

                        int ItemUtility = qmatrix.matrixItemUtility[row][i];
                        if (ItemUtility!=0) {
                            //update flags
                            int[] newMatch = updateMatch(item, IIMatch, IMatch, targetseq, 1);

                            /*****************判断剩余序列是否包含后缀****************/
                            boolean rsContainsuf;

                            if(newMatch[1]>=targetseq.size()) rsContainsuf=true;
                            else{
                                int lastpos = LOT.get(sid).get(newMatch[1]);
                                if(lastpos< i ){
                                    rsContainsuf = false;
                                }else
                                    rsContainsuf = true;
                            }

                            if (rsContainsuf) {
                                int PrefixUtility = utilitylist.List.get(j).acu;

                                ul.set_IIMatch(newMatch[0]);
                                ul.set_IMatch(newMatch[1]);
                                
                               if (mapUE.get(i) == null) {
                                	//rrs
                                    int ItemRsU = qmatrix.matrixItemRemainingUtility[row][i];//如果ItemUtility==0，这么取RemainingUtility可能出错
                                    int tempConItem = 0;
                                    int tempConItemUtility = 0;
                                    mapRrsIU.clear();
                                    for (int n=i+1; n<ItemsetNum; n++){
                                    	for (int m=0; m<ItemNum; m++) {
                                    		tempConItem = qmatrix.itemNames[m];
                                    		tempConItemUtility = qmatrix.matrixItemUtility[m][n];
                                    		if (tempConItemUtility != 0) {
                                            	if (!extraLowUList.contains(tempConItem)){
                                            		if(mapRrsIU.get(tempConItem)==null) {
                                            			mapRrsIU.put(tempConItem, tempConItemUtility);
                                            		} else {
                                            			if(tempConItemUtility > mapRrsIU.get(tempConItem)) {
                                            				mapRrsIU.put(tempConItem, tempConItemUtility);
                                            			}
                                            		}
                                            	} else {
                                            		ItemRsU -= tempConItemUtility;
                                            	}
                                    		}
                                    	}
                                    }

                                    for (int m=row+1; m<ItemNum; m++) {
                                    	tempConItem = qmatrix.itemNames[m];
                                    	tempConItemUtility = qmatrix.matrixItemUtility[m][i];
                                    	if (tempConItemUtility != 0) {
                                    		if (!extraLowUList.contains(tempConItem)){
                                    			if(mapRrsIU.get(tempConItem)==null) {
                                    				mapRrsIU.put(tempConItem, tempConItemUtility);
                                    			} else {
                                    				if(tempConItemUtility > mapRrsIU.get(tempConItem)) {
                                    					mapRrsIU.put(tempConItem, tempConItemUtility);
                                    				}
                                    			}
                                    		} else {
                                    			ItemRsU -= tempConItemUtility;
                                    		}
                                    	}
                                    }//End of rrs
                                    mapUE.put(i, l.new UtilityElement(i, PrefixUtility + ItemUtility, ItemRsU));
                                    mapmapRrsIU.put(i, new HashMap<>(mapRrsIU));
                                } else {
                                    //store the UtilityElement whose utility is larger prefix positions are different but pivot is the same.
                                    if (mapUE.get(i).acu < PrefixUtility + ItemUtility)
                                    	mapUE.put(i, l.new UtilityElement(i, PrefixUtility + ItemUtility, mapUE.get(i).rru));
                                }
                            }
                        }
                    }
                }
                // if the current transaction does not hold candidate
                if (mapUE.size()==0)
                    continue;

                //sort mapUE in tid ascending order
                List<Entry<Integer, TargetedList.UtilityElement>> list = new ArrayList<Entry<Integer, TargetedList.UtilityElement>>(mapUE.entrySet());
                if (mapUE.size()!=1){
                    Collections.sort(list, new Comparator<Entry<Integer, TargetedList.UtilityElement>>() {
                        @Override
                        public int compare(Entry<Integer, TargetedList.UtilityElement> o1, Entry<Integer, TargetedList.UtilityElement> o2) {
                            return o1.getKey().compareTo(o2.getKey());
                        }
                    });
                }
                // finish updating UtilityList of the current transaction
                for (int i = 0; i < list.size(); i++) {
                    TargetedList.UtilityElement tmpUE = list.get(i).getValue();
                    ul.add(tmpUE.tid,tmpUE.acu,tmpUE.rru);
                }
            }//finish the construction of the utilitylist of t' after s-extension

            // calculate utility and SRAU of candidate in the current transaction
            for (int i=0; i<ul.LengthOfUtilityList; i++){
                TargetedList.UtilityElement ue = ul.List.get(i);
                if (ue.acu>LocalUtility) {
                    LocalUtility = ue.acu;
                    localmapRrsIU = new HashMap<>(mapmapRrsIU.get(ue.tid));
                }
                if (qmatrix.matrixItemRemainingUtility[row][ue.tid]==0)
                    continue;
                if(ue.acu+ue.rru>LocalSRAU) {
                    LocalSRAU = ue.acu+ue.rru;
                    localmapRrsIU = new HashMap<>(mapmapRrsIU.get(ue.tid));
                }
            }

            //calculate utility and SRAU of candidate and update the two global variable SRAU and Utility
            Utility += LocalUtility;
            SRAU += LocalSRAU;
            ul.set_SRAU(LocalSRAU);

            if (ul.get_IMatch() > tempIMatch) {
            	tempIMatch = ul.get_IMatch();
            	tempIIMatch = ul.get_IIMatch();
            } else {
                if (ul.get_IIMatch() > tempIIMatch) {
            	    tempIIMatch = ul.get_IIMatch();
                }
            }
            
            for (Entry<Integer, Integer> entry:localmapRrsIU.entrySet()){
            	int ConItem = entry.getKey();
                lastrrsIU.merge(ConItem, entry.getValue(), Integer::sum);
            }

            //add UtilityList to UtilityChain
            uc.add(ul);
        }
        // if in debug mode, we print the UtilityChain that we have just built
        if(DEBUG==5){
            //System.out.println("**********************");
            System.out.print("Pattern: ");
            for (int i = 0; i < candidateLength; i++) {
                System.out.print(candidate[i] + " ");
            }
            //System.out.println();
            System.out.println("  总SRAU:" + SRAU + " 总Utility:" + Utility);
            for (int i = 0; i < uc.size(); i++) {
                System.out.println(i + "-th UtilityList:");
                for (int j = 0; j < uc.get(i).LengthOfUtilityList; j++) {
                    System.out.print("Element" + j + ": ");
                    System.out.print("sid:" + uc.get(i).get_sid());
                    System.out.print("  tid:" + uc.get(i).List.get(j).tid);
                    System.out.print("  acu:" + uc.get(i).List.get(j).acu);
                    System.out.println("  rru:" + uc.get(i).List.get(j).rru);
                }
                System.out.println("End of a UtilityList");
            }
            System.out.println("#####################");
        }
        
        candidate[candidateLength]=-1;
        candidate[candidateLength+1]=-2;


        HashSet<Integer> tempLowUList = new HashSet<>(extraLowUList);
        int extraLowIUtility = 0;
        int extrarrsICount = 0;
        int qSufIUtility = 0;
        int rrsMaxLen = 0;
        int sufTCount = 0;

        if (lastrrsIU!=null) {

            tempSufSet.clear();
            for (int l = tempIMatch; l < targetseq.size(); l++) {
            	for (int k = tempIIMatch; k <targetseq.get(l).size(); k++) {
            		int tempSufItem = targetseq.get(l).get(k);
            		tempSufSet.add(tempSufItem);
            		sufTCount++;
            	}
            }

            for (Map.Entry<Integer, Integer> entry : lastrrsIU.entrySet()) {
            	int tempItem = entry.getKey();
            	int tempValue = entry.getValue();
                if (tempValue < minAU) {
                    if (!tempSufSet.contains(tempItem)) {
                	    extraLowIUtility += tempValue;
                	    tempLowUList.add(tempItem);
                   } else {
                	   qSufIUtility += tempValue;
                   }
                } else {
                	extrarrsICount++;
                }
            }

            rrsMaxLen = Math.max(extrarrsICount, sufTCount);
            if (extrarrsICount < sufTCount)
            	extraLowIUtility += qSufIUtility;
        }

        //return an instance
        return new ItemConcatnation(Utility, SRAU-extraLowIUtility, rrsMaxLen, uc, candidate, candidateLength, tempLowUList, sufTCount);
    }

    /**
     * a recursive function to mine high utility pattern
     * @param prefix mine high utility pattern based on prefix
     * @param prefixLength length of prefix
     * @param database q-matrix of all sequences
     * @param utilitychain target chain of prefix
     * @param itemCount number of items in prefix
     * @param T target sequence
     * @param LOT last instance table
     * @param lastLowUList set of non-high utility item
     * @param sufTCount length of qSuf
     */
    private void TUSQ(int[] prefix, int prefixLength, List<QMatrix> database, ArrayList<TargetedList> utilitychain, int itemCount, int[] T, ArrayList<ArrayList<Integer>>LOT, Set<Integer> lastLowUList, int sufTCount){
        //Update the count of the candidate
        if(DEBUG==6){
            if (DEBUG_flag>0&&DEBUG_flag<10000){
                // Print the current prefix
                for(int i=0; i< prefixLength; i++){
                    System.out.print(prefix[i] + " ");
                }
//                System.out.println(DEBUG_flag+"TmpMinUtility:"+minUtility);
                System.out.println(DEBUG_flag+"TmpMinAU:"+minAU);
                System.out.println();
            }
        }

        //for storing TDU  after concatenation
        Map<Integer,Integer>mapiItemTDU = new HashMap<>();
        Map<Integer,Integer>mapsItemTDU = new HashMap<>();
        
        /**********************************************CONSTRUCTION of ILIST and SLIST**********************************************/
        //scan prefix-projected DB once to find items to be concatenated
        for (TargetedList utilitylist:utilitychain) {
            //store the qmatrix of the current transaction
            if(utilitylist.List.size()==0) {
                continue;
            }
            int sid = utilitylist.get_sid();
            QMatrix qmatrix = database.get(sid);

            //record the last item of Prefix
            int item = prefix[prefixLength-1];

            int row = 0;
            while (item!=qmatrix.itemNames[row]){
                row++;
            }

            /***********************************CONSTRUCTION of ILIST********************************/
            // put i-extension items into ilist
            // update the global variable mapiItemTDU
            int ItemNum = qmatrix.itemNames.length;

            for (int j = 0; j<utilitylist.LengthOfUtilityList;j++){
                int column = utilitylist.List.get(j).tid;
                
                //current element flags
                int IIMatch = utilitylist.get_IIMatch();
                int IMatch = utilitylist.get_IMatch();

                //extension item in current element for i-extension
                for (int i=row+1;i<ItemNum;i++){
                    int ConItem = qmatrix.itemNames[i];
                    /*******************************CALCULATION TDAU of ITEM in THE ILIST*********************************/
                    if (qmatrix.matrixItemUtility[i][column]!=0){
                    	
                        //update match flags
                        int[] newMatch = updateMatch(ConItem, IIMatch, IMatch, targetseq,0);
                        
                        /*****************CHECK for CONTAIN****************/
                        boolean rsContainsuf;

                        if(newMatch[1]>=targetseq.size()) rsContainsuf=true;
                        else{
                            int lastpos = LOT.get(sid).get(newMatch[1]);
                            if(lastpos < column){
                                rsContainsuf = false;
                            }else
                                rsContainsuf = true;
                        }

                        if(rsContainsuf) {

                        	if (mapiItemTDU.get(ConItem) == null) {
                                mapiItemTDU.put(ConItem, utilitylist.SRAU);
                            } else {
                                mapiItemTDU.merge(ConItem, utilitylist.SRAU, Integer::sum);
                            }
                        }
                    }
                }
            }

            /***********************************CONSTRUCTION of SLIST********************************/
            //put s-extension items into slist
            //get the items to be s-concatenated
            int column = utilitylist.List.get(0).tid;

            //current element flags
            int IIMatch = utilitylist.get_IIMatch();
            int IMatch = utilitylist.get_IMatch();

            Map<Integer, Integer>temp_mapsItemSRAU = new HashMap<Integer, Integer>();
            int ItemsetNum = qmatrix.matrixItemUtility[0].length;
            Map<Integer, Map<Integer, Integer>> temp_mapmapRsIU= new HashMap<>();
            Map<Integer,Integer>temp_mapsSufTCount = new HashMap<Integer,Integer>();

            for (int j = column+1; j < ItemsetNum; j++) {
                for (int i=0;i<ItemNum;i++) {
                    int ConItem = qmatrix.itemNames[i];
                    if (qmatrix.matrixItemUtility[i][j] != 0) {

                    	//update match flags
                    	int[] newMatch = updateMatch(ConItem, IIMatch, IMatch, targetseq, 1);
                        
                        /*****************判断剩余序列是否包含后缀****************/
                        boolean rsContainsuf;

                        if(newMatch[1]>=targetseq.size()) rsContainsuf=true;
                        else{
                            int lastpos = LOT.get(sid).get(newMatch[1]);
                            if(lastpos < j ){
                                rsContainsuf = false;
                            }else
                                rsContainsuf = true;
                        }

                        if(rsContainsuf) {
                            if (temp_mapsItemSRAU.get(ConItem) == null) {
                                temp_mapsItemSRAU.put(ConItem, utilitylist.SRAU);
                            } 
                        }
                    }
                }
            }

            /******************************CALCULATION TDAU of ITEM in THE SLIST*****************************/
            //update the global variable mapsItemTDU
            for (Entry<Integer, Integer> entry:temp_mapsItemSRAU.entrySet()){
            	int ConItem = entry.getKey();
                if(mapsItemTDU.get(ConItem)==null){
                    mapsItemTDU.put(ConItem, entry.getValue());
                }else{
                    mapsItemTDU.merge(ConItem, entry.getValue(), Integer::sum);
                }
            }

        }

        // for temporarily storing item and its SRAU
        ItemConcatnation ItemCom;

        /************************************  I-CONCATENATIONS  ***********************************/
        // We first try to perform I-Concatenations to grow the pattern larger.
        // be concatenated to the prefix.
        for (Entry<Integer,Integer> entry:mapiItemTDU.entrySet()){
            int tdu = entry.getValue();
            int ConItem = entry.getKey();

            //construct the candidate after concatenating
            prefix[prefixLength]=ConItem;

            /*******************WIDTH PRUNING STRATEGY**********************/
            int tempLowIUtility = 0;
            int temprrsICount = 0;

            if ( (tdu - tempLowIUtility) < minAU*(itemCount+ 0 + Math.max(0, sufTCount-1)) ){
                continue;
            }

            NumOfCandidate++;

            //call the function to construct UtilityChain of the candidate
            /*************************CONSTRUCTION of NEW UTILITYCHAIN****************************/
            //构造t'的utilitychain
            if (itemCount+1<=maxPatternLength){
                ItemCom = constructUtilityChain(prefix,prefixLength+1,database,utilitychain,0,T,LOT,lastLowUList);
                /********************UPDATE TAUSPs***********************/
                if(ItemCom.utility >= (minAU * (itemCount+1)) && ItemCom.UChain.get(0).IMatch >= targetseq.size()){
                    //writeOut(ItemCom.candidate,ItemCom.candidateLength,ItemCom.utility);
                    patternCount++;
                    //System.out.println("[ "+ToString(ItemCom.candidate, ItemCom.candidateLength)+"]"+"    Utility: "+ItemCom.utility);
                }
                
                // SRAU pruning strategy
                /******************************DEPTH PRUNING STRATEGY**********************************/
                if (ItemCom.SRAU >= minAU * (itemCount + 1 + ItemCom.rrsMaxLen)){
                	//Mine the database recursively
                    TUSQ(ItemCom.candidate, ItemCom.candidateLength, database, ItemCom.UChain, itemCount+1,T,LOT, ItemCom.extraLowUList, ItemCom.sufTCount);
                    }
            }
        }

        /************************************  S-CONCATENATIONS  ***********************************/
        // We first try to perform S-Concatenations to grow the pattern larger.
        // be concatenated to the prefix.
        for (Entry<Integer,Integer> entry:mapsItemTDU.entrySet()){
            int tdu = entry.getValue();
            int ConItem = entry.getKey();

            //construct the candidate after concatenating
            prefix[prefixLength]=-1;
            prefix[prefixLength+1]=ConItem;
            
            /*******************WIDTH PRUNING STRATEGY**********************/
            int tempLowIUtility = 0;
            int temprrsICount = 0;
            if ( (tdu - tempLowIUtility) < minAU*(itemCount+ 0 + Math.max(0, sufTCount-1)) ){
            	continue;
            }

            NumOfCandidate++;

            /*************************CONSTRUCTION of NEW UTILITYCHAIN****************************/
            //call the function to construct UtilityChain of the candidate
            if (itemCount+1<=maxPatternLength){
                ItemCom = constructUtilityChain(prefix,prefixLength+2,database,utilitychain,1,T,LOT,lastLowUList);
                /********************UPDATE TAUSPs**********************/
                if(ItemCom.utility >= minAU * (itemCount+1) && ItemCom.UChain.get(0).IMatch >= targetseq.size()){
                    //writeOut(ItemCom.candidate,ItemCom.candidateLength,ItemCom.utility);
                    patternCount++;
                    //System.out.println("[ "+ToString(ItemCom.candidate, ItemCom.candidateLength)+"]"+"    Utility: "+ItemCom.utility);
                }
                
                // SRAU pruning strategy
                /******************************DEPTH PRUNING STRATEGY**********************************/
                if (ItemCom.SRAU >= minAU * (itemCount + 1 + ItemCom.rrsMaxLen)){
                	//Mine the database recursively
                    TUSQ(ItemCom.candidate, ItemCom.candidateLength, database, ItemCom.UChain, itemCount+1,T,LOT, ItemCom.extraLowUList, ItemCom.sufTCount);
                    }
            }
        }

        // We check the memory usage
        MemoryLogger.getInstance().checkMemory();
    }

    
    private String ToString(int[] candidate, int candidateLength) {
		// TODO Auto-generated method stub
        StringBuilder stringBuilder = new StringBuilder();
        for(int i=0;i<candidateLength; i++){
            stringBuilder.append(candidate[i]);
        }
        return stringBuilder.toString();
	}

    
    /**
    * Update IMatch and IIMatch values.
    * 
    * @param exitem extension item
    * @param IMatch current IMatch value
    * @param IIMatch current IIMatch value
    * @param T target sequence
    * @param kind 0: i-Concatenation, 1: s-Concatenation
    * @return new int[] {new IMatch value, new IIMatch value}
    */
    public int[] updateMatch(int exitem, int IIMatch, int IMatch, ArrayList<ArrayList<Integer>> TargetNested, int kind) {
        if (IMatch >= TargetNested.size()) return new int[]{0, IMatch};

        List<Integer> currentItemset = TargetNested.get(IMatch);

        // Handling i-extension and s-extension cases
        if (kind == 0) {
            // i-extension case
            if (IIMatch >= currentItemset.size()) {
                return new int[]{IIMatch, IMatch};
            } else {
                if (currentItemset.get(IIMatch) < exitem) {
                    IIMatch = 0;
                    return new int[]{IIMatch, IMatch};
                } else if (currentItemset.get(IIMatch) > exitem) {
                    return new int[]{IIMatch, IMatch};
                } else {
                    IIMatch++;
                    if (IIMatch >= currentItemset.size()) {
                        IMatch++;
                        IIMatch = 0;
                    }
                    return new int[]{IIMatch, IMatch};
                }
            }
        } else {
            // s-extension case
            if (IIMatch >= currentItemset.size()) {
                IMatch++;
                IIMatch = 0;
                return updateMatch(exitem, IIMatch, IMatch, TargetNested, 0);
            } else {
                IIMatch = 0;
                return updateMatch(exitem, IIMatch, IMatch, TargetNested, 0);
            }
        }
    }

    
    /**
     * judge if sequence A contains sequence B
     * @param seqA sequence A
     * @param lenofA length of A
     * @param seqB sequence B
     * @return ture: A contains B; false: A does't contain B.
     */
    public boolean seqContain(int[] seqA, int lenofA, int[] seqB) {
        //将seqA和seqB转化为二维list
        List<List> A = new ArrayList<List>();
        List<List> B = new ArrayList<List>();
        List templist = new ArrayList();
        //将seqA放到A
        for (int i = 0; i < lenofA; i++) {
            if (seqA[i] == -1) {
                A.add(templist);
                templist = new ArrayList();
            } else {
                templist.add(seqA[i]);
            }
        }
        A.add(templist);
        templist = new ArrayList();
        //将seqB放到B
        int i = 0;
        while (seqB[i] != -2) {
            if (seqB[i] == -1) {
                B.add(templist);
                templist = new ArrayList();
                i++;
            } else {
                templist.add(seqB[i]);
                i++;
            }
        }
        //判断A是否包含B
        int j = 0, k = 0;
        while (j < B.size() && k < A.size()) {
            //System.out.println("A["+k+"]="+A.get(k).toString());
            //System.out.println("B["+j+"]="+B.get(j).toString());
            if (A.get(k).containsAll(B.get(j))) {
                j++;
                k++;
            } else {
                k++;
            }
        }
        if (j >= B.size()) {
            return true;
        } else return false;
    }

    
    /**
     * transfer array A to a list
     * @param T target sequence
     * @return list T.
     */
    public ArrayList<ArrayList<Integer>> convertT(int[] T){
        ArrayList<ArrayList<Integer>> B = new ArrayList<ArrayList<Integer>>();
        int i = 0;
        ArrayList<Integer> templist = new ArrayList<>();
        while (T[i] != -2) {
            if (T[i] == -1) {
                B.add(templist);
                templist = new ArrayList<>();
                i++;
            } else {
                templist.add(T[i]);
                i++;
            }
        }
        return B;
    }


    /**
     * fill the LOT
     * @param lot an empty table
     * @param T target sequence
     * @param itembuffer items in a sequence
     * @param bufferlength length of itembuffer
     */
    public void fillLOT(List<ArrayList<Integer>> lot, List<ArrayList<Integer>>T,  int[]itembuffer, int bufferlength){
        //记录T各项集当前最后出现位置
        int[] lastpos = new int[T.size()];
        //初始化为-1
        for(int i=0;i<lastpos.length;i++){
            lastpos[i]=-1;
        }

        //把itembuffer转为list形式，方便操作
        ArrayList<ArrayList<Integer>> qseq = new ArrayList<ArrayList<Integer>>();
        ArrayList<Integer> templist = new ArrayList<>();
        //将seqA放到A
        for (int i = 0; i < bufferlength; i++) {
            if (itembuffer[i] == -1) {
                qseq.add(templist);
                templist = new ArrayList<>();
            } else {
                templist.add(itembuffer[i]);
            }
        }
        qseq.add(templist);

        int j = T.size()-1; //从T最后一个项集开始
        //从qseq最后一个项集开始
        for(int i=qseq.size()-1; i>=0; i--){
            if(j<0) break;
            else {
                //如果qseq[i]包含T[j]，则记录位置
                if(qseq.get(i).containsAll(T.get(j))){
                    lastpos[j]=i;
                    j--;
                }
            }
        }

        templist = new ArrayList<>();
        //填LOT
        for(int i=0;i<lastpos.length;i++) {
            templist.add(lastpos[i]);
        }
        lot.add(templist);
    }


    /**
     * Set the maximum pattern length
     * @param maxPatternLength the maximum pattern length
     */
    public void setMaxPatternLength(int maxPatternLength) {
        this.maxPatternLength = maxPatternLength;
    }

    
    /**
     * Set the target sequence
     * @param targetSequence target sequence
     */
    public void setTargetsequence(int []targetSequence){
        this.targetSequence = targetSequence;}

    
    /**
     * Method to write a high utility itemset to the output file.
     * @param prefix prefix to be written o the output file
     * @param utility the utility of the prefix concatenated with the item
     * @param prefixLength the prefix length
     */
    private void writeOut(int[] prefix, int prefixLength, int utility) throws IOException {
        // increase the number of high utility itemsets found
        //patternCount++;

        StringBuilder buffer = new StringBuilder();

        // If the user wants to save in SPMF format
        if(SAVE_RESULT_EASIER_TO_READ_FORMAT == false) {
            // append each item of the pattern
            for (int i = 0; i < prefixLength; i++) {
                buffer.append(prefix[i]);
                buffer.append(' ');
            }

            // append the end of itemset symbol (-1) and end of sequence symbol (-2)
            buffer.append("-1 #UTIL: ");
            // append the utility of the pattern
            buffer.append(utility);
        }
        else {
            // Otherwise, if the user wants to save in a format that is easier to read for debugging.
            // Append each item of the pattern
            buffer.append('<');
            buffer.append('(');
            for (int i = 0; i < prefixLength; i++) {
                if(prefix[i] == -1) {
                    buffer.append(")(");
                }else {
                    buffer.append(prefix[i]);
                }
            }
            buffer.append(")>:");
            buffer.append(utility);
        }

        // write the pattern to the output file
        writer.write(buffer.toString());
        writer.newLine();

        // if in debugging mode, then also print the pattern to the console
        if(DEBUG==6) {
            System.out.println(" SAVING : " + buffer.toString());
            System.out.println();

            // check if the calculated utility is correct by reading the file
            // for debugging purpose
            checkIfUtilityOfPatternIsCorrect(prefix, prefixLength, utility);
        }
    }

    
    /**
     * This method check if the utility of a pattern has been correctly calculated for
     * debugging purposes. It is not designed to be efficient since it is just used for
     * debugging.
     * @param prefix a pattern stored in a buffer
     * @param prefixLength the pattern length
     * @param utility the utility of the pattern
     * @throws IOException if error while writting to file
     */
    private void checkIfUtilityOfPatternIsCorrect(int[] prefix, int prefixLength, int utility) throws IOException {
        int calculatedUtility = 0;

        BufferedReader myInput = new BufferedReader(new InputStreamReader( new FileInputStream(new File(input))));
        // we will read the database
        try {
            // prepare the object for reading the file

            String thisLine;
            // for each line (transaction) until the end of file
            while ((thisLine = myInput.readLine()) != null) {
                // if the line is  a comment, is  empty or is a kind of metadata
                if (thisLine.isEmpty() == true || thisLine.charAt(0) == '#' || thisLine.charAt(0) == '%' || thisLine.charAt(0) == '@') {
                    continue;
                }

                // split the sequence according to the " " separator
                String tokens[] = thisLine.split(" ");

                int tokensLength = tokens.length -3;

                int[] sequence = new int[tokensLength];
                int[] sequenceUtility = new int[tokensLength];

                // Copy the current sequence in the sequence buffer.
                // For each token on the line except the last three tokens
                // (the -1 -2 and sequence utility).
                for(int i=0; i< tokensLength; i++) {
                    String currentToken = tokens[i];

                    // if empty, continue to next token
                    if(currentToken.length() == 0) {
                        continue;
                    }

                    // read the current item
                    int item;
                    int itemUtility;

                    // if the current token is -1
                    if(currentToken.equals("-1")) {
                        item = -1;
                        itemUtility = 0;
                    }else {
                        // if  the current token is an item
                        //  We will extract the item from the string:
                        int positionLeftBracketString = currentToken.indexOf('[');
                        int positionRightBracketString = currentToken.indexOf(']');
                        String itemString = currentToken.substring(0, positionLeftBracketString);
                        item = Integer.parseInt(itemString);

                        // We also extract the utility from the string:
                        String utilityString = currentToken.substring(positionLeftBracketString+1, positionRightBracketString);
                        itemUtility = Integer.parseInt(utilityString);
                    }
                    sequence[i] = item;
                    sequenceUtility[i] = itemUtility;
                }

                // For each position of the sequence
                int util = tryToMatch(sequence,sequenceUtility, prefix, prefixLength, 0, 0, 0);
                calculatedUtility += util;
            }
        } catch (Exception e) {
            // catches exception if error while reading the input file
            e.printStackTrace();
        }finally {
            if(myInput != null){
                // close the input file
                myInput.close();
            }
        }

        if(calculatedUtility != utility) {
            System.out.print(" ERROR, WRONG UTILITY FOR PATTERN : ");
            for(int i=0; i<prefixLength; i++) {
                System.out.print(prefix[i]);
            }
            System.out.println(" utility is: " + utility + " but should be: " + calculatedUtility);
            System.in.read();
        }
    }

    static String arrTostr(int[] seq){
        StringBuilder stringBuilder = new StringBuilder();
        for(int i=0;i<seq.length; i++){
            stringBuilder.append(seq[i]+" ");
        }
        return stringBuilder.toString();
    }


    /**
     * This is some code for verifying that the utility of a pattern is correctly calculated
     * for debugging only. It is not efficient. But it is a mean to verify that
     * the result is correct.
     * @param sequence a sequence (the items and -1)
     * @param sequenceUtility a sequence (the utility values and -1)
     * @param prefix the current pattern stored in a buffer
     * @param prefixLength the current pattern length
     * @param prefixPos the position in the current pattern that we will try to match with the sequence
     * @param seqPos the position in the sequence that we will try to match with the pattenr
     * @param utility the calculated utility until now
     * @return the utility of the pattern
     */
    private int tryToMatch(int[] sequence, int[] sequenceUtility, int[] prefix,	int prefixLength,
                           int prefixPos, int seqPos, int utility) {

        // Note: I do not put much comment in this method because it is just
        // used for debugging.

        List<Integer> otherUtilityValues = new ArrayList<Integer>();

        // try to match the current itemset of prefix
        int posP = prefixPos;
        int posS = seqPos;

        int previousPrefixPos = prefixPos;
        int itemsetUtility = 0;
        while(posP < prefixLength & posS < sequence.length) {
            if(prefix[posP] == -1 && sequence[posS] == -1) {
                posS++;

                // try to skip the itemset in prefix
                int otherUtility = tryToMatch(sequence, sequenceUtility, prefix, prefixLength, previousPrefixPos, posS, utility);
                otherUtilityValues.add(otherUtility);

                posP++;
                utility += itemsetUtility;
                itemsetUtility = 0;
                previousPrefixPos = posP;
            }else if(prefix[posP] == -1) {
                // move to next itemset of sequence
                while(posS < sequence.length && sequence[posS] != -1){
                    posS++;
                }

                // try to skip the itemset in prefix
                int otherUtility = tryToMatch(sequence, sequenceUtility, prefix, prefixLength, previousPrefixPos, posS, utility);
                otherUtilityValues.add(otherUtility);

                utility += itemsetUtility;
                itemsetUtility = 0;
                previousPrefixPos = posP;

            }else if(sequence[posS] == -1) {
                posP = previousPrefixPos;
                itemsetUtility = 0;
                posS++;
            }else if(prefix[posP] == sequence[posS]) {
                posP++;
                itemsetUtility += sequenceUtility[posS];
                posS++;
                if(posP == prefixLength) {

                    // try to skip the itemset in prefix
                    // move to next itemset of sequence
                    while(posS < sequence.length && sequence[posS] != -1){
                        posS++;
                    }
                    int otherUtility = tryToMatch(sequence, sequenceUtility, prefix, prefixLength, previousPrefixPos, posS, utility);
                    otherUtilityValues.add(otherUtility);


                    utility += itemsetUtility;
                }
            }else if(prefix[posP] != sequence[posS]) {
                posS++;
            }
        }

        int max = 0;
        if(posP == prefixLength) {
            max = utility;
        }
        for(int utilValue : otherUtilityValues) {
            if(utilValue > utility) {
                max = utilValue;
            }
        }
        return max;
    }


    /**
     * Print statistics about the latest execution to System.out.
     */
    public void printStatistics() {
        System.out.println("============= ALGOTUSQ v1.0 - STATS =============");
        System.out.println(" Target sequence: " + arrTostr(targetSequence));
        System.out.println(" Threshold:" + this.minAU);
        System.out.println(" Total time ~ " + (endTimestamp - startTimestamp)/1000 + " s");
        System.out.println(" Max Memory ~ " + MemoryLogger.getInstance().getMaxMemory() + " MB");
        System.out.println(" High-utility sequential pattern count : " + patternCount);
        System.out.println(" Number Of Candidate : " + NumOfCandidate);
        System.out.println("========================================================"+" \n");
    }
}

