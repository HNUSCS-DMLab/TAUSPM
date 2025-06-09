/**
 * Copyright (C), 2015-2025, HNU
 * FileName: UtilityList_New
 * Author:   K. Cao
 * Date:     2025/6/1 08:00
 * Description: Add the new domains "IMatch", "IIMatch", "rru", "rrl" into UtilityList.
 */
package TAUSQ;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class TargetedList {
    public class UtilityElement {

        /** itemset  **/
        public int tid;

        /** prefix utility **/
        public int acu;

        /** rrs utility **/
        public int rru;
        
        public UtilityElement(int tid, int acu, int rru) {
            this.tid=tid;
            this.acu=acu;
            this.rru=rru;
        }
    }

    //sid
    public int sid;

    //IIMatch：Item flag for current match
    public int IIMatch;
    //IMatch：Itemset flag for current match
    public int IMatch;

    //UtilityList: for per instance
    List<UtilityElement> List = new ArrayList<UtilityElement>();

    //length: number of instances
    public int LengthOfUtilityList;

    //SRAU：Suffix Remain Average Utility
    public int SRAU;

    public TargetedList() {
        this.LengthOfUtilityList=0;
        this.SRAU = 0;
    }

    public void add(int tid, int acu, int rru) {
        this.List.add(new UtilityElement(tid, acu, rru));
        this.LengthOfUtilityList++;
    }

    public void set_SRAU(int srau) {
      this.SRAU = srau;
    }

    public void set_sid(int sid) {
        this.sid = sid;
    }

    public int get_sid() {
        return this.sid;
    }

    public void set_IIMatch(int IIMatch) {
        this.IIMatch = IIMatch;
    }
    public void set_IMatch(int IMatch) {
        this.IMatch = IMatch;
    }
    public int get_IIMatch() {
        return this.IIMatch;
    }
    public int get_IMatch() {
        return this.IMatch;
    }
}