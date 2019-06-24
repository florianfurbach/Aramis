/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.aramis.wmm;

import com.dat3m.aramis.Aramis;
import com.dat3m.dartagnan.wmm.axiom.Acyclic;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.utils.TupleSet;

/**
 *
 * @author Florian Furbach
 */
public class CandidateAxiom extends Acyclic {

    public Consistent[] pos=new Consistent[Aramis.posPrograms.size()];
    public Consistent[] neg=new Consistent[Aramis.negPrograms.size()];
    //public HashMap<Program, Boolean> consProg = new HashMap<>();
    //Denotes whether the axiom passes all POS tests.
    public boolean consistent=false;
    public int position;
    public CandidateAxiom[] next=new CandidateAxiom[Aramis.negPrograms.size()];
        //denotes whether the axiom fails a Neg test.

    public boolean relevant=false;
    //when encoding a relation generated from a templaterelation to find an exec, 
    //we need to encode the whole relation for not just what we need this time.
    private boolean generatedRel=false;
    
    public void largerthan(CandidateAxiom ax){
        for (int i = 0; i < pos.length; i++) {
            if(ax.pos[i]==Consistent.INCONSISTENT){
                consistent=false;
                pos[i]=ax.pos[i];
            }
        }
        for (int i = 0; i < neg.length; i++) {
            if(ax.neg[i]==Consistent.INCONSISTENT) neg[i]=ax.neg[i];
        }        
    }
    
    /**
     * Creates an acyclic Axiom that has additional information regarding its behaviour towards the reachability
     * @param rel
     */
    public CandidateAxiom(Relation rel) {
                super(rel);
    }
    
    /**
     * Creates an acyclic Axiom that has additional information regarding its behaviour towards the reachability
     * @param rel
     * @param generated denotes whether the relation is generated and needs to be encoded for all may pairs in order to get all necessary tuples for creating the execution.
     * 
     */
    public CandidateAxiom(Relation rel, boolean generated) {
                super(rel);
                this.generatedRel=generated;
    }

    @Override
    public TupleSet getEncodeTupleSet() {
        if(generatedRel) return rel.getMaxTupleSet();
        else return super.getEncodeTupleSet(); 
    }
    
    
    public void smallerthan(CandidateAxiom ax){
        consistent=(consistent || ax.consistent);
        for (int i = 0; i < pos.length; i++) {
            if(ax.pos[i]==Consistent.CONSISTENT) pos[i]=ax.pos[i];
        }
        for (int i = 0; i < neg.length; i++) {
            if(ax.neg[i]==Consistent.CONSISTENT) neg[i]=ax.neg[i];
        }
    }

    /**
     * This provides the next NEG test we have to cover in the dynamic synthesis.
     * @param firstUncovered
     * @return the index of the first NEG test that passes starting at firstUncovered
     */
    public int getNextpass(int firstUncovered) {
        for (int negprog = firstUncovered; negprog < Aramis.negPrograms.size(); negprog++) {
            if(neg[negprog]!=Consistent.CONSISTENT) return negprog; 
        }
        return Aramis.negPrograms.size();
    }
    
}

