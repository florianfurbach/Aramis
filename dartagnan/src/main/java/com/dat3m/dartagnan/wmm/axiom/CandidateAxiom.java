/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm.axiom;

import com.dat3m.dartagnan.wmm.Consistent;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.utils.TupleSet;

/**
 *
 * @author Florian Furbach
 */
public class CandidateAxiom extends Acyclic {

    public Consistent[] pos;
    public Consistent[] neg;
    //public HashMap<Program, Boolean> consProg = new HashMap<>();
    //Denotes whether the axiom passes all POS tests.
    public boolean consistent = false;
    public int position;
    public CandidateAxiom[] next;
    //denotes whether the axiom fails a Neg test.

    public boolean relevant = false;
    //when encoding a relation generated from a templaterelation to find an exec, 
    //we need to encode the whole relation for not just what we need this time.
    private boolean generatedRel = false;
    private int nrOfNEGs;

    public void largerthan(CandidateAxiom ax) {
        for (int i = 0; i < pos.length; i++) {
            if (ax.pos[i] == Consistent.INCONSISTENT) {
                consistent = false;
                pos[i] = ax.pos[i];
            }
        }
        for (int i = 0; i < neg.length; i++) {
            if (ax.neg[i] == Consistent.INCONSISTENT) {
                neg[i] = ax.neg[i];
            }
        }
    }

    /**
     * Creates an acyclic Axiom that has additional information regarding its
     * behaviour towards the reachability
     *
     * @param rel
     */
    public CandidateAxiom(Relation rel, int nrOfPOSs, int nrOfNEGs) {
        super(rel);
        this.nrOfNEGs = nrOfNEGs;
        this.next = new CandidateAxiom[nrOfNEGs];
        neg = new Consistent[nrOfNEGs];
        pos = new Consistent[nrOfPOSs];
    }

    /**
     * Creates an acyclic Axiom that has additional information regarding its
     * behaviour towards the reachability
     *
     * @param rel
     * @param generated denotes whether the relation is generated and needs to
     * be encoded for all may pairs in order to get all necessary tuples for
     * creating the execution.
     *
     */
    public CandidateAxiom(boolean generated, Relation rel, int nrOfPOSs, int nrOfNEGs) {
        super(rel);
        this.generatedRel = generated;
        this.nrOfNEGs = nrOfNEGs;
        this.next = new CandidateAxiom[nrOfNEGs];
        neg = new Consistent[nrOfNEGs];
        pos = new Consistent[nrOfPOSs];
    }

    @Override
    public TupleSet getEncodeTupleSet() {
        if (generatedRel) {
            return rel.getMaxTupleSet();
        } else {
            return super.getEncodeTupleSet();
        }
    }

    public void smallerthan(CandidateAxiom ax) {
        consistent = (consistent || ax.consistent);
        for (int i = 0; i < pos.length; i++) {
            if (ax.pos[i] == Consistent.CONSISTENT) {
                pos[i] = ax.pos[i];
            }
        }
        for (int i = 0; i < neg.length; i++) {
            if (ax.neg[i] == Consistent.CONSISTENT) {
                neg[i] = ax.neg[i];
            }
        }
    }

    /**
     * This provides the next NEG test we have to cover in the dynamic
     * synthesis.
     *
     * @param firstUncovered
     * @return the index of the first NEG test that passes starting at
     * firstUncovered
     */
    public int getNextpass(int firstUncovered) {
        for (int negprog = firstUncovered; negprog < nrOfNEGs; negprog++) {
            if (neg[negprog] != Consistent.CONSISTENT) {
                return negprog;
            }
        }
        return nrOfNEGs;
    }

}
