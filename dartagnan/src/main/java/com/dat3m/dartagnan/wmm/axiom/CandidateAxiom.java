/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm.axiom;

import com.dat3m.dartagnan.wmm.Consistent;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author Florian Furbach
 */
public class CandidateAxiom extends Acyclic {
    private static boolean enCodingExecMode=false;
    public Consistent[] pos;
    //public HashMap<Program, Boolean> consProg = new HashMap<>();
    //Denotes whether the axiom passes all POS tests.
    private boolean consistent = false;
    public int position;
    private Map<Execution, CandidateAxiom> next = new HashMap<>();
    //denotes whether the axiom fails a Neg test.
    private Map<Execution, Consistent> neg;

    public boolean relevant = false;
    //when encoding a relation generated from a templaterelation to find an exec, 
    //we need to encode the whole relation for not just what we need this time.
    private boolean generatedRel = false;
    private int nrOfNEGs;

    private Set<Execution> negCons = new HashSet<Execution>();
    private Set<Execution> negIncons = new HashSet<Execution>();

    public static boolean isEnCodingExecMode() {
        return enCodingExecMode;
    }

    public static void setEnCodingExecMode(boolean enCodingExecMode) {
        CandidateAxiom.enCodingExecMode = enCodingExecMode;
    }

    
    
    public boolean isConsistent() {
        return consistent;
    }

    public void setConsistent(boolean consistent) {
        this.consistent = consistent;
    }

    public Set<Execution> getNegCons() {
        return negCons;
    }

    public Set<Execution> getNegIncons() {
        return negIncons;
    }

    public CandidateAxiom getNext(Execution exec) {
        return next.get(exec);
    }

    public void setNext(Execution exec, CandidateAxiom next) {
        this.next.put(exec, next);
    }

    public void largerthan(CandidateAxiom ax) {
        for (int i = 0; i < pos.length; i++) {
            if (ax.pos[i] == Consistent.INCONSISTENT) {
                consistent = false;
                pos[i] = ax.pos[i];
            }
        }
        negCons.removeAll(ax.negIncons);
        negIncons.addAll(ax.negIncons);

    }

    /**
     * Creates an acyclic Axiom that has additional information regarding its
     * behaviour towards the reachability
     *
     * @param rel
     */
    public CandidateAxiom(Relation rel, int nrOfPOSs) {
        super(rel);
        this.nrOfNEGs = nrOfNEGs;
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
    public CandidateAxiom(boolean generated, Relation rel, int nrOfPOSs) {
        super(rel);
        this.generatedRel = generated;
        this.nrOfNEGs = nrOfNEGs;
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
        negCons.addAll(ax.negCons);
        negIncons.removeAll(ax.negCons);
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
        for (int nrOfNegExec = firstUncovered; nrOfNegExec < Execution.getExecutions().size(); nrOfNegExec++) {
            if (!negCons.contains(nrOfNegExec)) {
                return nrOfNegExec;
            }
        }

        return Execution.getExecutions().size();
    }

}
