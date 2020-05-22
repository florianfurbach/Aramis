/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm;

import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.wmm.axiom.Axiom;
import com.dat3m.dartagnan.wmm.axiom.CandidateAxiom;
import com.dat3m.dartagnan.wmm.filter.FilterAbstract;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.utils.Mode;
import com.dat3m.dartagnan.wmm.utils.RecursiveGroup;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.dat3m.dartagnan.wmm.utils.alias.Alias;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author Florian Furbach
 */
public class CandidateModel extends Wmm{

    private Map<Execution, CandidateAxiom> usedRelsforExecs=new HashMap<Execution, CandidateAxiom>(Execution.getExecutions().size());
    public CandidateModel(RelationRepository rep) {
        super();
        this.relationRepository=rep;
    }    
        
    public int size(){
        return getAxioms().size();
    }
    
    public void push(CandidateAxiom ax, Execution exec){
        if(!ax.getNegIncons().contains(exec)) {
            System.out.println(exec.getId()+" not forbidden by ax "+ax.toString()+" at push()");
            System.exit(1);
        }
        getAxioms().add(ax);        
        //usedRelsforExecs.put(exec, ax);
        //for (Execution execution : ax.getNegIncons()) {
            if(!usedRelsforExecs.containsKey(exec)) usedRelsforExecs.put(exec, ax);
        //}
    }
    
    
    
    public BoolExpr encode(Program program, Map<Relation, Map<Program, TupleSet>> maxpairs, Context ctx, Mode mode, Alias alias) {
        this.program = program;

        for (Axiom ax : axioms) {
            ax.getRel().updateRecursiveGroupId(ax.getRel().getRecursiveGroupId());
        }

        if(mode == Mode.KNASTER && drawExecutionGraph){
            mode = Mode.IDL;
        }

        for(RecursiveGroup recursiveGroup : recursiveGroups){
            recursiveGroup.setDoRecurse();
        }

        for(FilterAbstract filter : filters.values()){
            filter.initialise();
        }

        for (Axiom ax : axioms) {
            ax.getRel().initialise(program, maxpairs, ctx, mode);
        }
        for(RecursiveGroup recursiveGroup : recursiveGroups){
            recursiveGroup.initMaxTupleSets();
        }

        if(drawExecutionGraph){
            for(String relName : drawRelations){
                Relation relation = relationRepository.getRelation(relName);
                if(relation != null){
                    relation.addEncodeTupleSet(relation.getMaxTupleSet());
                }
            }
        }

        for (Axiom ax : axioms) {
            ax.getRel().addEncodeTupleSet(ax.getEncodeTupleSet());
        }

        Collections.reverse(recursiveGroups);
        for(RecursiveGroup recursiveGroup : recursiveGroups){
            recursiveGroup.updateEncodeTupleSets();
        }

        BoolExpr enc = ctx.mkTrue();
        for (Axiom ax : axioms) {
            enc = ctx.mkAnd(enc, ax.getRel().encode());
        }

        if(mode == Mode.KLEENE){
            for(RecursiveGroup group : recursiveGroups){
                enc = ctx.mkAnd(enc, group.encode(ctx));
            }
        }

        return enc;
    }
    
    public boolean pop(){
        if(getAxioms().size()<=1)return false;
        else{
            CandidateAxiom ax=(CandidateAxiom) getAxioms().get(getAxioms().size()-1);
            boolean works=false;
            for (Execution negIncon : ax.getNegIncons()) {
                if(usedRelsforExecs.remove(negIncon, ax)) works=true;                
            }
            if(!works) {
                System.err.println("Popping didnt remove a redundancy entry for "+ax.toString());
                System.exit(1);
            }
            getAxioms().remove(ax);
            return true;
        }
    }

    /**
     * 
     * @return the index of the next program in NEG that is still reachable according to the ax.neg info
     */
    public Execution getNextPassingNeg(){
        int negProgIndex;
        for (Execution execution : Execution.getExecutions()) {
            boolean passing=true;
            for (Axiom axiom : getAxioms()) {
                CandidateAxiom ax=(CandidateAxiom) axiom;
                Set<Execution> negAxiomBehavior=ax.getNegIncons();
                if(negAxiomBehavior.contains(execution)) passing=false;
            }
            if(passing) return execution;
        }
        return null;
    }

    /**
     * Checks if addingax covers an earlier neg that is already covered by an axiom with a smaller number.
     * This way we only add getAxioms() in decending order if we have the choice and we don't check models twice.
     * @param addingax the axiom that we consider adding.
     * @return whether the axiom has to be added.
     */
    public boolean oldredundand(CandidateAxiom addingax) {
        Execution temp=getNextPassingNeg();
        for (Iterator<Execution> iterator = Execution.getExecutions().iterator(); iterator.hasNext();) {
            Execution execution = iterator.next();
            if(execution==temp) return false;
            if(addingax.getNegIncons().contains(execution)){
                for (Axiom axiom : getAxioms()) {
                    CandidateAxiom ax=(CandidateAxiom) axiom;
                    if(ax.getNegIncons().contains(execution) && ax.position<=addingax.position) return true;
                }
            }
        }
        return false;
    }
    
        /**
     * Checks if addingax covers an earlier neg that is already covered by an axiom with a smaller number.
     * This way we only add getAxioms() in decending order if we have the choice and we don't check models twice.
     * @param addingax the axiom that we consider adding.
     * @return whether the axiom has to be added.
     */
    public boolean redundand(CandidateAxiom addingax) {
        Execution temp=getNextPassingNeg();
        for (Execution negIncon : addingax.getNegIncons()) {
            if (usedRelsforExecs.containsKey(negIncon)) {
                CandidateAxiom oldaxiom=usedRelsforExecs.get(negIncon);
                if(oldaxiom.position<=addingax.position) return true;
            }
        }
        return false;
    }
    
}
