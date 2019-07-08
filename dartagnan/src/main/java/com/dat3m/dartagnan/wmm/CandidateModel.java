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
import java.util.Map;

/**
 *
 * @author Florian Furbach
 */
public class CandidateModel extends Wmm{

    private final int nrOfNEGs;

    public CandidateModel(RelationRepository rep, int nrOfNEGs) {
        super();
        this.relationRepository=rep;
        this.nrOfNEGs=nrOfNEGs;
    }    
        
    public int size(){
        return getAxioms().size();
    }
    
    public void push(CandidateAxiom ax){
        getAxioms().add(ax);        
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
        if(getAxioms().size()<=0)return false;
        else{
            getAxioms().remove(getAxioms().size()-1);
            return true;
        }
    }
    
    /**
     * 
     * @return the index of the next program in NEG that is still reachable according to the ax.neg info
     */
    public int getNextPassingNeg(){
        int negProgIndex=0;
        while (true) {            
            boolean temp=true;
            if(negProgIndex>=nrOfNEGs) return negProgIndex;
            for (Axiom axiom : getAxioms()) {
                CandidateAxiom ax=(CandidateAxiom) axiom;
                Consistent[] negProgAxiomBehavior=ax.neg;
                if(negProgAxiomBehavior[negProgIndex]==Consistent.INCONSISTENT) temp=false;
            }
            if(temp)return negProgIndex;
            negProgIndex++;
        }
    }

    /**
     * Checks if addingax covers an earlier neg that is already covered by an axiom with a smaller number.
     * This way we only add getAxioms() in decending order if we have the choice and we don't check models twice.
     * @param addingax the axiom that we consider adding.
     * @return whether the axiom has to be added.
     */
    public boolean redundand(CandidateAxiom addingax) {
        for (int i = 0; i < getNextPassingNeg(); i++) {
            Consistent[] addingaxneg=addingax.neg;
            if(addingaxneg[i]==Consistent.INCONSISTENT){
                for (Axiom axiom : getAxioms()) {
                    CandidateAxiom ax=(CandidateAxiom) axiom;
                    Consistent[] axneg=ax.neg;                   
                    if(axneg[i]==Consistent.INCONSISTENT && ax.position<=addingax.position) return true;
                }
            }
        }
        return false;
    }
    
}
