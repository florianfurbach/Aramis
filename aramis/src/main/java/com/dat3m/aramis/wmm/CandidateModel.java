/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.aramis.wmm;

import com.dat3m.aramis.Aramis;
import com.dat3m.dartagnan.wmm.Wmm;
import com.dat3m.dartagnan.wmm.axiom.Axiom;

/**
 *
 * @author Florian Furbach
 */
public class CandidateModel extends Wmm{
    
    public int size(){
        return getAxioms().size();
    }
    
    public void push(CandidateAxiom ax){
        getAxioms().add(ax);        
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
            if(negProgIndex>=Aramis.negPrograms.size()) return negProgIndex;
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
