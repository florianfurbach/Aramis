/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm.relation.binary;

import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.basic.TemplateBasicRelation;
import com.dat3m.dartagnan.wmm.relation.basic.TemplateExecBasicRelation;
import com.dat3m.dartagnan.wmm.utils.TupleSet;

/**
 *
 * @author Florian Furbach
 */
public class TemplateExecRelation extends TemplateRelation{
    
    private Execution exec;
    private final String templateId;

    @Override
    protected String getID() {
        return templateId;
    }
    
    /**
     *
     * @param rel
     * @param exec
     */
    public TemplateExecRelation(TemplateRelation rel, Execution exec) {
        super(rel,rel);
        this.templateId=rel.getName();
        this.exec=exec;
        Relation r1temp;
        if(rel.r1 instanceof TemplateRelation) this.r1=new TemplateExecRelation((TemplateRelation) rel.r1, exec);
        else if(rel.r1 instanceof TemplateBasicRelation) this.r1=new TemplateExecBasicRelation((TemplateBasicRelation) rel.r1, exec);
        if(rel.r2 instanceof TemplateRelation) this.r2=new TemplateExecRelation((TemplateRelation) rel.r2, exec);
        else if(rel.r2 instanceof TemplateBasicRelation) this.r2=new TemplateExecBasicRelation((TemplateBasicRelation) rel.r2, exec);
        maxTupleSet=exec.gettemplateTupleSet();
        encodeTupleSet=maxTupleSet;        
    }

    @Override
    public TupleSet getMaxTupleSet() {
        maxTupleSet=exec.gettemplateTupleSet();
        encodeTupleSet=maxTupleSet;
        return maxTupleSet;
    }

    
    
    @Override
    public void addEncodeTupleSet(TupleSet tuples) {
        getMaxTupleSet();
        encodeTupleSet=maxTupleSet;
        r1.addEncodeTupleSet(encodeTupleSet);
        r2.addEncodeTupleSet(encodeTupleSet);
    }
    
    
}
