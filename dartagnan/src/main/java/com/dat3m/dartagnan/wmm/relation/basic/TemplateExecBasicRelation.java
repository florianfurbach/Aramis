/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm.relation.basic;

import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.relation.Relation;
import java.util.List;

/**
 *
 * @author Florian Furbach
 */
public class TemplateExecBasicRelation extends TemplateBasicRelation{
    private final String templateId;
    private Execution exec;

    public TemplateExecBasicRelation(TemplateBasicRelation r, Execution exec) {
        super();
        this.exec=exec;
        this.templateId=r.getName();
    }

    @Override
    protected String getbaserelid(Relation r) {
        String temp=((BasisExecRelation) r).getOriginalName();
        return temp+templateId;
    }

    
    @Override
    protected List<Relation> getrels() {
        return exec.getRelations();
    }


    
}
