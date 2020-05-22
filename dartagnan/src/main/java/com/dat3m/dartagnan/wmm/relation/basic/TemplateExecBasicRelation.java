/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm.relation.basic;

import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.utils.Utils;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.utils.Mode;
import com.dat3m.dartagnan.wmm.utils.Tuple;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
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
    public void initialise(Program program, Context ctx, Mode mode) {
        super.initialise(program, ctx, mode);
        for (Relation rel : getrels()) {
            rel.initialise(program, ctx, mode);
        }
    }

    @Override
    protected BoolExpr encodeApprox() {
    BoolExpr enc = ctx.mkFalse();
        for (Relation baserel : exec.getRelations()) {
            BoolExpr enc2 = ctx.mkTrue();
            for (Tuple tuple : exec.getMaxTupleSet()) {
                if(baserel.getMaxTupleSet().contains(tuple))
                    enc2 = ctx.mkAnd(enc2, Utils.edge(getName(), tuple.getFirst(), tuple.getSecond(), ctx));
                else
                    enc2 = ctx.mkAnd(enc2, ctx.mkNot(Utils.edge(getName(), tuple.getFirst(), tuple.getSecond(), ctx)));
            }

            BoolExpr baserelid = ctx.mkBoolConst(getbaserelid(baserel));
            enc = ctx.mkAnd(enc, ctx.mkImplies(baserelid, enc2));
            //enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(baserelid), enc), ctx.mkAnd(baserelid, enc2));
        }
        for (Tuple tuple : exec.gettemplateTupleSet()) {
            if(!exec.getMaxTupleSet().contains(tuple)) enc=ctx.mkAnd(enc,ctx.mkNot(Utils.edge(getName(), tuple.getFirst(), tuple.getSecond(), ctx)));
        }
        return enc;
    }
    
    

    @Override
    public TupleSet getMaxTupleSet() {
        maxTupleSet=exec.getMaxTupleSet();
        return maxTupleSet;
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

    @Override
    public void addEncodeTupleSet(TupleSet tuples) {
        encodeTupleSet=exec.getMaxTupleSet();
    }
    
    

}