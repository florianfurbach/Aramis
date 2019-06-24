/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm.relation.basic;

import static com.dat3m.dartagnan.utils.Utils.edge;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.relation.basic.BasicRelation;
import com.dat3m.dartagnan.wmm.utils.Tuple;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.BoolExpr;

/**
 *
 * @author Florian Furbach
 */
public class BasisExecRelation extends BasicRelation{

    public BasisExecRelation(BasicRelation r, Execution exec, TupleSet edges) {
        super(exec.getId()+":"+r.getName());
        this.orignialName = r.getName();
        this.maxTupleSet=edges;
    }
    
    String orignialName;
    @Override
    protected BoolExpr encodeApprox() {
        BoolExpr enc = ctx.mkTrue();
        for(Tuple tuple : encodeTupleSet) {
            BoolExpr rel = edge(this.getName(), tuple.getFirst(), tuple.getSecond(), ctx);
            enc = ctx.mkAnd(enc, rel);
        }
        return enc;
    }
    
    @Override
    public TupleSet getMaxTupleSet() {
        return maxTupleSet;
    }

    String getOriginalName() {
        return orignialName;
    }
    
}
