/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm.relation.basic;

import static com.dat3m.dartagnan.utils.Utils.edge;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.utils.Tuple;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.BoolExpr;

/**
 *
 * @author Florian Furbach
 */
public class BasisExecRelation extends BasicRelation{
    String originalName;
    private final TupleSet myEdges;
    Execution exec;
    
    public BasisExecRelation(Relation r, Execution exec, TupleSet edges) {
        super(exec.getId()+":"+r.getName());
        this.myEdges=edges;
        this.originalName = r.getName();
        this.exec=exec;
        
    }
    
//    @Override
//    protected BoolExpr encodeApprox() {
//        BoolExpr enc = ctx.mkTrue();
//        for(Tuple tuple : exec.gettemplateTupleSet()) {
//            BoolExpr rel = edge(this.getName(), tuple.getFirst(), tuple.getSecond(), ctx);
//            if(myEdges.contains(tuple))enc = ctx.mkAnd(enc, rel);
//            else enc = ctx.mkAnd(enc, ctx.mkNot(rel));
//        }
//        return enc;
//    }
//    
    @Override
    public TupleSet getMaxTupleSet() {
        maxTupleSet=myEdges;
        return maxTupleSet;
    }

    public String getOriginalName() {
        return originalName;
    }
//
//    @Override
//    public void initialise(Program program, Context ctx, Mode mode){
//        TupleSet temp = maxTupleSet;
//        super.initialise(program, ctx, mode);
//        this.maxTupleSet = temp;
//    }    
//
//    @Override
//    public void addEncodeTupleSet(TupleSet tuples) {
//         encodeTupleSet=maxTupleSet;
//    }
}
