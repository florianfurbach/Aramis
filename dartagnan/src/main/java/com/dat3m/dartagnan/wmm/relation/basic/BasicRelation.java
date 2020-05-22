package com.dat3m.dartagnan.wmm.relation.basic;

import com.microsoft.z3.BoolExpr;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.utils.Tuple;

import static com.dat3m.dartagnan.utils.Utils.edge;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.utils.Mode;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.Context;

public abstract class BasicRelation extends Relation {

    public BasicRelation() {
        super();
    }

    public BasicRelation(String name) {
        super(name);
    }

    @Override
    protected BoolExpr encodeApprox() {
        BoolExpr enc = ctx.mkTrue();
        for(Tuple tuple : encodeTupleSet) {
            BoolExpr rel = edge(this.getName(), tuple.getFirst(), tuple.getSecond(), ctx);
            enc = ctx.mkAnd(enc, ctx.mkEq(rel, ctx.mkAnd(tuple.getFirst().executes(ctx), tuple.getSecond().executes(ctx))));
        }
        return enc;
    }
    
    protected boolean setMaxPairs(Execution exec){
        for (Relation relation : exec.getRelations()) {
            BasisExecRelation brel= (BasisExecRelation) relation;
            if(brel.originalName.equals(this.getName())) {
                maxTupleSet=brel.getMaxTupleSet();
                return true;
            }
        }
        return false;
    }
        public void initialise(Execution execution, Context ctx, Mode mode) {
        this.initialise(execution.getProgram(), ctx, mode);
            setMaxPairs(execution);
    }
    
}
