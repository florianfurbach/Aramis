/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm.axiom;

import com.dat3m.dartagnan.program.event.Event;
import static com.dat3m.dartagnan.utils.Utils.edge;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.utils.Tuple;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import java.util.HashSet;
import java.util.Set;

/**
 *
 * @author Florian Furbach
 */
public class ExecAcyclic extends Acyclic{

    public ExecAcyclic(Relation rel) {
        super(rel);
    }
        
    public ExecAcyclic(Relation rel, boolean negate) {
        super(rel,negate);
    }

    @Override
    protected BoolExpr satCycleDef(Context ctx) {
        BoolExpr enc = ctx.mkTrue();
        Set<Event> encoded = new HashSet<>();
        String name = rel.getName();

        for(Tuple t : rel.getEncodeTupleSet()){
            Event e1 = t.getFirst();
            Event e2 = t.getSecond();

            enc = ctx.mkAnd(enc, ctx.mkImplies(
                    cycleEdge(name, e1, e2, ctx),
                    ctx.mkAnd(
                            edge(name, e1, e2, ctx),
                            cycleVar(name, e1, ctx),
                            cycleVar(name, e2, ctx)
            )));

            if(!encoded.contains(e1)){
                encoded.add(e1);

                BoolExpr source = ctx.mkFalse();
                for(Tuple tuple1 : rel.getEncodeTupleSet().getByFirst(e1)){
                    BoolExpr opt = cycleEdge(name, e1, tuple1.getSecond(), ctx);
                    for(Tuple tuple2 : rel.getEncodeTupleSet().getByFirst(e1)){
                        if(tuple1.getSecond().getCId() != tuple2.getSecond().getCId()){
                            opt = ctx.mkAnd(opt, ctx.mkNot(cycleEdge(name, e1, tuple2.getSecond(), ctx)));
                        }
                    }
                    source = ctx.mkOr(source, opt);
                }

                BoolExpr target = ctx.mkFalse();
                for(Tuple tuple1 : rel.getEncodeTupleSet().getBySecond(e1)){
                    BoolExpr opt = cycleEdge(name, tuple1.getFirst(), e1, ctx);
                    for(Tuple tuple2 : rel.getEncodeTupleSet().getBySecond(e1)){
                        if(tuple1.getFirst().getCId() != tuple2.getFirst().getCId()){
                            opt = ctx.mkAnd(opt, ctx.mkNot(cycleEdge(name, tuple2.getFirst(), e1, ctx)));
                        }
                    }
                    target = ctx.mkOr(target, opt);
                }

                enc = ctx.mkAnd(enc, ctx.mkImplies(cycleVar(name, e1, ctx), ctx.mkAnd(source, target)));
            }
        }

        return enc;
    }
    
    private BoolExpr cycleVar(String relName, Event e, Context ctx) {
        return ctx.mkBoolConst("Cycle(" + e.repr() + ")(" + relName + ")");
    }

    private BoolExpr cycleEdge(String relName, Event e1, Event e2, Context ctx) {
        return ctx.mkBoolConst("Cycle:" + relName + "(" + e1.repr() + "," + e2.repr() + ")");
    }    
    
    
}
