/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.aramis.wmm;

import com.dat3m.aramis.ListOfRels;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.program.event.Event;
import com.dat3m.dartagnan.utils.Utils;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.basic.BasicRelation;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Z3Exception;
import java.util.Set;

/**
 *
 * @author Florian Furbach
 */
public class TemplateBasicRelation extends Relation {

    /**
     *
     * @param s
     * @param ctx
     * @return
     */
    public BasicRelation getSolution(Solver s,Context ctx){
            for (String baserel : ListOfRels.baserels) {
                BoolExpr baserelid = ctx.mkBoolConst(baserel + name);
                if(s.getModel().eval(baserelid, true).isTrue()) return new BasicRelation(baserel);
            }
            System.err.println("could not find solution for basic relation template "+getName());
            return null;
        }

    
    public TemplateBasicRelation() {
        super("TBR"+String.valueOf(TemplateRelation.ID));
        TemplateRelation.ID++;
    }

    @Override
    public BoolExpr encode(Program program, Context ctx, Set<String> encodedRels) throws Z3Exception {
        return encodeBasic(program, ctx);
    }

    @Override
    protected BoolExpr encodeBasic(Program program, Context ctx) throws Z3Exception {
        BoolExpr enc = ctx.mkFalse();
        Set<Event> events = program.getMemEvents();
        for (String baserel : ListOfRels.baserels) {
            BoolExpr enc2 = ctx.mkTrue();
            BoolExpr baserelid = ctx.mkBoolConst(baserel + name);
            for (Event e1 : events) {
                for (Event e2 : events) {
                    enc2 = ctx.mkAnd(enc2, ctx.mkEq(Utils.edge(getName(), e1, e2, ctx), Utils.edge(TemplateRelation.PREFIX+baserel, e1, e2, ctx)));
                }
            }
            enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(baserelid), enc), ctx.mkAnd(baserelid, enc2));

        }
        return enc;
    }
//TODO: encode approx
    @Override
    protected BoolExpr encodePredicateBasic(Program program, Context ctx) throws Z3Exception {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    protected BoolExpr encodePredicateApprox(Program program, Context ctx) throws Z3Exception {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

}
