/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.aramis.wmm;

import com.dat3m.aramis.RelationCandidates;
import static com.dat3m.aramis.wmm.TRel.ID;
import com.dat3m.dartagnan.wmm.relation.binary.TemplateRelation;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.utils.Utils;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.basic.BasicRelation;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.Tuple;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 *
 * @author Florian Furbach
 */
public class TBasicRel extends Relation {
    private List<Relation> baserels=new ArrayList<Relation>(RelationCandidates.baserels.length);
    private static Map<Program, TupleSet> ActiveSets=new HashMap<Program, TupleSet>();
    private static Map<Program, TupleSet> MaySets=new HashMap<Program, TupleSet>();    
    
    /**
     *
     * @param s
     * @param ctx
     * @return
     */
    public BasicRelation getSolution(Solver s,Context ctx){
            for (String baserel : RelationCandidates.baserels) {
                BoolExpr baserelid = ctx.mkBoolConst(baserel + name);
                if(s.getModel().eval(baserelid, true).isTrue()) return (BasicRelation) new RelationRepository().getRelation(baserel);
            }
            System.err.println("could not find solution for basic relation template "+getName());
            return null;
        }

    
    public TBasicRel() {
        super("TBR"+String.valueOf(ID));
        ID++;
    }

    
    @Override
    public TupleSet getMaxTupleSet() {
        if(MaySets.get(program)==null){
            maxTupleSet = new TupleSet();
            for (Relation baserel : baserels) {
                maxTupleSet.addAll(baserel.getMaxTupleSet());
            }
            MaySets.put(program, maxTupleSet);
        }
        return MaySets.get(program);    
    }

    @Override
    protected BoolExpr encodeApprox() {
        BoolExpr enc = ctx.mkFalse();
        for (String baserel : RelationCandidates.baserels) {            
            BoolExpr enc2 = ctx.mkTrue();
            BoolExpr baserelid = ctx.mkBoolConst(baserel + name);
            for(Tuple tuple : getEncodeTupleSet()) {
                    enc2 = ctx.mkAnd(enc2, ctx.mkEq(Utils.edge(getName(), tuple.getFirst(), tuple.getSecond(), ctx), Utils.edge(TemplateRelation.PREFIX+baserel, tuple.getFirst(), tuple.getSecond(), ctx)));
                }
            
            enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(baserelid), enc), ctx.mkAnd(baserelid, enc2));

        }
        return enc;
    }
    
    
}
