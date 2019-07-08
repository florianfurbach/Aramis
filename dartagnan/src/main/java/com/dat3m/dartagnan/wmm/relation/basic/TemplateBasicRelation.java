/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm.relation.basic;

import com.dat3m.dartagnan.wmm.relation.binary.TemplateRelation;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.utils.Utils;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.utils.Mode;
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
public class TemplateBasicRelation extends Relation {
    private static final List<Relation> Baserels=new ArrayList<>();
    private static List<String> Baserelnames=new ArrayList<String>();
    protected static Map<Program, TupleSet> ActiveSets=new HashMap<Program, TupleSet>();
    protected static Map<Program, TupleSet> MaySets=new HashMap<Program, TupleSet>(); 

    public static Map<Program, TupleSet> getMaySets() {
        return MaySets;
    }

    public static List<Relation> getBaserels() {
        return Baserels;
    }

    public static void setBaserelnames(List<String> Baserelnames) {
        TemplateBasicRelation.Baserelnames = Baserelnames;
    }
    
    /**
     *
     * @param s
     * @param ctx
     * @return
     */
    public BasicRelation getSolution(Solver s,Context ctx){
            for (String baserel : Baserelnames) {
                BoolExpr baserelid = ctx.mkBoolConst(baserel + name);
                if(s.getModel().eval(baserelid, true).isTrue()) return (BasicRelation) new RelationRepository().getRelation(baserel);
            }
            System.err.println("could not find solution for basic relation template "+getName());
            return null;
        }

    
    public TemplateBasicRelation() {
        super("TBR"+String.valueOf(TemplateRelation.ID));
        TemplateRelation.ID++;
    }

    @Override
    public TupleSet getMaxTupleSet() {
        if(MaySets.get(program)==null){
            maxTupleSet = new TupleSet();
            for (Relation baserel : Baserels) {
                maxTupleSet.addAll(baserel.getMaxTupleSet());
            }
            MaySets.put(program, maxTupleSet);
        }
        return MaySets.get(program);    
    }

    @Override
    public void initialise(Program program, Context ctx, Mode mode) {
        super.initialise(program, ctx, mode);
        for (Relation Baserel : Baserels) {
            Baserel.initialise(program, ctx, mode);
        }
    }

    
    
    @Override
    protected BoolExpr encodeApprox() {
        BoolExpr enc = ctx.mkFalse();
        for (Relation baserel : getrels()) {    
            baserel.encode();
            BoolExpr enc2 = ctx.mkTrue();
            BoolExpr baserelid = ctx.mkBoolConst(getbaserelid(baserel));
            for(Tuple tuple : baserel.getEncodeTupleSet()) {
                    enc2 = ctx.mkAnd(enc2, ctx.mkEq(Utils.edge(getName(), tuple.getFirst(), tuple.getSecond(), ctx), Utils.edge(baserel.getName(), tuple.getFirst(), tuple.getSecond(), ctx)));
                }
            
            enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(baserelid), enc), ctx.mkAnd(baserelid, enc2));

        }
        return enc;
    }
    protected String getbaserelid(Relation r){
        return r.getName()+name;
    }
    
    protected List<Relation> getrels() {
        return TemplateBasicRelation.Baserels;
    }

    @Override
    public void addEncodeTupleSet(TupleSet tuples) {
        encodeTupleSet=getMaxTupleSet();
    }
    
    

}
