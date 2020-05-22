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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author Florian Furbach
 */
public class TemplateBasicRelation extends Relation {

    private static String minrelnames[] = {"(R*W)"};
    //private static String minrelnames[] = {};

    //public static String brelnames[] = {"po", "co", "fr", "rf", "mfence", "rfe", "po-loc"};
    private static String brelnames[] = {"po", "co", "fr", "rf", "rfe", "po-loc", "coe", "rmw"};
    //private static String brelnames[] = {"po", "co", "fr", "rf"};
    //private static String brelnames[] = {"po", "co", "fr", "rf", "rfe","po-loc",};

    static List<Relation> Baserels = new ArrayList<>();
    private static List<Relation> Minusrels = new ArrayList<>();
    private static List<String> Baserelnames = new ArrayList<String>(Arrays.asList(brelnames));
    private static List<String> Minusrelnames = new ArrayList<String>(Arrays.asList(minrelnames));

    protected static Map<Program, TupleSet> ActiveSets = new HashMap<Program, TupleSet>();
    protected static Map<Program, TupleSet> MaySets = new HashMap<Program, TupleSet>();

    public static List<Relation> getMinusrels() {
        return Minusrels;
    }

    public static List<Relation> getBaserels() {
        return Baserels;
    }

    protected List<Relation> getrels() {
        return Baserels;
    }
    
    public static void setBaserelnames(List<String> Baserelnames) {
        TemplateBasicRelation.Baserelnames = Baserelnames;
    }

    public static void setMinusrelnames(List<String> Minusrelnames) {
        TemplateBasicRelation.Minusrelnames = Minusrelnames;
    }

    public static void initiateBaseAndMinusrels(RelationRepository rep) {
        for (String baserel : Baserelnames) {
            Relation temp = rep.getRelation(baserel);
            if (temp == null) {
                System.err.println("Relation " + baserel + " cannot be infered");
                System.exit(1);
                return;
            }
            Baserels.add(temp);
        }
        for (String minusrel : Minusrelnames) {
            Relation temp = rep.getRelation(minusrel);
            if (temp == null) {
                System.err.println("Relation " + minusrel + " cannot be infered");
                System.exit(1);
                return;
            }
            Minusrels.add(temp);
        }
    }

    public static Map<Program, TupleSet> getMaySets() {
        return MaySets;
    }

    /**
     *
     * @param s
     * @param ctx
     * @return
     */
    public Relation getSolution(Solver s, Context ctx) {
        for (Relation Baserel : Baserels) {
            BoolExpr baserelid = ctx.mkBoolConst(Baserel.getName() + name);
            if (s.getModel().eval(baserelid, true).isTrue()) {
                return Baserel;
            }
        }
        System.err.println("could not find solution for basic relation template " + getName());
        return null;
    }
    
    public Relation getoldSolution(Solver s, Context ctx) {
        for (String baserel : Baserelnames) {
            BoolExpr baserelid = ctx.mkBoolConst(baserel + name);
            if (s.getModel().eval(baserelid, true).isTrue()) {
                return new RelationRepository().getRelation(baserel);
            }
        }
        System.err.println("could not find solution for basic relation template " + getName());
        return null;
    }
    
    public TemplateBasicRelation() {
        super("TBR" + String.valueOf(TemplateRelation.ID));
        TemplateRelation.ID++;
    }

    @Override
    public TupleSet getMaxTupleSet() {
        if (MaySets.get(program) == null) {
            maxTupleSet = new TupleSet();
            for (Relation baserel : Baserels) {
                maxTupleSet.addAll(baserel.getMaxTupleSet());
            }
            MaySets.put(program, maxTupleSet);
        }
        return MaySets.get(program);
    }

//    @Override
//    public void initialise(Program program, Context ctx, Mode mode) {
//        super.initialise(program, ctx, mode);
//        for (Relation Baserel : Baserels) {
//            Baserel.initialise(program, ctx, mode);
//        }
//    }

    @Override
    public void initialise(Program program, Map<Relation, Map<Program, TupleSet>> maxpairs, Context ctx, Mode mode) {
        for (Relation Baserel : Baserels) {
            Baserel.initialise(program, maxpairs, ctx, mode);
        }
        for (Relation Minusrel : Minusrels) {
            Minusrel.initialise(program, maxpairs, ctx, mode);
        }
        super.initialise(program, maxpairs, ctx, mode); //To change body of generated methods, choose Tools | Templates.
    }
    
    

    @Override
    protected BoolExpr encodeApprox() {
        BoolExpr enc = ctx.mkTrue();
        BoolExpr encbaserels=ctx.mkTrue();
        BoolExpr atleastone=ctx.mkFalse();
        BoolExpr atmostone=ctx.mkTrue();
        Set<BoolExpr> brelids=new HashSet<>(); 
        for (Relation baserel : getrels()) {
            encbaserels=ctx.mkAnd(encbaserels,baserel.encode());
            BoolExpr enc2 = ctx.mkTrue();
            BoolExpr baserelid = ctx.mkBoolConst(getbaserelid(baserel));
            atleastone=ctx.mkOr(atleastone, baserelid);
            for (BoolExpr brelid : brelids) {
                atmostone=ctx.mkAnd(atmostone, ctx.mkNot(ctx.mkAnd(brelid,baserelid)));
            }
            brelids.add(baserelid);
            for (Tuple tuple : baserel.getEncodeTupleSet()) {
                enc2 = ctx.mkAnd(enc2, ctx.mkEq(Utils.edge(getName(), tuple.getFirst(), tuple.getSecond(), ctx), Utils.edge(baserel.getName(), tuple.getFirst(), tuple.getSecond(), ctx)));
            }
            enc=ctx.mkAnd(enc, ctx.mkImplies(baserelid, enc2));
        }
        enc=ctx.mkAnd(enc,atleastone,atmostone,encbaserels);
        return enc;
    }

    protected String getbaserelid(Relation r) {
        return r.getName() + name;
    }


//    @Override
//    public void addEncodeTupleSet(TupleSet tuples) {
//        encodeTupleSet=getMaxTupleSet();
//    }
    @Override
    public void addEncodeTupleSet(TupleSet tuples) {
        TupleSet activeSet = new TupleSet();
        activeSet.addAll(tuples);
        activeSet.removeAll(encodeTupleSet);
        encodeTupleSet.addAll(activeSet);
        activeSet.retainAll(maxTupleSet);
        if (!activeSet.isEmpty()) {
            for (Relation baserel : getrels()) {
                baserel.addEncodeTupleSet(activeSet);                
            }
        }
    }

}
