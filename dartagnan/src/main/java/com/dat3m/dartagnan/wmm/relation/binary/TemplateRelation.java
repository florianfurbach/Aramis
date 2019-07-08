/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm.relation.binary;

import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.program.event.Event;
import com.dat3m.dartagnan.program.utils.EType;
import com.dat3m.dartagnan.utils.Utils;
import com.dat3m.dartagnan.wmm.filter.FilterBasic;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.basic.TemplateBasicRelation;
import com.dat3m.dartagnan.wmm.relation.unary.RelTransRef;
import com.dat3m.dartagnan.wmm.utils.Mode;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.Tuple;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Z3Exception;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author Florian Furbach
 */
public class TemplateRelation extends BinaryRelation{

public static int ID;
private BoolExpr unionexp;
private BoolExpr interexp;
private BoolExpr compexp;
private BoolExpr transrefexp;
private BoolExpr idexp;
public static String PREFIX="";
private static Map<Program, TupleSet> ActiveSets=new HashMap<Program, TupleSet>();
private static Map<Program, TupleSet> MaySets=new HashMap<Program, TupleSet>(); 

    public TemplateRelation(Relation r1, Relation r2) {
        super(r1,r2, "TR"+String.valueOf(ID));
        ID++;

    }
    
    public static TemplateRelation getTemplateRelation(int level) {
        if(level>1) return new TemplateRelation(getTemplateRelation(level-1),getTemplateRelation(level-1));
        else return new TemplateRelation(new TemplateBasicRelation(),new TemplateBasicRelation());
    }    
    
    public Relation getSolution(Solver s, RelationRepository rep, Context ctx){
        Model m=s.getModel();
        Relation rel1,rel2;
        if(r1 instanceof TemplateRelation)rel1=((TemplateRelation) r1).getSolution(s,rep,ctx);
        else rel1=((TemplateBasicRelation)r1).getSolution(s, ctx);
        if(r2 instanceof TemplateRelation)rel2=((TemplateRelation) r2).getSolution(s,rep,ctx);
        else rel2=((TemplateBasicRelation)r2).getSolution(s, ctx);  
        Relation temp = null;
        if(m.eval(unionexp, true).isTrue()) temp=new RelUnion(rel1, rel2);
        if(m.eval(interexp, true).isTrue()) temp=new RelIntersection(rel1, rel2);
        if(m.eval(compexp, true).isTrue()) temp=new RelComposition(rel1, rel2);
        if(m.eval(transrefexp, true).isTrue()) temp=new RelTransRef(rel1);
        if(m.eval(idexp, true).isTrue()) temp= rel1;
        if(temp==null) System.err.println("could not find Solution for TemplateRelation "+name);
        else {
            if(rep.getRelation(temp.getName())==null)
                rep.updateRelation(temp);
        }
        return temp;
    }
    
    protected String getID(){
        return name;
    }
    
    @Override
    protected BoolExpr encodeApprox() throws Z3Exception {        
        //TODO: relminus
        
        //union:
        RelUnion union=new RelUnion(r1, r2, name);
        BoolExpr enc;
        unionexp=ctx.mkBoolConst("union"+getID());
        enc = ctx.mkAnd(unionexp, union.encode(program, maxTupleSet, ctx, Mode.KNASTER));
        //inter:
        RelIntersection inter=new RelIntersection(r1, r2, name);
        interexp= ctx.mkBoolConst("inter"+getID());
        enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(interexp),enc), ctx.mkAnd(interexp, inter.encode(program, maxTupleSet, ctx, Mode.KNASTER)));
       
        //comp:
        RelComposition comp=new RelComposition(r1, r2, name);
        compexp= ctx.mkBoolConst("comp"+getID());
        enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(compexp),enc), ctx.mkAnd(compexp, comp.encode(program, maxTupleSet, ctx, Mode.KNASTER)));
        
        //RelTransRef:
        RelTransRef transref=new RelTransRef(r1, name);
        transrefexp= ctx.mkBoolConst("transref"+getID());
        transref.initialise(program, ctx, Mode.IDL);
        enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(transrefexp),enc), ctx.mkAnd(transrefexp, transref.encode(program, maxTupleSet, ctx, Mode.KNASTER)));
        
        //id:
        idexp= ctx.mkBoolConst("id"+getID());
        
            BoolExpr enc2=ctx.mkTrue();
        for(Tuple tuple : getMaxTupleSet()) {
            enc2 = ctx.mkAnd(enc2, ctx.mkEq(Utils.edge(getName(), tuple.getFirst(), tuple.getSecond(), ctx), 
                    Utils.edge(r1.getName(), tuple.getFirst(), tuple.getSecond(), ctx)));                                
        }        
        enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(idexp),enc), ctx.mkAnd(idexp, enc2));
                        
        return enc;
    }

    protected Map<Event, Set<Event>> getBasictransmaysets(){
        return TemplateBasicRelation.getMaySets().get(program).transMap();
    }
    
    
    
    @Override
    public TupleSet getMaxTupleSet() {
        if(MaySets.get(program)==null){
            Map<Event, Set<Event>> transitiveReachabilityMap = getBasictransmaysets();
            maxTupleSet = new TupleSet();
            for(Event e1 : transitiveReachabilityMap.keySet()){
                for(Event e2 : transitiveReachabilityMap.get(e1)){
                    maxTupleSet.add(new Tuple(e1, e2));
                }
            }
                     
            for(Event e : program.getCache().getEvents(FilterBasic.get(EType.ANY))){
                if(!transitiveReachabilityMap.get(e).contains(e))
                    maxTupleSet.add(new Tuple(e, e));
            }
            MaySets.put(program, maxTupleSet);
        }
        return MaySets.get(program);    
    }

    @Override
    public void addEncodeTupleSet(TupleSet tuples) {
        encodeTupleSet=maxTupleSet;
        r1.addEncodeTupleSet(maxTupleSet);
        r2.addEncodeTupleSet(maxTupleSet);
    }
    
    

}
