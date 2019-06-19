/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.aramis.wmm;

import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.program.event.Event;
import com.dat3m.dartagnan.utils.Utils;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.binary.BinaryRelation;
import com.dat3m.dartagnan.wmm.relation.binary.RelComposition;
import com.dat3m.dartagnan.wmm.relation.binary.RelUnion;
import com.dat3m.dartagnan.wmm.relation.unary.RelTransRef;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Z3Exception;
import java.util.HashSet;
import java.util.Set;

/**
 *
 * @author Florian Furbach
 */
public class TemplateRelation extends BinaryRelation{

protected static int ID;
private BoolExpr unionexp;
private BoolExpr interexp;
private BoolExpr compexp;
private BoolExpr transrefexp;
private BoolExpr idexp;
protected static String PREFIX="";

    public TemplateRelation(Relation r1, Relation r2) {
        super(r1,r2, "TR"+String.valueOf(ID));
        ID++;

    }
 
    
    
    public BoolExpr Inconsistent(String prefix, Program p, Context ctx) throws Z3Exception {
        PREFIX=prefix;
        boolean approxtemp=Relation.Approx;
        Relation.Approx=false;
        Set<Event> events = p.getMemEvents();
        BoolExpr enc=Encodings.satCycle(prefix+name, events, ctx);
        enc=ctx.mkAnd(enc,encode(p, ctx, new HashSet<String>()));
        
        for(Event e1 : events) {
            Set<BoolExpr> source = new HashSet<BoolExpr>();
            Set<BoolExpr> target = new HashSet<BoolExpr>();
            //TODO: cycles grober definieren. 
            for(Event e2 : events) {
                    source.add(Utils.cycleEdge(prefix+name, e1, e2, ctx));
                    target.add(Utils.cycleEdge(prefix+name, e2, e1, ctx));
                    enc = ctx.mkAnd(enc, ctx.mkImplies(Utils.cycleEdge(prefix+name, e1, e2, ctx),
                            ctx.mkAnd(Utils.edge(prefix+name, e1, e2, ctx), Utils.cycleVar(prefix+name, e1, ctx), Utils.cycleVar(prefix+name, e2, ctx))));
                }
            enc = ctx.mkAnd(enc, ctx.mkImplies(Utils.cycleVar(prefix+name, e1, ctx), ctx.mkAnd(encodeEO(source, ctx), encodeEO(target, ctx))));
            }
        
        PREFIX="";
        Relation.Approx=approxtemp;
        return enc;
    }

    
    public static TemplateRelation getTemplateRelation(int level) {
        if(level>1) return new TemplateRelation(getTemplateRelation(level-1),getTemplateRelation(level-1));
        else return new TemplateRelation(new TemplateBasicRelation(),new TemplateBasicRelation());
    }    
    
    public Relation getSolution(Solver s,Context ctx){
        Model m=s.getModel();
        Relation rel1,rel2;
        if(r1 instanceof TemplateRelation)rel1=((TemplateRelation) r1).getSolution(s,ctx);
        else rel1=((TemplateBasicRelation)r1).getSolution(s, ctx);
        if(r2 instanceof TemplateRelation)rel2=((TemplateRelation) r2).getSolution(s,ctx);
        else rel2=((TemplateBasicRelation)r2).getSolution(s, ctx);        
        if(m.eval(unionexp, true).isTrue()) return new RelUnion(rel1, rel2);
        if(m.eval(interexp, true).isTrue()) return new RelInterSect(rel1, rel2);
        if(m.eval(compexp, true).isTrue()) return new RelComposition(rel1, rel2);
        if(m.eval(transrefexp, true).isTrue()) return new RelTransRef(rel1);
        if(m.eval(idexp, true).isTrue()) return rel1;
        System.err.println("could not find Solution for TemplateRelation "+name);
        return null;
    }
    
    @Override
    protected BoolExpr encodeBasic(Program program, Context ctx) throws Z3Exception {        
        //TODO: relminus
        
        //union:
        RelUnion union=new RelUnion(r1, r2, name);
        BoolExpr enc;
        unionexp=ctx.mkBoolConst("union"+name);
        enc = ctx.mkAnd(unionexp, union.encodeBasic(program, ctx));
        
        //inter:
        RelInterSect inter=new RelInterSect(r1, r2, name);
        interexp= ctx.mkBoolConst("inter"+name);
        enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(interexp),enc), ctx.mkAnd(interexp, inter.encodeBasic(program, ctx)));
       
        //comp:
        RelComposition comp=new RelComposition(r1, r2, name);
        compexp= ctx.mkBoolConst("comp"+name);
        enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(compexp),enc), ctx.mkAnd(compexp, comp.encodeBasic(program, ctx)));
        
        //RelTransRef:
        RelTransRef transref=new RelTransRef(r1, name);
        transrefexp= ctx.mkBoolConst("transref"+name);
        enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(transrefexp),enc), ctx.mkAnd(transrefexp, transref.encodeBasic(program, ctx)));
        
        //id:
        idexp= ctx.mkBoolConst("id"+name);
        
            BoolExpr enc2=ctx.mkTrue();
            Set<Event> events = program.getMemEvents();
            for(Event e1 : events) {
            for(Event e2 : events) {
                            enc2 = ctx.mkAnd(enc2, ctx.mkEq(Utils.edge(getName(), e1, e2, ctx), Utils.edge(r1.getName(), e1, e2, ctx)));                                
            }
        }        
        enc = ctx.mkOr(ctx.mkAnd(ctx.mkNot(idexp),enc), ctx.mkAnd(idexp, enc2));
                        
        return enc;
    }

    //TODO: encode Approx
    @Override
    protected BoolExpr encodePredicateBasic(Program program, Context ctx) throws Z3Exception {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    protected BoolExpr encodePredicateApprox(Program program, Context ctx) throws Z3Exception {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }


}
