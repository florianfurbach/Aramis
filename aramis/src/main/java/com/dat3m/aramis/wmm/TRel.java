/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.aramis.wmm;

import com.dat3m.dartagnan.wmm.relation.basic.TemplateBasicRelation;
import com.dat3m.dartagnan.wmm.relation.binary.TemplateRelation;
import com.dat3m.dartagnan.program.event.Event;
import com.dat3m.dartagnan.utils.Utils;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.binary.BinaryRelation;
import com.dat3m.dartagnan.wmm.relation.binary.RelComposition;
import com.dat3m.dartagnan.wmm.relation.binary.RelIntersection;
import com.dat3m.dartagnan.wmm.relation.binary.RelUnion;
import com.dat3m.dartagnan.wmm.relation.unary.RelTransRef;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import java.util.Set;

/**
 *
 * @author Florian Furbach
 */
public class TRel extends BinaryRelation{
protected static int ID;
private BoolExpr unionexp;
private BoolExpr interexp;
private BoolExpr compexp;
private BoolExpr transrefexp;
private BoolExpr idexp;
public static String PREFIX="";

    public TRel(Relation r1, Relation r2, String name) {
        super(r1,r2, "TR"+String.valueOf(ID));
        ID++;
        }



    public TRel(Relation r1, Relation r2) {
        super(r1,r2, "TR"+String.valueOf(ID));
        ID++;

    }
 
    public static TRel getTemplateRelation(int level) {
        if(level>1) return new TRel(getTemplateRelation(level-1),getTemplateRelation(level-1));
        else return new TRel(new TemplateBasicRelation(),new TemplateBasicRelation());
    }    
    
    
    public Relation getSolution(Solver s,Context ctx){
        Model m=s.getModel();
        Relation rel1,rel2;
        if(r1 instanceof TemplateRelation)rel1=((TemplateRelation) r1).getSolution(s,ctx);
        else rel1=((TemplateBasicRelation)r1).getSolution(s, ctx);
        if(r2 instanceof TemplateRelation)rel2=((TemplateRelation) r2).getSolution(s,ctx);
        else rel2=((TemplateBasicRelation)r2).getSolution(s, ctx);        
        if(m.eval(unionexp, true).isTrue()) return new RelUnion(rel1, rel2);
        if(m.eval(interexp, true).isTrue()) return new RelIntersection(rel1, rel2);
        if(m.eval(compexp, true).isTrue()) return new RelComposition(rel1, rel2);
        if(m.eval(transrefexp, true).isTrue()) return new RelTransRef(rel1);
        if(m.eval(idexp, true).isTrue()) return rel1;
        System.err.println("could not find Solution for TemplateRelation "+name);
        return null;
    }
        
    @Override
    public TupleSet getMaxTupleSet() {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    protected BoolExpr encodeApprox() {
        //TODO: relminus
        
        //union:
        RelUnion union=new RelUnion(r1, r2, name);
        BoolExpr enc;
        unionexp=ctx.mkBoolConst("union"+name);
        enc = ctx.mkAnd(unionexp, union.encodeApprox(program, ctx));
        
        //inter:
        RelIntersection inter=new RelIntersection(r1, r2, name);
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
    
}
