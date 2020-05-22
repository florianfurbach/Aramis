/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm;

import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.program.event.Event;
import com.dat3m.dartagnan.utils.Utils;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.basic.BasisExecRelation;
import com.dat3m.dartagnan.wmm.relation.basic.TemplateBasicRelation;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.Tuple;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author Florian Furbach
 */
public class Execution {
    static private List<Execution> Executions=new ArrayList<>();
    private RelationRepository rep=new RelationRepository();
    String exec;
    private Program p;
    private String id;
    private static int idnr=0;
    private TupleSet maxTupleSet=new TupleSet();
    private Context ctx;
    public static List<Execution> getExecutions() {
        return Executions;
    }
    private TupleSet templateTupleSet;
    
    //TODO: support minusrels correctly!
    
    public Execution(Program p, Model m, Context ctx) {
        this.p=p;
        this.ctx=ctx;
        id="E"+idnr;
        exec=id+":"; 
        idnr++;
        //        for (Relation baserel : TemplateBasicRelation.getBaserels()) {
        for (Relation baserel : TemplateBasicRelation.getBaserels()) {
            TupleSet pairs=new TupleSet();
            for (Tuple tuple : baserel.getMaxTupleSet()) {
                BoolExpr relPair = Utils.edge(baserel.getName(), tuple.getFirst(), tuple.getSecond(), ctx);
                    if (m.eval(relPair, true).isTrue()) {
                        exec = exec + " " + String.format("%s(%s,%s)", baserel.getName(), tuple.getFirst().repr(), tuple.getSecond().repr());
                        pairs.add(tuple);
                    }
            }
            add(new BasisExecRelation(baserel, this, pairs));
        }
    }
    
    /**
     * Encodes relations co,po,rf with their original names.
     * @return
     */
    public BoolExpr encodeExecOriginal(){
        BoolExpr enc=ctx.mkTrue();
        for (Relation baserel : getRelations()) {
            BasisExecRelation brel = (BasisExecRelation) baserel;
            if(brel.getOriginalName().contentEquals("co")||brel.getOriginalName().contentEquals("po")||brel.getOriginalName().contentEquals("rf"))
            for (Tuple tuple : brel.getMaxTupleSet()) {
                BoolExpr relPair = Utils.edge(brel.getOriginalName(), tuple.getFirst(), tuple.getSecond(), ctx);
                enc=ctx.mkAnd(enc,relPair);
            }
 
        }
        return enc;
    }    
    
    private Set<Event> getEvents(){
        Set<Event> temp=new HashSet<>(maxTupleSet.size());
        for (Tuple tuple : maxTupleSet) {
            temp.add(tuple.getFirst());
            temp.add(tuple.getSecond());
        }
        return temp;
    }

    public TupleSet gettemplateTupleSet(){
       if(templateTupleSet!=null) return templateTupleSet;
        templateTupleSet=new TupleSet();
        Map<Event, Set<Event>> transitiveReachabilityMap = maxTupleSet.transMap();
            for(Event e1 : transitiveReachabilityMap.keySet()){
                for(Event e2 : transitiveReachabilityMap.get(e1)){
                    templateTupleSet.add(new Tuple(e1, e2));
                }
            }
            for (Event event : getEvents()) {
            templateTupleSet.add(new Tuple(event, event));
        }
            return templateTupleSet;
    }
    
    public String getId() {
        return id;
    }

    @Override
    public String toString() {
        return exec;
    }

    
    
    public TupleSet getMaxTupleSet() {
        return maxTupleSet;
    }

    
    public Execution() {
        this.id="E"+Integer.toString(idnr);
        idnr++;
    }
    
    private void add(BasisExecRelation r){
        rep.updateRelation(r);
        maxTupleSet.addAll(r.getMaxTupleSet());
    }
    public Relation getRelation(String name){
        return rep.getRelation(name);
    }

    public List<Relation> getRelations() {
        return new ArrayList<Relation>(rep.getRelations());
    }

    public Program getProgram() {
        return p;
    }
    
   
    
}
