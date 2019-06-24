/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.dartagnan.wmm;

import com.dat3m.dartagnan.utils.Utils;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.basic.BasicRelation;
import com.dat3m.dartagnan.wmm.relation.basic.BasisExecRelation;
import com.dat3m.dartagnan.wmm.relation.basic.TemplateBasicRelation;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.Tuple;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

/**
 *
 * @author Florian Furbach
 */
public class Execution {
    private RelationRepository rep=new RelationRepository();
    String exec;
    private String id;
    private static int idnr=0;
    private TupleSet maxTupleSet=new TupleSet();
    public Execution(Model m, Context ctx) {
        id="E"+idnr;
        exec=id+":"; 
        idnr++;
        for (Relation baserel : TemplateBasicRelation.getBaserels()) {
            TupleSet pairs=new TupleSet();
            for (Tuple tuple : baserel.getMaxTupleSet()) {
                BoolExpr relPair = Utils.edge(baserel.getName(), tuple.getFirst(), tuple.getSecond(), ctx);
                    if (m.eval(relPair, true).isTrue()) {
                        exec = exec + " " + String.format("%s(%s,%s)", baserel.getName(), tuple.getFirst().repr(), tuple.getSecond().repr());
                        pairs.add(tuple);
                    }
            }
            add(new BasisExecRelation((BasicRelation) baserel, this, pairs));
        }
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
    
   
    
}
