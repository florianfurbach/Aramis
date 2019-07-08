/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.aramis;

import static com.dat3m.aramis.Aramis.alias;
import static com.dat3m.aramis.Aramis.ctx;
import static com.dat3m.aramis.Aramis.mode;
import com.dat3m.dartagnan.wmm.axiom.CandidateAxiom;
import com.dat3m.dartagnan.wmm.relation.binary.TemplateRelation;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.wmm.CandidateModel;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.axiom.Acyclic;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.binary.RelIntersection;
import com.dat3m.dartagnan.wmm.relation.binary.RelMinus;
import com.dat3m.dartagnan.wmm.relation.binary.RelUnion;
import com.dat3m.dartagnan.wmm.relation.binary.TemplateExecRelation;
import com.dat3m.dartagnan.wmm.relation.unary.RelInverse;
import com.dat3m.dartagnan.wmm.relation.unary.RelTrans;
import com.dat3m.dartagnan.wmm.relation.unary.RelTransRef;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author Florian Furbach
 */
public class RelationCandidates {
    
    private static RelationRepository rep=new RelationRepository();
    private static Map<Relation, Map<Program, TupleSet>> maxpairs=new HashMap<>();
    private final ArrayList<CandidateAxiom> candidates = new ArrayList<>();
    private final Logger log = Logger.getLogger(RelationCandidates.class.getName());
    public int unchecked = 0;
    private int unCombined = 0;
    private static String minusrels[] = {"(R*W)"};
    //public static String baserels[] = {"po", "co", "fr", "rf", "mfence", "rfe", "po-loc"};
    public static String baserels[] = {"po", "co", "fr", "rf", "rfe", "po-loc","coe","rmw"};

    //cegis:
    private CandidateAxiom templateAx;
    private int templateLevel = 2;
    private TemplateRelation template;
    private int exID = 0;
    private String oldexec = "";
    private Execution exec;


       
    public RelationCandidates() {
        log.setLevel(Level.FINEST);
        //java.util.logging.ConsoleHandler.level=Level.ALL;
        //log.getHandlers()[0].setLevel( Level.FINEST );
        for (Handler h : Logger.getLogger("").getHandlers()) {
            h.setLevel(Level.FINEST);
            log.info("handler: " + h.toString());
        }

        //ConsoleHandler handler = new ConsoleHandler();
        // Publish this level
        //handler.setLevel(Level.FINEST);
        //log.addHandler(handler);
    }

    /**
     * Adds a new set of candidate relations to the list.
     *
     * @param isCEGIS is true if we use the CEGIS templates, false if we simply
     * enumerate all relations.
     */
    protected void addCandidates(boolean isCEGIS) {
        if (isCEGIS) {
            log.log(Level.WARNING, "Adding CEGIS relations of syntax tree depth " + templateLevel + ". Current size: " + candidates.size());
            unchecked = candidates.size();
            //Encode new templaterelation:
            template = TemplateRelation.getTemplateRelation(templateLevel);
            templateAx = new CandidateAxiom(template, Aramis.posPrograms.size(), Aramis.negPrograms.size());
            Solver s = Aramis.solCEGIS;
            s.push();
            CandidateModel model = new CandidateModel(rep, Aramis.negPrograms.size());
            model.addAxiom(templateAx);
            for (Program posProgram : Aramis.posPrograms) {
                s.add(model.encode(posProgram, RelationCandidates.getMaxpairs(), ctx, mode, alias));
                s.add(model.consistent(posProgram, ctx));
            }
            //call CEGIS loop:
            addCandidatesCEGIS(0);
            s.pop();
            templateLevel++;
        } else {
            addCandidatesSimple();
        }
    }

    /**
     * The CEGIS loop.
     *
     * @param currentProgs the set of negative programs that we have already
     * ensured to fail with the current encoding.
     */
    private void addCandidatesCEGIS(int currentProg) {
        //choose a program in NEG that we want to fail.
        for (int i = currentProg + 1; i < Aramis.negPrograms.size(); i++) {
            Aramis.solCEGIS.push();;
            log.fine("Processing NEG program " + Aramis.negPrograms.get(i).getName());
            //TODO: Tryout: Do we want to add that there is one inconsistent execution of P-?
            //Aramis.solCEGIS.add(Aramis.negExprs.get(i));
            //Aramis.solCEGIS.add(templateAx.Inconsistent(events, Aramis.ctx));
            while (Aramis.solCEGIS.check() == Status.SATISFIABLE) {
                //Get the generated relation from the solution
                Relation generatedRel = template.getSolution(Aramis.solCEGIS, rep, Aramis.ctx);
                log.info("generated relation " + generatedRel.toString());
                //TODO: Try adding all of the generated relations.
                //Try whether P- succeeds with the generated relation.
                CandidateModel generatedModel = new CandidateModel(rep, Aramis.negPrograms.size());
                generatedModel.addAxiom(new CandidateAxiom(true, generatedRel, Aramis.posPrograms.size(), Aramis.negPrograms.size()));
                Program p = Aramis.negPrograms.get(i);
                Solver s = Aramis.solvers.get(p);
                s.push();
                s.add(generatedModel.encode(p, maxpairs, ctx, mode, alias));
                s.add(generatedModel.consistent(p, Aramis.ctx));
                Status sat = s.check();
                if (sat == Status.SATISFIABLE) {
                    //encode execution to be avoided:
                    //log.info("Adding new execution " + prefix);
                    exec = new Execution(s.getModel(), ctx);
                    log.info(exec.toString());
                    if (exec.toString().contentEquals(oldexec)) {
                        System.err.println("Execution didnt change!");
                    }
                    oldexec = exec.toString();

                    TemplateExecRelation execrel = new TemplateExecRelation(template, exec);
                    CandidateModel execmodel = new CandidateModel(rep, Aramis.negPrograms.size());
                    execmodel.addAxiom(new Acyclic(execrel, true));
                    Aramis.solCEGIS.add(execmodel.encode(p, maxpairs, ctx, mode, alias));
                    Aramis.solCEGIS.add(execmodel.consistent(p, ctx));
                    //make sure execution is inconsistent:
                    //BoolExpr temp=template.Inconsistent(prefix, p, Aramis.ctx);
                    //log.info(temp.toString());
                    exID++;
                    s.pop();

                } else {
                    log.info("No consistent executions found, adding " + generatedRel.toString());
                    s.pop();

                    add(generatedRel);
                    addCandidatesCEGIS(i);
                    //TODO: try with adding and without

                }

            }
            Aramis.solCEGIS.pop();
            log.fine("Backtracking...");
        }

    }

    /**
     * Adds a relation
     *
     * @param rel
     * @return the added axiom.
     */
    public CandidateAxiom add(Relation r) {
        log.log(Level.FINE, "Adding {0}", r.getName());
        Relation reltemp=rep.getRelation(r.getName());
        Relation rel=r;
        if(reltemp!=null){
            rel=reltemp;
            log.warning("Relation add to list is already in Repository: "+r.getName());
        }
        else rep.updateRelation(rel);
        if(maxpairs.put(rel, new HashMap<>())!=null) log.warning("May Pairs for added relation "+rel.getName()+" already exist ");
        CandidateAxiom ax = new CandidateAxiom(rel, Aramis.posPrograms.size(), Aramis.negPrograms.size());
        //Aramis.checkCandidate(ax);
        ax.position = candidates.size();
        candidates.add(ax);
        return ax;

    }

    /**
     * Adds the basic relations add the beginning.
     */
    public void addBasicrels() {
        log.fine("Adding basic relations...");
        RelationRepository reptemp=new RelationRepository();
        for (String baserel : baserels) {
            Aramis.checkCandidate(add(reptemp.getRelation(baserel)));
        }
        for (String baserel : baserels) {
            if(!(baserel.equals("fr")| baserel.equals("rf")))
            Aramis.checkCandidate(add(new RelInverse(reptemp.getRelation(baserel))));
        }
    }

    /**
     * Combines all old relations the first unchecked relation, adds the results
     * to the list and computes their information.
     */
    public void addCandidatesSimple() {
        log.log(Level.WARNING, "Adding relations. Current size: {0}", candidates.size());
        int oldsize = candidates.size();
        candidates.ensureCapacity(3 * oldsize);
        CandidateAxiom c1 = candidates.get(unCombined);
        Relation r1 = c1.getRel();

        //Applying unary operations:
        if (!(r1 instanceof RelTransRef) && !(r1 instanceof RelTrans)) {
            CandidateAxiom ax = add(new RelTransRef(r1));
            ax.largerthan(c1);
            Aramis.checkCandidate(ax);
        }
//            if (!(r1 instanceof RelTransRef) && !(r1 instanceof RelTrans)) {
//                CandidateAxiom ax=add(new RelTrans(r1));
//                ax.largerthan(c1);
//                Aramis.checkCandidate(ax);
//            }

        if (!(r1 instanceof RelMinus)) {
            Relation rminus;
            RelationRepository rep = new RelationRepository();
            for (String minusrel : minusrels) {
                rminus = rep.getRelation(minusrel);
                CandidateAxiom ax = add(new RelMinus(r1, rminus));
                ax.smallerthan(c1);
                Aramis.checkCandidate(ax);
            }

        }
        //Applying binary operators:
        for (int i = 0; i < unCombined; i++) {
            CandidateAxiom c2 = candidates.get(i);
            Relation r2 = c2.getRel();
            //unions are always added from the left 
            CandidateAxiom union = null;
            if (!(r2 instanceof RelUnion)) {
                union = add(new RelUnion(r1, r2));
                union.largerthan(c1);
                union.largerthan(c2);
                Aramis.checkCandidate(union);
            }

            //intersections are always added from the left and have no unions nested inside.
            if (!(r2 instanceof RelIntersection) && !(r2 instanceof RelUnion) && !(r1 instanceof RelUnion)) {
                CandidateAxiom inter = add(new RelIntersection(r1, r2));
                inter.smallerthan(c1);
                inter.smallerthan(c2);
                Aramis.checkCandidate(inter);
            }

            //Relcompositions are nested from the left and contain no unions or intersections.
//                if (!(r2 instanceof RelComposition) && !(r1 instanceof RelInterSect)
//                        && !(r2 instanceof RelInterSect)
//                        && !(r1 instanceof RelUnion)
//                        && !(r2 instanceof RelUnion)) {
//                    
//                    CandidateAxiom ax = add(new RelComposition(r1, r2));
//                    if (union != null) {
//                        ax.smallerthan(union);
//                    }
//                    if (inter != null) {
//                        ax.largerthan(inter);
//                    }
//                    Aramis.checkCandidate(ax);
//                    if (!(r1 instanceof RelComposition)) {
//                        CandidateAxiom ax2 = add(new RelComposition(r2, r1));
//                        ax2.largerthan(ax);
//                        ax2.smallerthan(ax);
//                        Aramis.checkCandidate(ax2);
//                    }
//                }
        }

        unCombined++;
    }

    protected CandidateAxiom get(int i) {
        return candidates.get(i);
    }

    protected int size() {
        return candidates.size();
    }

    public static RelationRepository getRepository() {
        return rep;
    }

    public static Map<Relation, Map<Program, TupleSet>> getMaxpairs() {
        return maxpairs;
    }
    
    

}
