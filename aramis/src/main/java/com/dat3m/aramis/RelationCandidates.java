/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.aramis;

import static com.dat3m.aramis.Aramis.Log;
import static com.dat3m.aramis.Aramis.alias;
import static com.dat3m.aramis.Aramis.ctx;
import static com.dat3m.aramis.Aramis.mode;
import com.dat3m.dartagnan.wmm.axiom.CandidateAxiom;
import com.dat3m.dartagnan.wmm.relation.binary.TemplateRelation;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.wmm.CandidateModel;
import com.dat3m.dartagnan.wmm.Consistent;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.axiom.ExecAcyclic;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.basic.TemplateBasicRelation;
import com.dat3m.dartagnan.wmm.relation.binary.RelComposition;
import com.dat3m.dartagnan.wmm.relation.binary.RelIntersection;
import com.dat3m.dartagnan.wmm.relation.binary.RelMinus;
import com.dat3m.dartagnan.wmm.relation.binary.RelUnion;
import com.dat3m.dartagnan.wmm.relation.binary.TemplateExecRelation;
import com.dat3m.dartagnan.wmm.relation.unary.RelTrans;
import com.dat3m.dartagnan.wmm.relation.unary.RelTransRef;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;
import java.util.logging.Level;

/**
 *
 * @author Florian Furbach
 */
public class RelationCandidates {

    private static RelationRepository rep = new RelationRepository();
    private static Map<Relation, Map<Program, TupleSet>> maxpairs = new HashMap<>();
    private final ArrayList<CandidateAxiom> candidates = new ArrayList<>();
    //private final Logger Log = Logger.getLogger(RelationCandidates.class.getName());
    public int unchecked = 0;
    private int unCombined = 0;
    //cegis:
    private CandidateAxiom templateAx;
    private int templateLevel = 2;
    private TemplateRelation template;
    private int exID = 0;
    private String oldexec = "";
    private Execution exec;

    public RelationCandidates() {
        //Log.setLevel(Level.FINEST);
//        for (Handler h : Logger.getLogger("").getHandlers()) {
//            h.setLevel(Level.FINEST);
//            Log.info("handler: " + h.toString());
//        }

        //java.util.logging.ConsoleHandler.level=Level.ALL;
        //log.getHandlers()[0].setLevel( Level.FINEST );
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
            Log.log(Level.WARNING, "Adding CEGIS relations of syntax tree depth " + templateLevel + ". Current size: " + candidates.size());
            unchecked = candidates.size();
            //Encode new templaterelation:
            template = TemplateRelation.getTemplateRelation(templateLevel);
            templateAx = new CandidateAxiom(template, Aramis.posPrograms.size());
            Solver s = Aramis.solCEGIS;
            s.push();
            CandidateModel model = new CandidateModel(rep);
            model.addAxiom(templateAx);
            for (Program posProgram : Aramis.posPrograms) {
                s.add(model.encode(posProgram, RelationCandidates.getMaxpairs(), ctx, mode, alias));
                s.add(model.consistent(posProgram, ctx));
            }
            //call CEGIS loop:
            Stack<Execution> incons = new Stack();
            addCandidatesCEGIS(0, incons);
            s.pop();
            templateLevel++;
        } else {
            addCandidatesEnumerate();
        }
    }

    /**
     * The CEGIS loop.
     *
     * @param currentProgs the set of negative programs that we have already
     * ensured to fail with the current encoding.
     */
    private void addCandidatesCEGIS(int currentExec, Stack<Execution> incons) {
        Aramis.nrOfSMTcalls++;
        if (Aramis.solCEGIS.check() == Status.SATISFIABLE) {
            Relation generatedRel = template.getSolution(Aramis.solCEGIS, rep, Aramis.ctx);
            Aramis.solCEGIS.push();
            Log.info("Generated relation " + generatedRel.toString());

            CandidateAxiom genAxiom = add(generatedRel);
            for (int i = 0; i < Aramis.posPrograms.size(); i++) {
                genAxiom.pos[i] = Consistent.CONSISTENT;
            }

            //TODO: fix error remove check
            for (Execution incon : incons) {
                if (Aramis.checkCandidate(genAxiom, incon)) {
                    System.err.println(generatedRel + " passes an exec but shouldnt" + incon.getId());
                    System.exit(1);
                }
            }

            genAxiom.getNegIncons().addAll(incons);
            Aramis.checkCandidate(genAxiom);

            //choose an exec in NEG that we want to fail.
            for (Execution execution : genAxiom.getNegCons()) {
                if (Execution.getExecutions().indexOf(execution) >= currentExec) {

                    Log.fine("Adding CounterExample NEG Execution " + execution.getId());
                    TemplateExecRelation execrel = new TemplateExecRelation(template, execution);

                    RelationRepository reptemp = new RelationRepository();
                    execrel.addRelations(reptemp);
                    for (Relation relation : reptemp.getRelations()) {
                        relation.initialise(execution.getProgram(), ctx, mode);
                    }
                    for (Relation relation : reptemp.getRelations()) {
                        relation.getMaxTupleSet();
                    }
                    ExecAcyclic acytemp = new ExecAcyclic(execrel);

                    execrel.addEncodeTupleSet(acytemp.getEncodeTupleSet());
                    Aramis.solCEGIS.add(acytemp.inconsistent(ctx));
                    BoolExpr temp = execrel.encode();
                    //Log.finest(temp.toString());
                    Aramis.solCEGIS.add(temp);

//                    CandidateModel execmodel = new CandidateModel(rep);
//                    execmodel.addAxiom(new Acyclic(execrel, true));
//                    Aramis.solCEGIS.add(execmodel.encode(execution.getProgram(), maxpairs, ctx, mode, alias));
//                    Aramis.solCEGIS.add(execmodel.inconsistent(execution.getProgram(), ctx));
                    incons.push(execution);
                    addCandidatesCEGIS(Execution.getExecutions().indexOf(execution) + 1, incons);
                    incons.pop();
                }
            }
            Aramis.solCEGIS.pop();
            Log.fine("Backtracking...");
        }

    }

    /**
     * Adds a relation
     *
     * @param rel
     * @return the added axiom.
     */
    public CandidateAxiom add(Relation r) {
        Log.log(Level.FINE, "Adding {0}", r.getName());
        Relation rel = r;
        if(Aramis.isRememberMayPairs()){
        Relation reltemp = rep.getRelation(r.getName());
        if (reltemp != null) {
            rel = reltemp;
            Log.warning("Relation added to list is already in Repository: " + r.getName());
        } else {
            rep.updateRelation(rel);
        }
        if (maxpairs.put(rel, new HashMap<>()) != null) {
            Log.warning("May Pairs for added relation " + rel.getName() + " already exist ");
        }
        }
        CandidateAxiom ax = new CandidateAxiom(rel, Aramis.posPrograms.size());
        //Aramis.checkCandidate(ax);
        ax.position = candidates.size();
        candidates.add(ax);
        return ax;

    }

    /**
     * Adds the basic relations add the beginning.
     */
    public void addBasicrels() {
        Log.fine("Adding basic relations...");
        for (Relation baserel : TemplateBasicRelation.getBaserels()) {
            Aramis.checkCandidate(add(baserel));
        }

//        for (String baserel : baserels) {
//            //if(!(baserel.equals("fr")| baserel.equals("rf")))
//            Aramis.checkCandidate(add(new RelInverse(reptemp.getRelation(baserel))));
//        }
    }

    /**
     * Combines all old relations the first unchecked relation, adds the results
     * to the list and computes their information.
     */
    public void addCandidatesEnumerate() {
        Log.log(Level.WARNING, "Adding relations. Current size: {0}", candidates.size());
        int oldsize = candidates.size();
        candidates.ensureCapacity(2 * oldsize);
        CandidateAxiom c1 = candidates.get(unCombined);
        Relation r1 = c1.getRel();

        //Applying unary operations:
        if (!(r1 instanceof RelTransRef) && !(r1 instanceof RelTrans)) {
            CandidateAxiom ax = add(new RelTransRef(r1));
            ax.largerthan(c1);
            Aramis.checkCandidate(ax);
        }

        if (!(r1 instanceof RelMinus) && !(r1 instanceof RelIntersection) && !(r1 instanceof RelUnion)) {
            for (Relation minusrel : TemplateBasicRelation.getMinusrels()) {
                //rminus = rep.getRelation(minusrel);
                CandidateAxiom ax = add(new RelMinus(r1, minusrel));
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
            CandidateAxiom inter = null;
            if (!(r2 instanceof RelIntersection) && !(r2 instanceof RelUnion) && !(r1 instanceof RelUnion)) {
                inter = add(new RelIntersection(r1, r2));
                inter.smallerthan(c1);
                inter.smallerthan(c2);
                Aramis.checkCandidate(inter);
            }

            //Relcompositions are nested from the left and contain no unions or intersections.
            if (!(r2 instanceof RelComposition) && !(r1 instanceof RelIntersection)
                    && !(r2 instanceof RelIntersection)
                    && !(r1 instanceof RelUnion)
                    && !(r2 instanceof RelUnion)) {

                CandidateAxiom ax = add(new RelComposition(r1, r2));
                if (union != null) {
                    ax.smallerthan(union);
                }
                if (inter != null) {
                    ax.largerthan(inter);
                }
                Aramis.checkCandidate(ax);
                if (!(r1 instanceof RelComposition)) {
                    CandidateAxiom ax2 = add(new RelComposition(r2, r1));
                    ax2.largerthan(ax);
                    ax2.smallerthan(ax);
                    Aramis.checkCandidate(ax2);
                }
            }
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

    void add(Execution exec) {
        Execution.getExecutions().add(exec);
    }

}
