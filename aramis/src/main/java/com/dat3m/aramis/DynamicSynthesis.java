/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.aramis;

import static com.dat3m.aramis.Aramis.Log;
import static com.dat3m.aramis.Aramis.alias;
import static com.dat3m.aramis.Aramis.candidates;
import static com.dat3m.aramis.Aramis.ctx;
import static com.dat3m.aramis.Aramis.firstCandidates;
import static com.dat3m.aramis.Aramis.mode;
import static com.dat3m.aramis.Aramis.posPrograms;
import static com.dat3m.aramis.Aramis.solvers;
import com.dat3m.dartagnan.wmm.axiom.CandidateAxiom;
import com.dat3m.dartagnan.wmm.CandidateModel;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.Wmm;
import com.dat3m.dartagnan.wmm.axiom.Axiom;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import java.util.logging.Level;

/**
 *
 * @author Florian Furbach
 */
public class DynamicSynthesis {

    //bull
    private static CandidateModel model;

    /**
     * Dynamic synthesis: Checks the current model for consistency.
     *
     * @return true if all POS tests pass.
     */
    private static boolean checkDynamicCurrent() {
        Log.log(Level.FINE, "Checking {0}", model.toString());
        if (model.size() == 1) {
            return true;
        }
        Wmm tempmodel = null;
        if(!Aramis.isRememberMayPairs()){
            tempmodel=new Wmm();
            RelationRepository reptemp = tempmodel.getRelationRepository();
            for (Axiom axiom : model.getAxioms()) {
                axiom.getRel().addRelations(reptemp);
                tempmodel.addAxiom(axiom);
            }            
        }

        for (Program p : posPrograms) {
            Log.log(Level.FINER, "Checking program {0}", p.getName());
            Solver s = solvers.get(p);
            s.push();
            if (Aramis.isRememberMayPairs()) {
                s.add(model.encode(p, RelationCandidates.getMaxpairs(), ctx, mode, alias));
                s.add(model.consistent(p, ctx));
            } else {
                s.add(tempmodel.encode(p, ctx, mode, alias));
                s.add(tempmodel.consistent(p, ctx));
            }
            Status sat = s.check();
            Aramis.nrOfSMTcalls++;
            s.pop();
            if (sat != Status.SATISFIABLE) {
                return false;
            }

        }
        return true;
    }

    /**
     *
     * @param startingpoint
     * @return
     */
    private static boolean dynamicSynthesis(int startingpoint, int maxAxioms) {
        if (model.getAxioms().size() > maxAxioms) {
            return false;
        }
        Execution firstUncovered = model.getNextPassingNeg();
        if (firstUncovered == null) {
            return checkDynamicCurrent();
        }
        CandidateAxiom addingax = firstCandidates.get(firstUncovered);
        while (addingax != null) {
            if (addingax.position >= startingpoint) {
                return false;
            }
            if (!model.redundand(addingax)) {
                model.push(addingax, firstUncovered);
                Log.log(Level.FINE, "Pushing {0} on execution {1}", new Object[]{addingax.toString(), firstUncovered.getId()});
                if (dynamicSynthesis(startingpoint, maxAxioms)) {
                    return true;
                }
                model.pop();
                Log.log(Level.FINE, "Popping {0} on execution {1}", new Object[]{addingax.toString(), firstUncovered.getId()});
            }
            addingax = addingax.getNext(firstUncovered);
        }
        return false;
    }

    public static void initChecking() {
        model = new CandidateModel(candidates.getRepository());
        Log.info("Starting Dynamic Testing Phase...");
        boolean allNEGScovered = true;
        for (Execution execution : Execution.getExecutions()) {
            if (firstCandidates.get(execution) == null) {
                allNEGScovered = false;
            }
        }
        if (!allNEGScovered) {
            return;
        }

        //add axioms that are the only ones that forbid an exec
        for (Execution execution : Execution.getExecutions()) {
            if (firstCandidates.get(execution).getNext(execution) == null
                    && !model.getAxioms().contains(firstCandidates.get(execution))) {
                Log.fine("Adding necessary constraint: " + firstCandidates.get(execution).toString());
                model.addAxiom(firstCandidates.get(execution));
            }
        }
        int startingpoint = candidates.size() - 1;
        CandidateAxiom ax = candidates.get(startingpoint);
        //only use relations that pass all POS and fail at least one NEG
        if (ax.isConsistent() && ax.relevant) {
            if (!model.getAxioms().contains(ax)) {
                model.addAxiom(ax);
            }
            Log.fine("Pushing first axiom: " + ax.toString());
            //try out all relevant models with that relation:

            if (dynamicSynthesis(startingpoint, Aramis.getMaxAxioms())) {
                System.out.println("Number of enumerated relations: " + candidates.size());
                System.out.println("Number of SMT queries: " + Aramis.nrOfSMTcalls);
                System.out.println("Found Model: " + model.toString());
                System.exit(0);
            } else {
            }
        }
    }

    protected static void start(boolean cegis) {
        if (!cegis) {
            candidates.addBasicrels();
        }

        boolean finished = false;
        //repeatedly check and expand list:
        while (!finished) {
            candidates.addCandidates(cegis);
        }
    }

}
