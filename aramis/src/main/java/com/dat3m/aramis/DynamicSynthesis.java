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
import static com.dat3m.aramis.Aramis.negPrograms;
import static com.dat3m.aramis.Aramis.posPrograms;
import static com.dat3m.aramis.Aramis.solvers;
import com.dat3m.dartagnan.wmm.axiom.CandidateAxiom;
import com.dat3m.dartagnan.wmm.CandidateModel;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.wmm.Wmm;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import java.util.logging.Level;

/**
 *
 * @author Florian Furbach
 */
public class DynamicSynthesis {

    private static CandidateModel model;

    protected static Wmm start(boolean cegis) {
        model=new CandidateModel(candidates.getRepository(), negPrograms.size());
        if (!cegis) {
            candidates.addBasicrels();
        }

        boolean finished = false;
        //repeatedly check and expand list:
        while (!finished) {
            Log.warning("Starting Dynamic Testing Phase...");
            boolean allNEGScovered = true;
            for (int currentneg = 0; currentneg < negPrograms.size(); currentneg++) {
                if (firstCandidates[currentneg] == null) {
                    allNEGScovered = false;
                }
            }
            if (allNEGScovered) {
                //use all new relations as potential starting points for dyn. synthesis
                for (int startingpoint = candidates.size() - 1; startingpoint >= candidates.unchecked; startingpoint--) {
                    CandidateAxiom ax = candidates.get(startingpoint);
                    //only use relations that pass all POS and fail at least one NEG
                    if (ax.consistent && ax.relevant) {
                        model.push(ax);
                        Log.fine("Pushing " + ax.toString());
                        //try out all relevant models with that relation:
                        if (dynamicSynthesis(startingpoint)) {
                            System.out.println("Found Model: " + model.toString());
                            Log.log(Level.INFO, "Number of enumerated relations: {0}", candidates.size());
                            finished = true;
                        } else {
                            //get the stack empty again:
                            model.pop();
                            Log.log(Level.FINE, "Popping {0}", ax.toString());
                        }
                    }
                }
            }
            //expand list:
            if (!finished) {
                candidates.addCandidates(cegis);
            }
        }
        return model;
    }

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
        for (Program p : posPrograms) {
            Log.log(Level.FINER, "Checking pos {0}", p.getName());
            Solver s = solvers.get(p);
            s.push();
            s.add(model.encode(p, RelationCandidates.getMaxpairs(), ctx, mode, alias));
            s.add(model.consistent(p, ctx));
            Status sat = s.check();
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
    private static boolean dynamicSynthesis(int startingpoint) {
        int firstUncovered = model.getNextPassingNeg();
        if (firstUncovered >= negPrograms.size()) {
            return checkDynamicCurrent();
        }
        CandidateAxiom addingax = firstCandidates[firstUncovered];
        while (addingax != null) {
            if (addingax.position >= startingpoint) {
                return false;
            }
            if (!model.redundand(addingax)) {
                model.push(addingax);
                Log.log(Level.FINE, "Pushing {0} on level {1}", new Object[]{addingax.toString(), firstUncovered});
                if (dynamicSynthesis(startingpoint)) {
                    return true;
                }
                model.pop();
                Log.log(Level.FINE, "Popping {0} on level {1}", new Object[]{addingax.toString(), firstUncovered});
            }
            addingax = addingax.next[firstUncovered];
        }
        return false;
    }
}
