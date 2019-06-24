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
import static com.dat3m.aramis.Aramis.mode;
import static com.dat3m.aramis.Aramis.negPrograms;
import static com.dat3m.aramis.Aramis.posPrograms;
import static com.dat3m.aramis.Aramis.solvers;
import com.dat3m.aramis.wmm.Consistent;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.wmm.Wmm;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import java.util.logging.Level;

/**
 *
 * @author Florian Furbach
 */
public class StaticSynthesis {

    private static int[] current;
    protected static Wmm ModelCandidate;

    protected static Wmm start(int nrOfAxioms, boolean cegis) {
        current = new int[nrOfAxioms];
        Log.log(Level.FINE, "Axiom: {0}. Pos: {1}. Neg: {2}", new Object[]{nrOfAxioms, posPrograms.size(), negPrograms.size()});
        candidates.addBasicrels();
        boolean temp = false;
        while (!temp) {
            if (CheckingCandidates(candidates.unchecked, candidates.size(), current.length - 1)) {
                Log.log(Level.INFO, "Number of enumerated relations: {0}", candidates.size());
                temp = true;
            } else {
                //expand list:
                candidates.addCandidates(cegis);
            }
        }
        return ModelCandidate;
    }

    /**
     *
     * The main sketch based synthesis algorithm.
     *
     * @param unchecked index of the first unchecked candidate
     * @param end the the last checked index+1
     * @param currentAxiom the index of the current axiom in current
     * @return
     */
    private static boolean CheckingCandidates(int unchecked, int end, int currentAxiom) {
        //if we have set all candidates
        if (currentAxiom < 0) {
            return checkStaticCurrent();
        }
        //if we have not enough candidates for the axioms left
        if (end - unchecked < currentAxiom + 1) {
            return false;
        }
        int i = unchecked;
        while (i < end) {
            current[currentAxiom] = i;
            if (candidates.get(i).consistent) {
                if (CheckingCandidates(0, i - 1, currentAxiom - 1)) {
                    return true;
                }
            }
            i++;
        }
        return false;
    }

    /**
     * Sketch based synthesis: Checks the current model for consistency. TODO:
     * make sure some preprocessed neg cases get left out.
     *
     * @return
     */
    private static boolean checkStaticCurrent() {
        ModelCandidate = new Wmm();
        for (int i : current) {
            ModelCandidate.addAxiom(candidates.get(i));
        }
        Log.fine("Checking " + ModelCandidate.toString());
        for (int i = 0; i < negPrograms.size(); i++) {
            Program p = negPrograms.get(i);

            //check if p is already knwon to be inconsistent with one of the axioms, if so we can skip it.
            boolean cons = true;
            for (int j : current) {
                if (candidates.get(j).neg[i] == Consistent.INCONSISTENT) {
                    cons = false;
                }
            }
            if (cons) {
                Log.finer("Checking neg " + p.getName());
                Solver s = solvers.get(p);
                s.push();
                s.add(ModelCandidate.encode(p, ctx, mode, alias));
                s.add(ModelCandidate.consistent(p, ctx));
                Status sat = s.check();
                s.pop();
                if (sat == Status.SATISFIABLE) {
                    return false;
                }
            }

        }
        for (Program p : posPrograms) {
            Log.finer("Checking pos " + p.getName());
            Solver s = solvers.get(p);
            s.push();
            s.add(ModelCandidate.encode(p, ctx, mode, alias));
            s.add(ModelCandidate.consistent(p, ctx));
            Status sat = s.check();
            s.pop();
            if (sat != Status.SATISFIABLE) {
                return false;
            }

        }
        return true;
    }
}
