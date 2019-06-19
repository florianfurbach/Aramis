/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.dat3m.aramis;

/**
 *
 * @author Florian Furbach
 */
import com.dat3m.aramis.wmm.CandidateAxiom;
import com.dat3m.aramis.wmm.CandidateModel;
import com.dat3m.aramis.wmm.Consistent;
import com.dat3m.dartagnan.parsers.program.ProgramParser;
import com.microsoft.z3.BoolExpr;
import java.io.File;
import java.io.IOException;
import org.apache.commons.cli.*;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_ast_print_mode;

import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.wmm.Wmm;
import com.dat3m.dartagnan.wmm.utils.Arch;
import com.dat3m.dartagnan.wmm.utils.Mode;
import com.dat3m.dartagnan.wmm.utils.alias.Alias;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.logging.Level;
import java.util.logging.Logger;

@SuppressWarnings("deprecation")
public class Aramis {

    private static final Logger Log = Logger.getLogger(Aramis.class.getName());
    private static CandidateAxiom[] firstCandidates;
    private static CandidateAxiom[] lastNegCandidates;
    public static Mode mode;
    public static Alias alias;
    private static final ListOfRels candidates = new ListOfRels();
    public static ArrayList<Program> posPrograms;
    public static ArrayList<Program> negPrograms;
    private static int nrOfEvents=0;
    private static ArrayList<Solver> posSolvers;
    private static ArrayList<Solver> negSolvers;
    static final HashMap<Program, Solver> solvers = new HashMap<>();
    protected static final Context ctx = new Context();
    private static int[] current;
    private static Wmm ModelCandidate;
    private static CandidateModel model = new CandidateModel();
    //private static ArrayList<CandidateAxiom> currentAxioms;
    public static Solver solCEGIS;
    public static ArrayList<BoolExpr> negExprs;
    
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
     * Checks which Negs fail ax and updates the pointer.
     *
     * @param ax
     */
    protected static void computeNegs(CandidateAxiom ax) {
        for (int negPr = 0; negPr < negPrograms.size(); negPr++) {
            Program negProgram = negPrograms.get(negPr);

            //If the test outcome is not known, then compute it
            if (ax.neg[negPr] != Consistent.INCONSISTENT && ax.neg[negPr] != Consistent.CONSISTENT) {
                if (checkCandidate(ax, negProgram)) {
                    ax.neg[negPr] = Consistent.CONSISTENT;
                } else {
                    ax.neg[negPr] = Consistent.INCONSISTENT;
                }
            }

            //if the test fails store ax in the linked list of axioms where the test fails for the dynamic synthesis
            if (ax.neg[negPr] == Consistent.INCONSISTENT) {
                ax.relevant = true;
                if (firstCandidates[negPr] == null) {
                    firstCandidates[negPr] = ax;
                } else {
                    lastNegCandidates[negPr].next[negPr] = ax;
                }
                lastNegCandidates[negPr] = ax;
            }

        }
    }

    public static void main(String[] args) throws Z3Exception, IOException {
        Log.setLevel(Level.ALL);
        //ConsoleHandler handler = new ConsoleHandler();
        ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB_FULL);

        // Publish this level
        //handler.setLevel(Level.FINEST);
        //Log.addHandler(handler);
        Log.info("Starting...");

        //Command line options:
        Options options = new Options();

        Option pos = new Option("p", "positive", true, "Directory of program files that should pass the reachability tests");
        pos.setRequired(true);
        options.addOption(pos);

        Option neg = new Option("n", "negative", true, "Directory of program files that should fail the reachability tests");
        neg.setRequired(true);
        options.addOption(neg);

        Option axs = new Option("ax", "axioms", true, "Number of expected Axioms in the model to be synthesized");
        axs.setRequired(false);
        options.addOption(axs);

        Option cegis= new Option("cegis", false, "Using CEGIS");
        cegis.setRequired(false);
        options.addOption(cegis);        
        
        Option aliasOption = new Option("a", "alias", true, "Type of alias analysis {none|andersen|cfs}");
        options.addOption(aliasOption);
        
        Option targetOpt = new Option("t", "target", true, "Target architecture compilation {none|arm|arm8|power|tso}");
        targetOpt.setRequired(true);
        options.addOption(targetOpt);

        options.addOption(new Option("unroll", true, "Unrolling steps"));        
        
        Option modeOption = new Option("m", "mode", true, "Encoding mode {knastertarski|idl|kleene}");
        options.addOption(modeOption);
        
        CommandLine cmd;
        try {
            cmd = new DefaultParser().parse(options, args);
        }
        catch (ParseException e) {
            new HelpFormatter().printHelp("ARAMIS", options);
            System.exit(1);
            return;
        }
        mode = Mode.get(cmd.getOptionValue("mode"));
        alias = Alias.get(cmd.getOptionValue("alias"));


        Arch target = target = Arch.get(cmd.getOptionValue("target"));
        if(target == null) {
            System.out.println("Compilation target cannot be infered");
            System.exit(0);
            return;
        }
        
        int steps = 1;
        if(cmd.hasOption("unroll")) {
            steps = Integer.parseInt(cmd.getOptionValue("unroll"));
        }
        
        parsePrograms(new File(cmd.getOptionValue("positive")),new File(cmd.getOptionValue("negative")),target, steps);

        firstCandidates = new CandidateAxiom[negPrograms.size()];
        lastNegCandidates = new CandidateAxiom[negPrograms.size()];
        
        //Sketch based synthesis:
        if (cmd.hasOption("ax")) {
            int nrOfAxioms = Integer.parseInt(cmd.getOptionValue("ax"));
            current = new int[nrOfAxioms];
            Log.log(Level.FINE, "Axiom: {0}. Pos: {1}. Neg: {2}", new Object[]{nrOfAxioms, posPrograms.size(), negPrograms.size()});
            candidates.addBasicrels();
            boolean temp = false;
            while (!temp) {
                if (CheckingCandidates(candidates.unchecked, candidates.size(), current.length - 1)) {
                    System.out.println("Found Model: " + ModelCandidate.toString());
                    Log.log(Level.INFO, "Number of enumerated relations: {0}", candidates.size());
                    temp = true;
                } else {
                    //expand list:
                    candidates.addCandidates(cmd.hasOption("cegis"));
                }
            }
        } //Dynamic synthesis:
        else {
            //currentAxioms = new ArrayList<CandidateAxiom>(negPrograms.size());
            Log.log(Level.WARNING, "Dynamic Synthesis:  Pos: {0}. Neg: {1}", new Object[]{posPrograms.size(), negPrograms.size()});
            if(!cmd.hasOption("cegis")) candidates.addBasicrels();
            boolean temp = false;
            //repeatedly check and expand list:
            while (!temp) {
                Log.warning("Starting Testing Phase...");
                boolean covered=true;
                for (int currentneg = 0; currentneg < negPrograms.size(); currentneg++) {
                    if(firstCandidates[currentneg]==null)covered=false;
                }
                if(covered){
                //use all new relations as potential starting points for dyn. synthesis
                for (int startingpoint = candidates.size() - 1; startingpoint >= candidates.unchecked; startingpoint--) {
                    CandidateAxiom ax = candidates.get(startingpoint);
                    //only use relations that pass all POS and fail at least one NEG
                    if (ax.consistent && ax.relevant) {
                        model.push(ax);
                        Log.fine("Pushing "+ax.toString());
                        //try out all relevant models with that relation:
                        if (dynamicSynthesis(startingpoint)) {
                            System.out.println("Found Model: " + model.toString());
                            Log.log(Level.INFO, "Number of enumerated relations: {0}", candidates.size());
                            temp = true;
                        } else {
                            //get the stack empty again:
                            model.pop();
                            Log.log(Level.FINE, "Popping {0}", ax.toString());
                        }
                    }
                }
                }
                //expand list:
                if (!temp) {
                    candidates.addCandidates(cmd.hasOption("cegis"));
                }
            }

        }
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

    /**
     * Checks ax for consistency against all progs.
     *
     * @param ax
     * @return true if all pos pass
     */
    protected static boolean checkCandidate(CandidateAxiom ax) {
        for (int i = 0; i < posPrograms.size(); i++) {
            if (ax.pos[i] == Consistent.INCONSISTENT) {
                ax.consistent = false;
                return false;
            }
            if (ax.pos[i] != Consistent.CONSISTENT) {
                if (checkCandidate(ax, posPrograms.get(i))) {
                    ax.pos[i] = Consistent.CONSISTENT;
                } else {
                    ax.pos[i] = Consistent.INCONSISTENT;
                    ax.consistent = false;
                    return false;
                }
            }
        }
        ax.consistent = true;
        computeNegs(ax);
        return true;
    }

    /**
     * Checks ax for consistency against the given prog.
     *
     * @param ax
     * @param p
     * @return
     */
    private static boolean checkCandidate(CandidateAxiom ax, Program p) {
        Wmm tempmodel = new Wmm();
        tempmodel.addAxiom(ax);
        Solver s = solvers.get(p);
        s.push();
        s.add(tempmodel.encode(p, ctx, mode, alias));
        s.add(tempmodel.consistent(p, ctx));
        Status sat = s.check();
        s.pop();
        return (sat == Status.SATISFIABLE);
    }

    /**
     * Sketch based synthesis: Checks the current model for consistency. 
     * TODO: make sure some preprocessed neg cases get left out.
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
            Program p=negPrograms.get(i);
            
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

    /**
     * Dynamic synthesis: Checks the current model for consistency.
     *
     * @return true if all POS tests pass.
     */
    private static boolean checkDynamicCurrent() {
        Log.log(Level.FINE, "Checking {0}", model.toString());
        if(model.size()==1) return true;
        for (Program p : posPrograms) {
            Log.log(Level.FINER, "Checking pos {0}", p.getName());
            Solver s = solvers.get(p);
            s.push();
            s.add(model.encode(p, ctx, mode, alias));
            s.add(model.consistent(p, ctx));
            Status sat = s.check();
            s.pop();
            if (sat != Status.SATISFIABLE) {
                return false;
            }

        }
        return true;
    }

    private static void parsePrograms(File positiveDir, File negativeDir, Arch target, int steps) throws IOException {
        //parse pos tests
        posPrograms = new ArrayList<>(positiveDir.listFiles().length);
        posSolvers = new ArrayList<>(positiveDir.listFiles().length);
        solCEGIS=ctx.mkSolver();
        for (File listFile : positiveDir.listFiles()) {
            String filepath = listFile.getPath();

            if (!filepath.endsWith("pts") && !filepath.endsWith("litmus")) {
                Log.warning("Unrecognized program format for " + filepath);

            } else {
                Log.fine("Positive litmus test: " + filepath);
                Program p = new ProgramParser().parse(new File(filepath));
                if(p.getAss() == null){
                    Log.warning("Assert is required for Dartagnan tests");
                }
                posPrograms.add(p);
                solvers.put(p, ctx.mkSolver());
                Solver s = solvers.get(p);
                p.unroll(steps, 0);
                nrOfEvents=p.compile(target, nrOfEvents);
                BoolExpr temp=p.getAss().encode(ctx);
                if(p.getAssFilter() != null){
                    temp=ctx.mkAnd(p.getAssFilter().encode(ctx));
                }      
                temp=ctx.mkAnd(p.encodeCF(ctx));
                temp=ctx.mkAnd(p.encodeFinalRegisterValues(ctx));
                s.add(temp);                
                solCEGIS.add(temp);
            }

        }

        //parse neg tests
        negPrograms = new ArrayList<>(negativeDir.listFiles().length);
        for (File listFile : negativeDir.listFiles()) {
            String filepath = listFile.getPath();
            if (!filepath.endsWith("pts") && !filepath.endsWith("litmus")) {
                Log.warning("Unrecognized program format for " + filepath);

            } else {
                Log.fine("Positive litmus test: " + filepath);
                Program p = new ProgramParser().parse(new File(filepath));
                if(p.getAss() == null){
                    Log.warning("Assert is required for Dartagnan tests");
                }
                negPrograms.add(p);
                solvers.put(p, ctx.mkSolver());
                Solver s = solvers.get(p);
                p.unroll(steps, 0);
                nrOfEvents=p.compile(target, nrOfEvents);
                BoolExpr temp=p.getAss().encode(ctx);
                if(p.getAssFilter() != null){
                    temp=ctx.mkAnd(p.getAssFilter().encode(ctx));
                }      
                temp=ctx.mkAnd(p.encodeCF(ctx));
                temp=ctx.mkAnd(p.encodeFinalRegisterValues(ctx));
                s.add(temp);                
            }

        }    }
}
