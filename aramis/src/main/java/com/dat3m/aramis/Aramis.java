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
import com.dat3m.dartagnan.wmm.axiom.CandidateAxiom;
import com.dat3m.dartagnan.wmm.Consistent;
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
import com.dat3m.dartagnan.wmm.CandidateModel;
import com.dat3m.dartagnan.wmm.Wmm;
import com.dat3m.dartagnan.wmm.utils.Arch;
import com.dat3m.dartagnan.wmm.utils.Mode;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.alias.Alias;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.logging.Level;
import java.util.logging.Logger;

@SuppressWarnings("deprecation")
public class Aramis {

    protected static final Logger Log = Logger.getLogger(Aramis.class.getName());
    protected static CandidateAxiom[] firstCandidates;
    private static CandidateAxiom[] lastNegCandidates;
    protected static Mode mode;
    protected static Alias alias;
    protected static final RelationCandidates candidates = new RelationCandidates();
    public static ArrayList<Program> posPrograms;
    public static ArrayList<Program> negPrograms;
    private static int nrOfEvents = 0;
    private static ArrayList<Solver> posSolvers;
    private static ArrayList<Solver> negSolvers;
    static final HashMap<Program, Solver> solvers = new HashMap<>();
    protected static final Context ctx = new Context();
    //private static ArrayList<CandidateAxiom> currentAxioms;
    public static Solver solCEGIS;
    public static ArrayList<BoolExpr> negExprs;

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

        Option cegis = new Option("cegis", false, "Using CEGIS");
        cegis.setRequired(false);
        options.addOption(cegis);

        Option aliasOption = new Option("a", "alias", true, "Type of alias analysis {none|andersen|cfs}");
        options.addOption(aliasOption);

        Option targetOpt = new Option("t", "target", true, "Target architecture compilation {none|arm|arm8|power|tso}");
        targetOpt.setRequired(true);
        options.addOption(targetOpt);

        Option basicOpt = new Option("b", "basicrelations", true, "The basic relations the model uses");
        basicOpt.setRequired(false);
        options.addOption(basicOpt);

        Option unrollOpt = new Option("unroll", true, "Unrolling steps");
        unrollOpt.setRequired(false);
        options.addOption(unrollOpt);

        Option modeOption = new Option("m", "mode", true, "Encoding mode {knastertarski|idl|kleene}");
        options.addOption(modeOption);

        CommandLine cmd;
        try {
            cmd = new DefaultParser().parse(options, args);
        } catch (ParseException e) {
            new HelpFormatter().printHelp("ARAMIS", options);
            System.exit(1);
            return;
        }
        mode = Mode.get(cmd.getOptionValue("mode"));
        alias = Alias.get(cmd.getOptionValue("alias"));

        Arch target = Arch.get(cmd.getOptionValue("target"));
        if (target == null) {
            System.out.println("Compilation target cannot be infered");
            System.exit(0);
            return;
        }

        int steps = 1;
        if (cmd.hasOption("unroll")) {
            steps = Integer.parseInt(cmd.getOptionValue("unroll"));
        }
        if (cmd.hasOption("basicrelations")) {
            String[] basics = cmd.getOptionValue("basicrelations").split(" ");
            for (String basic : basics) {
                RelationRepository rep = new RelationRepository();
                if (rep.getRelation(basic) == null) {
                    System.out.println("Relation " + basic + " cannot be infered");
                    System.exit(0);
                    return;
                }
            }
            RelationCandidates.baserels=basics;
        }
        
        parsePrograms(new File(cmd.getOptionValue("positive")), new File(cmd.getOptionValue("negative")), target, steps);

        firstCandidates = new CandidateAxiom[negPrograms.size()];
        lastNegCandidates = new CandidateAxiom[negPrograms.size()];

        //Sketch based synthesis:
        if (cmd.hasOption("ax")) {
            int nrOfAxioms = Integer.parseInt(cmd.getOptionValue("ax"));
            Wmm m = StaticSynthesis.start(nrOfAxioms, cmd.hasOption("cegis"));
            System.out.println("Found Model: " + m.toString());
        } //Dynamic synthesis:
        else {
            Log.log(Level.WARNING, "Dynamic Synthesis:  Pos: {0}. Neg: {1}", new Object[]{posPrograms.size(), negPrograms.size()});
            DynamicSynthesis.start(cmd.hasOption("cegis"));

        }
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
        CandidateModel tempmodel = new CandidateModel(RelationCandidates.getRepository(), negPrograms.size());
        tempmodel.addAxiom(ax);
        Solver s = solvers.get(p);
        s.push();
        s.add(tempmodel.encode(p, RelationCandidates.getMaxpairs(), ctx, mode, alias));
        s.add(tempmodel.consistent(p, ctx));
        Status sat = s.check();
        s.pop();
        return (sat == Status.SATISFIABLE);
    }

    private static void parsePrograms(File positiveDir, File negativeDir, Arch target, int steps) throws IOException {
        //parse pos tests
        posPrograms = new ArrayList<>(positiveDir.listFiles().length);
        posSolvers = new ArrayList<>(positiveDir.listFiles().length);
        solCEGIS = ctx.mkSolver();
        for (File listFile : positiveDir.listFiles()) {
            String filepath = listFile.getPath();

            if (!filepath.endsWith("pts") && !filepath.endsWith("litmus")) {
                Log.warning("Unrecognized program format for " + filepath);
            } else {
                Log.fine("Positive litmus test: " + filepath);
                Program p = new ProgramParser().parse(new File(filepath));
                if (p.getAss() == null) {
                    Log.warning("Assert is required for Dartagnan tests");
                }
                posPrograms.add(p);
                Solver s =ctx.mkSolver();
                solvers.put(p, s);
                p.unroll(steps, 0);
                nrOfEvents = p.compile(target, nrOfEvents);
                BoolExpr temp = p.getAss().encode(ctx);
                if (p.getAssFilter() != null) {
                    temp = ctx.mkAnd(temp, p.getAssFilter().encode(ctx));
                }
                temp = ctx.mkAnd(temp, p.encodeCF(ctx));
                temp = ctx.mkAnd(temp, p.encodeFinalRegisterValues(ctx));
                temp = ctx.mkAnd(temp, new Wmm().encode(p, ctx, mode, alias));
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
                if (p.getAss() == null) {
                    Log.warning("Assert is required for Dartagnan tests");
                }
                negPrograms.add(p);
                solvers.put(p, ctx.mkSolver());
                Solver s = solvers.get(p);
                p.unroll(steps, 0);
                nrOfEvents = p.compile(target, nrOfEvents);
                BoolExpr temp = p.getAss().encode(ctx);
                if (p.getAssFilter() != null) {
                    temp = ctx.mkAnd(temp, p.getAssFilter().encode(ctx));
                }
                temp = ctx.mkAnd(temp, p.encodeCF(ctx));
                temp = ctx.mkAnd(temp, p.encodeFinalRegisterValues(ctx));
                temp = ctx.mkAnd(temp, new Wmm().encode(p, ctx, mode, alias));
                s.add(temp);
            }

        }
    }
}
