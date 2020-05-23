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
import com.dat3m.dartagnan.parsers.cat.ParserCat;
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
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.Wmm;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.relation.basic.TemplateBasicRelation;
import com.dat3m.dartagnan.wmm.utils.Arch;
import com.dat3m.dartagnan.wmm.utils.Mode;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.alias.Alias;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

@SuppressWarnings("deprecation")
public class Aramis {

    protected static final Logger Log = Logger.getLogger("");
    protected static Map<Execution, CandidateAxiom> firstCandidates = new HashMap<>();
    private static Map<Execution, CandidateAxiom> lastNegCandidates = new HashMap<>();
    protected static Mode mode;
    protected static Alias alias;
    private static Arch target;
    private static int steps = 1;
    protected static final RelationCandidates candidates = new RelationCandidates();
    public static ArrayList<Program> posPrograms;
    public static ArrayList<Program> negPrograms;
    private static int nrOfEvents = 0;
    static final HashMap<Program, Solver> solvers = new HashMap<>();
    protected static final Context ctx = new Context();
    public static Solver solCEGIS;
    private static RelationRepository baserelrep = new RelationRepository();
    private static ArrayList<String> posfilePaths;
    public static int nrOfSMTcalls = 0;
    private static int maxAxioms = 100;
    private static boolean rememberMayPairs = true;

    public static boolean isRememberMayPairs() {
        return rememberMayPairs;
    }
    public static int getMaxAxioms() {
        return maxAxioms;
    }

    /**
     * Checks which Neg Executions fail ax and updates the pointer.
     *
     * @param ax
     */
    protected static void computeNegs(CandidateAxiom ax) {
        for (Execution execution : Execution.getExecutions()) {
            if (!ax.getNegCons().contains(execution) && !ax.getNegIncons().contains(execution)) {
                if (checkCandidate(ax, execution)) {
                    ax.getNegCons().add(execution);
                } else {
                    ax.getNegIncons().add(execution);
                }
            }
        }

        for (Execution negIncon : ax.getNegIncons()) {
            ax.relevant = true;
            if (firstCandidates.get(negIncon) == null) {
                firstCandidates.put(negIncon, ax);
            } else {
                lastNegCandidates.get(negIncon).setNext(negIncon, ax);
            }
            lastNegCandidates.put(negIncon, ax);
        }
    }

    public static void main(String[] args) throws Z3Exception, IOException {

        //Command line options:
        Options options = new Options();

        Option pos = new Option("p", "positive", true, "Directory of program files that should pass the reachability tests");
        pos.setRequired(true);
        options.addOption(pos);

        Option neg = new Option("n", "negative", true, "Directory of program files that should fail the reachability tests");
        neg.setRequired(true);
        options.addOption(neg);

        Option axs = new Option("c", "constraints", true, "Bound on the number of constraints in the synthesized model");
        axs.setRequired(false);
        options.addOption(axs);

//        Option cegis = new Option("cegis", false, "Using CEGIS");
//        cegis.setRequired(false);
//        options.addOption(cegis);

        Option dyn = new Option("dynamic", false, "Using dynamic programming by storing may pairs");
        dyn.setRequired(false);
        options.addOption(dyn);
        
        Option partialmodel = new Option("model", false, "Using CEGIS");
        partialmodel.setRequired(false);
        options.addOption(partialmodel);

        Option verbose = new Option("v", "verbose", false, "Printing more information");
        verbose.setRequired(false);
        options.addOption(verbose);

        Option aliasOption = new Option("a", "alias", true, "Type of alias analysis {none|andersen|cfs}");
        options.addOption(aliasOption);

        Option targetOpt = new Option("t", "target", true, "Target architecture compilation {none|arm|arm8|power|tso}");
        targetOpt.setRequired(true);
        options.addOption(targetOpt);

        Option basicOpt = new Option("b", "basicrelations", true, "The basic relations the model uses");
        basicOpt.setRequired(false);
        basicOpt.setArgs(Option.UNLIMITED_VALUES);
        options.addOption(basicOpt);

        Option minusOpt = new Option("mr", "minusrelations", true, "The relations to be used by the operator setminus.");
        minusOpt.setRequired(false);
        minusOpt.setArgs(Option.UNLIMITED_VALUES);
        options.addOption(minusOpt);

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

        if (cmd.hasOption("verbose")) {
            Log.setLevel(Level.ALL);
            for (Handler handler : Log.getHandlers()) {
                handler.setLevel(Level.ALL);
            }
        } else {
            Log.setLevel(Level.ALL);
            for (Handler handler : Log.getHandlers()) {
                handler.setLevel(Level.OFF);
            }
            Log.setLevel(Level.OFF);
        }

        //ConsoleHandler handler = new ConsoleHandler();
        ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB_FULL);

        // Publish this level
        //handler.setLevel(Level.FINEST);
        //Log.addHandler(handler);
        Log.info("Starting...");

        rememberMayPairs=cmd.hasOption("dynamic");
        if(rememberMayPairs)System.out.println("Using dynamic programming.");
        else System.out.println("Not using dynamic programming.");

        mode = Mode.get(cmd.getOptionValue("mode"));
        alias = Alias.get(cmd.getOptionValue("alias"));

        target = Arch.get(cmd.getOptionValue("target"));
        if (target == null) {
            System.out.println("Compilation target cannot be infered");
            System.exit(0);
            return;
        }

        steps = 1;
        if (cmd.hasOption("unroll")) {
            steps = Integer.parseInt(cmd.getOptionValue("unroll"));
        }
        if (cmd.hasOption("basicrelations")) {
            String[] basics = cmd.getOptionValues("basicrelations");
            TemplateBasicRelation.setBaserelnames(Arrays.asList(basics));
            //RelationCandidates.baserels=basics;
        }
        if (cmd.hasOption("minusrelations")) {
            String[] minus = cmd.getOptionValues("minusrelations");
            TemplateBasicRelation.setMinusrelnames(Arrays.asList(minus));
            //RelationCandidates.baserels=basics;
        }
        TemplateBasicRelation.initiateBaseAndMinusrels(baserelrep);
        Wmm inputmodel = new Wmm();
        if (cmd.hasOption("model")) {
            inputmodel = new ParserCat().parse(new File(cmd.getOptionValue("model")));
        }
        parsePrograms(new File(cmd.getOptionValue("positive")), new File(cmd.getOptionValue("negative")), inputmodel, target, steps);

        //Sketch based synthesis:
        if (cmd.hasOption("constraints")) {
            maxAxioms = Integer.parseInt(cmd.getOptionValue("constraints"));
            System.out.println("Bound on the number of constraints in the synthesized model: " + maxAxioms);
        }

        //Dynamic synthesis:
        //Log.log(Level.WARNING, "Dynamic Synthesis:  Pos: {0}. Neg: {1}", new Object[]{posPrograms.size(), negPrograms.size()});
        DynamicSynthesis.start(cmd.hasOption("cegis"));
    }

    /**
     * Checks ax for consistency against all pos progs and neg execs.
     *
     * @param ax
     * @return true if all pos pass
     */
    protected static boolean checkCandidate(CandidateAxiom ax) {
        for (int i = 0; i < posPrograms.size(); i++) {
            if (ax.pos[i] == Consistent.INCONSISTENT) {
                ax.setConsistent(false);
                return false;
            }
        }
        for (int i = 0; i < posPrograms.size(); i++) {
            if (ax.pos[i] != Consistent.CONSISTENT) {
                Log.finest("Testing " + ax.getRel().getName() + " " + posPrograms.get(i).getName());
                if (checkCandidate(ax, i)) {
                    ax.pos[i] = Consistent.CONSISTENT;
                } else {
                    ax.pos[i] = Consistent.INCONSISTENT;
                    ax.setConsistent(false);
                    return false;
                }
            }
        }
        ax.setConsistent(true);
        computeNegs(ax);
        Log.fine("Relation is relevant: " + ax.relevant);
        if (ax.relevant) {
            DynamicSynthesis.initChecking();
        };
        return true;
    }

    /**
     * Checks ax for consistency against the given prog.
     *
     * @param ax
     * @param p
     * @return
     */
    private static boolean checkCandidate(CandidateAxiom ax, int i) {
        Program p = posPrograms.get(i);
        //boolean oldresult=oldcheckCandidate(ax, i);
        Solver s = solvers.get(p);
        s.push();
        CandidateModel tempmodel = null;
        if (rememberMayPairs) {
            tempmodel = new CandidateModel(RelationCandidates.getRepository());
            tempmodel.addAxiom(ax);
            s.add(tempmodel.encode(p, RelationCandidates.getMaxpairs(), ctx, mode, alias));
        } else {
            RelationRepository reptemp=new RelationRepository();
            ax.getRel().addRelations(reptemp);
            tempmodel=new CandidateModel(reptemp);
            tempmodel.addAxiom(ax);
            s.add(tempmodel.encode(p, ctx, mode, alias));
        }
        s.add(tempmodel.consistent(p, ctx));
        nrOfSMTcalls++;
        Status sat = s.check();
        s.pop();
        Log.finest("testing: " + ax.getRel().toString() + p.getName() + " " + sat);
        boolean result = (sat == Status.SATISFIABLE);
//        if(result!=oldresult) {
//            System.err.println("Result changed to: "+result);
//            System.exit(1);
//        }
        return (result);
    }

    private static void parsePrograms(File positiveDir, File negativeDir, Wmm model, Arch target, int steps) throws IOException {
        //parse pos tests
        posPrograms = new ArrayList<>(positiveDir.listFiles().length);
        posfilePaths = new ArrayList<>(positiveDir.listFiles().length);
        solCEGIS = ctx.mkSolver();
        for (File listFile : positiveDir.listFiles()) {
            String filepath = listFile.getPath();

            if (!filepath.endsWith("pts") && !filepath.endsWith("litmus")) {
                Log.warning("Unrecognized program format for " + filepath);
            } else {
                Log.fine("Positive litmus test: " + filepath);
                posfilePaths.add(filepath);
                Program p = new ProgramParser().parse(new File(filepath));
                if (p.getAss() == null) {
                    Log.warning("Assert is required for Dartagnan tests");
                }
                posPrograms.add(p);
                Solver s = ctx.mkSolver();
                solvers.put(p, s);
                p.unroll(steps, 0);
                Arch mytarget = target;
                if (p.getArch() != null) {
                    mytarget = p.getArch();
                }
                nrOfEvents = p.compile(target, nrOfEvents);
                BoolExpr temp = p.getAss().encode(ctx);
                if (p.getAssFilter() != null) {
                    temp = ctx.mkAnd(temp, p.getAssFilter().encode(ctx));
                }
                temp = ctx.mkAnd(temp, p.encodeCF(ctx));
                temp = ctx.mkAnd(temp, p.encodeFinalRegisterValues(ctx));
                temp = ctx.mkAnd(temp, model.encode(p, ctx, mode, alias));
                s.add(temp);
                solCEGIS.add(temp);
            }
        }
        int nrOfExecs = 0;
        //parse neg tests
        negPrograms = new ArrayList<>(negativeDir.listFiles().length);
        Log.info("Used base relations: " + baserelrep.getRelations());
        for (File listFile : negativeDir.listFiles()) {
            String filepath = listFile.getPath();
            if (!filepath.endsWith("pts") && !filepath.endsWith("litmus")) {
                Log.warning("Unrecognized program format for " + filepath);

            } else {
                Log.fine("Negative litmus test: " + filepath);
                Program p = new ProgramParser().parse(new File(filepath));
                if (p.getAss() == null) {
                    Log.warning("Assert is required for Dartagnan tests");
                }
                negPrograms.add(p);
                Solver s = ctx.mkSolver();
                p.unroll(steps, 0);
                nrOfEvents = p.compile(target, nrOfEvents);
                BoolExpr temp = p.getAss().encode(ctx);
                if (p.getAssFilter() != null) {
                    temp = ctx.mkAnd(temp, p.getAssFilter().encode(ctx));
                }
                temp = ctx.mkAnd(temp, p.encodeCF(ctx));
                temp = ctx.mkAnd(temp, p.encodeFinalRegisterValues(ctx));
                temp = ctx.mkAnd(temp, model.encode(p, ctx, mode, alias));
                for (Relation baserel : baserelrep.getRelations()) {
                    baserel.initialise(p, ctx, mode);
                }
                for (Relation baserel : baserelrep.getRelations()) {
                    baserel.addEncodeTupleSet(baserel.getMaxTupleSet());
                    temp = ctx.mkAnd(temp, baserel.encode());
                }
                s.add(temp);
                Status sat = s.check();
                nrOfSMTcalls++;
                while (sat == Status.SATISFIABLE) {
                    //encode execution to be avoided:
                    //log.info("Adding new execution " + prefix);
                    //TODO: remove oldexec
                    String oldexec = "";
                    Execution exec = new Execution(p, s.getModel(), ctx);
                    nrOfExecs++;
                    candidates.add(exec);
                    Log.fine(exec.toString());
                    s.add(ctx.mkNot(exec.encodeExecOriginal()));
                    oldexec = exec.toString();
                    sat = s.check();
                    nrOfSMTcalls++;
                }
            }

        }
        //Log.info("Number of NEG Executions: "+nrOfExecs);
        System.out.println("Size of POS: " + posPrograms.size());
        System.out.println("Size of NEG: " + negPrograms.size());
        System.out.println("Number of NEG Executions: " + nrOfExecs);
        System.out.println("Basic relations in use: " + TemplateBasicRelation.getBaserels().toString());
        System.out.println("Relations that occur in Setminus: " + TemplateBasicRelation.getMinusrels().toString());

    }

    public static boolean checkCandidate(CandidateAxiom ax, Execution execution) {
        ax.getRel().initialise(execution, ctx, mode);
        CandidateAxiom.setEnCodingExecMode(true);
        boolean result = ax.getEncodeTupleSet().isEmpty();
        CandidateAxiom.setEnCodingExecMode(false);
        return result;

    }
}
