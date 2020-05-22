package com.dat3m.dartagnan;

import com.dat3m.dartagnan.wmm.utils.alias.Alias;
import com.dat3m.dartagnan.wmm.utils.Mode;
import com.dat3m.dartagnan.wmm.utils.Arch;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.enumerations.Z3_ast_print_mode;
import com.dat3m.dartagnan.asserts.AbstractAssert;
import com.dat3m.dartagnan.parsers.program.ProgramParser;
import com.dat3m.dartagnan.parsers.cat.ParserCat;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.utils.Graph;
import com.dat3m.dartagnan.wmm.Wmm;
import org.apache.commons.cli.*;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;

public class Dartagnan {

    public static final String TACTIC = "qfufbv";

    public static void main(String[] args) throws IOException {

        Options options = new Options();

        Option inputOption = new Option("i", "input", true, "Pathff to the file with input program");
        inputOption.setRequired(true);
        options.addOption(inputOption);

        Option catOption = new Option("cat", true, "Path to the CAT file");
        catOption.setRequired(true);
        options.addOption(catOption);

        Option targetOption = new Option("t", "target", true, "Target architecture {none|arm|arm8|power|tso}");
        options.addOption(targetOption);

        Option modeOption = new Option("m", "mode", true, "Encoding mode {knastertarski|idl|kleene}");
        options.addOption(modeOption);

        Option aliasOption = new Option("a", "alias", true, "Type of alias analysis {none|andersen|cfs}");
        options.addOption(aliasOption);

        options.addOption(new Option("unroll", true, "Unrolling steps"));
        options.addOption(new Option("draw", true, "Path to save the execution graph if the state is reachable"));
        options.addOption(new Option("rels", true, "Relations to be drawn in the graph"));

        CommandLine cmd;
        try {
            cmd = new DefaultParser().parse(options, args);
        }
        catch (ParseException e) {
            new HelpFormatter().printHelp("DARTAGNAN", options);
            System.exit(1);
            return;
        }

        String inputFilePath = cmd.getOptionValue("input");
        if(!inputFilePath.endsWith("pts") && !inputFilePath.endsWith("litmus")) {
            System.out.println("Unrecognized program format");
            System.exit(0);
            return;
        }

        Mode mode = Mode.get(cmd.getOptionValue("mode"));
        Alias alias = Alias.get(cmd.getOptionValue("alias"));

        Program p = new ProgramParser().parse(new File(inputFilePath));
        
        Arch target = p.getArch();

        if(p.getArch() == null && cmd.hasOption("target")) {
        	target = Arch.get(cmd.getOptionValue("target"));
        }
        
        if(target == null) {
            System.out.println("Compilation target cannot be infered");
            System.exit(0);
            return;
        }
        
        if(p.getAss() == null){
            throw new RuntimeException("Assert is required for Dartagnan tests");
        }

        Wmm mcm = new ParserCat().parse(new File(cmd.getOptionValue("cat")));

        if(cmd.hasOption("draw")) {
            mcm.setDrawExecutionGraph();
            mcm.addDrawRelations(Graph.getDefaultRelations());
            if(cmd.hasOption("rels")) {
                mcm.addDrawRelations(Arrays.asList(cmd.getOptionValue("rels").split(",")));
            }
        }

        int steps = 1;
        if(cmd.hasOption("unroll")) {
            steps = Integer.parseInt(cmd.getOptionValue("unroll"));
        }

        Context ctx = new Context();
        Solver s = ctx.mkSolver(ctx.mkTactic(TACTIC));

        boolean result = testProgram(s, ctx, p, mcm, target, steps, mode, alias);

        if(p.getAssFilter() != null){
            System.out.println("Filter " + (p.getAssFilter()));
        }
        System.out.println("Condition " + p.getAss().toStringWithType());
        System.out.println(result ? "Ok" : "No");

        if(cmd.hasOption("draw") && canDrawGraph(p.getAss(), result)) {
            String outputPath = cmd.getOptionValue("draw");
            String[] relations = cmd.hasOption("rels") ? cmd.getOptionValue("rels").split(",") : new String[0];
            ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB_FULL);
            drawGraph(new Graph(s.getModel(), ctx, p, relations), outputPath);
            System.out.println("Execution graph is written to " + outputPath);
        }

        ctx.close();
    }

    public static boolean testProgram(Solver solver, Context ctx, Program program, Wmm wmm, Arch target, int steps,
                               Mode mode, Alias alias){

        program.unroll(steps, 0);
        program.compile(target, 0);

        solver.add(program.getAss().encode(ctx));
        if(program.getAssFilter() != null){
            solver.add(program.getAssFilter().encode(ctx));
        }
        solver.add(program.encodeCF(ctx));
        solver.add(program.encodeFinalRegisterValues(ctx));
        solver.add(wmm.encode(program, ctx, mode, alias));
        solver.add(wmm.consistent(program, ctx));

        boolean result = (solver.check() == Status.SATISFIABLE);
//        if(program.getAss().getInvert()){
//            result = !result;
//        }
        return result;
    }

    public static boolean canDrawGraph(AbstractAssert ass, boolean result){
        String type = ass.getType();
        if(type == null){
            return result;
        }

        if(result){
            return type.equals(AbstractAssert.ASSERT_TYPE_EXISTS) || type.equals(AbstractAssert.ASSERT_TYPE_FINAL);
        }
        return type.equals(AbstractAssert.ASSERT_TYPE_NOT_EXISTS) || type.equals(AbstractAssert.ASSERT_TYPE_FORALL);
    }

    public static void drawGraph(Graph graph, String path) throws IOException {
        File newTextFile = new File(path);
        FileWriter fw = new FileWriter(newTextFile);
        fw.write(graph.toString());
        fw.close();
    }
}
