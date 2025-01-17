package com.dat3m.dartagnan.wmm.relation.basic;

import com.dat3m.dartagnan.Dartagnan;
import com.dat3m.dartagnan.parsers.cat.ParserCat;
import com.dat3m.dartagnan.parsers.program.ProgramParser;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.program.arch.linux.utils.EType;
import com.dat3m.dartagnan.wmm.filter.FilterBasic;
import com.dat3m.dartagnan.wmm.relation.EdgeTestHelper;
import com.dat3m.dartagnan.wmm.utils.alias.Alias;
import com.dat3m.dartagnan.utils.ResourceHelper;
import com.dat3m.dartagnan.wmm.Wmm;
import com.dat3m.dartagnan.wmm.utils.Mode;
import com.microsoft.z3.*;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.util.*;

import static org.junit.Assert.*;

@RunWith(Parameterized.class)
public class RelCritTest {

    @Parameterized.Parameters(name = "{index}: {0}")
    public static Iterable<Object[]> data() throws IOException {
        Wmm wmm = new ParserCat().parse(new File(ResourceHelper.CAT_RESOURCE_PATH + "cat/linux-kernel.cat"));
        String path = ResourceHelper.TEST_RESOURCE_PATH + "wmm/relation/basic/crit/";

        List<Object[]> data = new ArrayList<>();
        data.add(new Object[]{path + "C-crit-01.litmus", wmm, new int[]{2, 3, 4, 5}});
        data.add(new Object[]{path + "C-crit-02.litmus", wmm, new int[]{2, 5, 3, 4}});
        data.add(new Object[]{path + "C-crit-03.litmus", wmm, new int[]{3, 4}});
        data.add(new Object[]{path + "C-crit-04.litmus", wmm, new int[]{3, 4}});
        data.add(new Object[]{path + "C-crit-05.litmus", wmm, new int[]{2, 3, 5, 8, 6, 7}});
        data.add(new Object[]{path + "C-crit-06.litmus", wmm, new int[]{2, 11, 3, 6, 4, 5, 7, 10, 8, 9}});
        data.add(new Object[]{path + "C-crit-07.litmus", wmm, new int[]{2, 4}});
        data.add(new Object[]{path + "C-crit-08.litmus", wmm, new int[]{2, 6}});
        data.add(new Object[]{path + "C-crit-09.litmus", wmm, new int[]{2, 7, 8, 10}});
        return data;
    }

    private String path;
    private Wmm wmm;
    private int[] expectedEdges;

    public RelCritTest(String path, Wmm wmm, int[] expectedEdges) {
        this.path = path;
        this.wmm = wmm;
        this.expectedEdges = expectedEdges;
    }

    @Test
    public void test() {
        try{
            Context ctx = new Context();
            Solver solver = ctx.mkSolver(ctx.mkTactic(Dartagnan.TACTIC));
            Program program = new ProgramParser().parse(new File(path));

            // Force encoding all possible "crit" relations
            wmm.setDrawExecutionGraph();
            wmm.addDrawRelations(Arrays.asList("crit"));

            // Sanity check, can be skipped
            assertTrue(Dartagnan.testProgram(solver, ctx, program, wmm, program.getArch(), 1, Mode.KNASTER, Alias.CFIS));

            // Test edges
            EdgeTestHelper helper = new EdgeTestHelper(
                    program,
                    wmm.getRelationRepository().getRelation("crit"),
                    FilterBasic.get(EType.RCU_LOCK),
                    FilterBasic.get(EType.RCU_UNLOCK)
            );
            solver.add(helper.encodeIllegalEdges(expectedEdges, ctx));
            assertSame(Status.UNSATISFIABLE, solver.check());

            ctx.close();

        } catch (IOException e){
            fail("Missing resource file");
        }
    }
}
