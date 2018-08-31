package dartagnan.program.event;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import com.microsoft.z3.*;

import dartagnan.expression.ExprInterface;
import dartagnan.program.Thread;
import dartagnan.utils.MapSSA;
import dartagnan.utils.Pair;

import static dartagnan.utils.Encodings.encodeMissingIndexes;
import static dartagnan.utils.Utils.mergeMaps;

public class If extends Event {

    private ExprInterface pred;
    private Thread t1;
    private Thread t2;

    public If(ExprInterface pred, Thread t1, Thread t2) {
        this.pred = pred;
        this.t1 = t1;
        this.t2 = t2;
        t1.incCondLevel();
        t2.incCondLevel();
    }

    public boolean is(String param){
        return false;
    }

    public String toString() {
        if (t2 instanceof Skip)
            return String.format("%sif (%s) {\n%s\n%s}", nTimesCondLevel(), pred, t1, nTimesCondLevel());
        else
            return String.format("%sif (%s) {\n%s\n%s}\n%selse {\n%s\n%s}", nTimesCondLevel(), pred, t1, nTimesCondLevel(), nTimesCondLevel(), t2, nTimesCondLevel());
    }

    private String nTimesCondLevel() {
        return String.join("", Collections.nCopies(condLevel, "  "));
    }

    public Thread getT1() {
        return t1;
    }

    public Thread getT2() {
        return t2;
    }

    public void setT1(Thread t) {
        t1 = t;
    }

    public void setT2(Thread t) {
        t2 = t;
    }

    public void incCondLevel() {
        condLevel++;
        t1.incCondLevel();
        t2.incCondLevel();
    }

    public void decCondLevel() {
        condLevel--;
        t1.decCondLevel();
        t2.decCondLevel();
    }

    public If unroll(int steps, boolean obsNoTermination) {
        t1 = t1.unroll(steps, obsNoTermination);
        t2 = t2.unroll(steps, obsNoTermination);
        return this;
    }

    public If unroll(int steps) {
        return unroll(steps, false);
    }

    public If compile(String target, boolean ctrl, boolean leading) {
        t1 = t1.compile(target, ctrl, leading);
        t2 = t2.compile(target, ctrl, leading);
        return this;
    }

    public If optCompile(boolean ctrl, boolean leading) {
        t1 = t1.optCompile(ctrl, leading);
        t2 = t2.optCompile(ctrl, leading);
        return this;
    }

    public If allCompile() {
        t1 = t1.allCompile();
        t2 = t2.allCompile();
        return this;
    }

    public If clone() {
        Thread newT1 = t1.clone();
        newT1.decCondLevel();
        Thread newT2 = t2.clone();
        newT2.decCondLevel();
        ExprInterface newPred = pred.clone();
        If newIf = new If(newPred, newT1, newT2);
        newIf.condLevel = condLevel;
        return newIf;
    }

    public void setGuard(BoolExpr guard, Context ctx) {
        t1.setGuard(ctx.mkAnd(guard, myGuard), ctx);
        t2.setGuard(ctx.mkAnd(guard, ctx.mkNot(myGuard)), ctx);
    }

    public void setMainThread(Thread t) {
        this.mainThread = t;
        t1.setMainThread(t);
        t2.setMainThread(t);
    }

    public Integer setEId(Integer i) {
        i = super.setEId(i);
        i = t1.setEId(i);
        i = t2.setEId(i);
        return i;
    }

    public Integer setTId(Integer i) {
        this.tid = i;
        i++;
        i = t1.setTId(i);
        i = t2.setTId(i);
        return i;
    }

    public Set<Event> getEvents() {
        Set<Event> ret = new HashSet<Event>();
        ret.addAll(t1.getEvents());
        ret.addAll(t2.getEvents());
        ret.add(this);
        return ret;
    }

    public Pair<BoolExpr, MapSSA> encodeDF(MapSSA map, Context ctx) throws Z3Exception {
        myGuard = pred.toZ3Boolean(map, ctx);
        if(mainThread == null){
            System.out.println(String.format("Check encodeDF for %s", this));
            return null;
        }
        else {
            MapSSA map1 = map.clone();
            MapSSA map2 = map.clone();

            BoolExpr enc = ctx.mkAnd(ctx.mkImplies(ctx.mkBoolConst(t1.cfVar()), pred.toZ3Boolean(map, ctx)),
                    ctx.mkImplies(ctx.mkBoolConst(t2.cfVar()), ctx.mkNot(pred.toZ3Boolean(map, ctx))));

            Pair<BoolExpr, MapSSA> p1 = t1.encodeDF(map1, ctx);
            enc = ctx.mkAnd(enc, p1.getFirst());
            Pair<BoolExpr, MapSSA> p2 = t2.encodeDF(map2, ctx);
            enc = ctx.mkAnd(enc, p2.getFirst());
            enc = ctx.mkAnd(enc, encodeMissingIndexes(this, map1, map2, ctx));
            map = mergeMaps(map1, map2);
            return new Pair<BoolExpr, MapSSA>(enc, map);
        }
    }

    public ExprInterface getExpr(){
        return pred;
    }

    public BoolExpr encodeCF(Context ctx) throws Z3Exception {
        return ctx.mkAnd(
                ctx.mkEq(ctx.mkBoolConst(cfVar()), ctx.mkXor(ctx.mkBoolConst(t1.cfVar()), ctx.mkBoolConst(t2.cfVar()))),
                ctx.mkEq(ctx.mkBoolConst(cfVar()), executes(ctx)),
                t1.encodeCF(ctx),
                t2.encodeCF(ctx));
    }

    public BoolExpr allExecute(Context ctx) throws Z3Exception {
        return ctx.mkAnd(
                ctx.mkEq(ctx.mkAnd(ctx.mkBoolConst(t1.cfVar()), ctx.mkBoolConst(t2.cfVar())), ctx.mkBoolConst(cfVar())),
                t1.allExecute(ctx),
                t2.allExecute(ctx));
    }
}