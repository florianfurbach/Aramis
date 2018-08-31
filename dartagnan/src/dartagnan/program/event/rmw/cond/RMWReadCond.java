package dartagnan.program.event.rmw.cond;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;
import dartagnan.expression.ExprInterface;
import dartagnan.program.Location;
import dartagnan.program.Register;
import dartagnan.program.event.Load;
import dartagnan.utils.MapSSA;
import dartagnan.utils.Pair;

import static dartagnan.utils.Utils.ssaLoc;
import static dartagnan.utils.Utils.ssaReg;

public abstract class RMWReadCond extends Load {

    protected ExprInterface cmp;
    protected BoolExpr z3Cond;

    public RMWReadCond(Register reg, ExprInterface cmp, Location loc, String atomic) {
        super(reg, loc, atomic);
        this.cmp = cmp;
    }

    public BoolExpr getCond(){
        if(z3Cond == null){
            // encodeDF must be called before encodeCF, otherwise this exception will be thrown
            throw new RuntimeException("z3Cond is requested before it has been initialised in " + this.getClass().getName());
        }
        return z3Cond;
    }

    public Pair<BoolExpr, MapSSA> encodeDF(MapSSA map, Context ctx) throws Z3Exception {
        if(mainThread == null){
            System.out.println(String.format("Check encodeDF for %s", this));
            return null;
        }
        else {
            Expr z3Reg = ssaReg(reg, map.getFresh(reg), ctx);
            Expr z3Loc = ssaLoc(loc, mainThread.getTId(), map.getFresh(loc), ctx);
            this.ssaLoc = z3Loc;
            this.ssaRegIndex = map.get(reg);
            this.z3Cond = ctx.mkEq(z3Reg, encodeValue(map, ctx, cmp));
            return new Pair<BoolExpr, MapSSA>(ctx.mkImplies(executes(ctx), ctx.mkEq(z3Reg, z3Loc)), map);
        }
    }

    private Expr encodeValue(MapSSA map, Context ctx, ExprInterface v){
        if(v instanceof Register){
            return ssaReg((Register) v, map.get(v), ctx);
        }
        return ctx.mkInt(v.toString());
    }
}