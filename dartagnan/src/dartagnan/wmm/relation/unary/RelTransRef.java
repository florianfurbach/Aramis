package dartagnan.wmm.relation.unary;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Z3Exception;
import dartagnan.program.Program;
import dartagnan.program.event.Event;
import dartagnan.program.utils.EventRepository;
import dartagnan.utils.Utils;
import dartagnan.wmm.relation.Relation;
import dartagnan.wmm.utils.Tuple;
import dartagnan.wmm.utils.TupleSet;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author Florian Furbach
 */
public class RelTransRef extends RelTrans {

    private TupleSet identityEncodeTupleSet = new TupleSet();
    private TupleSet transEncodeTupleSet = new TupleSet();

    public static String makeTerm(Relation r1){
        return r1.getName() + "^*";
    }

    public RelTransRef(Relation r1) {
        super(r1);
        term = makeTerm(r1);
    }

    public RelTransRef(Relation r1, String name) {
        super(r1, name);
        term = makeTerm(r1);
    }

    @Override
    public void initialise(Program program, Context ctx, int encodingMode){
        super.initialise(program, ctx, encodingMode);
        identityEncodeTupleSet = new TupleSet();
        transEncodeTupleSet = new TupleSet();
    }

    @Override
    public TupleSet getMaxTupleSet(){
        if(maxTupleSet == null){
            super.getMaxTupleSet();
            for (Map.Entry<Event, Set<Event>> entry : transitiveReachabilityMap.entrySet()) {
                entry.getValue().remove(entry.getKey());
            }
            for(Event e : program.getEventRepository().getEvents(EventRepository.EVENT_ALL)){
                maxTupleSet.add(new Tuple(e, e));
            }
        }
        return maxTupleSet;
    }

    @Override
    public void addEncodeTupleSet(TupleSet tuples){
        TupleSet activeSet = new TupleSet();
        activeSet.addAll(tuples);
        activeSet.removeAll(encodeTupleSet);
        encodeTupleSet.addAll(activeSet);
        activeSet.retainAll(maxTupleSet);

        for(Tuple tuple : activeSet){
            if(tuple.getFirst().getEId().equals(tuple.getSecond().getEId())){
                identityEncodeTupleSet.add(tuple);
            }
        }
        activeSet.removeAll(identityEncodeTupleSet);

        TupleSet temp = encodeTupleSet;
        encodeTupleSet = transEncodeTupleSet;
        super.addEncodeTupleSet(activeSet);
        encodeTupleSet = temp;
    }

    @Override
    protected BoolExpr encodeApprox() throws Z3Exception {
        return invokeEncode("encodeApprox");
    }

    @Override
    protected BoolExpr encodeIDL() throws Z3Exception {
        return invokeEncode("encodeIDL");
    }

    @Override
    protected BoolExpr encodeLFP() throws Z3Exception {
        return invokeEncode("encodeLFP");
    }

    private BoolExpr invokeEncode(String methodName){
        try{
            MethodHandle method = MethodHandles.lookup().findSpecial(RelTrans.class, methodName,
                    MethodType.methodType(BoolExpr.class), RelTransRef.class);

            TupleSet temp = encodeTupleSet;
            encodeTupleSet = transEncodeTupleSet;
            BoolExpr enc = (BoolExpr)method.invoke(this);
            encodeTupleSet = temp;

            for(Tuple tuple : identityEncodeTupleSet){
                enc = ctx.mkAnd(enc, Utils.edge(this.getName(), tuple.getFirst(), tuple.getFirst(), ctx));
            }
            return enc;

        } catch (Throwable e){
            e.printStackTrace();
            throw new RuntimeException("Failed to encode relation " + this.getName());
        }
    }
}