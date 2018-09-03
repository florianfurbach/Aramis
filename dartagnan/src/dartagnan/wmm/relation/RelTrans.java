package dartagnan.wmm.relation;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Z3Exception;
import dartagnan.program.Program;
import dartagnan.program.event.Event;
import dartagnan.program.utils.EventRepository;
import dartagnan.utils.Utils;
import dartagnan.wmm.relation.utils.Tuple;

import java.util.*;

/**
 *
 * @author Florian Furbach
 */
public class RelTrans extends UnaryRelation {

    public static String makeTerm(Relation r1){
        return r1.getName() + "^+";
    }

    private Map<Event, Set<Event>> reachabilityMap;

    public RelTrans(Relation r1) {
        super(r1);
        term = makeTerm(r1);
    }

    public RelTrans(Relation r1, String name) {
        super(r1, name);
        term = makeTerm(r1);
    }

    @Override
    public Set<Tuple> getMaxTupleSet(Program program){
        if(maxTupleSet == null){
            maxTupleSet = new HashSet<>();
            reachabilityMap = new HashMap<>();
            for(Tuple pair : r1.getMaxTupleSet(program)){
                reachabilityMap.putIfAbsent(pair.getFirst(), new HashSet<>());
                reachabilityMap.putIfAbsent(pair.getSecond(), new HashSet<>());
                Set<Event> events = reachabilityMap.get(pair.getFirst());
                events.add(pair.getSecond());
            }

            boolean changed = false;
            for(int i = 0; i < reachabilityMap.size(); i++){
                for(Event e1 : reachabilityMap.keySet()){
                    Set<Event> newEls = new HashSet<>();
                    for(Event e2 : reachabilityMap.get(e1)){
                        if(!(e1.getEId().equals(e2.getEId()))){
                            newEls.addAll(reachabilityMap.get(e2));
                        }
                    }
                    if(reachabilityMap.get(e1).addAll(newEls))
                        changed = true;
                }
                if(!changed) break;
            }

            for(Event e1 : reachabilityMap.keySet()){
                for(Event e2 : reachabilityMap.get(e1)){
                    maxTupleSet.add(new Tuple(e1, e2));
                }
            }
        }
        return maxTupleSet;
    }

    @Override
    public void addEncodeTupleSet(Set<Tuple> tuples){
        encodeTupleSet.addAll(tuples);
        Set<Tuple> activeSet = new HashSet<>(tuples);
        activeSet.retainAll(maxTupleSet);
        if(!activeSet.isEmpty()){
            // TODO: Implementation
            r1.addEncodeTupleSet(r1.maxTupleSet);
        }
    }

    @Override
    protected BoolExpr encodeBasic(Program program, Context ctx) throws Z3Exception {
        Collection<Event> events = program.getEventRepository().getEvents(this.eventMask | EventRepository.EVENT_LOCAL | EventRepository.EVENT_IF);
        BoolExpr enc = ctx.mkTrue();
        for (Event e1 : events) {
            for (Event e2 : events) {
                BoolExpr orTrans = ctx.mkFalse();
                for (Event e3 : events) {
                    //e1e2 caused by transitivity:
                    orTrans = ctx.mkOr(orTrans, ctx.mkAnd(Utils.edge(this.getName(), e1, e3, ctx), Utils.edge(this.getName(), e3, e2, ctx),
                            ctx.mkGt(Utils.intCount(this.getName(), e1, e2, ctx), Utils.intCount(this.getName(), e1, e3, ctx)),
                            ctx.mkGt(Utils.intCount(this.getName(), e1, e2, ctx), Utils.intCount(this.getName(), e3, e2, ctx))));
                }
                //r(e1,e2) caused by r1:
                BoolExpr orr1 = Utils.edge(r1.getName(), e1, e2, ctx);
                //allow for recursion in r1:
                if(r1.containsRec){
                    orr1 = ctx.mkAnd(orr1, ctx.mkGt(Utils.intCount(this.getName(), e1, e2, ctx), Utils.intCount(r1.getName(), e1, e2, ctx)));
                }
                enc = ctx.mkAnd(enc, ctx.mkEq(Utils.edge(this.getName(), e1, e2, ctx), ctx.mkOr(orTrans, orr1)));
            }
        }
        return enc;
    }

    @Override
    protected BoolExpr encodeApprox(Program program, Context ctx) throws Z3Exception {
        Collection<Event> events = program.getEventRepository().getEvents(this.eventMask | EventRepository.EVENT_LOCAL | EventRepository.EVENT_IF);
        BoolExpr enc = ctx.mkTrue();
        BoolExpr orclose1 = ctx.mkFalse();
        BoolExpr orclose2 = ctx.mkFalse();

        for (Event e1 : events) {
            for (Event e2 : events) {
                //transitive
                BoolExpr orClause = ctx.mkFalse();
                for (Event e3 : events) {
                    orClause = ctx.mkOr(orClause, ctx.mkAnd(Utils.edge(this.getName(), e1, e3, ctx), Utils.edge(this.getName(), e3, e2, ctx)));
                    if(Relation.CloseApprox){
                        orclose1 = ctx.mkOr(orclose1, Utils.edge(r1.getName(), e1, e3, ctx));
                        orclose2 = ctx.mkOr(orclose2, Utils.edge(r1.getName(), e3, e2, ctx));
                    }
                }
                //original relation
                orClause = ctx.mkOr(orClause, Utils.edge(r1.getName(), e1, e2, ctx));
                //putting it together:
                if(Relation.CloseApprox){
                    enc = ctx.mkAnd(enc, ctx.mkImplies(Utils.edge(this.getName(), e1, e2, ctx), ctx.mkAnd(orclose1, orclose2)));
                }
                if(Relation.PostFixApprox) {
                    enc = ctx.mkAnd(enc, ctx.mkImplies(orClause, Utils.edge(this.getName(), e1, e2, ctx)));
                } else {
                    enc = ctx.mkAnd(enc, ctx.mkEq(Utils.edge(this.getName(), e1, e2, ctx), orClause));
                }
            }
        }
        return enc;
    }
}