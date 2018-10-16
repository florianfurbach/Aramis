package dartagnan.wmm.relation.basic;

import dartagnan.program.event.Event;
import dartagnan.program.event.filter.FilterAbstract;
import dartagnan.wmm.utils.Tuple;
import dartagnan.wmm.utils.TupleSet;

import java.util.Collection;

public class RelCartesian extends BasicRelation {
    private FilterAbstract filter1;
    private FilterAbstract filter2;

    public static String makeTerm(FilterAbstract filter1, FilterAbstract filter2){
        return "(" + filter1 + "*" + filter2 + ")";
    }

    public RelCartesian(FilterAbstract filter1, FilterAbstract filter2) {
        this.filter1 = filter1;
        this.filter2 = filter2;
        this.term = makeTerm(filter1, filter2);
    }

    public RelCartesian(FilterAbstract filter1, FilterAbstract filter2, String name) {
        super(name);
        this.filter1 = filter1;
        this.filter2 = filter2;
        this.term = makeTerm(filter1, filter2);
    }

    @Override
    public TupleSet getMaxTupleSet(){
        if(maxTupleSet == null){
            maxTupleSet = new TupleSet();
            Collection<Event> eventsStart = program.getEventRepository().getEvents(filter1.toRepositoryCode());
            Collection<Event> eventsEnd = program.getEventRepository().getEvents(filter2.toRepositoryCode());
            for(Event e1 : eventsStart){
                if(filter1.filter(e1)){
                    for(Event e2 : eventsEnd){
                        if(filter2.filter(e2)){
                            maxTupleSet.add(new Tuple(e1, e2));
                        }
                    }
                }
            }
        }
        return maxTupleSet;
    }
}