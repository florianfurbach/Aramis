package com.dat3m.dartagnan.wmm.relation.basic;

import com.dat3m.dartagnan.program.event.Event;
import com.dat3m.dartagnan.program.utils.EType;
import com.dat3m.dartagnan.wmm.filter.FilterBasic;
import com.dat3m.dartagnan.wmm.utils.Tuple;
import com.dat3m.dartagnan.wmm.utils.TupleSet;

public class RelId extends BasicRelation {

    public RelId(){
        term = "id";
    }

    @Override
    public TupleSet getMaxTupleSet(){
        if(maxTupleSet == null){
            maxTupleSet = new TupleSet();
            for(Event e : program.getCache().getEvents(FilterBasic.get(EType.VISIBLE))){
                maxTupleSet.add(new Tuple(e, e));
            }
        }
        return maxTupleSet;
    }
}
