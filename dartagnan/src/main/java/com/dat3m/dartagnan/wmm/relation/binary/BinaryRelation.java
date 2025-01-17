package com.dat3m.dartagnan.wmm.relation.binary;

import com.dat3m.dartagnan.wmm.utils.Mode;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.relation.Relation;
import static com.dat3m.dartagnan.wmm.relation.Relation.Exec;
import com.dat3m.dartagnan.wmm.relation.basic.BasisExecRelation;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import java.util.Map;

/**
 *
 * @author Florian Furbach
 */
public abstract class BinaryRelation extends Relation {

    protected Relation r1;
    protected Relation r2;

    int lastEncodedIteration = -1;

    BinaryRelation(Relation r1, Relation r2) {
        this.r1 = r1;
        this.r2 = r2;
    }

    public BinaryRelation(Relation r1, Relation r2, String name) {
        super(name);
        this.r1 = r1;
        this.r2 = r2;
    }

    @Override
    public int updateRecursiveGroupId(int parentId){
        if(recursiveGroupId == 0 || forceUpdateRecursiveGroupId){
            forceUpdateRecursiveGroupId = false;
            int r1Id = r1.updateRecursiveGroupId(parentId | recursiveGroupId);
            int r2Id = r2.updateRecursiveGroupId(parentId | recursiveGroupId);
            recursiveGroupId |= (r1Id | r2Id) & parentId;
        }
        return recursiveGroupId;
    }

    @Override
    public void initialise(Program program, Context ctx, Mode mode){
        super.initialise(program, ctx, mode);
        lastEncodedIteration = -1;
    }

    @Override
    public boolean addRelations(RelationRepository rep) {
        if(super.addRelations(rep)){
            r1.addRelations(rep);
            r2.addRelations(rep);
            return true;
        }
        return false;
    }

    
    
    @Override
        public void initialise(Execution execution, Context ctx, Mode mode) {
        this.initialise(execution.getProgram(), ctx, mode);
            if(!setMaxPairs(execution)){
                r1.initialise(execution, ctx, mode);
                r2.initialise(execution, ctx, mode);
            }
    }
    
    @Override
    public void initialise(Program program, Map<Relation, Map<Program, TupleSet>> maxpairs, Context ctx, Mode mode) {
        r1.initialise(program, maxpairs, ctx, mode);
        r2.initialise(program, maxpairs, ctx, mode);
        super.initialise(program, maxpairs, ctx, mode); //To change body of generated methods, choose Tools | Templates.
    }

    
    
    @Override
    public void addEncodeTupleSet(TupleSet tuples){
        TupleSet activeSet = new TupleSet();
        activeSet.addAll(tuples);
        activeSet.removeAll(encodeTupleSet);
        encodeTupleSet.addAll(activeSet);
        activeSet.retainAll(maxTupleSet);
        if(!activeSet.isEmpty()){
            r1.addEncodeTupleSet(activeSet);
            r2.addEncodeTupleSet(activeSet);
        }
    }

    @Override
    public BoolExpr encode() {
        if(isEncoded){
            return ctx.mkTrue();
        }
        isEncoded = true;
        return ctx.mkAnd(r1.encode(), r2.encode(), doEncode());
    }

    @Override
    protected BoolExpr encodeLFP() {
        if(recursiveGroupId > 0){
            return ctx.mkTrue();
        }
        return encodeApprox();
    }
}
