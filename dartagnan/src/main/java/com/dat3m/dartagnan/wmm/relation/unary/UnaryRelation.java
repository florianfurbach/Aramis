package com.dat3m.dartagnan.wmm.relation.unary;

import com.dat3m.dartagnan.wmm.utils.Mode;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.relation.Relation;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import com.dat3m.dartagnan.wmm.utils.TupleSet;
import java.util.Map;

/**
 *
 * @author Florian Furbach
 */
public abstract class UnaryRelation extends Relation {

    protected Relation r1;

    UnaryRelation(Relation r1) {
        this.r1 = r1;
    }

    UnaryRelation(Relation r1, String name) {
        super(name);
        this.r1 = r1;
    }

    @Override
    public int updateRecursiveGroupId(int parentId){
        if(recursiveGroupId == 0 || forceUpdateRecursiveGroupId){
            forceUpdateRecursiveGroupId = false;
            int r1Id = r1.updateRecursiveGroupId(parentId | recursiveGroupId);
            recursiveGroupId |= r1Id & parentId;
        }
        return recursiveGroupId;
    }

    @Override
    public void initialise(Program program, Context ctx, Mode mode){
        super.initialise(program, ctx, mode);
        if(recursiveGroupId > 0){
            throw new RuntimeException("Recursion is not implemented for " + this.getClass().getName());
        }
    }

    @Override
    public void initialise(Execution execution, Context ctx, Mode mode) {
        this.initialise(execution.getProgram(), ctx, mode);
            if(!setMaxPairs(execution)){
                r1.initialise(execution, ctx, mode);
            }
    }

    @Override
    public boolean addRelations(RelationRepository rep) {
        if(super.addRelations(rep)){
            r1.addRelations(rep);
            return true;
        }
        return false;    }
    
    
    
    @Override
    public void initialise(Program program, Map<Relation, Map<Program, TupleSet>> maxpairs, Context ctx, Mode mode) {
        r1.initialise(program, maxpairs, ctx, mode);
        super.initialise(program, maxpairs, ctx, mode); //To change body of generated methods, choose Tools | Templates.
    }
    
    

    @Override
    public BoolExpr encode() {
        if(isEncoded){
            return ctx.mkTrue();
        }
        isEncoded = true;
        return ctx.mkAnd(r1.encode(), doEncode());
    }
}
