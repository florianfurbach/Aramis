package com.dat3m.dartagnan.wmm.relation;

import com.dat3m.dartagnan.wmm.utils.Mode;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.dat3m.dartagnan.program.Program;
import com.dat3m.dartagnan.wmm.utils.Tuple;
import com.dat3m.dartagnan.wmm.utils.TupleSet;

import java.util.HashSet;
import java.util.Set;

import static com.dat3m.dartagnan.utils.Utils.edge;
import com.dat3m.dartagnan.wmm.Execution;
import com.dat3m.dartagnan.wmm.relation.basic.BasisExecRelation;
import com.dat3m.dartagnan.wmm.utils.RelationRepository;
import java.util.HashMap;
import java.util.Map;

/**
 *
 * @author Florian Furbach
 */
public abstract class Relation {

    public static boolean PostFixApprox = false;
    
    public static Execution Exec=null;

    protected String name;
    protected String term;

    protected Program program;
    protected Context ctx;

    protected boolean isEncoded;
    private Mode mode;

    protected TupleSet maxTupleSet;
    protected TupleSet encodeTupleSet;

    protected int recursiveGroupId = 0;
    protected boolean forceUpdateRecursiveGroupId = false;
    protected boolean isRecursive = false;
    protected boolean forceDoEncode = false;

    public Relation() {}

    public Relation(String name) {
        this.name = name;
    }

    public int getRecursiveGroupId(){
        return recursiveGroupId;
    }

    public void setRecursiveGroupId(int id){
        forceUpdateRecursiveGroupId = true;
        recursiveGroupId = id;
    }

    public int updateRecursiveGroupId(int parentId){
        return recursiveGroupId;
    }

    public void initialise(Program program, Context ctx, Mode mode){
        this.program = program;
        this.ctx = ctx;
        this.mode = mode;
        this.maxTupleSet = null;
        this.isEncoded = false;
        encodeTupleSet = new TupleSet();
    }
    
    /**
     *Adds the relation and all its children to the repository.
     * @param rep
     * @return true if the relation was not in the repository
     */
    public boolean addRelations(RelationRepository rep){
        if(!rep.getRelations().contains(this)){
            rep.addRelation(this);
            return true;
        }
        return false;
    }
    
    /**
     * Defines the may pairs according to the given execution
     * @param exec
     * @return
     */
    protected boolean setMaxPairs(Execution exec){
        for (Relation relation : exec.getRelations()) {
            BasisExecRelation brel= (BasisExecRelation) relation;
            if(brel.getOriginalName().equals(this.getName())) {
                maxTupleSet=brel.getMaxTupleSet();
                return true;
            }
        }
        return false;
    }
    
    /**
     * Recursively initializes relations the normal way 
     * except for those that occur in the execution (denoted by setMaxPairs), 
     * here it uses the pairs from the execution
     * @param execution
     * @param ctx
     * @param mode
     */
    public void initialise(Execution execution, Context ctx, Mode mode) {
        this.initialise(execution.getProgram(), ctx, mode);
            setMaxPairs(execution);
    }
    
    /**
     * Initializes the relation with a given maxTupleSet, this is used by Aramis where we switch programs often and we want to avoid recomputing it.
     * @param program
     * @param maxTupleSet
     * @param ctx
     * @param mode
     */
    public void initialise(Program program, Map<Relation, Map<Program, TupleSet>> maxpairs, Context ctx, Mode mode){
        this.initialise(program, ctx, mode);
        if(maxpairs.get(this)==null) maxpairs.put(this, new HashMap<>()); 
        if(maxpairs.get(this).get(program)==null) maxpairs.get(this).put(program, this.getMaxTupleSet());
        this.maxTupleSet = maxpairs.get(this).get(program);
        //this.isEncoded = false;
        //encodeTupleSet = new TupleSet();
    }
    
    public BoolExpr encode(Program p, TupleSet set, Context ctx, Mode mode){
        this.initialise(program, ctx, mode);
        //this.encodeTupleSet=set;
        this.getMaxTupleSet();
        this.addEncodeTupleSet(set);
        BoolExpr value=this.encode();
        return value;
    }
//    public BoolExpr encode(Program p, TupleSet set, Context ctx, Mode mode){
//        Program ptemp=this.program;
//        Context ctxtemp=this.ctx;
//        TupleSet encodedtemp=this.encodeTupleSet;
//        Mode mtemp=this.mode;
//        this.program=p;
//        this.ctx=ctx;
//        this.mode=mode;
//        this.encodeTupleSet=set;
//        BoolExpr value=this.encode();
//        this.program=ptemp;
//        this.ctx=ctxtemp;
//        this.mode=mode;
//        this.encodeTupleSet=encodedtemp;
//        return value;
//    }

    
    public abstract TupleSet getMaxTupleSet();

    public TupleSet getMaxTupleSetRecursive(){
        return getMaxTupleSet();
    }

    public TupleSet getEncodeTupleSet(){
        return encodeTupleSet;
    }

    public void addEncodeTupleSet(TupleSet tuples){
        encodeTupleSet.addAll(tuples);
    }

    public String getName() {
        if(name != null){
            return name;
        }
        return term;
    }

    public Relation setName(String name){
        this.name = name;
        return this;
    }

    public String getTerm(){
        return term;
    }

    public boolean getIsNamed(){
        return name != null;
    }

    @Override
    public String toString(){
        if(name != null){
            return name + " := " + term;
        }
        return term;
    }

    @Override
    public int hashCode(){
        return getName().hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;

        if (obj == null || getClass() != obj.getClass())
            return false;

        return getName().equals(((Relation)obj).getName());
    }

    public BoolExpr encode() {
        if(isEncoded){
            return ctx.mkTrue();
        }
        isEncoded = true;
        return doEncode();
    }

    protected BoolExpr encodeLFP() {
        return encodeApprox();
    }

    protected BoolExpr encodeIDL() {
        return encodeApprox();
    }

    protected abstract BoolExpr encodeApprox();

    public BoolExpr encodeIteration(int recGroupId, int iteration){
        return ctx.mkTrue();
    }

    protected BoolExpr doEncode(){
        BoolExpr enc = encodeNegations();
        if(!encodeTupleSet.isEmpty() || forceDoEncode){
            if(mode == Mode.KLEENE) {
                return ctx.mkAnd(enc, encodeLFP());
            } else if(mode == Mode.IDL) {
                return ctx.mkAnd(enc, encodeIDL());
            }
            return ctx.mkAnd(enc, encodeApprox());
        }
        return enc;
    }

    private BoolExpr encodeNegations(){
        BoolExpr enc = ctx.mkTrue();
        if(!encodeTupleSet.isEmpty()){
            Set<Tuple> negations = new HashSet<>(encodeTupleSet);
            negations.removeAll(maxTupleSet);
            for(Tuple tuple : negations){
                enc = ctx.mkAnd(enc, ctx.mkNot(edge(this.getName(), tuple.getFirst(), tuple.getSecond(), ctx)));
            }
            encodeTupleSet.removeAll(negations);
        }
        return enc;
    }
    
}
