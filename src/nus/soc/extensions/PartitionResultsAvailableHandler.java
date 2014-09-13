package nus.soc.extensions;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Local;
import soot.PackManager;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.infoflow.InfoflowResults;
import soot.jimple.infoflow.InfoflowResults.SinkInfo;
import soot.jimple.infoflow.InfoflowResults.SourceInfo;
import soot.jimple.infoflow.aliasing.Aliasing;
import soot.jimple.infoflow.aliasing.PtsBasedAliasStrategy;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.handlers.ResultsAvailableHandler;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.util.BaseSelector;

class SourceAbstractionAndStmt 
{
	Abstraction abs;
	Stmt stmt;
	
	public SourceAbstractionAndStmt(Abstraction abs)
	{
		this.abs = abs.getPredecessor();
		this.stmt = abs.getCurrentStmt();
	}
	
	public SourceAbstractionAndStmt(Abstraction succ, Stmt stmt)
	{
		this.abs = succ;
		this.stmt = stmt;
	}
	
	public Abstraction getAbstraction()
	{
		return abs;
	}
	
	public Stmt getStmt()
	{
		return stmt;
	}
	
	@Override
	public boolean equals(Object obj)
	{
		if (super.equals(obj))
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		SourceAbstractionAndStmt other = (SourceAbstractionAndStmt) obj;
		
		return (abs.equals(other.getAbstraction()) &&
				stmt.equals(other.getStmt()));
	}

	@Override
	public int hashCode()
	{
			final int prime = 31;
			int result = 1;
			result = prime * result + ((stmt == null) ? 0 : stmt.hashCode());
			result = prime * result + ((abs == null) ? 0 : abs.hashCode());
			return result;
	}
}
public final class PartitionResultsAvailableHandler implements ResultsAvailableHandler {
	private static final String PROXY_SUFIX = "_proxy";
	//private final BufferedWriter wr;
	private final Logger logger;
	SootClass teeService, teeObject;
	SootMethod teeObjectConstructor, teeService$getData, teeService$setData;
	
	HashMap<SootMethod,Integer> methodRepresentationCounter;
	HashMap<SootMethodContext,SootMethod> methodRepresentations;
	HashMap<SootMethodContext,Integer> methodContextSliceCounter;
	HashSet<SootMethodContext> methodContextLog;
	HashMap<SootMethodContext, Boolean> methodContextNeedsRefactorCache;
	HashMap<SootMethodContext, Set<Abstraction>> worklist;
	
	Aliasing aliasing;
	private static HashMap<Value, Value> proxyCache;
	Set<SootClass> pathClasses;
	//HashSet<SourceAbstractionAndStmt> processedStmts;

	static final Set<Abstraction> zeroSet = Collections.singleton(TaintedStmtTag.getZeroAbstraction());
	
	public PartitionResultsAvailableHandler() {
	//	this.wr = null;
		this.logger = LoggerFactory.getLogger(getClass());
		methodRepresentationCounter = new HashMap<SootMethod,Integer>();
		methodRepresentations = new HashMap<SootMethodContext, SootMethod>();
		//processedStmts = new HashSet<SourceAbstractionAndStmt>();
		methodContextSliceCounter = new HashMap<SootMethodContext, Integer>();
		methodContextLog = new HashSet<SootMethodContext>();
		methodContextNeedsRefactorCache = new HashMap<SootMethodContext, Boolean>();
		
		worklist = new HashMap<SootMethodContext, Set<Abstraction>>();
		
		proxyCache = new HashMap<Value, Value>();
		pathClasses = new HashSet<SootClass>();
	}

	/*
	public PartitionResultsAvailableHandler(BufferedWriter wr) {
		this.wr = wr;
		this.logger = LoggerFactory.getLogger(getClass());
	}
	*/
	@Override
	public void onResultsAvailable(IInfoflowCFG cfg, InfoflowResults results) {
		// Dump the results
		if (results == null) {
			print("No results found.");
			return;
		}

		aliasing = new Aliasing(new PtsBasedAliasStrategy(cfg), cfg);
		createTEEServiceAndObjectClasses();
		
		for (SinkInfo sink : results.getResults().keySet()) {
			print("Found a flow to sink " + sink + ", from the following sources:");
			for (SourceInfo source : results.getResults().get(sink)) {
				print("\t- " + source.getSource() + " (in "
						+ cfg.getMethodOf(source.getContext()).getSignature()  + ")");
				
				// Put source context method in worklist
				worklist.put(new SootMethodContext(cfg.getMethodOf(source.getContext()), zeroSet),
						zeroSet);
			}
		}
		
		// Process worklist
		while(!worklist.isEmpty()) {
			Entry<SootMethodContext, Set<Abstraction>> firstInWorklist = worklist.entrySet().iterator().next();
			SootMethodContext smc = firstInWorklist.getKey();
			Set<Abstraction> callerD1s = firstInWorklist.getValue();
			
			if (!methodContextLog.contains(smc))
			{
				pathClasses.add(smc.getMethod().getDeclaringClass());	
				
				logger.info("LUCIA: processMethodContext {}", smc);
				processMethodContext(cfg, smc, callerD1s);
				methodContextLog.add(smc);
			}
			
			worklist.remove(smc);
		}
		
		for (SootClass cls: pathClasses)
		{
			logger.info("LUCIA: pathClass {}", cls);
			cls.setApplicationClass();
		}
		
		/*
		Options.v().setPhaseOption("jb.dae", "off");
		Options.v().setPhaseOption("jj.dae", "off");
		Options.v().setPhaseOption("jop.dae", "off");
		*/
		//Options.v().setPhaseOption("jop.ule", "off");
		PackManager.v().runPacks();
		PackManager.v().writeOutput();
		// Write output only for classes along the path
					
	}

	public void createTEEServiceAndObjectClasses()
	{
		SootClass objClass = Scene.v().getSootClass("java.lang.Object");
		
		Scene.v().loadClassAndSupport("java.lang.Object");
		teeService = new SootClass("TEEServices", Modifier.PUBLIC);
		teeService.setSuperclass(objClass);
		Scene.v().addClass(teeService);
		teeService.setApplicationClass();
		
		teeService$getData = new SootMethod("getData",
				Arrays.asList(new Type[] {objClass.getType()}),
				objClass.getType(),
				Modifier.PUBLIC | Modifier.STATIC | Modifier.NATIVE);
		teeService.addMethod(teeService$getData);
		
		teeService$setData = new SootMethod("setData",
				Arrays.asList(new Type[] {objClass.getType(), objClass.getType()}),
				VoidType.v(),
				Modifier.PUBLIC | Modifier.STATIC | Modifier.NATIVE);
		teeService.addMethod(teeService$setData);
		
		teeObject = new SootClass("TEEObject", Modifier.PUBLIC);
		teeObject.setSuperclass(Scene.v().getSootClass("java.lang.Object"));
		teeObject.setApplicationClass();
		
		createTEEObjectConstructor();
	}
	
	// Used model from: http://ptolemy.eecs.berkeley.edu/ptolemyII/ptII8.1/ptII/ptolemy/copernicus/kernel/EntitySootClass.java
	// FIXME: include License
    private void createTEEObjectConstructor() {
        // Create the constructor
    	SootClass objectClass = Scene.v().getSootClass("java.lang.Object");
    	SootMethod superConstructor = objectClass.getMethodByName("<init>");
    	
        teeObjectConstructor = new SootMethod("<init>", superConstructor
                .getParameterTypes(), superConstructor.getReturnType(),
                superConstructor.getModifiers());


		teeObject.addMethod(teeObjectConstructor);
		
        // create empty body
        JimpleBody body = Jimple.v().newBody(teeObjectConstructor);

        // Add this and read the parameters into locals
        body.insertIdentityStmts();
        teeObjectConstructor.setActiveBody(body);

        PatchingChain<Unit> units = body.getUnits();
        Local thisLocal = body.getThisLocal();

        // get a list of the locals that reference the parameters of the
        // constructor.
        List<Local> parameterList = new ArrayList();
        parameterList.addAll(body.getLocals());
        parameterList.remove(thisLocal);

        // Call the super constructor.
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(thisLocal,
                        superConstructor.makeRef(), parameterList)));
    }

	private void processMethodContext(IInfoflowCFG cfg, SootMethodContext methodContext, Set<Abstraction> callerD1s)
	{
		SootMethod method = methodContext.getMethod();
		Set<Abstraction> d1s = methodContext.getD1s();
		
		if(methodContextNeedsRefactor(methodContext))
		{
			SootMethod refactorMethod = getRepresentationForMethodContext(methodContext);
			
			PatchingChain<Unit> unitChain = method.getActiveBody().getUnits();
			HashMap<Unit, LinkedList<Unit>> replaceUnits = new HashMap<Unit, LinkedList<Unit>>();
			//HashMap<Local,Local> teeObjects;
			
			for (Unit unit: unitChain)
			{
				MethodData methodData = new MethodData();
				Stmt refactorStmt = processStmt(cfg, (Stmt) unit, d1s, callerD1s, methodData, null);
				
				if(methodData.isEmpty()) {
					if(refactorStmt != null) {
						logger.error("LUCIA: replaceUnits {} with\n\t\t{}", unit, refactorStmt);
						replaceUnits.put(unit, new LinkedList<Unit>(Arrays.asList(new Unit[]{refactorStmt})));
					}
					continue;
				}
				
				String name = refactorMethod.getDeclaringClass().getShortName() + "$" +
						refactorMethod.getName() + "$slice" + 
						newSliceInMethodContext(methodContext);
				logger.error("LUCIA: methodName {}", name);
				SootMethod newMethodSlice = methodData.newMethodSliceFromData(name);
				teeService.addMethod(newMethodSlice);
				
				// Create replacer stmts
				// Create call for method slice as TEE Service
				StaticInvokeExpr ie = Jimple.v().newStaticInvokeExpr(
						newMethodSlice.makeRef(), methodData.params);
				Stmt methodSliceCallStmt = Jimple.v().newInvokeStmt(ie);
				
				// Create NewExpr initialization for return taints
				LinkedList<Unit> refactorUnitList = methodData.getTaintRetInitialization();
				refactorUnitList.add(methodSliceCallStmt);
				
				// Make sure to replace original stmt with the replacer stmts
				// Cannot replace directly inside iterator
				replaceUnits.put(unit, refactorUnitList);
			}

			// FIXME: Copy old method to new refactorMethod
			PatchingChain<Unit> refactorChain = refactorMethod.getActiveBody().getUnits();
			
			// Make sure there is a replaceUnit for every unit
			// We cannot add the same units because of their connections with the old method body
			for (Unit unit: unitChain) {
				LinkedList<Unit> refactorUnits = replaceUnits.get(unit);
				if(refactorUnits == null) {
					refactorUnits = new LinkedList<Unit>();
					refactorUnits.add((Unit)unit.clone());
					replaceUnits.put(unit,  refactorUnits);
				}
			}
			
			// Refactor units
			for (Unit unit: unitChain) {
				LinkedList<Unit> refactorUnits = replaceUnits.get(unit);
				// Fix branch targets
				for (Unit refactorUnit : refactorUnits)
				{
					if (refactorUnit.branches())
					{
						List<UnitBox> targets = refactorUnit.getUnitBoxes();
						for(UnitBox targetBox: targets)
							targetBox.setUnit(replaceUnits.get(targetBox.getUnit()).getFirst());
					}
				}
				
				// Add to new chain
				refactorChain.addAll(refactorUnits);
			}
			
			// Add new Locals from def and use boxes if needed
			for(Unit unit: refactorChain) {
				
				List<ValueBox> valueBoxes = unit.getUseAndDefBoxes();
				for(ValueBox valueBox: valueBoxes) {
					if(valueBox.getValue() instanceof Local &&
							! refactorMethod.getActiveBody().getLocals().contains(valueBox.getValue())) {
						
						refactorMethod.getActiveBody().getLocals().add((Local) valueBox.getValue());
					}
				}
			}
		}	
	}

	public Integer newSliceInMethodContext(SootMethodContext sm)
	{
		Integer counter = methodContextSliceCounter.get(sm);
		if(counter == null)
			counter = new Integer(0);
		else 
			counter = new Integer(counter.intValue() + 1);
		methodContextSliceCounter.put(sm, counter);
		return counter;
	}
	
	public SootMethod getRepresentationForMethodContext(SootMethodContext smc)
	{
		assert (methodContextNeedsRefactor(smc));

		logger.error("LUCIA: getRepresentationForMethodContext {}", smc);
		if(methodRepresentations.containsKey(smc)) {
			logger.error("LUCIA: old representation: {}", methodRepresentations.get(smc).getName());
			return methodRepresentations.get(smc);
		}
		
		SootMethod method = smc.getMethod();
		Integer counter = newRepresentationForMethod(method);
		String refactorName = method.getName() + counter;
		SootMethod refactorMethod = new SootMethod(refactorName,
				method.getParameterTypes(), method.getReturnType(),
				method.getModifiers());
		
		JimpleBody body = Jimple.v().newBody();
		body.setMethod(refactorMethod);
		refactorMethod.setActiveBody(body);
		
		method.getDeclaringClass().addMethod(refactorMethod);
		
		logger.error("LUCIA: new representation {}", refactorMethod.getName());
		methodRepresentations.put(smc, refactorMethod);
		return refactorMethod;
	}
	
	public Integer newRepresentationForMethod(SootMethod m)
	{
		Integer counter = methodRepresentationCounter.get(m);
		if(counter == null)
			counter = new Integer(0);
		else
			counter = new Integer(counter.intValue() + 1);
		methodRepresentationCounter.put(m, counter);
		return counter;
	}

	private Stmt processStmt(IInfoflowCFG cfg,
			Stmt stmt,
			Set<Abstraction> d1s,
			Set<Abstraction> callerD1s, MethodData methodData,
			Stmt refactorStmt) {
		TaintedStmtTag tag = (TaintedStmtTag) stmt.getTag(TaintedStmtTag.TAG_NAME);
		if (tag == null) {
			logger.error("[NUS][Tag] Untagged stmt {}", stmt);
			
			if(stmt instanceof IdentityStmt)
				refactorStmt = processIdentityStmt(cfg.getMethodOf(stmt),
						(IdentityStmt) stmt, d1s, (IdentityStmt) refactorStmt);
			return refactorStmt;
		}
		
		if(cfg.isCallStmt(stmt)) {
			Set<SourceFlowAndType> sfatSet = tag.getSourceFlowAndTypeSet(d1s);
			for (SourceFlowAndType sfat: sfatSet)
				refactorStmt = processCallStmt(stmt, d1s, sfat, methodData, refactorStmt);
	
			// Refactor function name in method call if necessary
			SootMethod methodCalled = stmt.getInvokeExpr().getMethod();
			Set<Abstraction> calleeD1s = TaintedStmtTag.getCalleeD1s(stmt, d1s);
			SootMethodContext calleeContext = new SootMethodContext(methodCalled, calleeD1s);
			if(methodContextNeedsRefactor(calleeContext))
			{
				// Add to worklist
				worklist.put(calleeContext, d1s);
				
				// Refactor
				SootMethod methodToCall = getRepresentationForMethodContext(calleeContext);
				if (!methodToCall.equals(methodCalled)) {
					if (refactorStmt == null)
						refactorStmt = (Stmt) stmt.clone();
					refactorStmt = refactorCalleeSignature(refactorStmt, methodToCall);
				}
			}
		}
		else if(cfg.isExitStmt(stmt)) {
			Set<SourceFlowAndType> sfatSet = tag.getSourceFlowAndTypeSet(callerD1s);
			for (SourceFlowAndType sfat: sfatSet)
				refactorStmt = processExitStmt(stmt, d1s, sfat, refactorStmt);
		}
		else {
			Set<SourceFlowAndType> sfatSet = tag.getSourceFlowAndTypeSet(d1s);
			for (SourceFlowAndType sfat: sfatSet)
				refactorStmt = processNormalStmt(stmt, sfat, methodData, refactorStmt);
		}
		
		return refactorStmt;
	}
	 
	private Stmt refactorCalleeSignature(Stmt refactorCallStmt, SootMethod methodToCall) {
		InstanceInvokeExpr iie;
	
		// Refactor methodToCall argument types
		List<Value> callArgs = refactorCallStmt.getInvokeExpr().getArgs();
		List<Type> callArgsTypes = methodToCall.getParameterTypes();

		Type refactorArgsTypes[] = new Type[callArgsTypes.size()];
		callArgsTypes.toArray(refactorArgsTypes);
		
		for(int i = 0; i < callArgs.size(); i++) {
			if(! callArgsTypes.get(i).equals(callArgs.get(i).getType())) {
				refactorArgsTypes[i] = callArgs.get(i).getType();
			}
		}
		
		methodToCall.setParameterTypes(Arrays.asList(refactorArgsTypes));
		
		// Refactor methodToCall return type
		if(refactorCallStmt instanceof AssignStmt &&
				! methodToCall.getReturnType().equals(
						((AssignStmt) refactorCallStmt).getLeftOp().getType()))
			methodToCall.setReturnType(((AssignStmt) refactorCallStmt).getLeftOp().getType());
		
		// Refactor method name
		if (refactorCallStmt.getInvokeExpr() instanceof VirtualInvokeExpr) {
			iie = (VirtualInvokeExpr) refactorCallStmt.getInvokeExpr();
			refactorCallStmt.getInvokeExprBox().setValue(
					Jimple.v().newVirtualInvokeExpr(
							(Local) iie.getBase(), methodToCall.makeRef(), iie.getArgs()));
			
		} else if(refactorCallStmt.getInvokeExpr() instanceof SpecialInvokeExpr) {
			iie = (SpecialInvokeExpr) refactorCallStmt.getInvokeExpr();
			refactorCallStmt.getInvokeExprBox().setValue(
					Jimple.v().newSpecialInvokeExpr(
							(Local) iie.getBase(), methodToCall.makeRef(), iie.getArgs()));
			
		} else if(refactorCallStmt.getInvokeExpr() instanceof InterfaceInvokeExpr) {
			iie = (InterfaceInvokeExpr) refactorCallStmt.getInvokeExpr();
			refactorCallStmt.getInvokeExprBox().setValue(
					Jimple.v().newInterfaceInvokeExpr(
							(Local) iie.getBase(), methodToCall.makeRef(), iie.getArgs()));
		} else if(refactorCallStmt.getInvokeExpr() instanceof StaticInvokeExpr) {
			StaticInvokeExpr sie = (StaticInvokeExpr) refactorCallStmt.getInvokeExpr();
			refactorCallStmt.getInvokeExprBox().setValue(
					Jimple.v().newStaticInvokeExpr(methodToCall.makeRef(), sie.getArgs()));
		} else
			//FIXME: support other types of InvokeExpr
			throw new UnsupportedOperationException("Unsupported type of InvokeExpr " + refactorCallStmt);
		
		return refactorCallStmt;
	}

	public Stmt processIdentityStmt(SootMethod sm, IdentityStmt stmt, Set<Abstraction> d1s, IdentityStmt refactorStmt) {
		Value leftValue = stmt.getLeftOp();
		if(! (stmt.getRightOp() instanceof ParameterRef))
			return refactorStmt;
		
		int paramIndex = ((ParameterRef) stmt.getRightOp()).getIndex();
		
		for(Abstraction d1: d1s) {
			// Refactor parameter assignments x = param0 with taint_x = param0 if d1s contains x (BUT NOT x.f)
			// Also ensure right parameter type in identity stmt
			if(aliasing.mayAlias(leftValue, d1.getAccessPath().getPlainValue()) &&
					d1.getAccessPath().getFieldCount() == 0) {
				if(refactorStmt == null)
					refactorStmt = (IdentityStmt) stmt.clone();
				refactorStmt.getLeftOpBox().setValue(getProxyValue(leftValue));
				refactorStmt = Jimple.v().newIdentityStmt(
						getProxyValue(leftValue),
						Jimple.v().newParameterRef(
								getProxyValue(leftValue).getType(),
								paramIndex));
			}
		}
		
		return refactorStmt;
	}

	public boolean methodContextNeedsRefactor(SootMethodContext smc)
	{
		SootMethod sm = smc.getMethod();
		Set<Abstraction> d1s = smc.getD1s();
		
		if(methodContextNeedsRefactorCache.containsKey(smc))
			return methodContextNeedsRefactorCache.get(smc);
		
		if(!sm.hasActiveBody())
			return false;
			
		PatchingChain<Unit> unitChain = sm.getActiveBody().getUnits();
		boolean hasStmtThatNeedsRefactor = false;
		
		for(Unit unit: unitChain) {
			// Get tags
			TaintedStmtTag tag = (TaintedStmtTag) ((Stmt) unit).getTag(TaintedStmtTag.TAG_NAME);
			if (tag != null) {
				Set<SourceFlowAndType> sfatSet = tag.getSourceFlowAndTypeSet(d1s);
				if(!sfatSet.isEmpty()) {
					// For each source in set
					for(SourceFlowAndType sfat: sfatSet) {
						// If source is active
						if(sfat.getSource().isAbstractionActive()) {
							
							// For each value used in stmt
							for(ValueBox useBox: unit.getUseBoxes()) {
								if(!AccessPath.canContainValue(useBox.getValue()))
									continue;
								AccessPath valueAP = new AccessPath(useBox.getValue(), false);
								AccessPath mappedAP = aliasing.mayAlias(sfat.getSource().getAccessPath(), valueAP);
								
								// Check if mappedAP is equal to the value used (not more specific)
								if(mappedAP != null && mappedAP.entails(valueAP)) {
									logger.error("LUCIA hasStmtThatNeedsRefactor:\n\t\tmappedAP {}\n\t\tsource {}\n\t\tvalueAP {}", mappedAP, sfat.getSource(), valueAP);
									
									hasStmtThatNeedsRefactor = true;
									break;
								}	
							}
							
							// For each value defined in stmt
							for(ValueBox defBox: unit.getDefBoxes()) {
								if(!AccessPath.canContainValue(defBox.getValue()))
									continue;
								AccessPath valueAP = new AccessPath(defBox.getValue(), false);
								AccessPath mappedAP = aliasing.mayAlias(sfat.getSuccessor().getAccessPath(), valueAP);
								
								// Check if mappedAP is equal to the value used (not more specific)
								if(mappedAP != null && mappedAP.entails(valueAP)) {
									logger.error("LUCIA hasStmtThatNeedsRefactor:\n\t\tmappedAP {}\n\t\tsuccessor {}\n\t\tvalueAP {}", mappedAP, sfat.getSuccessor(), valueAP);
									
									hasStmtThatNeedsRefactor = true;
									break;
								}
							}
							
							if(hasStmtThatNeedsRefactor)
								break;
						}
					}
					if(hasStmtThatNeedsRefactor)
						break;
				}
			}
		}
		if(hasStmtThatNeedsRefactor)
			logger.error("LUCIA: hasStmtThatNeedsRefactor smc {} = {}", smc, hasStmtThatNeedsRefactor);
		methodContextNeedsRefactorCache.put(smc, hasStmtThatNeedsRefactor);
		return hasStmtThatNeedsRefactor;
	}
	
	public Stmt processCallStmt(Stmt stmt,
			Set<Abstraction> d1s,
			SourceFlowAndType sfat,
			MethodData methodData,
			Stmt refactorStmt)
	{

		if(sfat.getType() == TaintSourceType.CALL_BASE ||
				sfat.getType() == TaintSourceType.CALL_PARAM ||
				TaintedStmtTag.isCallsiteReturnType(sfat.getType())) {
			
			refactorStmt = refactorCallStmt(stmt, d1s, sfat, refactorStmt);
			return refactorStmt;
		}
		
		Abstraction source = sfat.getSource();
		Abstraction dest = sfat.getSuccessor();
		TaintSourceType type = sfat.getType();
		logger.error("[NUS][TAG] Tagged stmt({})\n\t\tsource({})\n\t\tabs({})\n\t\ttype({})",
				stmt, source, dest, type);
		
		if(!source.isAbstractionActive())
			return refactorStmt;
		
		boolean baseTaintSource = (type == TaintSourceType.WRAPPER_CALL_BASE ||
				type == TaintSourceType.WRAPPER_CALL_BASE_USE ||
				type == TaintSourceType.SINK_BASE);
		boolean paramTaintSource = (type == TaintSourceType.WRAPPER_CALL_PARAM ||
				type == TaintSourceType.WRAPPER_CALL_PARAM_USE ||
				type == TaintSourceType.SINK_PARAM);
		
		// Process base
		if(stmt.getInvokeExpr() instanceof InstanceInvokeExpr)
		{
			InstanceInvokeExpr iie = (InstanceInvokeExpr) stmt.getInvokeExpr();
			Value base = iie.getBase();
			// Add base as a paramTaint of the new method
			if (baseTaintSource) {
				assert aliasing.mayAlias(base, source.getAccessPath().getPlainValue());
				
				methodData.addTaintParam(base, true);
				methodData.addTaintRet(base, true);
			// Add base as returnTaints of the new method
			} else if (paramTaintSource) {
				if(aliasing.mayAlias(base, dest.getAccessPath().getPlainValue())) {
					methodData.addTaintParam(base, false);
					methodData.addTaintRet(base, true);
				} else {
					methodData.addTaintParam(base, false);
				}
			} else if (type == TaintSourceType.SOURCE) {
				methodData.addTaintParam(base, false);
			} else
				throw new UnsupportedOperationException("process base");
		}
		
		// Process method call params
		InvokeExpr ie = stmt.getInvokeExpr();
		if(ie.getArgs() != null)
		{
			int paramCount = ie.getArgCount(); 
			for(int i = 0; i < paramCount; i++)
			{
				if(ie.getArg(i) instanceof Constant)
					continue;
				
				if(paramTaintSource) {
					if(aliasing.mayAlias(ie.getArg(i), source.getAccessPath().getPlainValue())) {
						methodData.addTaintParam(ie.getArg(i), true);
					} else {
						methodData.addTaintParam(ie.getArg(i), false);
					}
				} else if(baseTaintSource || type == TaintSourceType.SOURCE) {
					methodData.addTaintParam(ie.getArg(i), false);
				} else
					throw new UnsupportedOperationException("process param " + i);
			}
		}
		
		// Add left value of definition as method return
		if(stmt instanceof DefinitionStmt)
		{
			ValueBox leftBox = ((DefinitionStmt) stmt).getLeftOpBox();
			if(paramTaintSource || baseTaintSource || type == TaintSourceType.SOURCE) {
				assert aliasing.mayAlias(leftBox.getValue(), dest.getAccessPath().getPlainValue());
				
				methodData.addTaintRet(leftBox.getValue(), true);
			} else
				throw new UnsupportedOperationException("process left side of call");
		}

		methodData.addStmt(stmt);		
		return refactorStmt;
	}
	
	public Stmt refactorCallStmt(Stmt stmt, Set<Abstraction> d1s, SourceFlowAndType sfat, Stmt refactorStmt)
	{
		Abstraction source = sfat.getSource();
		Abstraction dest = sfat.getSuccessor();
		TaintSourceType type = sfat.getType();
		logger.error("[NUS][TAG] Tagged stmt({})\n\t\tsource({})\n\t\tabs({})\n\t\ttype({})",
				stmt, source, dest, type);
		
		if(!source.isAbstractionActive())
			return refactorStmt;
		
		assert (type == TaintSourceType.CALL_BASE || type == TaintSourceType.CALL_PARAM ||
				TaintedStmtTag.isCallsiteReturnType(type));
		
		// Process base
		if(stmt.getInvokeExpr() instanceof InstanceInvokeExpr)
		{
			InstanceInvokeExpr iie = (InstanceInvokeExpr) stmt.getInvokeExpr();
			Value base = iie.getBase();
			
			if (type == TaintSourceType.CALL_BASE)
			{
				assert aliasing.mayAlias(base, source.getAccessPath().getPlainValue());
				
				// x.call() becomes taint_x.call() only when taint source is x (NOT x.f)
				if(source.getAccessPath().getFieldCount() == 0) {
					if (refactorStmt == null)
						refactorStmt = (Stmt) stmt.clone();
					((InstanceInvokeExpr) refactorStmt.getInvokeExpr()).setBase(getProxyValue(base));
					//FIXME: we cannot slice calls inside tainted base, we need to move them completely
				}	
			}
		}		
		
		// Process method call params
		InvokeExpr ie = stmt.getInvokeExpr();
		if(ie.getArgs() != null)
		{
			int paramCount = ie.getArgCount();
			
			for(int i = 0; i < paramCount; i++)
			{
				if(ie.getArg(i) instanceof Constant)
					continue;
				
				if(type == TaintSourceType.CALL_PARAM) {
					if (aliasing.mayAlias(ie.getArg(i), source.getAccessPath().getPlainValue())) {
						// we replace b.call(p1) with b.call(taint_p1) only when p1 is tainted (NOT p1.f)
						if (source.getAccessPath().getFieldCount() == 0) {
							if (refactorStmt == null)
								refactorStmt = (Stmt) stmt.clone();
							refactorStmt.getInvokeExpr().setArg(i, getProxyValue(ie.getArg(i)));
						}
					}
				}
			}
		}
		
		// Process left value of definition
		if(stmt instanceof DefinitionStmt) {
			Value leftValue = ((DefinitionStmt) stmt).getLeftOp();
			
			if (type == TaintSourceType.CALLSITE_RETURN_VALUE) {
				AccessPath leftAP = new AccessPath(leftValue, false);
				AccessPath mappedAP = aliasing.mayAlias(dest.getAccessPath(), leftAP);
				assert (mappedAP != null);
				
				// we replace c = call() with taint_c = call() only when c is tainted (NOT c.f)
				if(mappedAP.entails(leftAP)) {
					if(refactorStmt == null)
						refactorStmt = (DefinitionStmt) stmt.clone();
					
					((DefinitionStmt) refactorStmt).getLeftOpBox().setValue(getProxyValue(leftValue));
				}
			}
		}

		logger.error("LUCIA: refactorCallStmt {} as\n\t\t{}", stmt, refactorStmt);
		return refactorStmt;
	}
	
	public Stmt processExitStmt(Stmt exitStmt, Set<Abstraction> d1s, SourceFlowAndType sfat, Stmt refactorStmt)
	{
		Abstraction source = sfat.getSource();
		Abstraction dest = sfat.getSuccessor();
		TaintSourceType type = sfat.getType();
		logger.error("[NUS][TAG] Tagged stmt({})\n\t\tsource({})\n\t\tabs({})\n\t\ttype({})",
				exitStmt, source, dest, type);
	
		//assert (type == TaintSourceType.RETURN_VALUE);
		ReturnStmt returnStmt = (exitStmt instanceof ReturnStmt) ? (ReturnStmt) exitStmt : null;
		
		if(returnStmt != null) {
			Value returnOp = returnStmt.getOp();

			if(type == TaintSourceType.RETURN_VALUE)
			{
				AccessPath returnOpAP = new AccessPath(returnOp, false);
				AccessPath mappedAP = aliasing.mayAlias(source.getAccessPath(), returnOpAP); 
				assert (mappedAP != null);
				
				// Refactor "return x" iff x is tainted (NOT x.f)
				if (mappedAP.entails(returnOpAP))
				{
					if(refactorStmt == null)
						refactorStmt = (Stmt) returnStmt.clone();
					
					((ReturnStmt)refactorStmt).getOpBox().setValue(
							getProxyValue(returnOp));
				}
			}
		}
	
		return refactorStmt;
	}

	public Stmt processNormalStmt(Stmt stmt, SourceFlowAndType sfat, MethodData methodData, Stmt refactorStmt)
	{
		Abstraction source = sfat.getSource();
		Abstraction dest = sfat.getSuccessor();
		TaintSourceType type = sfat.getType();
		logger.error("[NUS][TAG] Tagged stmt({})\n\t\tsource({})\n\t\tabs({})\n\t\ttype({})",
				stmt, source, dest, type);
		
		if(!source.isAbstractionActive())
			return refactorStmt;
		
		boolean createProxyMethod = true;
		
		if(stmt instanceof AssignStmt) {
			AssignStmt assignStmt = (AssignStmt) stmt;
			ValueBox leftBox = BaseSelector.selectBaseBox(assignStmt.getLeftOpBox(), true);
			ValueBox rightBoxes[] = BaseSelector.selectBaseBoxList(assignStmt.getRightOpBox(), true);
			
			// Add right operands as parameters to new placeholder method
			for(int i=0; i<rightBoxes.length; i++)
			{
				Value right = rightBoxes[i].getValue();
				if(right instanceof Local) {
					if(aliasing.mayAlias(right, source.getAccessPath().getPlainValue())) {
						// x = y and y is tainted
						if (type == TaintSourceType.ASGN_LOCAL)
							methodData.addTaintParam(right, true);
						// x = y and y.f is tainted
						else if (type == TaintSourceType.ASGN_LOCAL_FIELD)
							// do nothing; a field is tainted, not the variable in use
							createProxyMethod = false;
						else
							throw new UnsupportedOperationException("right local with unsupported type");
					} else
						methodData.addTaintParam(right, false);
				
				} else if(right instanceof ArrayRef) {
					ValueBox rightBaseBox = ((ArrayRef) right).getBaseBox();
					Value rightIndex = ((ArrayRef)right).getIndex();
					
					// Add Array base as parameter to new placeholder method
					if(aliasing.mayAlias(rightBaseBox.getValue(), source.getAccessPath().getPlainValue())) {
						if(type == TaintSourceType.ASGN_ARRAY_REF)
							methodData.addTaintParam(rightBaseBox.getValue(), true);
						else throw new UnsupportedOperationException("unsupported type in ArrayRef assignment");
					} else
						methodData.addTaintParam(rightBaseBox.getValue(), false);
					
					// Add Array index as parameter to new placeholder method (if not Constant)
					if(!(rightIndex instanceof Constant)) {
						methodData.addTaintParam(rightIndex, false);
					}
				} else if(right instanceof InstanceFieldRef) {
					AccessPath rightAP = new AccessPath(right, false);
					AccessPath mappedAP = aliasing.mayAlias(source.getAccessPath(), rightAP);
					assert (mappedAP != null);

					// Refactor only if right op is tainted (not one of its subfields)
					if(type == TaintSourceType.ASGN_INSTANCE_FIELD &&
							mappedAP.entails(rightAP)) {
	
						Value proxyInstanceFieldRef = getProxyValue(right);
						
						if(refactorStmt == null)
							refactorStmt = (Stmt) assignStmt.clone();
						ValueBox refactorRightBoxes[] = BaseSelector.selectBaseBoxList(
								((AssignStmt)refactorStmt).getRightOpBox(), true);
						refactorRightBoxes[i].setValue(proxyInstanceFieldRef);
						
						createProxyMethod = false;
					}
				} else
					throw new UnsupportedOperationException("unsupported TaintSourceType " + type);
				
				// Add left operand as return value
				// FIXME: ArrayRef as well
				// Either left-side or right-side has to be Local
				// only if right side is Local, left can assume not Local type
				if(leftBox.getValue() instanceof Local)
				{
					if (aliasing.mayAlias(leftBox.getValue(), dest.getAccessPath().getPlainValue()))
					{
						if(type == TaintSourceType.ASGN_LOCAL ||
							type == TaintSourceType.ASGN_ARRAY_REF)
						{
							methodData.addTaintRet(leftBox.getValue(), true);
						
						} else if(type == TaintSourceType.ASGN_INSTANCE_FIELD) {
							AccessPath leftAP = new AccessPath(leftBox.getValue(), false);
							AccessPath mappedAP = aliasing.mayAlias(dest.getAccessPath(), leftAP);
							assert (mappedAP != null);
							
							if(mappedAP.entails(leftAP)) {
								if(refactorStmt == null)
									refactorStmt = (Stmt) assignStmt.clone();
							
								ValueBox refactorLeftBox = BaseSelector.selectBaseBox(
										((AssignStmt)refactorStmt).getLeftOpBox(), true); 
								refactorLeftBox.setValue(getProxyValue(leftBox.getValue()));	
							}
							
							createProxyMethod = false;
						// x = y, y.f tainted -> x.f becomes tainted => no refactoring or substitution with method needed
						} else if(type == TaintSourceType.ASGN_LOCAL_FIELD) {
							// do nothing
							createProxyMethod = false;
						} else 
							throw new UnsupportedOperationException("Assignment to Local with Unsupported type");
					} else {
						boolean aliases = aliasing.mayAlias(leftBox.getValue(), dest.getAccessPath().getPlainValue());
						logger.error("LUCIA: {} aliases {} returns {}",
								leftBox.getValue(),
								dest.getAccessPath().getPlainValue(),
								aliases);
						throw new UnsupportedOperationException(
								"Assignment to Local does not alias destination Abstraction");

					}
				} else if(leftBox.getValue() instanceof ArrayRef) {
					Value leftBase = ((ArrayRef) leftBox.getValue()).getBase();
					Value leftIndex = ((ArrayRef) leftBox.getValue()).getIndex();
					
					if(type == TaintSourceType.ASGN_LOCAL &&
							aliasing.mayAlias(leftBase, dest.getAccessPath().getPlainValue()))
					{
						methodData.addTaintParam(leftBase, false);
						methodData.addTaintRet(leftBase, true);						
					} else if(type == TaintSourceType.ASGN_TO_ARRAY_REF && 
							aliasing.mayAlias(leftBase, source.getAccessPath().getPlainValue()))
					{
						methodData.addTaintParam(leftBase, true);
						methodData.addTaintRet(leftBase, true);
					} else {
						throw new UnsupportedOperationException(
								"Assignment to ArrayRef does not alias source(type ASGN_TO_ARRAY_REF) OR destination(type ASGN_ARRAY_REF) Abstraction");
					}
					if(!(leftIndex instanceof Constant))
						methodData.addParam(leftIndex);
				
				} else if(leftBox.getValue() instanceof InstanceFieldRef) {
					AccessPath leftAP = new AccessPath(leftBox.getValue(), false);
					AccessPath mappedAP = aliasing.mayAlias(dest.getAccessPath(), leftAP);
					assert (mappedAP != null);
					
					// Refactor only if left side is tainted (not a subfield)
					if(mappedAP.entails(leftAP)) {
						
						Value proxyInstanceFieldRef = getProxyValue(leftBox.getValue());
						
						if(refactorStmt == null)
							refactorStmt = (Stmt) assignStmt.clone();
					
						ValueBox refactorLeftBox = BaseSelector.selectBaseBox(
								((AssignStmt)refactorStmt).getLeftOpBox(), true); 
						
						refactorLeftBox.setValue(proxyInstanceFieldRef);
						ValueBox rightBox = ((AssignStmt) stmt).getRightOpBox();
						ValueBox refactorRightBox = ((AssignStmt) refactorStmt).getRightOpBox();
						refactorRightBox.setValue(getProxyValue(rightBox.getValue()));
						
						createProxyMethod = false;
					} 
				} else {
					throw new UnsupportedOperationException("Unsupported LHS type " + stmt);
				}
				
			}
		}
		if (createProxyMethod)
			methodData.addStmt(stmt);
		else
			methodData.clear();
		logger.error("LUCIA: refactor {} as\n\t\t{}", stmt, refactorStmt);
		return refactorStmt;
	}

	public Value getProxyValue(Value val)
	{
		if (proxyCache.containsKey(val))
			return proxyCache.get(val);
		
		if (val instanceof Local)
		{
			Local local = (Local) val;
			Local clone = Jimple.v().newLocal(local.getName() + PROXY_SUFIX,
					teeObject.getType());
			
			//logger.error("LUCIA: compute clone");
			proxyCache.put(val, clone);
			return clone;
		} else if (val instanceof InstanceFieldRef) {
			
			Value base = ((InstanceFieldRef) val).getBase();
			SootClass baseClass = ((RefType) base.getType()).getSootClass();
			SootField field = ((InstanceFieldRef) val).getField();
			
			String cloneName = field.getName() + PROXY_SUFIX;
			SootField cloneField;
			
			if(!baseClass.declaresField(cloneName, teeObject.getType())) {
				cloneField = new SootField(cloneName, teeObject.getType());
				baseClass.addField(cloneField);
				// We're changing the baseClass so add baseClass as an app class
				pathClasses.add(baseClass);
			} else
				cloneField = baseClass.getField(cloneName, teeObject.getType());
			
			InstanceFieldRef ifr = Jimple.v().newInstanceFieldRef(base, cloneField.makeRef()); 
			proxyCache.put(val, ifr);
			return ifr;
		}
		
		return val;
	}
	
	class MethodData
	{
		// FIXME: make it work for multiple Abstraction Pairs 
		private LinkedList<Stmt> stmts;
		//ArrayList<Value> actualParams;
		private ArrayList<Value> params;
		//ArrayList<Value> actualParams;
		private ArrayList<Type> paramTypes;
		private HashSet<Local> locals;
		private Type retType;
		private HashMap<Value,Value> paramTaints;
		private HashMap<Value,Value> returnTaints;
		
		public MethodData()
		{
			stmts = new LinkedList<Stmt>();
			params = new ArrayList<Value>();
			//actualParams = new ArrayList<Value>();
			paramTypes = new ArrayList<Type>();
			locals = new HashSet<Local>();
			paramTaints = new HashMap<Value,Value>();
			returnTaints = new HashMap<Value,Value>();
			retType = VoidType.v();
		}

		public void clear() {
			stmts.clear();
			params.clear();
			locals.clear();
		}

		public boolean isEmpty()
		{
			return (stmts.isEmpty() && params.isEmpty() && locals.isEmpty());
		}
		
		public Local addTaintParam(Value value, boolean isTainted)
		{
			Value clone = value;
			if(isTainted)
				clone = getProxyValue(value);
			
			if(!params.contains(clone))
			{
				//logger.error("LUCIA: add param {}", clone);
				params.add(clone);
				paramTypes.add(clone.getType());
				locals.add((Local) clone);
			}
			
			if(isTainted && !paramTaints.containsKey(value))
			{

				//logger.error("LUCIA: add paramTaint {}", clone);
				paramTaints.put(value, clone);
				locals.add((Local) value);
			}
			
			return (Local)clone;
		}
		
		public Local addTaintRet(Value value, boolean isTainted)
		{
			Value clone = value;
			if(isTainted)
				clone = getProxyValue(value);
			
			if(!params.contains(clone))
			{
				params.add(clone);
				paramTypes.add(clone.getType());
				locals.add((Local) clone);
			}

			if(isTainted && !returnTaints.containsKey(value))
			{

				//logger.error("LUCIA: add returnTaint {}", clone);
				returnTaints.put(value, clone);
				locals.add((Local) value);
			}
			
			return (Local)clone;
		}
		
		public LinkedList<Unit> getTaintRetInitialization() {
			LinkedList<Unit> units = new LinkedList<Unit>();
			for(Value retTaint: returnTaints.values())
			{
				units.add(Jimple.v().newAssignStmt(retTaint,
						Jimple.v().newNewExpr(teeObject.getType())));
				units.add(Jimple.v().newInvokeStmt(
						Jimple.v().newSpecialInvokeExpr(
								(Local)retTaint, teeObjectConstructor.makeRef())));
			}
			return units;
		}
		
		public void addStmt(Stmt stmt)
		{
			if(!stmts.contains(stmt))
				stmts.add(stmt);
		}
		public SootMethod newMethodSliceFromData(String name)
		{
			SootMethod method = new SootMethod(name,
					paramTypes, retType,
					Modifier.PUBLIC | Modifier.STATIC);
			
			// Body
			JimpleBody body = Jimple.v().newBody();
			body.setMethod(method);
			method.setActiveBody(body);
			PatchingChain<Unit> units = body.getUnits();
			
			body.getLocals().addAll(locals);
			
			// Add params assignment
			for(int i=0; i<params.size(); i++)
				units.addLast(Jimple.v().newIdentityStmt(params.get(i),
							Jimple.v().newParameterRef(params.get(i).getType(), i)));

			// Add actual params to tainted params assignments
			for(Value actualValue: paramTaints.keySet())
			{
				Value taintedValue = paramTaints.get(actualValue);
				units.addLast(Jimple.v().newAssignStmt(actualValue,
						Jimple.v().newStaticInvokeExpr(teeService$getData.makeRef(), taintedValue)));
			}
			
			// Add original stmts
			units.addAll(stmts);
			
			// Add tainted returns to actual returns assignments
			for(Value actualValue: returnTaints.keySet())
			{
				Value taintedValue = returnTaints.get(actualValue);
				units.addLast(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
						teeService$setData.makeRef(),
						Arrays.asList(new Value[] {taintedValue, actualValue}))));
			}
			// Add return stmt
			/*
			if(retType != VoidType.v())
				units.addLast(Jimple.v().newReturnStmt(formalRet));
			*/
			
			logger.error("LUCIA: list of stmts\n\t\t{}", units);
			logger.error("LUCIA: method body\n\t\t{}", method.getActiveBody());
		
			return method;
		}

		public void addRet(Value value) {
			addTaintRet(value, false);
		}

		public void addParam(Value value) {
			addTaintParam(value, false);
			
		}
	}

	// [NUS] function to print Tags of stmt, left operand and right
	// operand if available
	private void printStmt(Stmt stmt) {
		print(stmt + "\nTAG\n\t\t" + stmt.getTag(TaintedStmtTag.TAG_NAME));
	}
	
	private void print(String string) {
		/*
		try {
			System.out.println(string);
			if (wr != null)
				wr.write(string + "\n");
		}
		catch (IOException ex) {
			// ignore
		}
		*/
		logger.info(string + "\n");
	}
}