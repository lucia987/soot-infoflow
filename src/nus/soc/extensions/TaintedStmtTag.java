package nus.soc.extensions;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.NullType;
import soot.jimple.NullConstant;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.source.SourceInfo;
import soot.jimple.internal.JimpleLocal;
import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class TaintedStmtTag implements Tag {

	public static final String TAG_NAME = "nus.soc.extensions.TaintedStmtTag";
	// Successor Abstraction and source type for each successor indexed by source Abstraction
	protected ConcurrentHashMap<Abstraction, HashSet<SourceFlowAndType>> sfatMap;
	protected static final Logger logger = LoggerFactory.getLogger(TaintedStmtTag.class.getClass());
	protected final static Abstraction zeroValue = new Abstraction(new JimpleLocal("zero", NullType.v()), new SourceInfo(false),
			NullConstant.v(), null, false, false);
	@Override
	public String getName() {
		return TAG_NAME;
	}
	
	public TaintedStmtTag(Abstraction d1, Abstraction abs, TaintSourceType type)
	{
		sfatMap = new ConcurrentHashMap<Abstraction, HashSet<SourceFlowAndType>>();
		Abstraction predecessor;
		
		switch(type) {
			case SINK_PARAM:
			case SINK_BASE:
				predecessor = abs;
				abs = getZeroAbstraction();
				break;
				/*
			case TRANSFER:
				predecessor = abs;
				break;
				*/
			default:
				predecessor = (abs.getPredecessor() != null)?
						abs.getPredecessor():
							getZeroAbstraction();
		}
		HashSet<SourceFlowAndType> sastSet = new HashSet<SourceFlowAndType>();
		sastSet.add(new SourceFlowAndType(predecessor, abs, type));
		sfatMap.put(d1, sastSet);
	}

	public void addAbstraction(Abstraction d1, Abstraction abs, TaintSourceType type)
	{
		Abstraction predecessor;
		
		switch(type) {
		case SINK_PARAM:
		case SINK_BASE:
			predecessor = abs;
			abs = getZeroAbstraction();
			break;
			/*
		case TRANSFER:
			predecessor = abs;
			break;
			*/
		default:
			predecessor = (abs.getPredecessor() != null)?
					abs.getPredecessor(): getZeroAbstraction();
		}

		HashSet<SourceFlowAndType> addSastSet = new HashSet<SourceFlowAndType>();
		addSastSet.add(new SourceFlowAndType(predecessor, abs, type));
		
		HashSet<SourceFlowAndType> sastSet = sfatMap.putIfAbsent(d1, addSastSet);
		if (sastSet != null)
		{
			//logger.info("LUCIA: addAbstraction BEFORE {}", sastSet);
			sastSet.addAll(addSastSet);
			//logger.info("LUCIA: addAbstraction AFTER {}", sastSet);
		}
	}

	public static class TaintSourceTypeException extends Exception 
	{
		public TaintSourceTypeException(String message)
		{
			super(message);
		}
	}
	
	public static void enhanceTag(Stmt stmt, Abstraction d1, Abstraction abs, TaintSourceType type)
	{
		if (stmt == null)
		{
			logger.error("LUCIA: NULL stmt!!");
			return;
		}
		synchronized(stmt.getTags()) {
			TaintedStmtTag tag = (TaintedStmtTag) stmt.getTag(TAG_NAME);
			if (tag == null)
				stmt.addTag(new TaintedStmtTag(d1, abs, type));
			else
				tag.addAbstraction(d1, abs, type);
		}
	}

	public Set<SourceFlowAndType> getSuccessorAndSourceTypeSet(Abstraction parent)
	{
		return sfatMap.get(parent);
	}
	
	@Override
	public byte[] getValue() throws AttributeValueException {
		return sfatMap.toString().getBytes();
	}
	
	public String toString() {
		return sfatMap.toString();
	}
	
	public static Abstraction getZeroAbstraction()
	{
		return zeroValue;
	}
	
	static Set<Abstraction> getCalleeD1s(Stmt callStmt, Set<Abstraction> callSiteD1s)
	{
		TaintedStmtTag tag = (TaintedStmtTag)callStmt.getTag(TAG_NAME);
		synchronized (callStmt.getTags())
		{
			if (tag == null)
				return null;
			else
			{
				HashSet<Abstraction> callTargetD1s = new HashSet<Abstraction>();
				for(Abstraction d1: callSiteD1s)
				{
					HashSet<SourceFlowAndType> sfatSet = tag.getSourceFlowAndTypeSet(d1);
					if (sfatSet == null)
						continue;
					for(SourceFlowAndType sfat: sfatSet) {
						if(!isCallsiteReturnType(sfat.getType()) &&
								sfat.getSource().isAbstractionActive())
							callTargetD1s.add(sfat.getSuccessor());
					}
				}
				return callTargetD1s;
			}
		}
	}
	
	public static boolean isCallsiteReturnType(TaintSourceType type) {
		
		return (type == TaintSourceType.CALLSITE_RETURN_VALUE ||
				type == TaintSourceType.CALLSITE_RETURN_PARAM ||
				type == TaintSourceType.CALLSITE_RETURN_BASE);
				
	}

	public HashSet<SourceFlowAndType> getSourceFlowAndTypeSet(Abstraction d1)
	{
		return sfatMap.get(d1);
	}
	
	public HashSet<SourceFlowAndType> getSourceFlowAndTypeSet(Set<Abstraction> d1s)
	{
		HashSet<SourceFlowAndType> sfatSet = new HashSet<SourceFlowAndType>();
		for (Abstraction d1: d1s)
		{
			HashSet<SourceFlowAndType> tmpSet = sfatMap.get(d1);
			if(tmpSet != null)
				sfatSet.addAll(tmpSet);
		}
		return sfatSet;
	}
}
