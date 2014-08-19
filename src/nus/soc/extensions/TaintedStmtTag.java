package nus.soc.extensions;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.jimple.Stmt;
import soot.jimple.infoflow.data.Abstraction;
import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

class SuccessorAndSourceType
{
	private TaintSourceType sourceType;
	private Abstraction successor;
	
	public SuccessorAndSourceType(Abstraction successor, TaintSourceType sourceType) {
		this.successor = successor;
		this.sourceType = sourceType;
	}
	
	public Abstraction getSuccessor()
	{
		return this.successor;
	}
	
	public TaintSourceType getType()
	{
		return this.sourceType;
	}
	
	public String toString()
	{
		return "successor(" + getSuccessor() + ") type(" + getType() + ")";
	}
	
	public int hashCode()
	{
		return successor.hashCode();
	}
}

public class TaintedStmtTag implements Tag {

	public static final String TAG_NAME = "nus.soc.extensions.TaintedStmtTag";
	// Successor Abstraction and source type for each successor indexed by source Abstraction
	ConcurrentHashMap<Abstraction, Set<SuccessorAndSourceType>> sastMap;
	protected static final Logger logger = LoggerFactory.getLogger(TaintedStmtTag.class.getClass());
	
	@Override
	public String getName() {
		return TAG_NAME;
	}
	
	public TaintedStmtTag(Abstraction abs, TaintSourceType type)
	{
		sastMap = new ConcurrentHashMap<Abstraction, Set<SuccessorAndSourceType>>();
		Abstraction predecessor;
		
		switch(type) {
			case SINK_PARAM:
			case SINK_BASE:
				predecessor = abs;
				break;
			default:
				predecessor = (abs.getPredecessor() != null)?
						abs.getPredecessor():
							Abstraction.getZeroAbstraction(true);
		}
		sastMap.put(predecessor,
				Collections.singleton(new SuccessorAndSourceType(abs, type)));
	}

	public void addAbstraction(Abstraction abs, TaintSourceType type)
	{
		Abstraction predecessor;
		
		switch(type) {
		case SINK_PARAM:
		case SINK_BASE:
			predecessor = abs;
			break;
		default:
			predecessor = (abs.getPredecessor() != null)?
					abs.getPredecessor():
						Abstraction.getZeroAbstraction(true);
		}

		SuccessorAndSourceType sast = new SuccessorAndSourceType(abs, type);
		Set<SuccessorAndSourceType> sastSet = sastMap.putIfAbsent(predecessor,
				Collections.singleton(sast));
		if (sastSet != null)
		{
			sastSet = new HashSet<SuccessorAndSourceType>(sastSet);
			sastSet.add(sast);
		}
	}

	public static class TaintSourceTypeException extends Exception 
	{
		public TaintSourceTypeException(String message)
		{
			super(message);
		}
	}
	
	public static void enhanceTag(Stmt stmt, Abstraction abs, TaintSourceType type)
	{
		if (stmt == null)
		{
			logger.error("LUCIA: NULL stmt!!");
			return;
		}
		synchronized(stmt.getTags()) {
			TaintedStmtTag tag = (TaintedStmtTag) stmt.getTag(TAG_NAME);
			if (tag == null)
				stmt.addTag(new TaintedStmtTag(abs, type));
			else
				tag.addAbstraction(abs, type);
		}
	}

	@Override
	public byte[] getValue() throws AttributeValueException {
		return sastMap.toString().getBytes();
	}
	
	public String toString() {
		return sastMap.toString();
	}
}
