package nus.soc.extensions;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.jimple.infoflow.data.Abstraction;

public class SourceFlowAndType
{
	private TaintSourceType sourceType;
	private Abstraction successor;
	private Abstraction source;
	int hashCode = 0;
	Logger logger = LoggerFactory.getLogger(getClass());
	
	public SourceFlowAndType(Abstraction source, Abstraction successor, TaintSourceType sourceType) {
		this.source = source;
		this.successor = successor;
		this.sourceType = sourceType;
	}
	
	public Abstraction getSource()
	{
		return this.source;
	}
	
	public Abstraction getSuccessor()
	{
		return this.successor;
	}
	
	public TaintSourceType getType()
	{
		return this.sourceType;
	}
	
	public int hashCode()
	{
		if (this.hashCode != 0)
			return hashCode;
		
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((source == null) ? 0 : source.hashCode());
		result = prime * result
				+ ((successor == null) ? 0 : successor.hashCode());
		result = prime * result
				+ ((sourceType == null) ? 0 : sourceType.hashCode());
		hashCode = result;
		return hashCode;
	}
	
	public boolean equals(Object obj)
	{
		
		if (super.equals(obj))
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		SourceFlowAndType other = (SourceFlowAndType) obj;
		
		// If we have already computed hash codes, we can use them for
		// comparison
		/*
		if (this.hashCode != 0
				&& other.hashCode != 0
				&& this.hashCode != other.hashCode)
			return false;
			*/	
		boolean ret =  (source.equals(other.getSource()) &&
				successor.equals(other.getSuccessor()) &&
				sourceType.equals(other.getType()));
		return ret;
	}
	
	public String toString()
	{
		return "source(" + source +
				") succ(" + successor +
				") type(" + sourceType + ")";
	}
}

