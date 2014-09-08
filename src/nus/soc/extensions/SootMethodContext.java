package nus.soc.extensions;

import java.util.Set;

import soot.SootMethod;
import soot.jimple.infoflow.data.Abstraction;

import com.google.common.collect.ImmutableSet;

public class SootMethodContext {
	SootMethod method;
	ImmutableSet<Abstraction> d1s;
	int hashCode = 0;
	
	public SootMethodContext(SootMethod sm, Set<Abstraction> d1Set)
	{
		method = sm;
		d1s = ImmutableSet.copyOf(d1Set);
	}
	
	public SootMethod getMethod()
	{
		return method;
	}
	
	public Set<Abstraction> getD1s()
	{
		return d1s;
	}
	
	public boolean equals(Object o)
	{
		if (!(o instanceof SootMethodContext))
			return false;
		SootMethodContext other = (SootMethodContext)o;
		return (method.equals(other.getMethod()) &&
				d1s.containsAll(other.getD1s()) &&
				other.getD1s().containsAll(d1s));
	}
	
	public int hashCode()
	{
		if(hashCode != 0)
			return hashCode;
	
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((method == null) ? 0 : method.hashCode());
		if (d1s != null)
		{
			int sum = 0;
			for(Abstraction d1: d1s)
				sum += (d1 == null) ? 0 : d1.hashCode();
			result = prime * result + sum;
		}
		hashCode = result;
		return hashCode;
	}
	
	public String toString()
	{
		return "method(" + method.getSignature() + ")\td1S(" + d1s + ")";
	}
}
