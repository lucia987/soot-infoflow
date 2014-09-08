package nus.soc.extensions;

public enum TaintSourceType {
	NONE,
	IMPLICIT,							// FIXME(implicitFlows)
	SOURCE, 							// DONE
	CATCH_EXCEPTION_REF,
	// y = X.f and X.f tainted
	ASGN_STATIC_FIELD, 
	// y = x.f and x tainted
	ASGN_INSTANCE,
	// y = x.f and x.f tainted
	ASGN_INSTANCE_FIELD,				// DONE
	// y = x or y.f = x and x.f tainted 
	ASGN_LOCAL_FIELD,
	// y = x[i]
	ASGN_ARRAY_REF,						// DONE
	// y = x
	ASGN_LOCAL,							// DONE for left side as: Local, ArrayRef, InstanceFieldRef
	THROW, 								// FIXME(exceptions)
	CONDITIONAL, 						// FIXME(implicitFlows)
	// x.invoke_method() when x is tainted
	CALL_BASE,							// TODO(process associated return)
	CALL_PARAM,							// TODO(process associated return)
	RETURN_IMPLICIT,					// FIXME(implicitFlows)
	RETURN_VALUE,
	CALLSITE_RETURN_VALUE,
	CALLSITE_RETURN_PARAM, CALLSITE_RETURN_BASE, 
	WRAPPER_NATIVE,
	WRAPPER_CALL_BASE,					// DONE
	WRAPPER_CALL_PARAM,					// DONE
	SINK_PARAM, SINK_BASE,				// DONE
	//TRANSFER,
	// x[i] = y when x[i] is tainted, y not tainted because writes to secure arrays must be handled in the secure world
	ASGN_TO_ARRAY_REF,					// DONE
	// tainted_base.taint_wrapped_call() BUT with no left operand to taint is still a use of a tainted value
	WRAPPER_CALL_BASE_USE,				// DONE
	// taint_wrapped_call(tainted_param) that does not taint base or with no left operand is still a use of a tainted value
	WRAPPER_CALL_PARAM_USE,				// DONE
	;
	/*
	int index=0;
	
	public void setIndex(int index)
	{
		this.index = index;
	}
	
	public int getIndex()
	{
		return index;
	}
	*/
}
