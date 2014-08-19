package nus.soc.extensions;

public enum TaintSourceType {
	NONE,
	IMPLICIT,
	SOURCE, 
	CATCH_EXCEPTION_REF,
	// y = X.f and X.f tainted
	ASGN_STATIC_FIELD, 
	// y = x.f and x tainted
	ASGN_INSTANCE,
	// y = x.f and x.f tainted
	ASGN_INSTANCE_FIELD,
	// y = x or y.f = x and x.f tainted 
	ASGN_LOCAL_FIELD,
	// y = x[i]
	ASGN_ARRAY_REF,
	// y = x
	ASGN_LOCAL,
	THROW, CONDITIONAL, 
	// x.invoke_method() when x is tainted
	CALL_BASE,
	CALL_PARAM,
	RETURN_IMPLICIT, RETURN_VALUE, RETURN_PARAM, RETURN_BASE, 
	WRAPPER_NATIVE,
	WRAPPER_CALL_BASE, WRAPPER_CALL_PARAM,
	SINK_PARAM, SINK_BASE
	;
}
