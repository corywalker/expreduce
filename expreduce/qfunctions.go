package expreduce

type singleParamQType (func(Ex) bool)
type singleParamQLogType (func(Ex, *CASLogger) bool)
type doubleParamQLogType (func(Ex, Ex, *CASLogger) bool)
type evalFnType (func(*Expression, *EvalState) Ex)

func singleParamQEval(fn singleParamQType) evalFnType {
	return (func(this *Expression, es *EvalState) Ex {
		if len(this.Parts) != 2 {
			return this
		}
		if fn(this.Parts[1]) {
			return &Symbol{"True"}
		}
		return &Symbol{"False"}
	})
}

func singleParamQLogEval(fn singleParamQLogType) evalFnType {
	return (func(this *Expression, es *EvalState) Ex {
		if len(this.Parts) != 2 {
			return this
		}
		if fn(this.Parts[1], &es.CASLogger) {
			return &Symbol{"True"}
		}
		return &Symbol{"False"}
	})
}

func doubleParamQLogEval(fn doubleParamQLogType) evalFnType {
	return (func(this *Expression, es *EvalState) Ex {
		if len(this.Parts) != 3 {
			return this
		}
		if fn(this.Parts[1], this.Parts[2], &es.CASLogger) {
			return &Symbol{"True"}
		}
		return &Symbol{"False"}
	})
}

func numberQ(e Ex) bool {
	_, ok := e.(*Integer)
	if ok {
		return true
	}
	_, ok = e.(*Flt)
	if ok {
		return true
	}
	_, ok = e.(*Rational)
	if ok {
		return true
	}
	return false
}

func vectorQ(e Ex) bool {
	l, isL := HeadAssertion(e, "List")
	if isL {
		for i := 1; i < len(l.Parts); i++ {
			_, subIsL := HeadAssertion(l.Parts[i], "List")
			if subIsL {
				return false
			}
		}
		return true
	}
	return false
}

func matrixQ(e Ex, cl *CASLogger) bool {
	l, isL := HeadAssertion(e, "List")
	if isL {
		return len(dimensions(l, 0, cl)) == 2
	}
	return false
}

func patternsOrderedQ(a Ex, b Ex, cl *CASLogger) bool {
	return false
}

func symbolNameQ(e Ex, name string, cl *CASLogger) bool {
	sym, isSym := e.(*Symbol)
	if isSym {
		return sym.Name == name
	}
	return false
}

func trueQ(e Ex, cl *CASLogger) bool {
	return symbolNameQ(e, "True", cl)
}

func falseQ(e Ex, cl *CASLogger) bool {
	return symbolNameQ(e, "False", cl)
}

func booleanQ(e Ex, cl *CASLogger) bool {
	sym, isSym := e.(*Symbol)
	if isSym {
		return sym.Name == "False" || sym.Name == "True"
	}
	return false
}
