package expreduce

type singleParamQType (func(Ex) bool)
type evalFnType (func (*Expression, *EvalState) Ex)

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
