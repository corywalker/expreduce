package expreduce

import (
	"math/big"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type iterSpec interface {
	// Should be called before every iteration:
	reset()
	next()
	cont() bool
	getCurr() expreduceapi.Ex
	getI() expreduceapi.Ex
	getIName() string
}

type iterSpecRange struct {
	i     expreduceapi.Ex
	iName string
	iMin  expreduceapi.Ex
	iMax  expreduceapi.Ex
	step  expreduceapi.Ex
	curr  expreduceapi.Ex
	es    expreduceapi.EvalStateInterface
}

type iterSpecList struct {
	i     expreduceapi.Ex
	iName string
	pos   int
	list  expreduceapi.ExpressionInterface
}

func tryIterParam(e expreduceapi.Ex) (expreduceapi.Ex, bool) {
	if _, isInt := e.(*Integer); isInt {
		return e, true
	}
	if _, isReal := e.(*Flt); isReal {
		return e, true
	}
	if _, isRat := e.(*Rational); isRat {
		return e, true
	}
	if _, isComp := e.(*Complex); isComp {
		return e, true
	}
	return nil, false
}

func iterSpecFromList(es expreduceapi.EvalStateInterface, listEx expreduceapi.Ex) (iterSpec, bool) {
	isr := &iterSpecRange{}
	isr.es = es
	isl := &iterSpecList{}

	listEx = evalIterSpecCandidate(es, listEx)
	list, isList := HeadAssertion(listEx, "System`List")
	if isList {
		iOk, iMinOk, iMaxOk, stepOk := false, false, false, false
		if len(list.Parts) > 2 {
			iAsSymbol, iIsSymbol := list.Parts[1].(*Symbol)
			if iIsSymbol {
				iOk = true
				isr.i, isl.i = iAsSymbol, iAsSymbol
				isr.iName, isl.iName = iAsSymbol.Name, iAsSymbol.Name
			}
			iAsExpression, iIsExpression := list.Parts[1].(expreduceapi.ExpressionInterface)
			if iIsExpression {
				headAsSymbol, headIsSymbol := iAsExpression.Parts[0].(*Symbol)
				if headIsSymbol {
					iOk = true
					isr.i, isl.i = iAsExpression, iAsExpression
					isr.iName, isl.iName = headAsSymbol.Name, headAsSymbol.Name
				}
			}
		}
		if len(list.Parts) == 3 {
			isr.iMin, iMinOk = NewInteger(big.NewInt(1)), true
			isr.iMax, iMaxOk = tryIterParam(list.Parts[2])
			isr.step, stepOk = NewInteger(big.NewInt(1)), true
		} else if len(list.Parts) == 4 {
			isr.iMin, iMinOk = tryIterParam(list.Parts[2])
			isr.iMax, iMaxOk = tryIterParam(list.Parts[3])
			isr.step, stepOk = NewInteger(big.NewInt(1)), true
		} else if len(list.Parts) == 5 {
			isr.iMin, iMinOk = tryIterParam(list.Parts[2])
			isr.iMax, iMaxOk = tryIterParam(list.Parts[3])
			isr.step, stepOk = tryIterParam(list.Parts[4])
		}
		if iOk && iMinOk && iMaxOk && stepOk {
			isr.reset()
			return isr, true
		}

		// Conversion to iterSpecRange failed. Try iterSpecList.
		iterListOk := false
		if len(list.Parts) == 3 {
			isl.list, iterListOk = HeadAssertion(list.Parts[2], "System`List")
		}
		if iOk && iterListOk {
			isl.reset()
			return isl, true
		}
	}
	return isr, false
}

func (this *iterSpecRange) reset() {
	//this.curr = this.iMin
	this.curr = E(S("Plus"), this.iMin, E(S("Times"), NewInt(0), this.step)).Eval(this.es)
}

func (this *iterSpecRange) next() {
	this.curr = E(S("Plus"), this.curr, this.step).Eval(this.es)
}

func (this *iterSpecRange) cont() bool {
	return ExOrder(this.curr, this.iMax) >= 0
}

func (this *iterSpecRange) getCurr() expreduceapi.Ex {
	return this.curr
}

func (this *iterSpecRange) getI() expreduceapi.Ex {
	return this.i
}

func (this *iterSpecRange) getIName() string {
	return this.iName
}

func (this *iterSpecList) reset() {
	this.pos = 1
}

func (this *iterSpecList) next() {
	this.pos++
}

func (this *iterSpecList) cont() bool {
	return this.pos < len(this.list.Parts)
}

func (this *iterSpecList) getCurr() expreduceapi.Ex {
	return this.list.Parts[this.pos]
}

func (this *iterSpecList) getI() expreduceapi.Ex {
	return this.i
}

func (this *iterSpecList) getIName() string {
	return this.iName
}

type multiIterSpec struct {
	iSpecs     []iterSpec
	origDefs   []expreduceapi.Ex
	isOrigDefs []bool
	shouldCont bool
}

func multiIterSpecFromLists(es expreduceapi.EvalStateInterface, lists []expreduceapi.Ex) (mis multiIterSpec, isOk bool) {
	// Retrieve variables of iteration
	mis.shouldCont = true
	for i := range lists {
		is, isOk := iterSpecFromList(es, lists[i])
		if !isOk {
			return mis, false
		}
		mis.iSpecs = append(mis.iSpecs, is)
		mis.shouldCont = mis.shouldCont && is.cont()
	}
	return mis, true
}

func (this *multiIterSpec) next() {
	for i := len(this.iSpecs) - 1; i >= 0; i-- {
		this.iSpecs[i].next()
		if this.iSpecs[i].cont() {
			return
		}
		this.iSpecs[i].reset()
	}
	this.shouldCont = false
}

func (this *multiIterSpec) cont() bool {
	return this.shouldCont
}

func (this *multiIterSpec) takeVarSnapshot(es expreduceapi.EvalStateInterface) {
	this.origDefs = make([]expreduceapi.Ex, len(this.iSpecs))
	this.isOrigDefs = make([]bool, len(this.iSpecs))
	for i := range this.iSpecs {
		this.origDefs[i], this.isOrigDefs[i], _ = es.GetDef(this.iSpecs[i].getIName(), this.iSpecs[i].getI())
	}
}

func (this *multiIterSpec) restoreVarSnapshot(es expreduceapi.EvalStateInterface) {
	for i := range this.iSpecs {
		if this.isOrigDefs[i] {
			es.Define(this.iSpecs[i].getI(), this.origDefs[i])
		} else {
			es.Clear(this.iSpecs[i].getIName())
		}
	}
}

func (this *multiIterSpec) defineCurrent(es expreduceapi.EvalStateInterface) {
	for i := range this.iSpecs {
		es.Define(this.iSpecs[i].getI(), this.iSpecs[i].getCurr())
	}
}

func (this *multiIterSpec) currentPDManager() *PDManager {
	pm := &PDManager{make(map[string]expreduceapi.Ex)}
	for i := range this.iSpecs {
		pm.patternDefined[this.iSpecs[i].getIName()] = this.iSpecs[i].getCurr()
	}
	return pm
}

func (this expreduceapi.ExpressionInterface) evalIterationFunc(es expreduceapi.EvalStateInterface, init expreduceapi.Ex, op string) expreduceapi.Ex {
	if len(this.Parts) >= 3 {
		mis, isOk := multiIterSpecFromLists(es, this.Parts[2:])
		if isOk {
			// Simulate evaluation within Block[]
			mis.takeVarSnapshot(es)
			var toReturn expreduceapi.Ex = init
			for mis.cont() {
				mis.defineCurrent(es)
				toReturn = (NewExpression([]expreduceapi.Ex{NewSymbol(op), toReturn, this.Parts[1].DeepCopy().Eval(es)})).Eval(es)
				mis.next()
			}
			mis.restoreVarSnapshot(es)
			return toReturn
		}
	}
	return this
}

func evalIterSpecCandidate(es expreduceapi.EvalStateInterface, cand expreduceapi.Ex) expreduceapi.Ex {
	// Special handling for Lists, which might have variables of iteration in
	// them.
	list, isList := HeadAssertion(cand, "System`List")
	if isList {
		toReturn := NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
		for i := 1; i < len(list.Parts); i++ {
			toAdd := list.Parts[i].DeepCopy()
			// Do not evaluate the variable of iteration. Even if "n" is
			// defined already, we just want it to be "n".
			if i != 1 {
				toAdd = toAdd.Eval(es)
			}
			toReturn.Parts = append(toReturn.Parts, toAdd)
		}
		return toReturn
	}
	// We should attempt to evaluate all non-Lists, since we expect them to not
	// have any variables of iteration in them.
	return cand.Eval(es)
}
