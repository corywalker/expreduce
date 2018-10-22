package iterspec

import (
	"math/big"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/matcher"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type iterSpec interface {
	// Should be called before every iteration:
	reset()
	Next()
	Cont() bool
	GetCurr() expreduceapi.Ex
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
	if _, isInt := e.(*atoms.Integer); isInt {
		return e, true
	}
	if _, isReal := e.(*atoms.Flt); isReal {
		return e, true
	}
	if _, isRat := e.(*atoms.Rational); isRat {
		return e, true
	}
	if _, isComp := e.(*atoms.Complex); isComp {
		return e, true
	}
	return nil, false
}

func IterSpecFromList(es expreduceapi.EvalStateInterface, listEx expreduceapi.Ex) (iterSpec, bool) {
	isr := &iterSpecRange{}
	isr.es = es
	isl := &iterSpecList{}

	listEx = evalIterSpecCandidate(es, listEx)
	list, isList := atoms.HeadAssertion(listEx, "System`List")
	if isList {
		iOk, iMinOk, iMaxOk, stepOk := false, false, false, false
		if len(list.GetParts()) > 2 {
			iAsSymbol, iIsSymbol := list.GetParts()[1].(*atoms.Symbol)
			if iIsSymbol {
				iOk = true
				isr.i, isl.i = iAsSymbol, iAsSymbol
				isr.iName, isl.iName = iAsSymbol.Name, iAsSymbol.Name
			}
			iAsExpression, iIsExpression := list.GetParts()[1].(expreduceapi.ExpressionInterface)
			if iIsExpression {
				headAsSymbol, headIsSymbol := iAsExpression.GetParts()[0].(*atoms.Symbol)
				if headIsSymbol {
					iOk = true
					isr.i, isl.i = iAsExpression, iAsExpression
					isr.iName, isl.iName = headAsSymbol.Name, headAsSymbol.Name
				}
			}
		}
		if len(list.GetParts()) == 3 {
			isr.iMin, iMinOk = atoms.NewInteger(big.NewInt(1)), true
			isr.iMax, iMaxOk = tryIterParam(list.GetParts()[2])
			isr.step, stepOk = atoms.NewInteger(big.NewInt(1)), true
		} else if len(list.GetParts()) == 4 {
			isr.iMin, iMinOk = tryIterParam(list.GetParts()[2])
			isr.iMax, iMaxOk = tryIterParam(list.GetParts()[3])
			isr.step, stepOk = atoms.NewInteger(big.NewInt(1)), true
		} else if len(list.GetParts()) == 5 {
			isr.iMin, iMinOk = tryIterParam(list.GetParts()[2])
			isr.iMax, iMaxOk = tryIterParam(list.GetParts()[3])
			isr.step, stepOk = tryIterParam(list.GetParts()[4])
		}
		if iOk && iMinOk && iMaxOk && stepOk {
			isr.reset()
			return isr, true
		}

		// Conversion to iterSpecRange failed. Try iterSpecList.
		iterListOk := false
		if len(list.GetParts()) == 3 {
			isl.list, iterListOk = atoms.HeadAssertion(list.GetParts()[2], "System`List")
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
	this.curr = this.es.Eval(atoms.E(atoms.S("Plus"), this.iMin, atoms.E(atoms.S("Times"), atoms.NewInt(0), this.step)))
}

func (this *iterSpecRange) Next() {
	this.curr = this.es.Eval(atoms.E(atoms.S("Plus"), this.curr, this.step))
}

func (this *iterSpecRange) Cont() bool {
	return atoms.ExOrder(this.curr, this.iMax) >= 0
}

func (this *iterSpecRange) GetCurr() expreduceapi.Ex {
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

func (this *iterSpecList) Next() {
	this.pos++
}

func (this *iterSpecList) Cont() bool {
	return this.pos < len(this.list.GetParts())
}

func (this *iterSpecList) GetCurr() expreduceapi.Ex {
	return this.list.GetParts()[this.pos]
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

func MultiIterSpecFromLists(es expreduceapi.EvalStateInterface, lists []expreduceapi.Ex) (mis multiIterSpec, isOk bool) {
	// Retrieve variables of iteration
	mis.shouldCont = true
	for i := range lists {
		is, isOk := IterSpecFromList(es, lists[i])
		if !isOk {
			return mis, false
		}
		mis.iSpecs = append(mis.iSpecs, is)
		mis.shouldCont = mis.shouldCont && is.Cont()
	}
	return mis, true
}

func (this *multiIterSpec) Next() {
	for i := len(this.iSpecs) - 1; i >= 0; i-- {
		this.iSpecs[i].Next()
		if this.iSpecs[i].Cont() {
			return
		}
		this.iSpecs[i].reset()
	}
	this.shouldCont = false
}

func (this *multiIterSpec) Cont() bool {
	return this.shouldCont
}

func (this *multiIterSpec) TakeVarSnapshot(es expreduceapi.EvalStateInterface) {
	this.origDefs = make([]expreduceapi.Ex, len(this.iSpecs))
	this.isOrigDefs = make([]bool, len(this.iSpecs))
	for i := range this.iSpecs {
		this.origDefs[i], this.isOrigDefs[i], _ = es.GetDef(this.iSpecs[i].getIName(), this.iSpecs[i].getI())
	}
}

func (this *multiIterSpec) RestoreVarSnapshot(es expreduceapi.EvalStateInterface) {
	for i := range this.iSpecs {
		if this.isOrigDefs[i] {
			es.Define(this.iSpecs[i].getI(), this.origDefs[i])
		} else {
			es.Clear(this.iSpecs[i].getIName())
		}
	}
}

func (this *multiIterSpec) DefineCurrent(es expreduceapi.EvalStateInterface) {
	for i := range this.iSpecs {
		es.Define(this.iSpecs[i].getI(), this.iSpecs[i].GetCurr())
	}
}

func (this *multiIterSpec) CurrentPDManager() *matcher.PDManager {
	pm := matcher.EmptyPD()
	for i := range this.iSpecs {
		pm.Define(this.iSpecs[i].getIName(), this.iSpecs[i].GetCurr())
	}
	return pm
}

func EvalIterationFunc(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface, init expreduceapi.Ex, op string) expreduceapi.Ex {
	if len(this.GetParts()) >= 3 {
		mis, isOk := MultiIterSpecFromLists(es, this.GetParts()[2:])
		if isOk {
			// Simulate evaluation within Block[]
			mis.TakeVarSnapshot(es)
			var toReturn expreduceapi.Ex = init
			for mis.Cont() {
				mis.DefineCurrent(es)
				toReturn = es.Eval((atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol(op), toReturn, es.Eval(this.GetParts()[1].DeepCopy())})))
				mis.Next()
			}
			mis.RestoreVarSnapshot(es)
			return toReturn
		}
	}
	return this
}

func evalIterSpecCandidate(es expreduceapi.EvalStateInterface, cand expreduceapi.Ex) expreduceapi.Ex {
	// Special handling for Lists, which might have variables of iteration in
	// them.
	list, isList := atoms.HeadAssertion(cand, "System`List")
	if isList {
		toReturn := atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`List")})
		for i := 1; i < len(list.GetParts()); i++ {
			toAdd := list.GetParts()[i].DeepCopy()
			// Do not evaluate the variable of iteration. Even if "n" is
			// defined already, we just want it to be "n".
			if i != 1 {
				toAdd = es.Eval(toAdd)
			}
			toReturn.AppendEx(toAdd)
		}
		return toReturn
	}
	// We should attempt to evaluate all non-Lists, since we expect them to not
	// have any variables of iteration in them.
	return es.Eval(cand)
}
