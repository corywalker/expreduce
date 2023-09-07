package iterspec

import (
	"math/big"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/matcher"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type IterSpec interface {
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

func SpecFromList(
	es expreduceapi.EvalStateInterface,
	listEx expreduceapi.Ex,
) (IterSpec, bool) {
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
			isl.list, iterListOk = atoms.HeadAssertion(
				list.GetParts()[2],
				"System`List",
			)
		}
		if iOk && iterListOk {
			isl.reset()
			return isl, true
		}
	}
	return isr, false
}

func (isr *iterSpecRange) reset() {
	//isr.curr = isr.iMin
	isr.curr = isr.es.Eval(
		atoms.E(
			atoms.S("Plus"),
			isr.iMin,
			atoms.E(atoms.S("Times"), atoms.NewInt(0), isr.step),
		),
	)
}

func (isr *iterSpecRange) Next() {
	isr.curr = isr.es.Eval(atoms.E(atoms.S("Plus"), isr.curr, isr.step))
}

func (isr *iterSpecRange) Cont() bool {
	return atoms.ExOrder(isr.curr, isr.iMax) >= 0
}

func (isr *iterSpecRange) GetCurr() expreduceapi.Ex {
	return isr.curr
}

func (isr *iterSpecRange) getI() expreduceapi.Ex {
	return isr.i
}

func (isr *iterSpecRange) getIName() string {
	return isr.iName
}

func (isl *iterSpecList) reset() {
	isl.pos = 1
}

func (isl *iterSpecList) Next() {
	isl.pos++
}

func (isl *iterSpecList) Cont() bool {
	return isl.pos < len(isl.list.GetParts())
}

func (isl *iterSpecList) GetCurr() expreduceapi.Ex {
	return isl.list.GetParts()[isl.pos]
}

func (isl *iterSpecList) getI() expreduceapi.Ex {
	return isl.i
}

func (isl *iterSpecList) getIName() string {
	return isl.iName
}

type MultiIterSpec struct {
	iSpecs     []IterSpec
	origDefs   []expreduceapi.Ex
	isOrigDefs []bool
	shouldCont bool
}

func MultiSpecFromLists(
	es expreduceapi.EvalStateInterface,
	lists []expreduceapi.Ex,
) (mis MultiIterSpec, isOk bool) {
	// Retrieve variables of iteration
	mis.shouldCont = true
	for i := range lists {
		is, isOk := SpecFromList(es, lists[i])
		if !isOk {
			return mis, false
		}
		mis.iSpecs = append(mis.iSpecs, is)
		mis.shouldCont = mis.shouldCont && is.Cont()
	}
	return mis, true
}

func (mis *MultiIterSpec) Next() {
	for i := len(mis.iSpecs) - 1; i >= 0; i-- {
		mis.iSpecs[i].Next()
		if mis.iSpecs[i].Cont() {
			return
		}
		mis.iSpecs[i].reset()
	}
	mis.shouldCont = false
}

func (mis *MultiIterSpec) Cont() bool {
	return mis.shouldCont
}

func (mis *MultiIterSpec) TakeVarSnapshot(es expreduceapi.EvalStateInterface) {
	mis.origDefs = make([]expreduceapi.Ex, len(mis.iSpecs))
	mis.isOrigDefs = make([]bool, len(mis.iSpecs))
	for i := range mis.iSpecs {
		mis.origDefs[i], mis.isOrigDefs[i], _ = es.GetDef(
			mis.iSpecs[i].getIName(),
			mis.iSpecs[i].getI(),
		)
	}
}

func (mis *MultiIterSpec) RestoreVarSnapshot(
	es expreduceapi.EvalStateInterface,
) {
	for i := range mis.iSpecs {
		if mis.isOrigDefs[i] {
			es.Define(mis.iSpecs[i].getI(), mis.origDefs[i])
		} else {
			es.Clear(mis.iSpecs[i].getIName())
		}
	}
}

func (mis *MultiIterSpec) DefineCurrent(es expreduceapi.EvalStateInterface) {
	for i := range mis.iSpecs {
		es.Define(mis.iSpecs[i].getI(), mis.iSpecs[i].GetCurr())
	}
}

func (mis *MultiIterSpec) CurrentPDManager() *matcher.PDManager {
	pm := matcher.EmptyPD()
	for i := range mis.iSpecs {
		pm.Define(mis.iSpecs[i].getIName(), mis.iSpecs[i].GetCurr())
	}
	return pm
}

func EvalIterationFunc(
	expr expreduceapi.ExpressionInterface,
	es expreduceapi.EvalStateInterface,
	init expreduceapi.Ex,
	op string,
) expreduceapi.Ex {
	if len(expr.GetParts()) >= 3 {
		mis, isOk := MultiSpecFromLists(es, expr.GetParts()[2:])
		if isOk {
			// Simulate evaluation within Block[]
			mis.TakeVarSnapshot(es)
			var toReturn expreduceapi.Ex = init
			for mis.Cont() {
				mis.DefineCurrent(es)
				toReturn = es.Eval(
					(atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol(op), toReturn, es.Eval(expr.GetParts()[1].DeepCopy())})),
				)
				mis.Next()
			}
			mis.RestoreVarSnapshot(es)
			return toReturn
		}
	}
	return expr
}

func evalIterSpecCandidate(
	es expreduceapi.EvalStateInterface,
	cand expreduceapi.Ex,
) expreduceapi.Ex {
	// Special handling for Lists, which might have variables of iteration in
	// them.
	list, isList := atoms.HeadAssertion(cand, "System`List")
	if isList {
		toReturn := atoms.NewExpression(
			[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
		)
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
