package expreduce

import "math/big"

type iterSpec interface {
	// Should be called before every iteration:
	reset()
	next()
	cont() bool
	getCurr() Ex
	getI() Ex
	getIName() string
}

type iterSpecRange struct {
	i       Ex
	iName   string
	iMin    *Integer
	iMax    *Integer
	curr    int64
	iMaxInt int64
}

type iterSpecList struct {
	i     Ex
	iName string
	pos   int
	list  *Expression
}

func iterSpecFromList(es *EvalState, listEx Ex) (iterSpec, bool) {
	isr := &iterSpecRange{}
	isl := &iterSpecList{}

	listEx = evalIterSpecCandidate(es, listEx)
	list, isList := HeadAssertion(listEx, "List")
	if isList {
		iOk, iMinOk, iMaxOk := false, false, false
		if len(list.Parts) > 2 {
			iAsSymbol, iIsSymbol := list.Parts[1].(*Symbol)
			if iIsSymbol {
				iOk = true
				isr.i, isl.i = iAsSymbol, iAsSymbol
				isr.iName, isl.iName = iAsSymbol.Name, iAsSymbol.Name
			}
			iAsExpression, iIsExpression := list.Parts[1].(*Expression)
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
			isr.iMin, iMinOk = &Integer{big.NewInt(1)}, true
			isr.iMax, iMaxOk = list.Parts[2].(*Integer)
		} else if len(list.Parts) == 4 {
			isr.iMin, iMinOk = list.Parts[2].(*Integer)
			isr.iMax, iMaxOk = list.Parts[3].(*Integer)
		}
		if iOk && iMinOk && iMaxOk {
			isr.reset()
			return isr, true
		}

		// Conversion to iterSpecRange failed. Try iterSpecList.
		iterListOk := false
		if len(list.Parts) == 3 {
			isl.list, iterListOk = HeadAssertion(list.Parts[2], "List")
		}
		if iOk && iterListOk {
			isl.reset()
			return isl, true
		}
	}
	return isr, false
}

func (this *iterSpecRange) reset() {
	this.curr = this.iMin.Val.Int64()
	this.iMaxInt = this.iMax.Val.Int64()
}

func (this *iterSpecRange) next() {
	this.curr++
}

func (this *iterSpecRange) cont() bool {
	return this.curr <= this.iMaxInt
}

func (this *iterSpecRange) getCurr() Ex {
	return &Integer{big.NewInt(this.curr)}
}

func (this *iterSpecRange) getI() Ex {
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

func (this *iterSpecList) getCurr() Ex {
	return this.list.Parts[this.pos]
}

func (this *iterSpecList) getI() Ex {
	return this.i
}

func (this *iterSpecList) getIName() string {
	return this.iName
}

type multiIterSpec struct {
	iSpecs     []iterSpec
	origDefs   []Ex
	isOrigDefs []bool
	shouldCont bool
}

func multiIterSpecFromLists(es *EvalState, lists []Ex) (mis multiIterSpec, isOk bool) {
	// Retrieve variables of iteration
	mis.shouldCont = true
	for i := range lists {
		is, isOk := iterSpecFromList(es, lists[i])
		if !isOk {
			return mis, false
		}
		mis.iSpecs = append(mis.iSpecs, is)
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

func (this *multiIterSpec) takeVarSnapshot(es *EvalState) {
	this.origDefs = make([]Ex, len(this.iSpecs))
	this.isOrigDefs = make([]bool, len(this.iSpecs))
	for i := range this.iSpecs {
		this.origDefs[i], this.isOrigDefs[i] = es.GetDef(this.iSpecs[i].getIName(), this.iSpecs[i].getI())
	}
}

func (this *multiIterSpec) restoreVarSnapshot(es *EvalState) {
	for i := range this.iSpecs {
		if this.isOrigDefs[i] {
			es.Define(this.iSpecs[i].getIName(), this.iSpecs[i].getI(), this.origDefs[i])
		} else {
			es.Clear(this.iSpecs[i].getIName())
		}
	}
}

func (this *multiIterSpec) defineCurrent(es *EvalState) {
	for i := range this.iSpecs {
		es.Define(this.iSpecs[i].getIName(), this.iSpecs[i].getI(), this.iSpecs[i].getCurr())
	}
}

func (this *Expression) evalIterationFunc(es *EvalState, init Ex, op string) Ex {
	if len(this.Parts) >= 3 {
		mis, isOk := multiIterSpecFromLists(es, this.Parts[2:])
		if isOk {
			// Simulate evaluation within Block[]
			mis.takeVarSnapshot(es)
			var toReturn Ex = init
			for mis.cont() {
				mis.defineCurrent(es)
				toReturn = (&Expression{[]Ex{&Symbol{op}, toReturn, this.Parts[1].DeepCopy().Eval(es)}}).Eval(es)
				mis.next()
			}
			mis.restoreVarSnapshot(es)
			return toReturn
		}
	}
	return this
}

func evalIterSpecCandidate(es *EvalState, cand Ex) Ex {
	// Special handling for Lists, which might have variables of iteration in
	// them.
	list, isList := HeadAssertion(cand, "List")
	if isList {
		toReturn := &Expression{[]Ex{&Symbol{"List"}}}
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
