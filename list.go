package expreduce

import "bytes"
import "math/big"

func (this *Expression) ToStringList(form string) (bool, string) {
	if form == "FullForm" {
		return false, ""
	}
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range this.Parts[1:] {
		buffer.WriteString(e.String())
		if i != len(this.Parts[1:])-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return true, buffer.String()
}

type IterSpec struct {
	i       Ex
	iName   string
	iMin    *Integer
	iMax    *Integer
	curr    int64
	iMaxInt int64
}

func IterSpecFromList(listEx Ex) (is IterSpec, isOk bool) {
	list, isList := HeadAssertion(listEx, "List")
	if isList {
		iOk, iMinOk, iMaxOk := false, false, false
		if len(list.Parts) > 2 {
			iAsSymbol, iIsSymbol := list.Parts[1].(*Symbol)
			if iIsSymbol {
				iOk = true
				is.i = iAsSymbol
				is.iName = iAsSymbol.Name
			}
			iAsExpression, iIsExpression := list.Parts[1].(*Expression)
			if iIsExpression {
				headAsSymbol, headIsSymbol := iAsExpression.Parts[0].(*Symbol)
				if headIsSymbol {
					iOk = true
					is.i = iAsExpression
					is.iName = headAsSymbol.Name
				}
			}
		}
		if len(list.Parts) == 3 {
			is.iMin, iMinOk = &Integer{big.NewInt(1)}, true
			is.iMax, iMaxOk = list.Parts[2].(*Integer)
		} else if len(list.Parts) == 4 {
			is.iMin, iMinOk = list.Parts[2].(*Integer)
			is.iMax, iMaxOk = list.Parts[3].(*Integer)
		}
		if iOk && iMinOk && iMaxOk {
			is.Reset()
			return is, true
		}
	}
	return is, false
}

func (this *IterSpec) Reset() {
	this.curr = this.iMin.Val.Int64()
	this.iMaxInt = this.iMax.Val.Int64()
}

func (this *IterSpec) Next() {
	this.curr++
}

func (this *IterSpec) Cont() bool {
	return this.curr <= this.iMaxInt
}

type MultiIterSpec struct {
	iSpecs     []IterSpec
	origDefs   []Ex
	isOrigDefs []bool
	cont       bool
}

func MultiIterSpecFromLists(lists []Ex) (mis MultiIterSpec, isOk bool) {
	// Retrieve variables of iteration
	mis.cont = true
	for i := range lists {
		is, isOk := IterSpecFromList(lists[i])
		if !isOk {
			return mis, false
		}
		mis.iSpecs = append(mis.iSpecs, is)
	}
	return mis, true
}

func (this *MultiIterSpec) Next() {
	for i := len(this.iSpecs) - 1; i >= 0; i-- {
		this.iSpecs[i].Next()
		if this.iSpecs[i].Cont() {
			return
		}
		this.iSpecs[i].Reset()
	}
	this.cont = false
}

func (this *MultiIterSpec) Cont() bool {
	return this.cont
}

func (this *MultiIterSpec) TakeVarSnapshot(es *EvalState) {
	this.origDefs = make([]Ex, len(this.iSpecs))
	this.isOrigDefs = make([]bool, len(this.iSpecs))
	for i := range this.iSpecs {
		this.origDefs[i], this.isOrigDefs[i] = es.GetDef(this.iSpecs[i].iName, this.iSpecs[i].i)
	}
}

func (this *MultiIterSpec) RestoreVarSnapshot(es *EvalState) {
	for i := range this.iSpecs {
		if this.isOrigDefs[i] {
			es.Define(this.iSpecs[i].iName, this.iSpecs[i].i, this.origDefs[i])
		} else {
			es.Clear(this.iSpecs[i].iName)
		}
	}
}

func (this *MultiIterSpec) DefineCurrent(es *EvalState) {
	for i := range this.iSpecs {
		es.Define(this.iSpecs[i].iName, this.iSpecs[i].i, &Integer{big.NewInt(this.iSpecs[i].curr)})
	}
}

func (this *Expression) EvalIterationFunc(es *EvalState, init Ex, op string) Ex {
	if len(this.Parts) >= 3 {
		mis, isOk := MultiIterSpecFromLists(this.Parts[2:])
		if isOk {
			// Simulate evaluation within Block[]
			mis.TakeVarSnapshot(es)
			var toReturn Ex = init
			for mis.Cont() {
				mis.DefineCurrent(es)
				toReturn = (&Expression{[]Ex{&Symbol{op}, toReturn, this.Parts[1].DeepCopy().Eval(es)}}).Eval(es)
				mis.Next()
			}
			mis.RestoreVarSnapshot(es)
			return toReturn
		}
	}
	return this
}

func MemberQ(components []Ex, item Ex, cl *CASLogger) bool {
	for _, part := range components {
		if matchq, _ := IsMatchQ(part, item, EmptyPD(), cl); matchq {
			return true
		}
	}
	return false
}

func ValidatePadParams(this *Expression) (list *Expression, n int64, x Ex, valid bool) {
	valid = false
	x = &Integer{big.NewInt(0)}
	if len(this.Parts) == 4 {
		x = this.Parts[3]
	} else if len(this.Parts) != 3 {
		return
	}

	nInt, nIsInt := this.Parts[2].(*Integer)
	if !nIsInt {
		return
	}
	n = nInt.Val.Int64()

	list, listIsExpr := this.Parts[1].(*Expression)
	if !listIsExpr {
		return
	}

	valid = true
	return
}

func CalcDepth(ex Ex) int {
	expr, isExpr := ex.(*Expression)
	if !isExpr {
		return 1
	}
	theMax := 1
	// Find max depth of params. Heads are not counted.
	for i := 1; i < len(expr.Parts); i++ {
		theMax = Max(theMax, CalcDepth(expr.Parts[i]))
	}
	return theMax + 1
}

func GetListDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name:     "List",
		attributes: []string{"Locked"},
		toString: (*Expression).ToStringList,
	})
	defs = append(defs, Definition{
		name:      "Total",
		docstring: "Sum all the values in the list.",
		rules: []Rule{
			{"Total[l__List]", "Apply[Plus, l]"},
		},
		tests: []TestInstruction{
			&SameTest{"10", "Total[{1,2,3,4}]"},
			&SameTest{"0", "Total[{}]"},
		},
	})
	defs = append(defs, Definition{
		name:      "Mean",
		docstring: "Calculate the statistical mean of the list.",
		rules: []Rule{
			{"Mean[l__List]", "Total[l]/Length[l]"},
		},
		tests: []TestInstruction{
			&SameTest{"11/2", "Mean[{5,6}]"},
		},
	})
	defs = append(defs, Definition{
		name:      "Depth",
		docstring: "Return the depth of an expression.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			return &Integer{big.NewInt(int64(CalcDepth(this.Parts[1])))}
		},
		tests: []TestInstruction{
			&SameTest{"1", "Depth[foo]"},
			&SameTest{"2", "Depth[{foo}]"},
			&SameTest{"2", "Depth[bar[foo, bar]]"},
			&SameTest{"3", "Depth[foo[foo[]]]"},
			&SameTest{"1", "Depth[3]"},
			&SameTest{"1", "Depth[3.5]"},
			&SameTest{"1", "Depth[3/5]"},
			&SameTest{"2", "Depth[foo[{{{}}}][]]"},
		},
	})
	defs = append(defs, Definition{
		name: "Length",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			list, isList := HeadAssertion(this.Parts[1], "List")
			if isList {
				return &Integer{big.NewInt(int64(len(list.Parts) - 1))}
			}
			return this
		},
		tests: []TestInstruction{
			&SameTest{"4", "Length[{1,2,3,4}]"},
			&SameTest{"0", "Length[{}]"},
			&SameTest{"1", "Length[{5}]"},
		},
	})
	defs = append(defs, Definition{
		name: "Table",
		attributes: []string{"HoldAll"},
		rules: []Rule{
			{"Table[a_, b_Integer]", "Table[a, {i, 1, b}]"},
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) >= 3 {
				mis, isOk := MultiIterSpecFromLists(this.Parts[2:])
				if isOk {
					// Simulate evaluation within Block[]
					mis.TakeVarSnapshot(es)
					toReturn := &Expression{[]Ex{&Symbol{"List"}}}
					for mis.Cont() {
						mis.DefineCurrent(es)
						toReturn.Parts = append(toReturn.Parts, this.Parts[1].DeepCopy().Eval(es))
						es.Debugf("%v\n", toReturn)
						mis.Next()
					}
					mis.RestoreVarSnapshot(es)
					return toReturn
				}
			}
			return this
		},
		tests: []TestInstruction{
			&SameTest{"{a, a, a, a, a}", "Table[a, 5]"},
			&SameTest{"{5, 6, 7, 8, 9, 10}", "Table[i, {i, 5, 10}]"},
			&StringTest{"i", "i"},
			&SameTest{"10", "i = 10"},
			&SameTest{"{5, 6, 7, 8, 9, 10}", "Table[i, {i, 5, 10}]"},
			&StringTest{"10", "i"},
			&SameTest{"{1, 4, 9, 16, 25, 36, 49, 64, 81, 100}", "Table[n^2, {n, 1, 10}]"},
			&SameTest{"{0,1,2}", "Table[x[99], {x[_], 0, 2}]"},
		},
	})
	defs = append(defs, Definition{
		name: "Sum",
		attributes: []string{"HoldAll", "ReadProtected"},
		rules: []Rule{
			{"Sum[i_Symbol, {i_Symbol, 0, n_Integer}]", "1/2*n*(1 + n)"},
			{"Sum[i_Symbol, {i_Symbol, 1, n_Integer}]", "1/2*n*(1 + n)"},
			{"Sum[i_Symbol, {i_Symbol, 0, n_Symbol}]", "1/2*n*(1 + n)"},
			{"Sum[i_Symbol, {i_Symbol, 1, n_Symbol}]", "1/2*n*(1 + n)"},
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			return this.EvalIterationFunc(es, &Integer{big.NewInt(0)}, "Plus")
		},
		tests: []TestInstruction{
			&SameTest{"45", "Sum[i, {i, 5, 10}]"},
			&SameTest{"55", "Sum[i, {i, 1, 10}]"},
			&SameTest{"55", "Sum[i, {i, 0, 10}]"},
			&SameTest{"450015000", "Sum[i, {i, 1, 30000}]"},
			&SameTest{"450015000", "Sum[i, {i, 0, 30000}]"},
			&SameTest{"1/2*n*(1 + n)", "Sum[i, {i, 0, n}]"},
			&SameTest{"1/2*n*(1 + n)", "Sum[i, {i, 1, n}]"},
			&SameTest{"30", "Sum[a + b, {a, 0, 2}, {b, 0, 3}]"},
		},
	})
	defs = append(defs, Definition{
		name: "Product",
		attributes: []string{"HoldAll", "ReadProtected"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			return this.EvalIterationFunc(es, &Integer{big.NewInt(1)}, "Times")
		},
		tests: []TestInstruction{
			&SameTest{"120", "Product[a, {a, 1, 5}]"},
			&SameTest{"14400", "Product[a^2, {a, 1, 5}]"},
			&SameTest{"576", "Product[a^2, {a, 4}]"},
			&SameTest{"1440", "Product[a + b, {a, 1, 2}, {b, 1, 3}]"},
		},
	})
	defs = append(defs, Definition{
		name: "MemberQ",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			list, isList := HeadAssertion(this.Parts[1], "List")
			if isList {
				if MemberQ(list.Parts, this.Parts[2], &es.CASLogger) {
					return &Symbol{"True"}
				}
			}
			return &Symbol{"False"}
		},
		tests: []TestInstruction{
			&SameTest{"False", "MemberQ[{1, 2, 3}, 0]"},
			&SameTest{"True", "MemberQ[{1, 2, 3}, 1]"},
			&SameTest{"False", "MemberQ[{1, 2, 3}, {1}]"},
			&SameTest{"True", "MemberQ[{1, 2, 3}, _Integer]"},
			&SameTest{"True", "MemberQ[{1, 2, 3}, _]"},
			&SameTest{"False", "MemberQ[{1, 2, 3}, _Real]"},
			&SameTest{"True", "MemberQ[{1, 2, 3}, testmatch_Integer]"},
			&StringTest{"testmatch", "testmatch"},
			&SameTest{"False", "MemberQ[a, a]"},
			&SameTest{"False", "MemberQ[a, _]"},
			// More tests to be used in OrderlessIsMatchQ
			&SameTest{"False", "MemberQ[{a, b}, c]"},
			&SameTest{"True", "MemberQ[{a, b}, a]"},
			&SameTest{"True", "MemberQ[{a, b}, ___]"},
			&SameTest{"True", "MemberQ[{a, b}, __]"},
			&SameTest{"False", "MemberQ[{a, b}, __Integer]"},
			&SameTest{"False", "MemberQ[{a, b}, ___Integer]"},
			&SameTest{"True", "MemberQ[{a, b}, ___Symbol]"},
			&SameTest{"True", "MemberQ[{a, b}, __Symbol]"},
			&SameTest{"True", "MemberQ[{a, b, 1}, __Symbol]"},
			&SameTest{"True", "MemberQ[{a, b, 1}, __Integer]"},
		},
	})
	defs = append(defs, Definition{
		name: "Map",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			list, isList := HeadAssertion(this.Parts[2], "List")
			if isList {
				toReturn := &Expression{[]Ex{&Symbol{"List"}}}
				for i := 1; i < len(list.Parts); i++ {
					toReturn.Parts = append(toReturn.Parts, &Expression{[]Ex{
						this.Parts[1].DeepCopy(),
						list.Parts[i].DeepCopy(),
					}})
				}
				return toReturn
			}
			return this.Parts[2]
		},
		tests: []TestInstruction{
			&SameTest{"{foo[a], foo[b], foo[c]}", "Map[foo, {a, b, c}]"},
			&SameTest{"{foo[a], foo[b], foo[c]}", "foo /@ {a, b, c}"},
			&SameTest{"{2, 4, 9}", "Times /@ {2, 4, 9}"},
			&SameTest{"{foo[{a, b}], foo[c]}", "Map[foo, {{a, b}, c}]"},
			&SameTest{"Map[foo]", "Map[foo]"},
			&SameTest{"foo", "Map[foo, foo]"},
			&SameTest{"Map[foo, foo, foo]", "Map[foo, foo, foo]"},
			&SameTest{"{4,16}", "Function[x, x^2] /@ {2,4}"},
			&SameTest{"{4,16}", "Function[#^2] /@ {2,4}"},
		},
	})
	defs = append(defs, Definition{
		name: "Array",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			nInt, nOk := this.Parts[2].(*Integer)
			if nOk {
				n := nInt.Val.Int64()
				toReturn := &Expression{[]Ex{&Symbol{"List"}}}
				for i := int64(1); i <= n; i++ {
					toReturn.Parts = append(toReturn.Parts, &Expression{[]Ex{
						this.Parts[1].DeepCopy(),
						&Integer{big.NewInt(i)},
					}})
				}
				return toReturn
			}
			return this.Parts[2]
		},
		tests: []TestInstruction{
			&SameTest{"{f[1], f[2], f[3]}", "Array[f, 3]"},
			&SameTest{"Null", "mytest[x_] := 5"},
			&SameTest{"{5, 5, 5}", "Array[mytest, 3]"},
			&SameTest{"{(a + b)[1], (a + b)[2], (a + b)[3]}", "Array[a + b, 3]"},
			&SameTest{"Array[a, a]", "Array[a, a]"},
		},
	})
	defs = append(defs, Definition{
		name: "Cases",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			list, isList := HeadAssertion(this.Parts[1], "List")
			if isList {
				toReturn := &Expression{[]Ex{&Symbol{"List"}}}

				for i := 1; i < len(list.Parts); i++ {
					if matchq, _ := IsMatchQ(list.Parts[i], this.Parts[2], EmptyPD(), &es.CASLogger); matchq {
						toReturn.Parts = append(toReturn.Parts, list.Parts[i])
					}
				}

				return toReturn
			}
			return this
		},
		tests: []TestInstruction{
			&SameTest{"{5, 2, 3.5, x, y, 4}", "Cases[{5, 2, 3.5, x, y, 4}, _]"},
			&SameTest{"{5,2,4}", "Cases[{5, 2, 3.5, x, y, 4}, _Integer]"},
			&SameTest{"{3.5}", "Cases[{5, 2, 3.5, x, y, 4}, _Real]"},
		},
	})
	defs = append(defs, Definition{
		name: "PadRight",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			list, n, x, valid := ValidatePadParams(this)
			if !valid {
				return this
			}
			toReturn := &Expression{[]Ex{list.Parts[0]}}
			for i := int64(0); i < n; i++ {
				if i >= int64(len(list.Parts)-1) {
					toReturn.Parts = append(toReturn.Parts, x)
				} else {
					toReturn.Parts = append(toReturn.Parts, list.Parts[i+1])
				}
			}
			return toReturn
		},
		tests: []TestInstruction{
			&SameTest{"{1, 2, 0, 0, 0}", "PadRight[{1, 2}, 5]"},
			&SameTest{"{1, 2, x, x, x}", "PadRight[{1, 2}, 5, x]"},
			&SameTest{"{1}", "PadRight[{1, 2}, 1, x]"},
		},
	})
	defs = append(defs, Definition{
		name: "PadLeft",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			list, n, x, valid := ValidatePadParams(this)
			if !valid {
				return this
			}
			toReturn := &Expression{[]Ex{list.Parts[0]}}
			for i := int64(0); i < n; i++ {
				if i < n-int64(len(list.Parts))+1 {
					toReturn.Parts = append(toReturn.Parts, x)
				} else {
					listI := int64(len(list.Parts)) - (n - i)
					toReturn.Parts = append(toReturn.Parts, list.Parts[listI])
				}
			}
			return toReturn
		},
		tests: []TestInstruction{
			&SameTest{"{0, 0, 0, 1, 2}", "PadLeft[{1, 2}, 5]"},
			&SameTest{"{x, x, x, 1, 2}", "PadLeft[{1, 2}, 5, x]"},
			&SameTest{"{2}", "PadLeft[{1, 2}, 1, x]"},
			&SameTest{"a[x, x, x, x, x]", "PadLeft[a[], 5, x]"},
		},
	})
	defs = append(defs, Definition{
		name: "Range",
		attributes: []string{"Listable"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			// I should probably refactor the IterSpec system so that it does not
			// require being passed a list and a variable of iteration. TODO
			iterSpecList := &Expression{[]Ex{&Symbol{"List"}, &Symbol{"$DUMMY"}}}
			iterSpecList.Parts = append(iterSpecList.Parts, this.Parts[1:]...)
			is, isOk := IterSpecFromList(iterSpecList)
			if !isOk {
				return this
			}
			toReturn := &Expression{[]Ex{&Symbol{"List"}}}
			for is.Cont() {
				toReturn.Parts = append(toReturn.Parts, &Integer{big.NewInt(is.curr)})
				is.Next()
			}
			return toReturn
		},
		tests: []TestInstruction{
			&SameTest{"{1, 2, 3}", "Range[3]"},
			&SameTest{"{2, 3, 4, 5}", "Range[2, 5]"},
			//&SameTest{"{}", "Range[2, -5]"},
		},
	})
	return
}
