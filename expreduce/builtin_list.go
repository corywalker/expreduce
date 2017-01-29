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

func applyIndex(ex Ex, index Ex) (Ex, bool) {
	expr, isExpr := ex.(*Expression)
	if !isExpr {
		return nil, false
	}
	iInt, iIsInt := index.(*Integer)
	if iIsInt {
		if iInt.Val.Int64() >= int64(len(expr.Parts)) {
			return nil, false
		}
		return expr.Parts[iInt.Val.Int64()], true
	}
	iSym, iIsSym := index.(*Symbol)
	if iIsSym {
		if iSym.Name == "All" {
			return expr, true
		}
	}
	return nil, false
}

func GetListDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:       "List",
		Usage:      "`{e1, e2, ...}` groups expressions together.",
		Attributes: []string{"Locked"},
		toString:   (*Expression).ToStringList,
		SimpleExamples: []TestInstruction{
			&SameTest{"{1, 2, a}", "List[1,2,a]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Total",
		Usage: "`Total[list]` sums all the values in `list`.",
		Rules: []Rule{
			{"Total[l__List]", "Apply[Plus, l]"},
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"10", "Total[{1,2,3,4}]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"The total of an empty list is zero:"},
			&SameTest{"0", "Total[{}]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Mean",
		Usage: "`Mean[list]` calculates the statistical mean of `list`.",
		Rules: []Rule{
			{"Mean[l__List]", "Total[l]/Length[l]"},
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"11/2", "Mean[{5,6}]"},
		},
	})
	defs = append(defs, Definition{
		Name: "Table",
		Usage: "`Table[expr, n]` returns a list with `n` copies of `expr`.\n\n" +
			"`Table[expr, {sym, n}]` returns a list with `expr` evaluated with `sym` = 1 to `n`.\n\n" +
			"`Table[expr, {sym, m, n}]` returns a list with `expr` evaluated with `sym` = `m` to `n`.",
		Attributes: []string{"HoldAll"},
		Rules: []Rule{
			// Use a UniqueDefined` prefix, or else Table[i, 5] will return
			// incorrect results.
			{"Table[a_, b_Integer]", "Table[a, {UniqueDefined`i, 1, b}]"},
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) >= 3 {
				mis, isOk := multiIterSpecFromLists(es, this.Parts[2:])
				if isOk {
					// Simulate evaluation within Block[]
					mis.takeVarSnapshot(es)
					toReturn := NewExpression([]Ex{&Symbol{"List"}})
					for mis.cont() {
						mis.defineCurrent(es)
						toReturn.Parts = append(toReturn.Parts, this.Parts[1].DeepCopy().Eval(es))
						es.Debugf("%v\n", toReturn)
						mis.next()
					}
					mis.restoreVarSnapshot(es)
					return toReturn
				}
			}
			return this
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{a, a, a, a, a}", "Table[a, 5]"},
			&SameTest{"{5, 6, 7, 8, 9, 10}", "Table[i, {i, 5, 10}]"},
			&TestComment{"Create a list of the first 10 squares:"},
			&SameTest{"{1, 4, 9, 16, 25, 36, 49, 64, 81, 100}", "Table[n^2, {n, 1, 10}]"},
			&TestComment{"Iteration definitions do not have side effects:"},
			&StringTest{"i", "i"},
			&SameTest{"22", "i = 22"},
			&SameTest{"{5, 6, 7, 8, 9, 10}", "Table[i, {i, 5, 10}]"},
			&StringTest{"22", "i"},
		},
		FurtherExamples: []TestInstruction{
			&SameTest{"{0,1,2}", "Table[x[99], {x[_], 0, 2}]"},
		},
		Tests: []TestInstruction{
			&TestComment{"Test proper evaluation of the iterspec."},
			&SameTest{"Null", "testn := 5;"},
			&SameTest{"{1, 2, 3, 4, 5}", "Table[i, {i, testn}]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "MemberQ",
		Usage: "`MemberQ[expr, pat]` returns True if any of the elements in `expr` match `pat`, otherwise returns False.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			expr, isExpr := this.Parts[1].(*Expression)
			if isExpr {
				if MemberQ(expr.Parts[1:], this.Parts[2], &es.CASLogger) {
					return &Symbol{"True"}
				}
			}
			return &Symbol{"False"}
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"False", "MemberQ[{1, 2, 3}, 0]"},
			&SameTest{"True", "MemberQ[{1, 2, 3}, 1]"},
			&SameTest{"False", "MemberQ[{1, 2, 3}, {1}]"},
			&TestComment{"`MemberQ` works with patterns:"},
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
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"`MemberQ` works with BlankSequences:"},
			&SameTest{"True", "MemberQ[{a, b}, ___]"},
			&SameTest{"True", "MemberQ[{a, b}, __]"},
			&SameTest{"False", "MemberQ[{a, b}, __Integer]"},
			&SameTest{"False", "MemberQ[{a, b}, ___Integer]"},
			&SameTest{"True", "MemberQ[{a, b}, ___Symbol]"},
			&SameTest{"True", "MemberQ[{a, b}, __Symbol]"},
			&SameTest{"True", "MemberQ[{a, b, 1}, __Symbol]"},
			&SameTest{"True", "MemberQ[{a, b, 1}, __Integer]"},
			&TestComment{"`expr` need not be a List:"},
			&SameTest{"True", "MemberQ[bar[a, b, c], a]"},
			&SameTest{"False", "MemberQ[bar[a, b, c], bar]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Cases",
		Usage: "`Cases[expr, pat]` returns a new `List` of all elements in `expr` that match `pat`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[1].(*Expression)
			if isExpr {
				toReturn := NewExpression([]Ex{&Symbol{"List"}})

				for i := 1; i < len(expr.Parts); i++ {
					if matchq, _ := IsMatchQ(expr.Parts[i], this.Parts[2], EmptyPD(), &es.CASLogger); matchq {
						toReturn.Parts = append(toReturn.Parts, expr.Parts[i])
					}
				}

				return toReturn
			}
			return this
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{5, 2, 3.5, x, y, 4}", "Cases[{5, 2, 3.5, x, y, 4}, _]"},
			&SameTest{"{5,2,4}", "Cases[{5, 2, 3.5, x, y, 4}, _Integer]"},
			&SameTest{"{3.5}", "Cases[{5, 2, 3.5, x, y, 4}, _Real]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"`expr` need not be a list:"},
			&SameTest{"{a}", "Cases[bar[a, b, c], a]"},
		},
	})
	defs = append(defs, Definition{
		Name: "PadRight",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			list, n, x, valid := ValidatePadParams(this)
			if !valid {
				return this
			}
			toReturn := NewExpression([]Ex{list.Parts[0]})
			for i := int64(0); i < n; i++ {
				if i >= int64(len(list.Parts)-1) {
					toReturn.Parts = append(toReturn.Parts, x)
				} else {
					toReturn.Parts = append(toReturn.Parts, list.Parts[i+1])
				}
			}
			return toReturn
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{1, 2, 0, 0, 0}", "PadRight[{1, 2}, 5]"},
			&SameTest{"{1, 2, x, x, x}", "PadRight[{1, 2}, 5, x]"},
			&SameTest{"{1}", "PadRight[{1, 2}, 1, x]"},
		},
	})
	defs = append(defs, Definition{
		Name: "PadLeft",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			list, n, x, valid := ValidatePadParams(this)
			if !valid {
				return this
			}
			toReturn := NewExpression([]Ex{list.Parts[0]})
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
		SimpleExamples: []TestInstruction{
			&SameTest{"{0, 0, 0, 1, 2}", "PadLeft[{1, 2}, 5]"},
			&SameTest{"{x, x, x, 1, 2}", "PadLeft[{1, 2}, 5, x]"},
			&SameTest{"{2}", "PadLeft[{1, 2}, 1, x]"},
			&SameTest{"a[x, x, x, x, x]", "PadLeft[a[], 5, x]"},
		},
	})
	defs = append(defs, Definition{
		Name: "Range",
		Usage: "`Range[n]` returns a `List` of integers from 1 to `n`.\n\n" +
			"`Range[m, n]` returns a `List` of integers from `m` to `n`.",
		Attributes: []string{"Listable"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			// I should probably refactor the IterSpec system so that it does not
			// require being passed a list and a variable of iteration. TODO
			iterSpecList := NewExpression([]Ex{&Symbol{"List"}, &Symbol{"$DUMMY"}})
			iterSpecList.Parts = append(iterSpecList.Parts, this.Parts[1:]...)
			is, isOk := iterSpecFromList(es, iterSpecList)
			if !isOk {
				return this
			}
			toReturn := NewExpression([]Ex{&Symbol{"List"}})
			for is.cont() {
				toReturn.Parts = append(toReturn.Parts, is.getCurr())
				is.next()
			}
			return toReturn
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{1, 2, 3}", "Range[3]"},
			&SameTest{"{2, 3, 4, 5}", "Range[2, 5]"},
			//&SameTest{"{}", "Range[2, -5]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Part",
		Usage:      "`expr[[i]]` or `Part[expr, i]` returns the `i`th element of `expr`.",
		Attributes: []string{"NHoldRest", "ReadProtected"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) == 1 {
				return this
			}
			applied, ok := this.Parts[1], true
			// This assumes that e[[a, b]] is equivalent to e[[a]][[b]]. It is
			// in most cases, but try this with mat[[All, 5]]. It seems that
			// the indices are aware of each other and the fact that e is a
			// matrix. I will most likely need to perform this selection using
			// another method. TODO
			for i := 2; i < len(this.Parts); i++ {
				//es.Infof("applyIndex(%v, %v)", applied, this.Parts[i])
				applied, ok = applyIndex(applied, this.Parts[i])
				//es.Infof("after running, applied = %v", applied)
				if !ok {
					return this
				}
			}
			return applied
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Return the second item in a list:"},
			&SameTest{"b", "{a, b, c, d}[[2]]"},
			&TestComment{"Multi-dimensional indices are supported:"},
			&SameTest{"{{1, 4, 9, 16, 25}, {2, 8, 18, 32, 50}, {3, 12, 27, 48, 75}, {4, 16, 36, 64, 100}, {5, 20, 45, 80, 125}}", "mat = Table[Table[a*b^2, {b, 5}], {a, 5}]"},
			&SameTest{"20", "mat[[5, 2]]"},
			&TestComment{"Use `All` to select along the entire dimension:"},
			&SameTest{"{5, 20, 45, 80, 125}", "mat[[5, All]]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"Out of bounds issues will prevent the expression from evaluating:"},
			&SameTest{"{a}[[2]]", "Part[{a}, 2]"},
			&TestComment{"The input need not be a `List`:"},
			&SameTest{"foo", "Part[foo[a], 0]"},
			&TestComment{"Omitting an index will return the original expression:"},
			&SameTest{"i", "Part[i]"},
		},
		Tests: []TestInstruction{
			&SameTest{"i", "Part[i]"},
			&SameTest{"Part[]", "Part[]"},
			&SameTest{"{a, b}[[1.5]]", "Part[{a, b}, 1.5]"},
			&SameTest{"{a, b}[[a, 1.5]]", "Part[{a, b}, a, 1.5]"},
			&SameTest{"foo", "Part[foo[a], 0]"},
			&SameTest{"{{1, 4, 9, 16, 25}, {2, 8, 18, 32, 50}, {3, 12, 27, 48, 75}, {4, 16, 36, 64, 100}, {5, 20, 45, 80, 125}}", "mat = Table[Table[a*b^2, {b, 5}], {a, 5}]"},
			&SameTest{"20", "mat[[5, 2]]"},
			&SameTest{"{5, 20, 45, 80, 125}", "mat[[5, All]]"},
			//&SameTest{"{25, 50, 75, 100, 125}", "mat[[All, 5]]"},
			&SameTest{"foo[a, b, c]", "foo[a, b, c][[All]]"},
			&SameTest{"1[[5]]", "Part[1, 5]"},
			//&SameTest{"Integer[]", "Part[1, All]"},
			//&SameTest{"Symbol[]", "Part[a, All]"},
			&SameTest{"a", "Part[{a}, 1]"},
			&SameTest{"{a}[[2]]", "Part[{a}, 2]"},
			&SameTest{"{5, 20, 45, 80, 125}", "mat[[All]][[5]]"},
			&SameTest{"3", "{{1, 2}, {3, 4}}[[2, 1]]"},
			&SameTest{"{{1, 2}, {3}}[[2, 2]]", "{{1, 2}, {3}}[[2, 2]]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "All",
		Usage: "`All` allows selection along a dimension in `Part`.",
		SimpleExamples: []TestInstruction{
			&SameTest{"{{1, 4, 9, 16, 25}, {2, 8, 18, 32, 50}, {3, 12, 27, 48, 75}, {4, 16, 36, 64, 100}, {5, 20, 45, 80, 125}}", "mat = Table[Table[a*b^2, {b, 5}], {a, 5}]"},
			&TestComment{"Use `All` to select along the entire dimension:"},
			&SameTest{"{5, 20, 45, 80, 125}", "mat[[5, All]]"},
		},
	})
	return
}
