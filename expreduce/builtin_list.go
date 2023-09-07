package expreduce

import (
	"bytes"
	"math/big"
	"sort"
	"sync"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/iterspec"
	"github.com/corywalker/expreduce/expreduce/matcher"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

const maxUint64 = ^uint64(0)
const maxInt64 = int64(maxUint64 >> 1)

func toStringList(
	this expreduceapi.ExpressionInterface,
	params expreduceapi.ToStringParams,
) (bool, string) {
	if params.Form == "FullForm" {
		return false, ""
	}
	var buffer bytes.Buffer
	if params.Form == "TeXForm" {
		buffer.WriteString("\\left\\{")
	} else {
		buffer.WriteString("{")
	}
	for i, e := range this.GetParts()[1:] {
		params.PreviousHead = "<TOPLEVEL>"
		buffer.WriteString(e.StringForm(params))
		if i != len(this.GetParts()[1:])-1 {
			buffer.WriteString(",")
			if params.Form != "TeXForm" {
				buffer.WriteString(" ")
			}
		}
	}
	if params.Form == "TeXForm" {
		buffer.WriteString("\\right\\}")
	} else {
		buffer.WriteString("}")
	}
	return true, buffer.String()
}

func toStringPart(
	this expreduceapi.ExpressionInterface,
	params expreduceapi.ToStringParams,
) (bool, string) {
	if params.Form == "FullForm" {
		return false, ""
	}
	subParams := params
	subParams.PreviousHead = "<TOPLEVEL>"
	var buffer bytes.Buffer
	for i, e := range this.GetParts()[1:] {
		if i == 0 {
			buffer.WriteString(e.StringForm(params))
			buffer.WriteString("[[")
		} else {
			buffer.WriteString(e.StringForm(subParams))
			if i != len(this.GetParts()[1:])-1 {
				buffer.WriteString(",")
			}
		}
	}
	buffer.WriteString("]]")
	return true, buffer.String()
}

func memberQ(
	components []expreduceapi.Ex,
	item expreduceapi.Ex,
	es expreduceapi.EvalStateInterface,
) bool {
	for _, part := range components {
		if matchq, _ := matcher.IsMatchQ(part, item, matcher.EmptyPD(), es); matchq {
			return true
		}
	}
	return false
}

func validatePadParams(
	this expreduceapi.ExpressionInterface,
) (list expreduceapi.ExpressionInterface, n int64, x expreduceapi.Ex, valid bool) {
	valid = false
	x = atoms.NewInteger(big.NewInt(0))
	if len(this.GetParts()) == 4 {
		x = this.GetParts()[3]
	} else if len(this.GetParts()) != 3 {
		return
	}

	nInt, nIsInt := this.GetParts()[2].(*atoms.Integer)
	if !nIsInt {
		return
	}
	n = nInt.Val.Int64()

	list, listIsExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
	if !listIsExpr {
		return
	}

	valid = true
	return
}

func validateIndex(i expreduceapi.Ex, l int) (int64, bool) {
	iInt, iIsInt := i.(*atoms.Integer)
	if !iIsInt {
		return 0, false
	}
	if iInt.Val.Int64() >= int64(l) {
		return 0, false
	}
	// TODO: support this in the future.
	if iInt.Val.Int64() < 0 {
		return 0, false
	}
	return iInt.Val.Int64(), true
}

func applyIndex(
	ex expreduceapi.Ex,
	indices []expreduceapi.Ex,
	currDim int,
) (expreduceapi.Ex, bool) {
	// Base case
	if currDim >= len(indices) {
		return ex, true
	}
	expr, isExpr := ex.(expreduceapi.ExpressionInterface)
	if !isExpr {
		return nil, false
	}

	// Singular selection
	if _, iIsInt := indices[currDim].(*atoms.Integer); iIsInt {
		indexVal, indexOk := validateIndex(
			indices[currDim],
			len(expr.GetParts()),
		)
		if !indexOk {
			return nil, false
		}
		return applyIndex(expr.GetParts()[indexVal], indices, currDim+1)
	}

	// Range selections
	rangeMin, rangeMax, rangeOk := int64(0), int64(0), false
	if iSpan, iIsSpan := atoms.HeadAssertion(indices[currDim], "System`Span"); iIsSpan {
		if len(iSpan.GetParts()) != 3 {
			return nil, false
		}
		start, startOk := validateIndex(
			iSpan.GetParts()[1],
			len(expr.GetParts())+1,
		)
		end, endOk := validateIndex(iSpan.GetParts()[2], len(expr.GetParts()))
		if endSym, endIsSym := iSpan.GetParts()[2].(*atoms.Symbol); endIsSym {
			if endSym.Name == "System`All" {
				end, endOk = int64(len(expr.GetParts())-1), true
			}
		}
		if !startOk || !endOk {
			return nil, false
		}
		rangeMin, rangeMax, rangeOk = start, end, true
	}
	iSym, iIsSym := indices[currDim].(*atoms.Symbol)
	if iIsSym {
		if iSym.Name == "System`All" {
			rangeMin, rangeMax, rangeOk = 1, int64(len(expr.GetParts())-1), true
		}
	}
	if rangeOk {
		toReturn := atoms.E(expr.GetParts()[0])
		for i := rangeMin; i <= rangeMax; i++ {
			applied, appOk := applyIndex(expr.GetParts()[i], indices, currDim+1)
			if !appOk {
				return nil, false
			}
			toReturn.AppendEx(applied)
		}
		return toReturn, true
	}
	return nil, false
}

func threadExpr(
	expr expreduceapi.ExpressionInterface,
) (expreduceapi.ExpressionInterface, bool) {
	lengths := []int{}
	for i := 1; i < len(expr.GetParts()); i++ {
		list, isList := atoms.HeadAssertion(expr.GetParts()[i], "System`List")
		if isList {
			lengths = append(lengths, len(list.GetParts())-1)
		}
	}
	if len(lengths) == 0 {
		return expr, false
	}
	allSame := true
	for i := range lengths {
		allSame = allSame && (lengths[0] == lengths[i])
	}
	if !allSame {
		return expr, false
	}
	listLen := lengths[0]
	toReturn := atoms.NewExpression(
		[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
	)
	for listI := 0; listI < listLen; listI++ {
		thisExpr := atoms.NewExpression(
			[]expreduceapi.Ex{expr.GetParts()[0].DeepCopy()},
		)
		for i := 1; i < len(expr.GetParts()); i++ {
			list, isList := atoms.HeadAssertion(
				expr.GetParts()[i],
				"System`List",
			)
			if isList {
				thisExpr.AppendEx(list.GetParts()[listI+1])
			} else {
				thisExpr.AppendEx(expr.GetParts()[i])
			}
		}
		toReturn.AppendEx(thisExpr)
	}
	return toReturn, true
}

func countFunctionLevelSpec(
	pattern expreduceapi.Ex,
	e expreduceapi.Ex,
	partList []int64,
	generated *int64,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	if isMatch, _ := matcher.IsMatchQ(e, pattern, matcher.EmptyPD(), es); isMatch {
		*generated++
	}
	return e
}

func getListDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:     "List",
		toString: toStringList,
	})
	defs = append(defs, Definition{
		Name: "Total",
	})
	defs = append(defs, Definition{
		Name: "Mean",
	})
	defs = append(defs, Definition{
		Name: "Table",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) >= 3 {
				mis, isOk := iterspec.MultiSpecFromLists(
					es,
					this.GetParts()[2:],
				)
				if isOk {
					// Simulate evaluation within Block[]
					mis.TakeVarSnapshot(es)
					toReturn := atoms.NewExpression(
						[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
					)
					for mis.Cont() {
						mis.DefineCurrent(es)
						toReturn.AppendEx(es.Eval(this.GetPart(1).DeepCopy()))
						mis.Next()
					}
					mis.RestoreVarSnapshot(es)
					return toReturn
				}
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "ParallelTable",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) >= 3 {
				mis, isOk := iterspec.MultiSpecFromLists(
					es,
					this.GetParts()[2:],
				)
				if isOk {
					// Simulate evaluation within Block[]
					toReturn := atoms.NewExpression(
						[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
					)
					for mis.Cont() {
						toReturn.AppendEx(
							matcher.ReplacePD(
								this.GetParts()[1].DeepCopy(),
								es,
								mis.CurrentPDManager(),
							),
						)
						mis.Next()
					}
					var wg sync.WaitGroup
					for i := 1; i < len(toReturn.GetParts()); i++ {
						wg.Add(1)
						go func(idx int) {
							defer wg.Done()
							toReturn.GetParts()[idx] = es.Eval(
								toReturn.GetParts()[idx],
							)
						}(i)
					}
					wg.Wait()
					return toReturn
				}
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "MemberQ",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if isExpr {
				if memberQ(expr.GetParts()[1:], this.GetParts()[2], es) {
					return atoms.NewSymbol("System`True")
				}
			}
			return atoms.NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "Cases",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if isExpr {
				toReturn := atoms.NewExpression(
					[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
				)
				pattern := this.GetParts()[2]
				rule, isRule := atoms.HeadAssertion(
					this.GetParts()[2],
					"System`Rule",
				)
				if isRule {
					if len(rule.GetParts()) != 3 {
						return toReturn
					}
					pattern = rule.GetParts()[1]
				}

				for i := 1; i < len(expr.GetParts()); i++ {
					if matchq, pd := matcher.IsMatchQ(expr.GetParts()[i], pattern, matcher.EmptyPD(), es); matchq {
						toAdd := expr.GetParts()[i]
						if isRule {
							toAdd = matcher.ReplacePD(
								rule.GetParts()[2],
								es,
								pd,
							)
						}
						toReturn.AppendEx(toAdd)
					}
				}

				return toReturn
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "DeleteCases",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if isExpr {
				toReturn := atoms.NewExpression(
					[]expreduceapi.Ex{expr.GetParts()[0]},
				)
				pattern := this.GetParts()[2]
				for i := 1; i < len(expr.GetParts()); i++ {
					if matchq, _ := matcher.IsMatchQ(expr.GetParts()[i], pattern, matcher.EmptyPD(), es); !matchq {
						toAdd := expr.GetParts()[i]
						toReturn.AppendEx(toAdd)
					}
				}

				return toReturn
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Union",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) == 1 {
				return atoms.NewExpression(
					[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
				)
			}
			var firstHead expreduceapi.Ex
			var allParts expreduceapi.ExpressionInterface
			for _, part := range this.GetParts()[1:] {
				expr, isExpr := part.(expreduceapi.ExpressionInterface)
				if !isExpr {
					return this
				}
				if firstHead == nil {
					firstHead = expr.GetParts()[0]
					allParts = atoms.NewExpression([]expreduceapi.Ex{firstHead})
				} else if !atoms.IsSameQ(firstHead, expr.GetParts()[0]) {
					return this
				}
				allParts.AppendExArray(expr.GetParts()[1:])
			}
			sort.Sort(allParts)
			toReturn := atoms.NewExpression([]expreduceapi.Ex{firstHead})
			var lastEx expreduceapi.Ex
			for _, part := range allParts.GetParts()[1:] {
				if lastEx == nil || !atoms.IsSameQ(lastEx, part) {
					lastEx = part
					toReturn.AppendEx(part)
				}
			}

			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "Complement",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) == 1 {
				return this
			}
			var firstHead expreduceapi.Ex
			exclusions := map[uint64]bool{}
			for _, part := range this.GetParts()[1:] {
				expr, isExpr := part.(expreduceapi.ExpressionInterface)
				if !isExpr {
					return this
				}
				if firstHead == nil {
					firstHead = expr.GetParts()[0]
					continue
				} else if !atoms.IsSameQ(firstHead, expr.GetParts()[0]) {
					return this
				}
				for _, excludedPart := range expr.GetParts()[1:] {
					exclusions[hashEx(excludedPart)] = true
				}
			}
			toReturn := atoms.NewExpression([]expreduceapi.Ex{firstHead})
			added := map[uint64]bool{}
			for _, part := range this.GetParts()[1].(expreduceapi.ExpressionInterface).GetParts()[1:] {
				hash := hashEx(part)
				_, alreadyAdded := added[hash]
				_, excluded := exclusions[hash]
				if !excluded && !alreadyAdded {
					added[hash] = true
					toReturn.AppendEx(part)
				}
			}
			sort.Sort(toReturn)
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "Intersection",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) == 1 {
				return this
			}
			var firstHead expreduceapi.Ex
			intersection := map[uint64]int{}
			for _, part := range this.GetParts()[1:] {
				expr, isExpr := part.(expreduceapi.ExpressionInterface)
				if !isExpr {
					return this
				}
				if firstHead == nil {
					firstHead = expr.GetParts()[0]
				} else if !atoms.IsSameQ(firstHead, expr.GetParts()[0]) {
					return this
				}
				theseParts := map[uint64]bool{}
				for _, innerPart := range expr.GetParts()[1:] {
					theseParts[hashEx(innerPart)] = true
				}
				for hash := range theseParts {
					currVal, hasVal := intersection[hash]
					if !hasVal {
						intersection[hash] = 1
					} else {
						intersection[hash] = currVal + 1
					}
				}
			}
			toReturn := atoms.E(firstHead)
			added := map[uint64]bool{}
			for _, part := range this.GetParts()[1].(expreduceapi.ExpressionInterface).GetParts()[1:] {
				hash := hashEx(part)
				_, alreadyAdded := added[hash]
				intersection := intersection[hash] == this.Len()
				if intersection && !alreadyAdded {
					added[hash] = true
					toReturn.AppendEx(part)
				}
			}
			sort.Sort(toReturn)
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "PadRight",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			list, n, x, valid := validatePadParams(this)
			if !valid {
				return this
			}
			toReturn := atoms.NewExpression(
				[]expreduceapi.Ex{list.GetParts()[0]},
			)
			for i := int64(0); i < n; i++ {
				if i >= int64(len(list.GetParts())-1) {
					toReturn.AppendEx(x)
				} else {
					toReturn.AppendEx(list.GetParts()[i+1])
				}
			}
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "PadLeft",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			list, n, x, valid := validatePadParams(this)
			if !valid {
				return this
			}
			toReturn := atoms.NewExpression(
				[]expreduceapi.Ex{list.GetParts()[0]},
			)
			for i := int64(0); i < n; i++ {
				if i < n-int64(len(list.GetParts()))+1 {
					toReturn.AppendEx(x)
				} else {
					listI := int64(len(list.GetParts())) - (n - i)
					toReturn.AppendEx(list.GetParts()[listI])
				}
			}
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "Range",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			// I should probably refactor the IterSpec system so that it does not
			// require being passed a list and a variable of iteration. TODO
			iterSpecList := atoms.NewExpression(
				[]expreduceapi.Ex{
					atoms.NewSymbol("System`List"),
					atoms.NewSymbol("System`$DUMMY"),
				},
			)
			iterSpecList.AppendExArray(this.GetParts()[1:])
			is, isOk := iterspec.SpecFromList(es, iterSpecList)
			if !isOk {
				return this
			}
			toReturn := atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
			)
			for is.Cont() {
				toReturn.AppendEx(is.GetCurr())
				is.Next()
			}
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name:     "Part",
		toString: toStringPart,
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) == 1 {
				return this
			}
			applied, ok := applyIndex(
				this.GetParts()[1],
				this.GetParts()[2:],
				0,
			)
			if !ok {
				return this
			}
			return applied
		},
	})
	defs = append(defs, Definition{Name: "Span"})
	defs = append(defs, Definition{Name: "All"})
	defs = append(defs, Definition{
		Name: "Thread",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if !isExpr {
				return this.GetParts()[1]
			}
			newExpr, _ := threadExpr(expr)
			return newExpr
		},
	})
	defs = append(defs, Definition{
		Name: "Append",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if !isExpr {
				return this
			}
			res := atoms.NewExpression(
				append([]expreduceapi.Ex{}, expr.GetParts()...),
			)
			res.AppendEx(this.GetParts()[2])
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "AppendTo",
	})
	defs = append(defs, Definition{
		Name: "Prepend",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if !isExpr {
				return this
			}
			res := atoms.NewExpression([]expreduceapi.Ex{expr.GetParts()[0]})
			res.AppendEx(this.GetParts()[2])
			res.AppendExArray(expr.GetParts()[1:])
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "PrependTo",
	})
	defs = append(defs, Definition{
		Name: "DeleteDuplicates",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if isExpr {
				toReturn := atoms.NewExpression(
					[]expreduceapi.Ex{expr.GetParts()[0]},
				)
				seen := map[uint64]bool{}
				for _, orig := range expr.GetParts()[1:] {
					hash := hashEx(orig)
					_, isDupe := seen[hash]
					if !isDupe {
						seen[hash] = true
						toReturn.AppendEx(orig)
					}
				}
				return toReturn
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Select",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			maxN := maxInt64
			if len(this.GetParts()) == 4 {
				if asInt, isInt := this.GetParts()[3].(*atoms.Integer); isInt {
					maxN = asInt.Val.Int64()
					if maxN < 0 {
						return this
					}
				} else {
					return this
				}
			} else if len(this.GetParts()) != 3 {
				return this
			}

			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if isExpr {
				res := atoms.NewExpression(
					[]expreduceapi.Ex{expr.GetParts()[0]},
				)
				added := int64(0)
				for _, part := range expr.GetParts()[1:] {
					if added >= maxN {
						break
					}
					pass :=

						es.Eval((atoms.NewExpression([]expreduceapi.Ex{
							this.GetParts()[2],
							part,
						})))

					passSymbol, passIsSymbol := pass.(*atoms.Symbol)
					if passIsSymbol {
						if passSymbol.Name == "System`True" {
							res.AppendEx(part)
							added++
						}
					}
				}
				return res
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Scan",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			expr, isExpr := this.GetParts()[2].(expreduceapi.ExpressionInterface)
			if !isExpr {
				return this
			}
			for _, part := range expr.GetParts()[1:] {
				res :=

					es.Eval((atoms.NewExpression([]expreduceapi.Ex{
						this.GetParts()[1],
						part,
					})))

				if es.HasThrown() {
					return es.Thrown()
				}
				if asReturn, isReturn := atoms.HeadAssertion(res, "System`Return"); isReturn {
					if len(asReturn.GetParts()) < 2 {
						return atoms.NewSymbol("System`Null")
					}
					return asReturn.GetParts()[1]
				}
			}
			return atoms.NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "Join",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) <= 1 {
				return atoms.NewHead("System`List")
			}

			res := atoms.NewEmptyExpression()
			for _, part := range this.GetParts()[1:] {
				expr, isExpr := part.(expreduceapi.ExpressionInterface)
				if !isExpr {
					return this
				}
				if len(res.GetParts()) == 0 {
					res.AppendExArray(expr.GetParts())
				} else {
					if !atoms.IsSameQ(expr.GetParts()[0], res.GetParts()[0]) {
						return this
					}
					res.AppendExArray(expr.GetParts()[1:])
				}
			}
			return res
		},
	})
	defs = append(defs, Definition{Name: "ListQ"})
	defs = append(defs, Definition{Name: "Last"})
	defs = append(defs, Definition{Name: "First"})
	defs = append(defs, Definition{Name: "Rest"})
	defs = append(defs, Definition{
		Name: "Count",
		legacyEvalFn: levelSpecFunction(
			countFunctionLevelSpec,
			unoptimizedSimpleLevelSpec,
			true,
			true,
		),
	})
	defs = append(defs, Definition{Name: "Tally"})
	defs = append(defs, Definition{Name: "ConstantArray"})
	defs = append(defs, Definition{
		Name: "Reverse",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if !isExpr {
				return this
			}
			res := atoms.NewExpression([]expreduceapi.Ex{expr.GetParts()[0]})
			for i := len(expr.GetParts()) - 1; i > 0; i-- {
				res.AppendEx(expr.GetParts()[i])
			}
			return res
		},
	})
	return
}
