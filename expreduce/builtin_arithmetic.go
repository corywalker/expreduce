package expreduce

import (
	"bytes"
	"fmt"
	"math/big"
	"strings"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/iterspec"
	"github.com/corywalker/expreduce/expreduce/parser/parens"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

// Define a special NumberQ for our purposes since this logic does not support
// complex numbers yet. TODO(corywalker): fix this.
func numberQForTermCollection(e expreduceapi.Ex) bool {
	// _, ok := e.(*Complex)
	// if ok {
	// 	return false
	// }
	return atoms.NumberQ(e)
}

func splitTerm(e expreduceapi.Ex) (expreduceapi.Ex, expreduceapi.Ex, bool) {
	asSym, isSym := e.(*atoms.Symbol)
	if isSym {
		return atoms.NewInteger(
				big.NewInt(1),
			), atoms.NewExpression(
				[]expreduceapi.Ex{
					atoms.NewSymbol("System`Times"),
					asSym,
				},
			),

			true
	}
	asTimes, isTimes := atoms.HeadAssertion(e, "System`Times")
	if isTimes {
		if len(asTimes.GetParts()) < 2 {
			return nil, nil, false
		}
		if numberQForTermCollection(asTimes.GetParts()[1]) {
			if len(asTimes.GetParts()) > 2 {
				return asTimes.GetParts()[1], atoms.NewExpression(
					append(
						[]expreduceapi.Ex{atoms.NewSymbol("System`Times")},
						asTimes.GetParts()[2:]...),
				), true
			}
		} else {
			return atoms.NewInteger(big.NewInt(1)), atoms.NewExpression(append([]expreduceapi.Ex{atoms.NewSymbol("System`Times")}, asTimes.GetParts()[1:]...)), true
		}
	}
	asExpr, isExpr := e.(expreduceapi.ExpressionInterface)
	if isExpr {
		return atoms.NewInteger(
				big.NewInt(1),
			), atoms.NewExpression(
				[]expreduceapi.Ex{
					atoms.NewSymbol("System`Times"),
					asExpr,
				},
			),

			true
	}
	return nil, nil, false
}

func collectedToTerm(
	coeffs []expreduceapi.Ex,
	vars expreduceapi.Ex,
	fullPart expreduceapi.Ex,
) expreduceapi.Ex {
	// Preserve the original expression if there is no need to change it.
	// We can keep all the cached values like the hash.
	if len(coeffs) == 1 {
		return fullPart
	}

	finalC, _ := atoms.ComputeNumericPart(
		atoms.FoldFnAdd,
		atoms.NewExpression(append([]expreduceapi.Ex{
			atoms.NewSymbol("System`Plus")}, coeffs...)),
	)

	toAdd := atoms.NewExpression(
		[]expreduceapi.Ex{atoms.NewSymbol("System`Times")},
	)
	cAsInt, cIsInt := finalC.(*atoms.Integer)
	if !(cIsInt && cAsInt.Val.Cmp(big.NewInt(1)) == 0) {
		toAdd.AppendEx(finalC)
	}
	vAsExpr, vIsExpr := atoms.HeadAssertion(vars, "System`Times")
	if vIsExpr && len(vAsExpr.GetParts()) == 2 {
		vars = vAsExpr.GetParts()[1]
	}
	toAdd.AppendEx(vars)
	if len(toAdd.GetParts()) == 2 {
		return toAdd.GetParts()[1]
	}
	return toAdd
}

func collectTerms(
	e expreduceapi.ExpressionInterface,
) expreduceapi.ExpressionInterface {
	collected := atoms.NewExpression(
		[]expreduceapi.Ex{atoms.NewSymbol("System`Plus")},
	)
	var lastVars expreduceapi.Ex
	var lastFullPart expreduceapi.Ex
	lastCoeffs := []expreduceapi.Ex{}
	for _, part := range e.GetParts()[1:] {
		coeff, vars, isTerm := splitTerm(part)
		if isTerm {
			if lastVars == nil {
				lastCoeffs = []expreduceapi.Ex{coeff}
				lastVars = vars
				lastFullPart = part
			} else {
				if hashEx(vars) == hashEx(lastVars) {
					lastCoeffs = append(lastCoeffs, coeff)
				} else {
					collected.AppendEx(collectedToTerm(lastCoeffs, lastVars, lastFullPart))

					lastCoeffs = []expreduceapi.Ex{coeff}
					lastVars = vars
					lastFullPart = part
				}
			}
		} else {
			collected.AppendEx(part)
		}
	}
	if lastVars != nil {
		collected.AppendEx(collectedToTerm(lastCoeffs, lastVars, lastFullPart))
	}
	return collected
}

func splitFrac(ex expreduceapi.Ex) (num expreduceapi.Ex, den expreduceapi.Ex) {
	asPow, isPow := atoms.HeadAssertion(ex, "System`Power")
	if isPow {
		if asPow.Len() != 2 {
			return ex, nil
		}
		powInt, powIsInt := asPow.GetPart(2).(*atoms.Integer)
		if !powIsInt {
			return ex, nil
		}
		if powInt.Val.Int64() == -1 {
			return nil, asPow.GetPart(1)
		}
	}
	asRat, isRat := ex.(*atoms.Rational)
	if isRat {
		if asRat.Num.Int64() == 1 {
			return nil, atoms.NewInteger(asRat.Den)
		}
		return atoms.NewInteger(asRat.Num), atoms.NewInteger(asRat.Den)
	}
	return ex, nil
}

func getArithmeticDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:    "Plus",
		Default: "0",
		toString: func(this expreduceapi.ExpressionInterface, p expreduceapi.ToStringParams) (bool, string) {
			thisHead := "System`Plus"
			parts := this.GetParts()[1:]
			if p.Form != "InputForm" && p.Form != "OutputForm" &&
				p.Form != "TeXForm" {
				return false, ""
			}
			if len(parts) < 2 {
				return false, ""
			}
			addParens := parens.NeedsParens(thisHead, p.PreviousHead)
			var buffer bytes.Buffer
			if addParens {
				if p.Form == "TeXForm" {
					buffer.WriteString("{\\left(")
				} else {
					buffer.WriteString("(")
				}
			}
			nextParams := p
			nextParams.PreviousHead = thisHead
			for i := 0; i < len(parts); i++ {
				toWrite := parts[i].StringForm(nextParams)
				if i != 0 {
					if toWrite[0] == '-' {
						buffer.WriteString(" - ")
						toWrite = toWrite[1:]
					} else {
						buffer.WriteString(" + ")
					}
				}
				buffer.WriteString(toWrite)
			}
			if addParens {
				if p.Form == "TeXForm" {
					buffer.WriteString("\\right)}")
				} else {
					buffer.WriteString(")")
				}
			}
			return true, buffer.String()
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			// Calls without argument receive identity values
			if len(this.GetParts()) == 1 {
				return atoms.NewInteger(big.NewInt(0))
			}

			res := this
			realPart, symStart := atoms.ComputeNumericPart(
				atoms.FoldFnAdd,
				this,
			)
			if realPart != nil {
				if symStart == -1 {
					return realPart
				}
				res = atoms.NewExpression(
					[]expreduceapi.Ex{atoms.NewSymbol("System`Plus")},
				)
				rAsInt, rIsInt := realPart.(*atoms.Integer)
				if !(rIsInt && rAsInt.Val.Cmp(big.NewInt(0)) == 0) {
					res.AppendEx(realPart)
				}
				res.AppendExArray(this.GetParts()[symStart:])
			}

			collected := collectTerms(res)
			if hashEx(collected) != hashEx(res) {
				res = collected
			}

			// If one expression remains, replace this Plus with the expression
			if len(res.GetParts()) == 2 {
				return res.GetParts()[1]
			}

			// Not exactly right because of "1. + foo[1]", but close enough.
			if _, rIsReal := realPart.(*atoms.Flt); rIsReal {
				return exprToN(es, res)
			}
			if rComplex, rIsComplex := realPart.(*atoms.Complex); rIsComplex &&
				rComplex.HasReal() {
				return exprToN(es, res)
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Sum",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			return iterspec.EvalIterationFunc(
				this,
				es,
				atoms.NewInteger(big.NewInt(0)),
				"System`Plus",
			)
		},
	})
	defs = append(defs, Definition{
		Name:    "Times",
		Default: "1",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			delim := "*"
			if params.Form == "TeXForm" {
				delim = " "
			}

			timesParts := atoms.E(atoms.S("Times"))
			for _, part := range this.GetParts()[1:] {
				partAsComplex, partIsComplex := part.(*atoms.Complex)
				if partIsComplex {
					asExpr := partAsComplex.AsExpr()
					cmplxTimes, cmplxIsTimes := atoms.HeadAssertion(
						asExpr,
						"System`Times",
					)
					if cmplxIsTimes {
						for _, cmplxPart := range cmplxTimes.GetParts()[1:] {
							timesParts.AppendEx(cmplxPart)
						}
						continue
					}
				}
				timesParts.AppendEx(part)
			}

			num := atoms.E(atoms.S("Times"))
			den := atoms.E(atoms.S("Times"))
			for _, part := range timesParts.GetParts()[1:] {
				numPart, denPart := splitFrac(part)
				if numPart != nil {
					num.AppendEx(numPart)
				}
				if denPart != nil {
					den.AppendEx(denPart)
				}
			}
			if den.Len() > 0 {
				numOk, numStr := toStringInfix(
					num.GetParts()[1:],
					delim,
					"System`Times",
					params,
				)
				if num.Len() == 1 {
					numOk, numStr = true, num.GetPart(1).StringForm(params)
				}
				denOk, denStr := toStringInfix(
					den.GetParts()[1:],
					delim,
					"System`Times",
					params,
				)
				if den.Len() == 1 {
					denOk, denStr = true, den.GetPart(1).StringForm(params)
				}
				if !numOk || !denOk {
					return false, ""
				}
				prefix := ""
				if strings.HasPrefix(numStr, "-1"+delim) {
					prefix = "-"
					numStr = numStr[3:]
				}
				if params.Form == "TeXForm" {
					return true, fmt.Sprintf(
						"%v\\frac{%v}{%v}",
						prefix,
						numStr,
						denStr,
					)
				}
				if params.Form == "FullForm" {
					return false, ""
				}
				return true, fmt.Sprintf("%v(%v)/(%v)", prefix, numStr, denStr)
			}
			ok, res := toStringInfix(
				num.GetParts()[1:],
				delim,
				"System`Times",
				params,
			)
			if !ok {
				return false, ""
			}
			if strings.HasPrefix(res, "-1"+delim) {
				return true, "-" + res[3:]
			}
			return true, res
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			// Calls without argument receive identity values
			if len(this.GetParts()) == 1 {
				return atoms.NewInteger(big.NewInt(1))
			}

			res := this
			realPart, symStart := atoms.ComputeNumericPart(
				atoms.FoldFnMul,
				this,
			)
			if realPart != nil {
				if symStart == -1 {
					return realPart
				}
				res = atoms.NewExpression(
					[]expreduceapi.Ex{atoms.NewSymbol("System`Times")},
				)
				rAsInt, rIsInt := realPart.(*atoms.Integer)
				if rIsInt && rAsInt.Val.Cmp(big.NewInt(0)) == 0 {
					containsInfinity := memberQ(
						this.GetParts()[symStart:],
						atoms.NewExpression([]expreduceapi.Ex{
							atoms.NewSymbol("System`Alternatives"),
							atoms.NewSymbol("System`Infinity"),
							atoms.NewSymbol("System`ComplexInfinity"),
							atoms.NewSymbol("System`Indeterminate"),
						}),

						es,
					)
					if containsInfinity {
						return atoms.NewSymbol("System`Indeterminate")
					}
					return atoms.NewInteger(big.NewInt(0))
				}
				if !(rIsInt && rAsInt.Val.Cmp(big.NewInt(1)) == 0) {
					res.AppendEx(realPart)
				}
				res.AppendExArray(this.GetParts()[symStart:])
			}

			// If one expression remains, replace this Times with the expression
			if len(res.GetParts()) == 2 {
				return res.GetParts()[1]
			}

			// Automatically Expand negations (*-1), not (*-1.) of a Plus expression
			// Perhaps better implemented as a rule.
			if len(res.GetParts()) == 3 {
				leftint, leftintok := res.GetParts()[1].(*atoms.Integer)
				rightplus, rightplusok := atoms.HeadAssertion(
					res.GetParts()[2],
					"System`Plus",
				)
				if leftintok && rightplusok {
					if leftint.Val.Cmp(big.NewInt(-1)) == 0 {
						toreturn := atoms.NewExpression(
							[]expreduceapi.Ex{atoms.NewSymbol("System`Plus")},
						)
						addends := rightplus.GetParts()[1:len(rightplus.GetParts())]
						for i := range addends {
							toAppend := atoms.NewExpression([]expreduceapi.Ex{
								atoms.NewSymbol("System`Times"),
								addends[i],
								atoms.NewInteger(big.NewInt(-1)),
							})

							toreturn.AppendEx(toAppend)
						}
						return es.Eval(toreturn)
					}
				}
			}

			// Not exactly right because of "1. + foo[1]", but close enough.
			if _, rIsReal := realPart.(*atoms.Flt); rIsReal {
				return exprToN(es, res)
			}
			if rComplex, rIsComplex := realPart.(*atoms.Complex); rIsComplex &&
				rComplex.HasReal() {
				return exprToN(es, res)
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Product",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			return iterspec.EvalIterationFunc(
				this,
				es,
				atoms.NewInteger(big.NewInt(1)),
				"System`Times",
			)
		},
	})
	defs = append(defs, Definition{Name: "Abs"})
	defs = append(defs, Definition{Name: "Divide"})
	defs = append(defs, Definition{Name: "Increment"})
	defs = append(defs, Definition{Name: "Decrement"})
	defs = append(defs, Definition{Name: "PreIncrement"})
	defs = append(defs, Definition{Name: "PreDecrement"})
	defs = append(defs, Definition{Name: "AddTo"})
	defs = append(defs, Definition{Name: "SubtractFrom"})
	return
}
