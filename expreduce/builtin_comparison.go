package expreduce

import (
	"sort"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type extremaFnType int

const (
	MaxFn extremaFnType = iota
	MinFn
)

func extremaFunction(this *expreduceapi.Expression, fnType extremaFnType, es *expreduceapi.EvalState) expreduceapi.Ex {
	// Flatten nested lists into arguments.
	origHead := this.Parts[0]
	this.Parts[0] = S("List")
	dst := E(S("List"))
	flattenExpr(this, dst, 999999999, &es.CASLogger)
	// Previously I always set the pointer but it led to an endless
	// eval loop. I think evaluation might use the pointer to make a
	// "same" comparison.
	if !IsSameQ(this, dst, &es.CASLogger) {
		this = dst
		sort.Sort(this)
	}
	this.Parts[0] = origHead

	if len(this.Parts) == 1 {
		if fnType == MaxFn {
			return E(S("Times"), NewInt(-1), S("Infinity"))
		} else {
			return S("Infinity")
		}
	}
	if len(this.Parts) == 2 {
		return this.Parts[1]
	}
	var i int
	for i = 1; i < len(this.Parts); i++ {
		if !numberQ(this.Parts[i]) {
			break
		}
	}
	if fnType == MaxFn {
		i -= 1
		return NewExpression(append([]expreduceapi.Ex{this.Parts[0]}, this.Parts[i:]...))
	}
	if i == 1 {
		return this
	}
	return NewExpression(append(this.Parts[:2], this.Parts[i:]...))
}

func getCompSign(e expreduceapi.Ex) int {
	sym, isSym := e.(*Symbol)
	if !isSym {
		return -2
	}
	switch sym.Name {
	case "System`Less":
		return -1
	case "System`LessEqual":
		return -1
	case "System`Equal":
		return 0
	case "System`GreaterEqual":
		return 1
	case "System`Greater":
		return 1
	}
	return -2
}

func getComparisonDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Equal",
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " == ", "System`Equal", false, "", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) < 1 {
				return this
			}

			isequal := true
			for i := 2; i < len(this.Parts); i++ {
				var equalstr string = this.Parts[1].IsEqual(this.Parts[i])
				if equalstr == "EQUAL_UNK" {
					return this
				}
				isequal = isequal && (equalstr == "EQUAL_TRUE")
			}
			if isequal {
				return NewSymbol("System`True")
			}
			return NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "Unequal",
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " != ", "System`Unequal", false, "", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			var isequal string = this.Parts[1].IsEqual(this.Parts[2])
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return NewSymbol("System`False")
			} else if isequal == "EQUAL_FALSE" {
				return NewSymbol("System`True")
			}

			return NewExpression([]expreduceapi.Ex{NewSymbol("System`Error"), NewString("Unexpected equality return value.")})
		},
	})
	defs = append(defs, Definition{
		Name: "SameQ",
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " === ", "System`SameQ", false, "", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) < 1 {
				return this
			}

			issame := true
			for i := 2; i < len(this.Parts); i++ {
				issame = issame && IsSameQ(this.Parts[1], this.Parts[i], &es.CASLogger)
			}
			if issame {
				return NewSymbol("System`True")
			} else {
				return NewSymbol("System`False")
			}
		},
	})
	defs = append(defs, Definition{
		Name: "UnsameQ",
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " =!= ", "System`UnsameQ", false, "", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) < 1 {
				return this
			}

			for i := 1; i < len(this.Parts); i++ {
				for j := i + 1; j < len(this.Parts); j++ {
					if IsSameQ(this.Parts[i], this.Parts[j], &es.CASLogger) {
						return NewSymbol("System`False")
					}
				}
			}
			return NewSymbol("System`True")
		},
	})
	defs = append(defs, Definition{
		Name: "AtomQ",
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}

			_, IsExpr := this.Parts[1].(*expreduceapi.Expression)
			if IsExpr {
				return NewSymbol("System`False")
			}
			return NewSymbol("System`True")
		},
	})
	defs = append(defs, Definition{
		Name:         "NumberQ",
		legacyEvalFn: singleParamQEval(numberQ),
	})
	defs = append(defs, Definition{
		Name: "NumericQ",
	})
	defs = append(defs, Definition{
		Name: "Less",
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " < ", "", true, "", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			a := NewExpression([]expreduceapi.Ex{NewSymbol("System`N"), this.Parts[1]}).Eval(es)
			b := NewExpression([]expreduceapi.Ex{NewSymbol("System`N"), this.Parts[2]}).Eval(es)

			if !numberQ(a) || !numberQ(b) {
				return this
			}

			// Less
			if ExOrder(a, b) == 1 {
				return NewSymbol("System`True")
			}
			return NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "Greater",
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " > ", "", true, "", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			a := NewExpression([]expreduceapi.Ex{NewSymbol("System`N"), this.Parts[1]}).Eval(es)
			b := NewExpression([]expreduceapi.Ex{NewSymbol("System`N"), this.Parts[2]}).Eval(es)

			if !numberQ(a) || !numberQ(b) {
				return this
			}
			// Greater
			if ExOrder(a, b) == -1 {
				return NewSymbol("System`True")
			}
			return NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "LessEqual",
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " <= ", "", true, "", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			a := NewExpression([]expreduceapi.Ex{NewSymbol("System`N"), this.Parts[1]}).Eval(es)
			b := NewExpression([]expreduceapi.Ex{NewSymbol("System`N"), this.Parts[2]}).Eval(es)

			if !numberQ(a) || !numberQ(b) {
				return this
			}
			// Less
			if ExOrder(a, b) == 1 {
				return NewSymbol("System`True")
			}
			// Equal
			if ExOrder(a, b) == 0 {
				return NewSymbol("System`True")
			}
			return NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "GreaterEqual",
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " >= ", "", true, "", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			a := NewExpression([]expreduceapi.Ex{NewSymbol("System`N"), this.Parts[1]}).Eval(es)
			b := NewExpression([]expreduceapi.Ex{NewSymbol("System`N"), this.Parts[2]}).Eval(es)

			if !numberQ(a) || !numberQ(b) {
				return this
			}
			// Greater
			if ExOrder(a, b) == -1 {
				return NewSymbol("System`True")
			}
			// Equal
			if ExOrder(a, b) == 0 {
				return NewSymbol("System`True")
			}
			return NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "Positive",
	})
	defs = append(defs, Definition{
		Name: "Negative",
	})
	defs = append(defs, Definition{
		Name: "Max",
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			return extremaFunction(this, MaxFn, es)
		},
	})
	defs = append(defs, Definition{
		Name: "Min",
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			return extremaFunction(this, MinFn, es)
		},
	})
	defs = append(defs, Definition{Name: "PossibleZeroQ"})
	defs = append(defs, Definition{Name: "MinMax"})
	defs = append(defs, Definition{Name: "Element"})
	defs = append(defs, Definition{
		Name: "Inequality",
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) == 1 {
				return this
			}
			if len(this.Parts) == 2 {
				return S("True")
			}
			if len(this.Parts)%2 != 0 {
				return this
			}
			firstSign := getCompSign(this.Parts[2])
			if firstSign == -2 {
				return this
			}
			if firstSign != 0 {
				for i := 4; i < len(this.Parts); i += 2 {
					thisSign := getCompSign(this.Parts[i])
					if thisSign == -2 {
						return this
					}
					if thisSign == -firstSign {
						firstIneq := E(S("Inequality"))
						secondIneq := E(S("Inequality"))
						for j := 1; j < len(this.Parts); j++ {
							if j < i {
								firstIneq.appendEx(this.Parts[j])
							}
							if j > (i - 2) {
								secondIneq.appendEx(this.Parts[j])
							}
						}
						return E(S("And"), firstIneq, secondIneq)
					}
				}
			}
			res := E(S("Inequality"))
			for i := 0; i < (len(this.Parts)-1)/2; i++ {
				lhs := this.Parts[2*i+1]
				if len(res.Parts) > 1 {
					lhs = res.Parts[len(res.Parts)-1]
				}
				op := this.Parts[2*i+2]
				rhs := this.Parts[2*i+3]
				for rhsI := 2*i + 3; rhsI < len(this.Parts); rhsI += 2 {
					if falseQ(E(op, lhs, this.Parts[rhsI]).Eval(es), &es.CASLogger) {
						return S("False")
					}
				}
				evalRes := E(op, lhs, rhs).Eval(es)
				if !trueQ(evalRes, &es.CASLogger) {
					if !IsSameQ(res.Parts[len(res.Parts)-1], lhs, &es.CASLogger) {
						res.appendEx(lhs)
					}
					res.appendEx(op)
					res.appendEx(rhs)
				}
			}
			if len(res.Parts) == 1 {
				return S("True")
			}
			if len(res.Parts) == 4 {
				return E(res.Parts[2], res.Parts[1], res.Parts[3])
			}
			return res
		},
	})
	return
}
