package expreduce

import "sort"

type extremaFnType int

const (
	MaxFn extremaFnType = iota
	MinFn
)

func extremaFunction(this *Expression, fnType extremaFnType, es *EvalState) Ex {
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
		return NewExpression(append([]Ex{this.Parts[0]}, this.Parts[i:]...))
	}
	if i == 1 {
		return this
	}
	return NewExpression(append(this.Parts[:2], this.Parts[i:]...))
}

func getComparisonDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Equal",
		toString: func(this *Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " == ", true, "", "", params)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) < 1 {
				return this
			}

			isequal := true
			for i := 2; i < len(this.Parts); i++ {
				var equalstr string = this.Parts[1].IsEqual(this.Parts[i], &es.CASLogger)
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
		toString: func(this *Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " != ", true, "", "", params)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			var isequal string = this.Parts[1].IsEqual(this.Parts[2], &es.CASLogger)
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return NewSymbol("System`False")
			} else if isequal == "EQUAL_FALSE" {
				return NewSymbol("System`True")
			}

			return NewExpression([]Ex{NewSymbol("System`Error"), NewString("Unexpected equality return value.")})
		},
	})
	defs = append(defs, Definition{
		Name: "SameQ",
		toString: func(this *Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " === ", true, "", "", params)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
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
		toString: func(this *Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " =!= ", true, "", "", params)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
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
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			_, IsExpr := this.Parts[1].(*Expression)
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
		toString: func(this *Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " < ", true, "", "", params)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			a := NewExpression([]Ex{NewSymbol("System`N"), this.Parts[1]}).Eval(es)
			b := NewExpression([]Ex{NewSymbol("System`N"), this.Parts[2]}).Eval(es)

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
		toString: func(this *Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " > ", true, "", "", params)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			a := NewExpression([]Ex{NewSymbol("System`N"), this.Parts[1]}).Eval(es)
			b := NewExpression([]Ex{NewSymbol("System`N"), this.Parts[2]}).Eval(es)

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
		toString: func(this *Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " <= ", true, "", "", params)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			a := NewExpression([]Ex{NewSymbol("System`N"), this.Parts[1]}).Eval(es)
			b := NewExpression([]Ex{NewSymbol("System`N"), this.Parts[2]}).Eval(es)

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
		toString: func(this *Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " >= ", true, "", "", params)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			a := NewExpression([]Ex{NewSymbol("System`N"), this.Parts[1]}).Eval(es)
			b := NewExpression([]Ex{NewSymbol("System`N"), this.Parts[2]}).Eval(es)

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
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			return extremaFunction(this, MaxFn, es)
		},
	})
	defs = append(defs, Definition{
		Name: "Min",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			return extremaFunction(this, MinFn, es)
		},
	})
	defs = append(defs, Definition{Name: "PossibleZeroQ"})
	return
}
