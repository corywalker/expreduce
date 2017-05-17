package expreduce

func GetBooleanDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:       "And",
		Usage:      "`e1 && e2 && ...` returns `True` if all expressions evaluate to `True`.",
		Attributes: []string{"Flat", "HoldAll", "OneIdentity"},
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfix(this.Parts[1:], " && ", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			res := &Expression{[]Ex{&Symbol{"And"}}}
			for i := 1; i < len(this.Parts); i++ {
				this.Parts[i] = this.Parts[i].Eval(es)
				if booleanQ(this.Parts[i], &es.CASLogger) {
				    if falseQ(this.Parts[i], &es.CASLogger) {
						return &Symbol{"False"}
					}
				} else {
					res.appendEx(this.Parts[i])
				}
			}
			if len(res.Parts) == 1 {
				return &Symbol{"True"}
			}
			if len(res.Parts) == 2 {
				return res.Parts[1]
			}
			return res
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"False", "True && False"},
			&SameTest{"True", "True && True && True"},
		},
		Tests: []TestInstruction{
			&SameTest{"True", "And[]"},
			&SameTest{"1", "1 && True && True"},
			&SameTest{"False", "True && False"},
			&SameTest{"False", "False && True"},
			&SameTest{"True", "True && True"},
			&SameTest{"False", "False && 1"},
			&SameTest{"False", "1 && False"},
			&SameTest{"1 && 1", "1 && 1"},
			&SameTest{"1 && 1 && kfdkkfd", "1 && 1 && kfdkkfd"},
			&SameTest{"1 && 1 && kfdkkfd", "1 && 1 && True && kfdkkfd"},
			&SameTest{"False", "1 && 1 && True && False && kfdkkfd"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Or",
		Usage:      "`e1 || e2 || ...` returns `True` if any expressions evaluate to `True`.",
		Attributes: []string{"Flat", "HoldAll", "OneIdentity"},
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfix(this.Parts[1:], " || ", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			res := &Expression{[]Ex{&Symbol{"Or"}}}
			for i := 1; i < len(this.Parts); i++ {
				this.Parts[i] = this.Parts[i].Eval(es)
				if booleanQ(this.Parts[i], &es.CASLogger) {
				    if trueQ(this.Parts[i], &es.CASLogger) {
						return &Symbol{"True"}
					}
				} else {
					res.appendEx(this.Parts[i])
				}
			}
			if len(res.Parts) == 1 {
				return &Symbol{"False"}
			}
			if len(res.Parts) == 2 {
				return res.Parts[1]
			}
			return res
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "True || False"},
			&SameTest{"False", "False || False || False"},
		},
		Tests: []TestInstruction{
			&SameTest{"a || b", "a || b"},
			&SameTest{"True", "a || True || b"},
			&SameTest{"True", "a || True || False"},
			&SameTest{"a || b", "a || b || False"},
			&SameTest{"a || b", "a || b || False || False"},
			&SameTest{"a || b", "a || False || b || False || False"},
			&SameTest{"True", "True || False"},
			&SameTest{"False", "False || False"},
			&SameTest{"False", "Or[False]"},
			&SameTest{"False", "Or[]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Not",
		Usage:      "`!e` returns `True` if `e` is `False` and `False` if `e` is `True`.",
		Attributes: []string{},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			if trueQ(this.Parts[1], &es.CASLogger) {
				return &Symbol{"False"}
			}
			if falseQ(this.Parts[1], &es.CASLogger) {
				return &Symbol{"True"}
			}
			return this
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"False", "!True"},
			&SameTest{"True", "!False"},
			&SameTest{"!a", "!a"},
			&SameTest{"a", "!!a"},
		},
		Rules: []Rule{
			{"!!e_", "e"},
		},
	})
	defs = append(defs, Definition{
		Name:         "TrueQ",
		Usage:        "`TrueQ[expr]` returns True if `expr` is True, False otherwise.",
		legacyEvalFn: singleParamQLogEval(trueQ),
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "TrueQ[True]"},
			&SameTest{"False", "TrueQ[False]"},
			&SameTest{"False", "TrueQ[1]"},
		},
	})
	defs = append(defs, Definition{
		Name:         "BooleanQ",
		Usage:        "`BooleanQ[expr]` returns True if `expr` is True or False, False otherwise.",
		legacyEvalFn: singleParamQLogEval(booleanQ),
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "BooleanQ[True]"},
			&SameTest{"True", "BooleanQ[False]"},
			&SameTest{"False", "BooleanQ[1]"},
		},
	})
	defs = append(defs, Definition{
		Name:         "AllTrue",
		Usage:        "`AllTrue[list, condition]` returns True if all parts of `list` satisfy `condition`.",
		SimpleExamples: []TestInstruction{
			&SameTest{"False", "AllTrue[{1, a}, NumberQ]"},
			&SameTest{"True", "AllTrue[{1, 2}, NumberQ]"},
		},
		Rules: []Rule{
			{"AllTrue[_[elems___], cond_]", "And @@ (cond /@ {elems})"},
		},
	})
	/*
	defs = append(defs, Definition{
		Name: "LogicalExpand",
		SimpleExamples: []TestInstruction{
			&TestComment{"`LogicalExpand` can expand logic expressions."},
		},
		Rules: []Rule{
			{"LogicalExpand[exp_]", "exp //. {And[begin___,e_,!e_,end___]:>And[begin, end]}"},
		},
	})*/
	return
}
