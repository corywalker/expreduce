package expreduce

func getComparisonDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "Equal",
		Usage: "`lhs == rhs` evaluates to True or False if equality or inequality is known.",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " == ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			var isequal string = this.Parts[1].IsEqual(this.Parts[2], &es.CASLogger)
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return &Symbol{"True"}
			} else if isequal == "EQUAL_FALSE" {
				return &Symbol{"False"}
			}

			return &Expression{[]Ex{&Symbol{"Error"}, &String{"Unexpected equality return value."}}}
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Expressions known to be equal will evaluate to True:"},
			&StringTest{"True", "9*x==x*9"},
			&TestComment{"Sometimes expressions may or may not be equal, or Expreduce does not know how to test for equality. In these cases, the statement will remain unevaluated:"},
			&StringTest{"((9 * x)) == ((10 * x))", "9*x==x*10"},

			&TestComment{"Equal considers Integers and Reals that are close enough to be equal:"},
			&StringTest{"5", "tmp=5"},
			&StringTest{"True", "tmp==5"},
			&StringTest{"True", "tmp==5."},
			&StringTest{"True", "tmp==5.00000"},

			&TestComment{"Equal can test for Rational equality:"},
			&StringTest{"False", "4/3==3/2"},
			&StringTest{"True", "4/3==8/6"},
		},
		FurtherExamples: []TestInstruction{
			&StringTest{"True", "If[xx == 2, yy, zz] == If[xx == 2, yy, zz]"},
			&TestComment{"Equal does not match patterns:"},
			&SameTest{"{1, 2, 3} == _List", "{1, 2, 3} == _List"},
			&TestComment{"This functionality is reserved for MatchQ:"},
			&SameTest{"True", "MatchQ[{1, 2, 3}, _List]"},
		},
		Tests: []TestInstruction{

			&StringTest{"5", "tmp=5"},
			&StringTest{"True", "tmp==5"},
			&StringTest{"True", "5==tmp"},
			&StringTest{"False", "tmp==6"},
			&StringTest{"False", "6==tmp"},

			&StringTest{"(a) == (b)", "a==b"},
			&StringTest{"True", "a==a"},
			&StringTest{"(a) == (2)", "a==2"},
			&StringTest{"(2) == (a)", "2==a"},
			&StringTest{"(2) == ((a + b))", "2==a+b"},
			&StringTest{"(2.) == (a)", "2.==a"},
			&StringTest{"(2^k) == (a)", "2^k==a"},
			&StringTest{"(2^k) == (2^a)", "2^k==2^a"},
			&StringTest{"(2^k) == ((2 + k))", "2^k==k+2"},
			&StringTest{"(k) == ((2 * k))", "k==2*k"},
			&StringTest{"((2 * k)) == (k)", "2*k==k"},
			&StringTest{"True", "1+1==2"},
			&StringTest{"(y) == ((b + (m * x)))", "y==m*x+b"},

			&StringTest{"True", "1==1."},
			&StringTest{"True", "1.==1"},

			&StringTest{"True", "(x==2)==(x==2)"},
			&StringTest{"True", "(x==2.)==(x==2)"},
			&StringTest{"True", "(x===2.)==(x===2)"},

			&StringTest{"(If[(xx) == (3), yy, zz]) == (If[(xx) == (2), yy, zz])", "If[xx == 3, yy, zz] == If[xx == 2, yy, zz]"},

			&StringTest{"True", "(1 == 2) == (2 == 3)"},
			&StringTest{"False", "(1 == 2) == (2 == 2)"},

			&SameTest{"True", "foo[x == 2, y, x] == foo[x == 2, y, x]"},
			&SameTest{"True", "foo[x == 2, y, x] == foo[x == 2., y, x]"},
			&SameTest{"foo[x == 2, y, x] == foo[x == 2., y, y]", "foo[x == 2, y, x] == foo[x == 2., y, y]"},
			&SameTest{"foo[x == 2, y, x] == bar[x == 2, y, x]", "foo[x == 2, y, x] == bar[x == 2, y, x]"},

			&StringTest{"(foo[x, y, z]) == (foo[x, y])", "foo[x, y, z] == foo[x, y]"},
			&StringTest{"(foo[x, y, z]) == (foo[x, y, 1])", "foo[x, y, z] == foo[x, y, 1]"},
			&SameTest{"True", "foo[x, y, 1] == foo[x, y, 1]"},
			&SameTest{"True", "foo[x, y, 1.] == foo[x, y, 1]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Unequal",
		Usage: "`lhs != rhs` evaluates to True if inequality is known or False if equality is known.",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " != ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			var isequal string = this.Parts[1].IsEqual(this.Parts[2], &es.CASLogger)
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return &Symbol{"False"}
			} else if isequal == "EQUAL_FALSE" {
				return &Symbol{"True"}
			}

			return &Expression{[]Ex{&Symbol{"Error"}, &String{"Unexpected equality return value."}}}
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Expressions known to be unequal will evaluate to True:"},
			&StringTest{"True", "9 != 8"},
			&TestComment{"Sometimes expressions may or may not be unequal, or Expreduce does not know how to test for inequality. In these cases, the statement will remain unevaluated:"},
			&StringTest{"((9 * x)) != ((10 * x))", "9*x != x*10"},

			&TestComment{"Unequal considers Integers and Reals that are close enough to be equal:"},
			&StringTest{"5", "tmp=5"},
			&StringTest{"False", "tmp != 5"},
			&StringTest{"False", "tmp != 5."},
			&StringTest{"False", "tmp != 5.00000"},

			&TestComment{"Unequal can test for Rational inequality:"},
			&StringTest{"True", "4/3 != 3/2"},
			&StringTest{"False", "4/3 != 8/6"},
		},
	})
	defs = append(defs, Definition{
		Name:  "SameQ",
		Usage: "`lhs === rhs` evaluates to True if `lhs` and `rhs` are identical after evaluation, False otherwise.",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " === ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			var issame bool = IsSameQ(this.Parts[1], this.Parts[2], &es.CASLogger)
			if issame {
				return &Symbol{"True"}
			} else {
				return &Symbol{"False"}
			}
		},
		SimpleExamples: []TestInstruction{
			&StringTest{"True", "a===a"},
			&StringTest{"True", "5 === 5"},
			&TestComment{"Unlike Equal, SameQ does not forgive differences between Integers and Reals:"},
			&StringTest{"False", "5 === 5."},
			&TestComment{"SameQ considers the arguments of all expressions and subexpressions:"},
			&SameTest{"True", "foo[x == 2, y, x] === foo[x == 2, y, x]"},
			&SameTest{"False", "foo[x == 2, y, x] === foo[x == 2., y, x]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"SameQ does not match patterns:"},
			&SameTest{"False", "{1, 2, 3} === _List"},
			&TestComment{"This functionality is reserved for MatchQ:"},
			&SameTest{"True", "MatchQ[{1, 2, 3}, _List]"},
		},
		Tests: []TestInstruction{
			&StringTest{"5", "tmp=5"},
			&StringTest{"False", "a===b"},
			&StringTest{"True", "tmp===5"},
			&StringTest{"False", "tmp===5."},
			&StringTest{"True", "1+1===2"},
			&StringTest{"False", "y===m*x+b"},

			&StringTest{"False", "1===1."},
			&StringTest{"False", "1.===1"},

			&StringTest{"True", "(x===2.)===(x===2)"},
			&StringTest{"False", "(x==2.)===(x==2)"},

			&StringTest{"True", "If[xx == 2, yy, zz] === If[xx == 2, yy, zz]"},
			&StringTest{"False", "If[xx == 2, yy, zz] === If[xx == 2., yy, zz]"},
			&StringTest{"False", "If[xx == 3, yy, zz] === If[xx == 2, yy, zz]"},
			&StringTest{"False", "(x == y) === (y == x)"},
			&StringTest{"True", "(x == y) === (x == y)"},

			&SameTest{"False", "foo[x == 2, y, x] === foo[x == 2., y, y]"},
			&SameTest{"False", "foo[x == 2, y, x] === bar[x == 2, y, x]"},

			&SameTest{"False", "foo[x, y, z] === foo[x, y]"},
			&SameTest{"False", "foo[x, y, z] === foo[x, y, 1]"},
			&SameTest{"True", "foo[x, y, 1] === foo[x, y, 1]"},
			&SameTest{"False", "foo[x, y, 1.] === foo[x, y, 1]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "AtomQ",
		Usage: "`AtomQ[expr]` returns True if `expr` is an atomic type, and False if `expr` is a full expression.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			_, IsExpr := this.Parts[1].(*Expression)
			if IsExpr {
				return &Symbol{"False"}
			}
			return &Symbol{"True"}
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "AtomQ[\"hello\"]"},
			&SameTest{"True", "AtomQ[5/3]"},
			&SameTest{"True", "AtomQ[hello]"},
			&SameTest{"False", "AtomQ[a/b]"},
			&SameTest{"False", "AtomQ[bar[x]]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "NumberQ",
		Usage: "`NumberQ[expr]` returns True if `expr` is numeric, otherwise False.",
		legacyEvalFn: singleParamQEval(numberQ),
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "NumberQ[2]"},
			&SameTest{"True", "NumberQ[2.2]"},
			&SameTest{"True", "NumberQ[Rational[5, 2]]"},
			&SameTest{"False", "NumberQ[Infinity]"},
			&SameTest{"False", "NumberQ[Sqrt[2]]"},
			&SameTest{"False", "NumberQ[randomvar]"},
			&SameTest{"False", "NumberQ[\"hello\"]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Less",
		Usage: "`a < b` returns True if `a` is less than `b`.",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " < ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			if !numberQ(this.Parts[1]) || !numberQ(this.Parts[2]) {
				return this
			}
			// Less
			if ExOrder(this.Parts[1], this.Parts[2]) == 1 {
				return &Symbol{"True"}
			}
			return &Symbol{"False"}
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"a < b", "a < b"},
			&SameTest{"True", "1 < 2"},
			&SameTest{"True", "3 < 5.5"},
			&SameTest{"False", "5.5 < 3"},
			&SameTest{"False", "3 < 3"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Greater",
		Usage: "`a > b` returns True if `a` is greater than `b`.",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " > ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			if !numberQ(this.Parts[1]) || !numberQ(this.Parts[2]) {
				return this
			}
			// Greater
			if ExOrder(this.Parts[1], this.Parts[2]) == -1 {
				return &Symbol{"True"}
			}
			return &Symbol{"False"}
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"a > b", "a > b"},
			&SameTest{"False", "1 > 2"},
			&SameTest{"False", "3 > 5.5"},
			&SameTest{"True", "5.5 > 3"},
			&SameTest{"False", "3 > 3"},
		},
	})
	defs = append(defs, Definition{
		Name:  "LessEqual",
		Usage: "`a <= b` returns True if `a` is less than or equal to `b`.",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " <= ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			if !numberQ(this.Parts[1]) || !numberQ(this.Parts[2]) {
				return this
			}
			// Less
			if ExOrder(this.Parts[1], this.Parts[2]) == 1 {
				return &Symbol{"True"}
			}
			// Equal
			if ExOrder(this.Parts[1], this.Parts[2]) == 0 {
				return &Symbol{"True"}
			}
			return &Symbol{"False"}
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"a <= b", "a <= b"},
			&SameTest{"True", "1 <= 2"},
			&SameTest{"True", "3 <= 5.5"},
			&SameTest{"False", "5.5 <= 3"},
			&SameTest{"True", "3 <= 3"},
		},
	})
	defs = append(defs, Definition{
		Name:  "GreaterEqual",
		Usage: "`a >= b` returns True if `a` is greater than or equal to `b`.",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], " >= ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			if !numberQ(this.Parts[1]) || !numberQ(this.Parts[2]) {
				return this
			}
			// Greater
			if ExOrder(this.Parts[1], this.Parts[2]) == -1 {
				return &Symbol{"True"}
			}
			// Equal
			if ExOrder(this.Parts[1], this.Parts[2]) == 0 {
				return &Symbol{"True"}
			}
			return &Symbol{"False"}
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"a >= b", "a >= b"},
			&SameTest{"False", "1 >= 2"},
			&SameTest{"False", "3 >= 5.5"},
			&SameTest{"True", "5.5 >= 3"},
			&SameTest{"True", "3 >= 3"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Positive",
		Usage:      "`Positive[x]` returns `True` if `x` is positive.",
		Attributes: []string{"Listable"},
		Rules: []Rule{
			{"Positive[x_?NumberQ]", "x > 0"},
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{True, False, False, Positive[a]}", "Map[Positive, {1, 0, -1, a}]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Negative",
		Usage:      "`Negative[x]` returns `True` if `x` is positive.",
		Attributes: []string{"Listable"},
		Rules: []Rule{
			{"Negative[x_?NumberQ]", "x < 0"},
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{False, False, True, Negative[a]}", "Map[Negative, {1, 0, -1, a}]"},
		},
	})
	return
}
