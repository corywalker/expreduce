package expreduce

func getReplacementDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "ReplaceAll",
		Usage: "`expr /. rule` replaces all occurences of the LHS of `rule` with the RHS of `rule` in `expr`.\n\n" +
			"`expr /. {r1, r2, ...}` performes the same operation as `expr /. rule`, but evaluating each `r_n` in sequence.",
		toString: func(this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " /. ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			rulesRule, ok := HeadAssertion(this.Parts[2], "Rule")
			if !ok {
				rulesRule, ok = HeadAssertion(this.Parts[2], "RuleDelayed")
			}
			if ok {
				newEx := ReplaceAll(this.Parts[1], rulesRule, &es.CASLogger, EmptyPD())
				return newEx.Eval(es)
			}

			// Also handle a list of Rules
			asList, isList := HeadAssertion(this.Parts[2], "List")
			if isList {
				toReturn := this.Parts[1]
				for i := 1; i < len(asList.Parts); i++ {
					rulesRule, ok := HeadAssertion(asList.Parts[i], "Rule")
					if !ok {
						rulesRule, ok = HeadAssertion(asList.Parts[i], "RuleDelayed")
					}
					if ok {
						toReturn = ReplaceAll(toReturn.DeepCopy(), rulesRule, &es.CASLogger, EmptyPD())
					}
				}
				return toReturn.Eval(es)
			}

			return this
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"2^(y+1) + y", "2^(x^2+1) + x^2 /. x^2->y"},
			&TestComment{"If no match is found, `ReplaceAll` evaluates to an unchanged `expr`:"},
			&SameTest{"2^(x^2+1) + x^2", "2^(x^2+1) + x^2 /. z^2->y"},
			&TestComment{"`ReplaceAll` works within Orderless expressions as well (such as `Plus`):"},
			&SameTest{"b + c + d", "a + b + c + c^2 /. c^2 + a -> d"},
			&TestComment{"`ReplaceAll` can use named patterns:"},
			&SameTest{"a^b + c + d", "a + b + c + d/. x_Symbol + y_Symbol -> x^y"},
			&SameTest{"a + 99 * b + 99 * c", "a + 2*b + 5*c /. (c1_Integer*a_Symbol) -> 99*a"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"`ReplaceAll` can be used to replace sequences of expressions:"},
			&SameTest{"foo[b, c, d]", "a + b + c + d /. a + amatch___ -> foo[amatch]"},
			&TestComment{"The `Head` of functions can be replaced just as the subexpressions:"},
			&SameTest{"11", "(x + 2)[5, 6] /. (2 + x) -> Plus"},
			&SameTest{"2[2, 2, 2, 2]", "a*b*c*d /. _Symbol -> 2"},
		},
		Tests: []TestInstruction{
			&SameTest{"a * b * c", "a*b*c /. c + a -> d"},
			&SameTest{"b * d", "a*b*c /. c*a -> d"},
			&SameTest{"2 * a + b + c + c^2", "2 * a + b + c + c^2 /. c^2 + a -> d"},
			&SameTest{"a^2 + b + c + d", "a^2 + a + b + c + c^2 /. c^2 + a -> d"},
			&SameTest{"a * b * c + a * b^2 * c", "(a*b*c) + (a*b^2*c)"},
			&SameTest{"b * d + b^2 * d", "(a*b*c) + (a*b^2*c) /. c*a -> d"},
			&SameTest{"b * d + b^2 * d", "(a*b*c) + (a*b^2*c) /. a*c -> d"},
			&SameTest{"a + b + c", "a + b + c /. c + a -> c + a"},
			&SameTest{"d", "a*b*c /. c*a*b -> d"},
			&SameTest{"a * b * c", "a*b*c /. c*a*b*d -> d"},
			&SameTest{"a*b*c*d*e", "a*b*c*d*e /. a*b*f -> z"},
			&SameTest{"z*d*e", "a*b*c*d*e /. a*b*c -> z"},
			&SameTest{"z*a*b", "a*b*c*d*e /. e*d*c -> z"},
			&SameTest{"z*a*b", "a*b*c*d*e /. c*e*d -> z"},

			// Using named placeholders
			&SameTest{"a^b", "a + b /. x_Symbol + y_Symbol -> x^y"},
			&SameTest{"2", "x = 2"},
			&SameTest{"2^b", "a + b /. x_Symbol + y_Symbol -> x^y"},
			&SameTest{"2", "x"},
			&SameTest{"a^b", "a == b /. j_Symbol == k_Symbol -> j^k"},
			&SameTest{"2", "a == b /. j_Equal -> 2"},
			&SameTest{"(a == b)^k", "a == b /. j_Equal -> j^k"},
			&SameTest{"3^k", "2^k /. base_Integer -> base + 1"},
			&SameTest{"3^k", "2^k /. base_Integer^exp_ -> (base + 1)^exp"},
			&SameTest{"(2 + k)^k", "2^k /. base_Integer^exp_ -> (base + exp)^exp"},
			&SameTest{"(2 + k)^k", "2^k /. base_Integer^exp_Symbol -> (base + exp)^exp"},
			&SameTest{"1 + (2 + k)^k", "2^k + 1 /. base_Integer^exp_Symbol -> (base + exp)^exp"},
			&SameTest{"a^c + b", "a^c + b /. test_Symbol^test_Symbol + test_Symbol -> test + 1"},
			&SameTest{"1 + a", "a^a + a /. test_Symbol^test_Symbol + test_Symbol -> test + 1"},
			&SameTest{"a^a", "a^a /. (test_Symbol^test) -> 2"},
			&SameTest{"2", "a^a /. (test_Symbol^test_Symbol) -> 2"},
			&SameTest{"a^a", "a^a /. (test^test_Symbol) -> 2"},
			&SameTest{"2", "test^a /. (test^test_Symbol) -> 2"},
			&SameTest{"2", "a^test /. (test_Symbol^test) -> 2"},

			&ResetState{},
			&SameTest{"testa*testb", "testa*testb /. a_Symbol*a_Symbol -> 5"},
			&SameTest{"False", "MatchQ[testa*testb, a_Symbol*a_Symbol]"},
			&SameTest{"testa+testb", "testa+testb /. a_Symbol+a_Symbol -> 5"},
			&SameTest{"5", "testa*testb /. a_Symbol*b_Symbol -> 5"},
			&SameTest{"a+b", "a + b /. (b_Symbol + b_Symbol) -> 2"},

			// Test matching/replacement contexts
			&ResetState{},
			&SameTest{"99^k", "test = 99^k"},
			&SameTest{"2", "99^k /. test -> 2"},
			&SameTest{"2", "99^k /. test_ -> 2"},
			&SameTest{"3", "test2 = 3"},
			&SameTest{"3", "99 /. test2_Integer -> test2"},

			&SameTest{"a^b", "a^b /. test3_Symbol^test3_Symbol -> k"},
			&SameTest{"5", "test3 = 5"},
			&SameTest{"a^b", "a^b /. test3_Symbol^test3_Symbol -> k"},

			&ResetState{},
			&SameTest{"a + 99 * b + 99 * c", "a + 2*b + 5*c /. (c1_Integer*a_Symbol) -> 99*a"},
			&SameTest{"a + 99 * b + 5 * c", "a + 2*b + 5*c /. (2*a_Symbol) -> 99*a"},
			&SameTest{"a + 99 * b + 99 * c", "a + 2*b + 2*c /. (2*a_Symbol) -> 99*a"},
			&SameTest{"a + 99 * b + 99 * c + 99 * d", "a + 2*b + 3*c + 3*d /. (cl_Integer*a_Symbol) -> 99*a"},

			// Work way up to combining like terms
			&ResetState{},
			&SameTest{"a + 99 * b + 99 * c", "a + 2*b + 5*c /. (c1_Integer*a_Symbol) -> 99*a"},
			&SameTest{"a + 99 * b", "a + 2*b + 5*c /. (c1_Integer*matcha_Symbol) + (c2_Integer*matchb_Symbol) -> 99*matcha"},
			&SameTest{"a + (2 * b) + (5 * c)", "a + 2*b + 5*c /. (c1_Integer*matcha_Symbol) + (c2_Integer*matcha_Symbol) -> (c1+c2)*matcha"},
			&SameTest{"(a + (7 * b))", "a + 2*b + 5*b /. (c1_Integer*matcha_Symbol) + (c2_Integer*matcha_Symbol) -> (c1+c2)*matcha"},

			&ResetState{},
			&SameTest{"2", "a + b /. (d_Symbol + c_Symbol) -> 2"},
			&SameTest{"2 + c", "a + b + c /. (d_Symbol + c_Symbol) -> 2"},
			&SameTest{"2 + c + d", "a + b + c + d /. (d_Symbol + c_Symbol) -> 2"},
			&SameTest{"a+99+c+d", "a + b + c + d /. (dmatch_Symbol + cmatch_Symbol) -> cmatch + 99"},
			// Causes stack overflow
			//&SameTest{"99 + a + b + c + d", "a + b + c + d /. (d_Symbol + c_Symbol) -> c + 99 + d"},
			&SameTest{"a * b + c + d", "a + b + c + d /. (d_Symbol + c_Symbol) -> c*d"},
			&SameTest{"98", "d = 98"},
			//&SameTest{"98 + 98 * a + c", "a + b + c + d /. (dmatch_Symbol + cmatch_Symbol) -> cmatch*dmatch"},
			&SameTest{"c+98+(b*a)", "a + b + c + d /. (dmatch_Symbol + cmatch_Symbol) -> cmatch*dmatch"},

			&ResetState{},
			&SameTest{"2 * a^2 - 2 * b^2", "2 * a^2 - 2 * b^2 /. matcha_ - matchb_ -> 2"},
			&SameTest{"3 * a^2 + 5 * b^2", "2 * a^2 - 2 * b^2 /. 2*matcha_ - 2*matchb_ -> 3*matcha + 5*matchb"},
			&SameTest{"2 * a^2 - 2 * b^2", "2 * a^2 - 2 * b^2 /. _Integer*matcha_ - _Integer*matchb_ -> 2"},
			&SameTest{"2 * a^2 - 2 * b^2", "2 * a^2 - 2 * b^2 /. _*matcha_ - _*matchb_ -> 2"},
			&SameTest{"2 * a^2 - 2 * b^2", "2 * a^2 - 2 * b^2 /. _ - _ -> 2"},
			&SameTest{"2 * a^2 - 2 * b^2", "2 * a^2 - 2 * b^2 /. _ - 2*_ -> 2"},

			// Test replacing functions
			&SameTest{"test[]", "kfdsfdsf[] /. _Symbol -> test"},
			&SameTest{"11", "(x + 2)[5, 6] /. (2 + x) -> Plus"},
			&SameTest{"2[2, 2, 2, 2]", "a*b*c*d /. _Symbol -> 2"},
			&SameTest{"2", "foo[2*x, x] /. foo[matcha_Integer*matchx_, matchx_] -> matcha"},

			// Test replacing with BlankSequence
			&SameTest{"foo[]", "a + b /. a + b + amatch___ -> foo[amatch]"},
			&SameTest{"foo[b, c, d]", "a + b + c + d /. a + amatch___ -> foo[amatch]"},
			&SameTest{"foo[a + b + c + d]", "a + b + c + d /. amatch___ -> foo[amatch]"},
			&SameTest{"a + b", "a + b /. a + b + amatch__ -> foo[amatch]"},
			&SameTest{"foo[b, c, d]", "a + b + c + d /. a + amatch__ -> foo[amatch]"},
			&SameTest{"foo[a + b + c + d]", "a + b + c + d /. amatch__ -> foo[amatch]"},

			// Test replacement within Hold parts
			&SameTest{"3", "{a, b, c} /. {n__} :> Length[{n}]"},
			&SameTest{"1", "{a, b, c} /. {n__} -> Length[{n}]"},

			&SameTest{"bar[m,n]", "foo[m, n] /. foo[a_, m_] -> bar[a, m]"},

			// Test replacement of functions and arguments
			&SameTest{"foo[False, y, 5]", "foo[x == 2, y, x] /. x -> 5"},
			&SameTest{"foo[5, y, x]", "foo[x * 2, y, x] /. x * 2 -> 5"},
			&SameTest{"k", "foo[k] /. foo[k] -> k"},
			&SameTest{"foo[k]", "foo[foo[k]] /. foo[k] -> k"},
			&SameTest{"k", "(foo[foo[k]] /. foo[k] -> k) /. foo[k] -> k"},
			&SameTest{"foo[bla]", "foo[foo[k]] /. foo[k] -> bla"},

			&SameTest{"2 * a + 12 * b", "foo[1, 2, 3, 4] /. foo[1, amatch__Integer, bmatch___Integer] -> a*Times[amatch] + b*Times[bmatch]"},
			&SameTest{"a + 24 * b", "foo[1, 2, 3, 4] /. foo[1, amatch___Integer, bmatch___Integer] -> a*Times[amatch] + b*Times[bmatch]"},
		},
	})
	defs = append(defs, Definition{
		Name: "ReplaceRepeated",
		Usage: "`expr //. rule` replaces all occurences of the LHS of `rule` with the RHS of `rule` in `expr` repeatedly until the expression stabilizes.\n\n" +
			"`expr //. {r1, r2, ...}` performes the same operation as `expr //. rule`, but evaluating each `r_n` in sequence.",
		toString: func(this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " //. ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			es.Infof("Starting ReplaceRepeated.")
			isSame := false
			oldEx := this.Parts[1]
			es.Infof("In ReplaceRepeated. Initial expr: %v", oldEx)
			for !isSame {
				newEx := (NewExpression([]Ex{
					&Symbol{"ReplaceAll"},
					oldEx.DeepCopy(),
					this.Parts[2],
				})).Eval(es)
				//newEx = newEx.Eval(es)
				es.Infof("In ReplaceRepeated. New expr: %v", newEx)

				if IsSameQ(oldEx, newEx, &es.CASLogger) {
					isSame = true
				}
				oldEx = newEx
			}
			return oldEx
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"`ReplaceRepeated` can be used to implement logarithm expansion:"},
			&SameTest{"Null", "logRules := {Log[x_ y_] :> Log[x] + Log[y], Log[x_^k_] :> k Log[x]}"},
			&SameTest{"b Log[a] + (c^d) Log[b]", "Log[a^b*b^(c^d)] //. logRules"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Rule",
		Usage:      "`lhs -> rhs` can be used in replacement functions to say that instances of `lhs` should be replaced with `rhs`.",
		Attributes: []string{"SequenceHold"},
		toString: func(this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " -> ", true, "", "", form)
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"2^(y+1) + y", "2^(x^2+1) + x^2 /. x^2 -> y"},
			&TestComment{"To demonstrate the difference between `Rule` and `RuleDelayed`:"},
			&SameTest{"True", "Equal @@ ({1, 1} /. 1 -> RandomReal[])"},
			&SameTest{"False", "Equal @@ ({1, 1} /. 1 :> RandomReal[])"},
		},
	})
	defs = append(defs, Definition{
		Name:       "RuleDelayed",
		Usage:      "`lhs :> rhs` can be used in replacement functions to say that instances of `lhs` should be replaced with `rhs`, evaluating `rhs` only after replacement.",
		Attributes: []string{"HoldRest", "SequenceHold"},
		toString: func(this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " :> ", true, "", "", form)
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"2^(y+1) + y", "2^(x^2+1) + x^2 /. x^2 :> y"},
			&TestComment{"To demonstrate the difference between `Rule` and `RuleDelayed`:"},
			&SameTest{"True", "Equal @@ ({1, 1} /. 1 -> RandomReal[])"},
			&SameTest{"False", "Equal @@ ({1, 1} /. 1 :> RandomReal[])"},
		},
	})
	return
}
