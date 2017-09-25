ReplaceAll::usage = "`expr /. rule` replaces all occurences of the LHS of `rule` with the RHS of `rule` in `expr`.

`expr /. {r1, r2, ...}` performes the same operation as `expr /. rule`, but evaluating each `r_n` in sequence.";
Attributes[ReplaceAll] = {Protected};
Tests`ReplaceAll = {
    ESimpleExamples[
        ESameTest[2^(y+1) + y, 2^(x^2+1) + x^2 /. x^2->y],
        EComment["If no match is found, `ReplaceAll` evaluates to an unchanged `expr`:"],
        ESameTest[2^(x^2+1) + x^2, 2^(x^2+1) + x^2 /. z^2->y],
        EComment["`ReplaceAll` works within Orderless expressions as well (such as `Plus`):"],
        ESameTest[b + c + d, a + b + c + c^2 /. c^2 + a -> d],
        EComment["`ReplaceAll` can use named patterns:"],
        ESameTest[a^b + c + d, a + b + c + d/. x_Symbol + y_Symbol -> x^y],
        ESameTest[a + 99 * b + 99 * c, a + 2*b + 5*c /. (c1_Integer*a_Symbol) -> 99*a]
    ], EFurtherExamples[
        EComment["`ReplaceAll` can be used to replace sequences of expressions:"],
        ESameTest[foo[b, c, d], a + b + c + d /. a + amatch___ -> foo[amatch]],
        EComment["The `Head` of functions can be replaced just as the subexpressions:"],
        ESameTest[11, (x + 2)[5, 6] /. (2 + x) -> Plus],
        ESameTest[2[2, 2, 2, 2], a*b*c*d /. _Symbol -> 2]
    ], ETests[
        ESameTest[a * b * c, a*b*c /. c + a -> d],
        ESameTest[b * d, a*b*c /. c*a -> d],
        ESameTest[2 * a + b + c + c^2, 2 * a + b + c + c^2 /. c^2 + a -> d],
        ESameTest[a^2 + b + c + d, a^2 + a + b + c + c^2 /. c^2 + a -> d],
        ESameTest[a * b * c + a * b^2 * c, (a*b*c) + (a*b^2*c)],
        ESameTest[b * d + b^2 * d, (a*b*c) + (a*b^2*c) /. c*a -> d],
        ESameTest[b * d + b^2 * d, (a*b*c) + (a*b^2*c) /. a*c -> d],
        ESameTest[a + b + c, a + b + c /. c + a -> c + a],
        ESameTest[d, a*b*c /. c*a*b -> d],
        ESameTest[a * b * c, a*b*c /. c*a*b*d -> d],
        ESameTest[a*b*c*d*e, a*b*c*d*e /. a*b*f -> z],
        ESameTest[z*d*e, a*b*c*d*e /. a*b*c -> z],
        ESameTest[z*a*b, a*b*c*d*e /. e*d*c -> z],
        ESameTest[z*a*b, a*b*c*d*e /. c*e*d -> z],
        ESameTest[a^b, a + b /. x_Symbol + y_Symbol -> x^y],
        ESameTest[2, x = 2],
        ESameTest[2^b, a + b /. x_Symbol + y_Symbol -> x^y],
        ESameTest[2, x],
        ESameTest[a^b, a == b /. j_Symbol == k_Symbol -> j^k],
        ESameTest[2, a == b /. j_Equal -> 2],
        ESameTest[(a == b)^k, a == b /. j_Equal -> j^k],
        ESameTest[3^k, 2^k /. base_Integer -> base + 1],
        ESameTest[3^k, 2^k /. base_Integer^exp_ -> (base + 1)^exp],
        ESameTest[(2 + k)^k, 2^k /. base_Integer^exp_ -> (base + exp)^exp],
        ESameTest[(2 + k)^k, 2^k /. base_Integer^exp_Symbol -> (base + exp)^exp],
        ESameTest[1 + (2 + k)^k, 2^k + 1 /. base_Integer^exp_Symbol -> (base + exp)^exp],
        ESameTest[a^c + b, a^c + b /. test_Symbol^test_Symbol + test_Symbol -> test + 1],
        ESameTest[1 + a, a^a + a /. test_Symbol^test_Symbol + test_Symbol -> test + 1],
        ESameTest[a^a, a^a /. (test_Symbol^test) -> 2],
        ESameTest[2, a^a /. (test_Symbol^test_Symbol) -> 2],
        ESameTest[a^a, a^a /. (test^test_Symbol) -> 2],
        ESameTest[2, test^a /. (test^test_Symbol) -> 2],
        ESameTest[2, a^test /. (test_Symbol^test) -> 2],
        EResetState[],
        ESameTest[testa*testb, testa*testb /. a_Symbol*a_Symbol -> 5],
        ESameTest[False, MatchQ[testa*testb, a_Symbol*a_Symbol]],
        ESameTest[testa+testb, testa+testb /. a_Symbol+a_Symbol -> 5],
        ESameTest[5, testa*testb /. a_Symbol*b_Symbol -> 5],
        ESameTest[a+b, a + b /. (b_Symbol + b_Symbol) -> 2],
        EResetState[],

        (*Test matching/replacement contexts*)
        ESameTest[99^k, test = 99^k],
        ESameTest[2, 99^k /. test -> 2],
        ESameTest[2, 99^k /. test_ -> 2],
        ESameTest[3, test2 = 3],
        ESameTest[3, 99 /. test2_Integer -> test2],
        ESameTest[a^b, a^b /. test3_Symbol^test3_Symbol -> k],
        ESameTest[5, test3 = 5],
        ESameTest[a^b, a^b /. test3_Symbol^test3_Symbol -> k],

        EResetState[],
        ESameTest[a + 99 * b + 99 * c, a + 2*b + 5*c /. (c1_Integer*a_Symbol) -> 99*a],
        ESameTest[a + 99 * b + 5 * c, a + 2*b + 5*c /. (2*a_Symbol) -> 99*a],
        ESameTest[a + 99 * b + 99 * c, a + 2*b + 2*c /. (2*a_Symbol) -> 99*a],
        ESameTest[a + 99 * b + 99 * c + 99 * d, a + 2*b + 3*c + 3*d /. (cl_Integer*a_Symbol) -> 99*a],

        (*Work way up to combining like terms*)
        EResetState[],
        ESameTest[a + 99 * b + 99 * c, a + 2*b + 5*c /. (c1_Integer*a_Symbol) -> 99*a],
        ESameTest[a + 99 * b, a + 2*b + 5*c /. (c1_Integer*matcha_Symbol) + (c2_Integer*matchb_Symbol) -> 99*matcha],
        ESameTest[a + (2 * b) + (5 * c), a + 2*b + 5*c /. (c1_Integer*matcha_Symbol) + (c2_Integer*matcha_Symbol) -> (c1+c2)*matcha],
        ESameTest[(a + (7 * b)), a + 2*b + 5*b /. (c1_Integer*matcha_Symbol) + (c2_Integer*matcha_Symbol) -> (c1+c2)*matcha],

        EResetState[],
        ESameTest[2, a + b /. (d_Symbol + c_Symbol) -> 2],
        ESameTest[2 + c, a + b + c /. (d_Symbol + c_Symbol) -> 2],
        ESameTest[2 + c + d, a + b + c + d /. (d_Symbol + c_Symbol) -> 2],
        ESameTest[a+99+c+d, a + b + c + d /. (dmatch_Symbol + cmatch_Symbol) -> cmatch + 99],
        ESameTest[a * b + c + d, a + b + c + d /. (d_Symbol + c_Symbol) -> c*d],
        ESameTest[98, d = 98],
        ESameTest[c+98+(b*a), a + b + c + d /. (dmatch_Symbol + cmatch_Symbol) -> cmatch*dmatch],

        EResetState[],
        ESameTest[2 * a^2 - 2 * b^2, 2 * a^2 - 2 * b^2 /. matcha_ - matchb_ -> 2],
        ESameTest[3 * a^2 + 5 * b^2, 2 * a^2 - 2 * b^2 /. 2*matcha_ - 2*matchb_ -> 3*matcha + 5*matchb],
        ESameTest[2 * a^2 - 2 * b^2, 2 * a^2 - 2 * b^2 /. _Integer*matcha_ - _Integer*matchb_ -> 2],
        ESameTest[2 * a^2 - 2 * b^2, 2 * a^2 - 2 * b^2 /. _*matcha_ - _*matchb_ -> 2],
        ESameTest[2 * a^2 - 2 * b^2, 2 * a^2 - 2 * b^2 /. _ - _ -> 2],
        ESameTest[2 * a^2 - 2 * b^2, 2 * a^2 - 2 * b^2 /. _ - 2*_ -> 2],

        (*Test replacing functions*)
        ESameTest[test[], kfdsfdsf[] /. _Symbol -> test],
        ESameTest[11, (x + 2)[5, 6] /. (2 + x) -> Plus],
        ESameTest[2[2, 2, 2, 2], a*b*c*d /. _Symbol -> 2],
        ESameTest[2, foo[2*x, x] /. foo[matcha_Integer*matchx_, matchx_] -> matcha],
        ESameTest[foo[], a + b /. a + b + amatch___ -> foo[amatch]],
        ESameTest[foo[b, c, d], a + b + c + d /. a + amatch___ -> foo[amatch]],
        ESameTest[foo[a + b + c + d], a + b + c + d /. amatch___ -> foo[amatch]],
        ESameTest[a + b, a + b /. a + b + amatch__ -> foo[amatch]],
        ESameTest[foo[b, c, d], a + b + c + d /. a + amatch__ -> foo[amatch]],
        ESameTest[foo[a + b + c + d], a + b + c + d /. amatch__ -> foo[amatch]],

        (*Test replacement within Hold parts*)
        ESameTest[3, {a, b, c} /. {n__} :> Length[{n}]],
        ESameTest[1, {a, b, c} /. {n__} -> Length[{n}]],
        ESameTest[bar[m,n], foo[m, n] /. foo[a_, m_] -> bar[a, m]],

        (*Test replacement of functions and arguments*)
        ESameTest[foo[False, y, 5], foo[x == 2, y, x] /. x -> 5],
        ESameTest[foo[5, y, x], foo[x * 2, y, x] /. x * 2 -> 5],
        ESameTest[k, foo[k] /. foo[k] -> k],
        ESameTest[foo[k], foo[foo[k]] /. foo[k] -> k],
        ESameTest[k, (foo[foo[k]] /. foo[k] -> k) /. foo[k] -> k],
        ESameTest[foo[bla], foo[foo[k]] /. foo[k] -> bla],

        ESameTest[2 * a + 12 * b, foo[1, 2, 3, 4] /. foo[1, amatch__Integer, bmatch___Integer] -> a*Times[amatch] + b*Times[bmatch]],
        ESameTest[a + 24 * b, foo[1, 2, 3, 4] /. foo[1, amatch___Integer, bmatch___Integer] -> a*Times[amatch] + b*Times[bmatch]],

        (*Test handling of orderless and Flat attributes.*)
        ESameTest[False, MatchQ[Plus[a, b], Plus[a, b, c]]],
        ESameTest[f && c, And[a, b, c] /. And[a, b] -> f],
        ESameTest[False, MatchQ[And[a, b, c], And[b, c]]],
        ESameTest[False, MatchQ[And[a, b, c], And[a, b]]],
        ESameTest[jjj && eee && c, And[a, b, c] /. And[a, b] -> Sequence[jjj, eee]],
        ESameTest[myand[a, b, c], myand[a, b, c] /. myand[a, b] -> f],
        ESameTest[a && b && c, And[a, b, c] /. And[b, a] -> Sequence[jjj, eee]],
        ESameTest[c + eee + jjj, Plus[a, b, c] /. Plus[b, a] -> Sequence[jjj, eee]],
        ESameTest[c + eee + jjj, Plus[a, b, c] /. Plus[a, b] -> Sequence[jjj, eee]],
        ESameTest[a && b && c, And[a, b, c] /. And[a, c] -> Sequence[jjj, eee]],
        ESameTest[1 && 2 && a && b && jjj && eee, And[1, 2, a, b, c] /. And[___Integer, c] -> Sequence[jjj, eee]],
        ESameTest[1 && 2 && a && b && c, And[1, 2, a, b, c] /. And[__Integer, c] -> Sequence[jjj, eee]],
        ESameTest[jjj && eee && b && c, And[1, 2, a, b, c] /. And[__Integer, a] -> Sequence[jjj, eee]],
        ESameTest[Sequence[jjj, eee], And[1, 2, a, b, c] /. And[__Integer, a, __Symbol] -> Sequence[jjj, eee]],
        ESameTest[1 && 2 && a && b && c, And[1, 2, a, b, c] /. And[__Symbol, a, __Integer] -> Sequence[jjj, eee]],
        ESameTest[1 && 2 && jjj && eee && b && c, And[1, 2, a, b, c] /. And[___Symbol, a, ___Integer] -> Sequence[jjj, eee]]
    ], EKnownDangerous[
        (*Causes stack overflow*)
        ESameTest[99 + a + b + c + d, a + b + c + d /. (d_Symbol + c_Symbol) -> c + 99 + d]
    ]
};

Replace::usage = "`Replace[expr, rules]` applies `rules` to `expr` if they match at the base level.";
Attributes[Replace] = {Protected};
Tests`Replace = {
    ESimpleExamples[
        ESameTest[2, Replace[a+b,a+b->2]],
        ESameTest[a+b, Replace[a+b,a->2]],
        ESameTest[2, Replace[a+b,_->2]],
        ESameTest[c+d, Replace[a+b,{a+b->c+d,c+d->3}]]
    ]
};

ReplaceRepeated::usage = "`expr //. rule` replaces all occurences of the LHS of `rule` with the RHS of `rule` in `expr` repeatedly until the expression stabilizes.

`expr //. {r1, r2, ...}` performes the same operation as `expr //. rule`, but evaluating each `r_n` in sequence.";
Attributes[ReplaceRepeated] = {Protected};
Tests`ReplaceRepeated = {
    ESimpleExamples[
        EComment["`ReplaceRepeated` can be used to implement logarithm expansion:"],
        ESameTest[Null, logRules := {Log[x_ y_] :> Log[x] + Log[y], Log[x_^k_] :> k Log[x]}],
        ESameTest[b Log[a] + (c^d) Log[b], Log[a^b*b^(c^d)] //. logRules]
    ]
};

Rule::usage = "`lhs -> rhs` can be used in replacement functions to say that instances of `lhs` should be replaced with `rhs`.";
Attributes[Rule] = {SequenceHold, Protected};
Tests`Rule = {
    ESimpleExamples[
        ESameTest[2^(y+1) + y, 2^(x^2+1) + x^2 /. x^2 -> y],
        EComment["To demonstrate the difference between `Rule` and `RuleDelayed`:"],
        ESameTest[True, Equal @@ ({1, 1} /. 1 -> RandomReal[])],
        ESameTest[False, Equal @@ ({1, 1} /. 1 :> RandomReal[])]
    ]
};

RuleDelayed::usage = "`lhs :> rhs` can be used in replacement functions to say that instances of `lhs` should be replaced with `rhs`, evaluating `rhs` only after replacement.";
Attributes[RuleDelayed] = {HoldRest, SequenceHold, Protected};
Tests`RuleDelayed = {
    ESimpleExamples[
        ESameTest[2^(y+1) + y, 2^(x^2+1) + x^2 /. x^2 :> y],
        EComment["To demonstrate the difference between `Rule` and `RuleDelayed`:"],
        ESameTest[True, Equal @@ ({1, 1} /. 1 -> RandomReal[])],
        ESameTest[False, Equal @@ ({1, 1} /. 1 :> RandomReal[])]
    ]
};

ReplacePart::usage = "`ReplacePart[e, {loc1 -> newval1, ...}]` replaces the value at the locations with their corresponding new values in `e`.";
Attributes[ReplacePart] = {Protected};
ReplacePart[e_?((! AtomQ[#]) &), r_, i_Integer?Positive] :=
  
  If[i <= Length[e] === True,
   Join[e[[1 ;; i - 1]], Head[e][r], e[[i + 1 ;; Length[e]]]],
   Print["Index too large for ReplacePart!"]];
ReplacePart[e_, r_Rule] := ReplacePart[e, {r}];
Tests`ReplacePart = {
    ESimpleExamples[
        ESameTest[{1,foo,3,4}, ReplacePart[Range[4],foo,2]],
        ESameTest[{1,2,foo,4}, ReplacePart[Range[4],3->foo]],
        ESameTest[{1,2,foo,4}, ReplacePart[Range[4],{3}->foo]],
        ESameTest[{1,2,3,4}, ReplacePart[Range[4],{3,1}->foo]],
    ], EFurtherExamples[
        ESameTest[{foo,foo,foo,foo}, ReplacePart[Range[4],i_->foo]],
        ESameTest[{1,2,3,4}, ReplacePart[Range[4],7->foo]],
        ESameTest[a+b^foo, ReplacePart[a+b^c,{2,2}->foo]],
        ESameTest[a+b^c, ReplacePart[a+b^c,{2,2,1}->foo]],
    ], ETests[
        ESameTest[a+foo^foo, ReplacePart[a+b^c,{2,_}->foo]],
        ESameTest[a+b^foo, ReplacePart[a+b^c,{{2,2}->foo}]],
        ESameTest[b^foo+foo, ReplacePart[a+b^c,{{2,2}->foo,{1}->foo}]],
        ESameTest[b^foo+foo, ReplacePart[a+b^c,{{1}->foo,{2,2}->foo}]],
        ESameTest[ReplacePart[a+b^c,{{1}->foo,bar}], ReplacePart[a+b^c,{{1}->foo,bar}]],
        ESameTest[3, ReplacePart[a+b^c,{{a_}->a}]],
        ESameTest[hi, ReplacePart[hi,{{a_}->a}]],
        ESameTest[a+foo[1]^foo[2], ReplacePart[a+b^c,{{_,a_}->foo[a]}]],
    ], EKnownFailures[
        ESameTest[foo[a,b^c], ReplacePart[a+b^c,{{0}->foo}]],
        ESameTest[a+foo, ReplacePart[a+b^c,{{-1}->foo}]],
    ]
};
