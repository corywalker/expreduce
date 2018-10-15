MatchQ::usage = "`MatchQ[expr, form]` returns True if `expr` matches `form`, False otherwise.";
Attributes[MatchQ] = {Protected};
Tests`MatchQ = {
    ESimpleExamples[
        EComment["A `Blank[]` expression matches everything:"],
        ESameTest[True, MatchQ[2*x, _]],
        EComment["Although a more specific pattern would have matched as well:"],
        ESameTest[True, MatchQ[2*x, c1_Integer*a_Symbol]],
        EComment["Since `Times` is `Orderless`, this would work as well:"],
        ESameTest[True, MatchQ[x*2, c1_Integer*a_Symbol]],
        EComment["As would the `FullForm`:"],
        ESameTest[True, MatchQ[Times[x, 2], c1_Integer*a_Symbol]],
        EComment["Named patterns must match the same expression, or the match will fail:"],
        ESameTest[False, MatchQ[a + b, x_Symbol + x_Symbol]]
    ], EFurtherExamples[
        ESameTest[True, MatchQ[{2^a, a}, {2^x_Symbol, x_Symbol}]],
        ESameTest[False, MatchQ[{2^a, b}, {2^x_Symbol, x_Symbol}]],
        EComment["`Blank` sequences allow for the matching of multiple objects. `BlankSequence` (__) matches one or more parts of the expression:"],
        ESameTest[True, MatchQ[{a, b}, {a, __}]],
        ESameTest[False, MatchQ[{a}, {a, __}]],
        EComment["`BlankNullSequence` (___) allows for zero or more matches:"],
        ESameTest[True, MatchQ[{a}, {a, ___}]]
    ], ETests[
        ESameTest[True, MatchQ[2^x, base_Integer^pow_Symbol]],
        ESameTest[True, MatchQ[2+x, c1_Integer+a_Symbol]],
        ESameTest[True, MatchQ[a + b, x_Symbol + y_Symbol]],
        ESameTest[True, MatchQ[{a,b}, {x_Symbol,y_Symbol}]],
        ESameTest[False, MatchQ[{a,b}, {x_Symbol,x_Symbol}]],
         (*Test speed of OrderlessIsMatchQ*)
        ESameTest[Null, Plus[testa, testb, rest___] := bar + rest],
        ESameTest[bar + 1 + a + b + c + d + e + f + g, Plus[testa,1,testb,a,b,c,d,e,f,g]],
        ESameTest[True, MatchQ[foo[2*x, x], foo[matcha_Integer*matchx_, matchx_]]],
        ESameTest[False, MatchQ[foo[2*x, x], bar[matcha_Integer*matchx_, matchx_]]],
        ESameTest[False, MatchQ[foo[2*x, y], foo[matcha_Integer*matchx_, matchx_]]],
        ESameTest[False, MatchQ[foo[x, 2*y], foo[matcha_Integer*matchx_, matchx_]]],
        ESameTest[True, MatchQ[foo[2 * x,2], foo[(p_ * v_), v_]]],

        ESameTest[True, MatchQ[mysolve[m*x + b == 0, x], mysolve[x_*__ + _ == _, x_]]],
        ESameTest[False, MatchQ[mysolve[m*x + b == 0, y], mysolve[x_*__ + _ == _, x_]]],
        ESameTest[True, MatchQ[mysolve[m*x+a, m], mysolve[x_*_+a, x_]]],
        ESameTest[True, MatchQ[bar[foo[a + b] + c + d, c, d, a, b], bar[w_ + x_ + foo[y_ + z_], w_, x_, y_, z_]]],
        ESameTest[True, MatchQ[bar[foo[a + b] + c + d, d, c, b, a], bar[w_ + x_ + foo[y_ + z_], w_, x_, y_, z_]]],
        ESameTest[False, MatchQ[bar[foo[a + b] + c + d, d, a, b, c], bar[w_ + x_ + foo[y_ + z_], w_, x_, y_, z_]]],

        (* We disable the tests that use rm because they require the
        freezeStateDuringPreMatch flag, which is now turned off by default. *)
         (*Test order of pattern checking*)
        (*ESameTest[Null, rm[pattern_]:=pattern?((pats=Append[pats,{pattern[[1]],#}];True)&);],
        ESameTest[True, pats={};MatchQ[foo[a,b,c],foo[x_//rm,y_//rm,z_//rm]]],
        ESameTest[{{x,a},{y,b},{z,c}}, pats],*)

         (*Test pinning in flat*)
        (*ESameTest[{{{a},{c}}}, pats={};ReplaceList[ExpreduceFlatFn[a,b,c],ExpreduceFlatFn[x___//rm,b//rm,y___//rm]->{{x},{y}}]],

        ESameTest[{{{a,a,c}},{{a,a,c}},{{a,a,c}},{{a,a,c}}}, pats={};ReplaceList[ExpreduceFlOrOiFn[a,a,c],ExpreduceFlOrOiFn[b___//rm,c//rm,a___//rm]->{{a,b,c}}]],
        ESameTest[{{{},{a,c}},{{a},{c}},{{c},{a}},{{a,c},{}}}, pats={};ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[x___//rm,b//rm,y___//rm]->{{x},{y}}]],*)

         (*Test pinning in orderless*)
        (*ESameTest[{{b[[1]],b},{y,a},{y,c},{b[[1]],b},{x,a},{y,c},{b[[1]],b},{x,c},{y,a},{b[[1]],b},{x,a},{x,c}}, pats],*)

        ESameTest[True, MatchQ[(a+b)[testsym],Blank[(a+b)]]]
    ], EKnownFailures[
         (*Test order of pattern checking*)
         (*These probably fail because of my formparsing of PatternTest.*)
         (*Try these without the //rm. They will most likely work.*)
        ESameTest[{{c[[1]],c},{b,a},{b,a},{c[[1]],c},{a,a},{b,a},{c[[1]],c},{a,a},{b,a},{c[[1]],c},{a,a},{a,a}}, pats],
        ESameTest[{{x,a},{b[[1]],b},{y,c}}, pats]
    ]
};

Pattern::usage = "`name{BLANKFORM}` is equivalent to `Pattern[name, {BLANKFORM}]` and can be used in pattern matching to refer to the matched expression as `name`, where `{BLANKFORM}` is one of `{_, __, ___}`.

`name{BLANKFORM}head` is equivalent to `Pattern[name, {BLANKFORM}head]` and can be used in pattern matching to refer to the matched expression as `name`, where `{BLANKFORM}` is one of `{_, __, ___}`.";
Attributes[Pattern] = {HoldFirst, Protected};
Tests`Pattern = {
    ESimpleExamples[
        EComment["To demonstrate referencing `name` in the replacement RHS:"],
        ESameTest[2, foo[2, 1] /. foo[a_, b_] -> a],
        EComment["If two matches share the same name, they must be equivalent:"],
        ESameTest[foo[2, 1], foo[2, 1] /. foo[a_, a_] -> a],
        ESameTest[2, foo[2, 2] /. foo[a_, a_] -> a],
        EComment["To demonstrate the head matching capability:"],
        ESameTest[True, MatchQ[2, a_Integer]],
        ESameTest[False, MatchQ[2, a_Real]]
    ], EFurtherExamples[
        EComment["To demonstrate patterns matching a sequence of expressions:"],
        ESameTest[bar[2, 1], foo[2, 1] /. foo[a___Integer] -> bar[a]]
    ]
};

Blank::usage = "`_` matches any expression.

`_head` matches any expression with a `Head` of `head`.";
Attributes[Blank] = {Protected};
Tests`Blank = {
    ESimpleExamples[
        ESameTest[True, MatchQ[a + b, _]],
        ESameTest[True, MatchQ[1, _Integer]],
        ESameTest[False, MatchQ[s, _Integer]],
        EComment["`Blank` works with nonatomic `head`s:"],
        ESameTest[2, a*b*c*d /. _Times -> 2]
    ], EFurtherExamples[
        EComment["For `Orderless` functions, the match engine will attempt to find a match in any order:"],
        ESameTest[True, MatchQ[x+3., c1match_Real+matcha_]]
    ], ETests[
        ESameTest[True, MatchQ[s, _Symbol]],
        ESameTest[False, MatchQ[1, _Symbol]],
        ESameTest[False, MatchQ[_Symbol, _Symbol]],
        ESameTest[False, MatchQ[_Integer, _Integer]],
        ESameTest[True, MatchQ[_Symbol, _Blank]],
        ESameTest[True, MatchQ[_Symbol, test_Blank]],
        ESameTest[True, MatchQ[_Symbol, test_Blank]],
        ESameTest[False, MatchQ[_Symbol, test_Symbol]],
        ESameTest[False, MatchQ[name_Symbol, test_Blank]],
        ESameTest[True, MatchQ[name_Symbol, test_Pattern]],
        ESameTest[True, MatchQ[_Symbol, test_Blank]],
        ESameTest[False, MatchQ[_Symbol, test_Pattern]],
        ESameTest[False, MatchQ[1.5, _Integer]],
        ESameTest[True, MatchQ[1.5, _Real]],
        ESameTest[True, _Symbol == _Symbol],
        ESameTest[_Symbol == _Integer, _Symbol == _Integer],
        ESameTest[False, MatchQ[_Symbol, s]],
        ESameTest[False, MatchQ[_Integer, 1]],
        ESameTest[_Integer == 1, _Integer == 1],
        ESameTest[1 == _Integer, 1 == _Integer],
        ESameTest[False, _Integer === 1],
        ESameTest[False, 1 === _Integer],
        ESameTest[True, _Integer === _Integer],
        ESameTest[False, _Symbol === a],
        ESameTest[False, a === _Symbol],
        ESameTest[True, _Symbol === _Symbol],
        ESameTest[a == b, a == b],
        ESameTest[2, a == b /. _Equal -> 2],
        ESameTest[If[1 == k, itstrue, itsfalse], If[1 == k, itstrue, itsfalse]],
        ESameTest[99, If[1 == k, itstrue, itsfalse] /. _If -> 99],
        ESameTest[False, MatchQ[kfdsfdsf[], _Function]],
        ESameTest[True, MatchQ[kfdsfdsf[], _kfdsfdsf]],
        ESameTest[99, kfdsfdsf[] /. _kfdsfdsf -> 99],
        ESameTest[a + b, a + b],
        ESameTest[2, a + b /. _Plus -> 2],
        ESameTest[2, a*b /. _Times -> 2],
        ESameTest[2, a^b /. _Power -> 2],
        ESameTest[2, a -> b /. _Rule -> 2],
        ESameTest[2, a*b*c*d /. _Times -> 2],
        ESameTest[True, MatchQ[x*3., c1match_Real*matcha_]],
        ESameTest[True, MatchQ[3.*x, c1match_Real*matcha_]],
        ESameTest[True, MatchQ[x+3., c1match_Real+matcha_]],
        ESameTest[True, MatchQ[3.+x, c1match_Real+matcha_]],
        ESameTest[True, MatchQ[y + x, matcha_]],
        ESameTest[True, MatchQ[y*x, matcha_]]
    ]
};

BlankSequence::usage = "`__` matches any sequence of one or more expressions.

`__head` matches any sequence of one or more expressions, each with a `Head` of `head`.";
Attributes[BlankSequence] = {Protected};
Tests`BlankSequence = {
    ESimpleExamples[
        ESameTest[True, MatchQ[a + b + c, a + b + __]],
        ESameTest[False, MatchQ[a + b + c, a + b + c + __]]
    ], EFurtherExamples[
        EComment["With head assertions:"],
        ESameTest[False, MatchQ[a * b, __Symbol]],
        ESameTest[False, MatchQ[a * b, x__Symbol]],
        ESameTest[True, MatchQ[a, __Symbol]],
        ESameTest[True, MatchQ[a * b, x__Times]],
        ESameTest[False, MatchQ[a * b, x__Plus]],
        ESameTest[True, MatchQ[a + b, x__Plus]]
    ], ETests[
         (*Be wary of the false matches - the default is usually false.*)
        ESameTest[True, MatchQ[a, __]],
        ESameTest[True, MatchQ[a + b, __]],
        ESameTest[True, MatchQ[a*b, __]],
        ESameTest[False, MatchQ[a, a*__]],
        ESameTest[True, MatchQ[a + b + c, a + b + __]],
        ESameTest[True, MatchQ[a + b + c + d, a + b + __]],
        ESameTest[False, MatchQ[a*b, __Symbol]],
        ESameTest[False, MatchQ[a*b, x__Symbol]],
        ESameTest[True, MatchQ[a, __Symbol]],
        ESameTest[True, MatchQ[a*b, x__Times]],
        ESameTest[False, MatchQ[a*b, x__Plus]],
        ESameTest[True, MatchQ[a + b, x__Plus]],
        ESameTest[True, MatchQ[a + b + c, a + x__Symbol]],
        ESameTest[False, MatchQ[a + b + c, a + x__Plus]],
        ESameTest[True, MatchQ[a + b, a + x__Symbol]],
        ESameTest[False, MatchQ[a + b, a + x__Plus]],
        ESameTest[False, MatchQ[a + b, a + b + x__Symbol]],
        ESameTest[False, MatchQ[a + b, a + b + x__Plus]],
        ESameTest[True, MatchQ[4*a*b*c*d*e*f, __]],
        ESameTest[True, MatchQ[4*a*b*c*d*e*f, 4*__]],
        ESameTest[False, MatchQ[4*a*b*c*4*d*e*f, 4*__]],
        ESameTest[False, MatchQ[4*a*b*c*4*d*e*f, 4*__]],
        ESameTest[True, MatchQ[a*b*c*4*d*e*f, 4*__]],
        ESameTest[True, MatchQ[a*b*c*4*d*e*f, 4*__]],
        ESameTest[False, MatchQ[a*b*c*4*d*e*f, 5*__]],
        ESameTest[False, MatchQ[a*b*c*4*d*e*f + 5, 4*__]],
        ESameTest[False, MatchQ[a*b*c*4*d*e*f + 5*k, 4*__]],
        ESameTest[False, MatchQ[a*b*c*4*d*e*f + 5*k, 4*__]],
        ESameTest[True, MatchQ[a*b*c*4*d*e*f + 5*k, 4*__ + 5*k]],
        ESameTest[False, MatchQ[a*b*c*4*d*e*f + 2 + 5*k, 4*__ + 5*k]],
        ESameTest[True, MatchQ[(a*b*c)^e, __^e]],
        ESameTest[False, MatchQ[(a*b*c)^e, __^f + __^e]],
        ESameTest[True, MatchQ[(a*b*c)^e + (a*b*c)^f, __^f + __^e]],
        ESameTest[True, MatchQ[(a*b*c)^e + (a + b + c)^f, __^f + __^e]],
        ESameTest[False, MatchQ[(a*b*c)^e + (a + b + c)^f, amatch__^f + amatch__^e]],
        ESameTest[True, MatchQ[(a*b*c)^e + (a*b*c)^f, amatch__^f + amatch__^e]],

         (*Warm up for combining like terms*)
        ESameTest[True, MatchQ[bar[1, foo[a, b]], bar[amatch_Integer, foo[cmatch__]]]],
        ESameTest[True, MatchQ[bar[1, foo[a, b, c]], bar[amatch_Integer, foo[cmatch__]]]],
        ESameTest[False, MatchQ[bar[1, foo[]], bar[amatch_Integer, foo[cmatch__]]]],
        ESameTest[2, bar[1, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] -> 2],
        ESameTest[4, bar[1, foo[a, b]] + bar[5, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] -> 2],
        ESameTest[6 * buzz[a, b], bar[1, foo[a, b]] + bar[5, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] -> amatch*buzz[cmatch]],
        ESameTest[bar[3, foo[a, b]], bar[1, foo[a, b]] + bar[2, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] + bar[bmatch_Integer, foo[cmatch__]] -> bar[amatch + bmatch, foo[cmatch]]],

         (*Test special case of Orderless sequence matches*)
        ESameTest[Null, fooPlus[Plus[addends__]] := Hold[addends]],
        ESameTest[Null, fooList[List[addends__]] := Hold[addends]],
        ESameTest[Null, fooBlank[_[addends__]] := Hold[addends]],
        ESameTest[Hold[a, b, c], fooList[List[a, b, c]]],
        ESameTest[Hold[a, b, c], fooBlank[Plus[a, b, c]]],

        ESameTest[True, MatchQ[foo[1, 2, 3], foo[__Integer]]],
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[__]]],
        ESameTest[False, MatchQ[foo[1, 2, 3], foo[__Real]]],
        ESameTest[True, MatchQ[foo[1.], foo[__Real]]],
        ESameTest[False, MatchQ[foo[], foo[__Real]]],
        ESameTest[True, MatchQ[foo[1.], foo[__]]],
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[1, __Integer]]],
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[1, 2, __Integer]]],
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[1, 2, 3, ___Integer]]],
        ESameTest[False, MatchQ[foo[1, 2, 3], foo[1, 2, 3, 4, ___Integer]]],
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[1, ___Integer, 3]]],

        ESameTest[False, MatchQ[foo[1, 2, 3], foo[1, 2, 3, a__Integer]]],
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3]]],
        ESameTest[False, MatchQ[foo[1, 2, 3], foo[1, a__Integer, 5]]]
    ]
};

BlankNullSequence::usage = "`___` matches any sequence of zero or more expressions.

`___head` matches any sequence of zero or more expressions, each with a `Head` of `head`.";
Attributes[BlankNullSequence] = {Protected};
Tests`BlankNullSequence = {
    ESimpleExamples[
        ESameTest[True, MatchQ[a*b, ___]],
        ESameTest[True, MatchQ[a + b, a + b + ___]]
    ], EFurtherExamples[
        EComment["With head assertions:"],
        ESameTest[True, MatchQ[a + b + c, a + x___Symbol]],
        ESameTest[False, MatchQ[a + b + c, a + x___Plus]]
    ], ETests[
        ESameTest[True, MatchQ[a*b, ___]],
        ESameTest[False, MatchQ[a, a*___]],
        ESameTest[False, MatchQ[a, a + ___]],
        ESameTest[True, MatchQ[a + b, a + b + ___]],
        ESameTest[False, MatchQ[a*b, ___Integer]],
        ESameTest[False, MatchQ[a*b, ___Symbol]],
        ESameTest[True, MatchQ[a, ___Symbol]],
        ESameTest[False, MatchQ[a + b, ___Symbol]],
        ESameTest[True, MatchQ[a + b + c, a + x___Symbol]],
        ESameTest[False, MatchQ[a + b + c, a + x___Plus]],
        ESameTest[True, MatchQ[a + b, a + b + x___Symbol]],
        ESameTest[True, MatchQ[foo[1.], foo[___]]],
        ESameTest[True, MatchQ[foo[1.], foo[___Real]]],
        ESameTest[False, MatchQ[foo[1.], foo[___Integer]]],
        ESameTest[True, MatchQ[foo[], foo[___Integer]]],
        ESameTest[False, MatchQ[foo[1, 2, 3], foo[1, 2]]],
        ESameTest[False, MatchQ[foo[1, 2], foo[1, 2, 3]]],
        ESameTest[False, MatchQ[foo[1, 2, 3], foo[1, 2, 3, __Integer]]],
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[1, __Integer, 3]]],
        ESameTest[False, MatchQ[foo[1, 2, 3], foo[1, __Integer, 5]]],

         (*Make sure some similar cases still work with Patterns, not just Blanks*)
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[1, 2, 3, a___Integer]]],
        ESameTest[False, MatchQ[foo[1, 2, 3], foo[1, 2, 3, 4, a___Integer]]],
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[1, a___Integer, 3]]],
        ESameTest[False, MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3, b__Integer]]],
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3, b___Integer]]],
        ESameTest[True, MatchQ[foo[1, 2, 3, 4], foo[1, a__Integer, 3, b___Integer, 4]]]
    ]
};

Except::usage = "`Except[pat]` matches all expressions except those that match `pat`.

`Except[pat1, pat2]` matches all expressions that match `pat2` but not `pat1`.";
Attributes[Except] = {Protected};
Tests`Except = {
    ESimpleExamples[
        ESameTest[{5, 2, x, y, 4}, Cases[{5, 2, 3.5, x, y, 4}, Except[_Real]]],
        ESameTest[{5, 2, x, y, 4}, Cases[{5, 2, a^b, x, y, 4}, Except[_Symbol^_Symbol]]],
        ESameTest[{a, b, 0, foo[1], foo[2], x, y}, {a, b, 0, 1, 2, x, y} /. Except[0, a_Integer] -> foo[a]]
    ]
};

PatternTest::usage = "`pat?test` matches when the expression matches `pat` and `test[MATCH]` evaluates to `True`.";
Attributes[PatternTest] = {HoldRest, Protected};
Tests`PatternTest = {
    ESimpleExamples[
        ESameTest[True, MatchQ[1, _?NumberQ]],
        ESameTest[False, MatchQ[a, _?NumberQ]],
        ESameTest[True, MatchQ[1, 1?NumberQ]],
        ESameTest[False, MatchQ[1, 1.5?NumberQ]],
        ESameTest[True, MatchQ[1.5, 1.5?NumberQ]],
        ESameTest[{5,2,4.5}, Cases[{5, 2, a^b, x, y, 4.5}, _?NumberQ]]
    ]
};

Condition::usage = "`pat /; cond` matches an expression if the expression matches `pat`, and if `cond` evaluates to `True` with all the named patterns substituted in.";
Attributes[Condition] = {HoldAll, Protected};
Tests`Condition = {
    ESimpleExamples[
        ESameTest[True, MatchQ[5, _ /; True]],
        ESameTest[False, MatchQ[5, _ /; False]],
        ESameTest[True, MatchQ[5, y_ /; True]],
        ESameTest[False, MatchQ[5, y_Real /; True]],
        ESameTest[True, MatchQ[5, y_Integer /; True]],
        ESameTest[False, MatchQ[5, y_ /; y == 0]],
        ESameTest[True, MatchQ[5, y_ /; y == 5]],
        ESameTest[{1,2,3,5}, {3, 5, 2, 1} //. {x___, y_, z_, k___} /; (Order[y, z] == -1) -> {x, z, y, k}],
        ESameTest[myfn[1], Replace[1,a_Integer:>myfn[a]/;a>0]],
        ESameTest[-1, Replace[-1,a_Integer:>myfn[a]/;a>0]],

        ESameTest[4, Replace[foo[2,3],foo[x_,y_]:>With[{a=x},x^2/;a==2]/;y==3]],
        ESameTest[foo[3,3], Replace[foo[3,3],foo[x_,y_]:>With[{a=x},x^2/;a==2]/;y==3]],
        ESameTest[foo[2,4], Replace[foo[2,4],foo[x_,y_]:>With[{a=x},x^2/;a==2]/;y==3]],
        ESameTest[4, Replace[bar[2],bar[x_]:>With[{a=x},x^2/;a==2]]],
        ESameTest[bar[3], Replace[bar[3],bar[x_]:>With[{a=x},x^2/;a==2]]],

        ESameTest[4, Replace[foo[2,3],foo[x_,y_]:>Module[{a=x},x^2/;a==2]/;y==3]],
        ESameTest[foo[3,3], Replace[foo[3,3],foo[x_,y_]:>Module[{a=x},x^2/;a==2]/;y==3]],
        ESameTest[foo[2,4], Replace[foo[2,4],foo[x_,y_]:>Module[{a=x},x^2/;a==2]/;y==3]],
        ESameTest[4, Replace[bar[2],bar[x_]:>Module[{a=x},x^2/;a==2]]],
        ESameTest[bar[3], Replace[bar[3],bar[x_]:>Module[{a=x},x^2/;a==2]]],

        ESameTest[4, Replace[2,x_:>Condition[Condition[Condition[x^2,x==2],x==2],x==2]]],
        ESameTest[3, Replace[3,x_:>Condition[Condition[Condition[x^2,x==2],x==2],x==2]]]
    ]
};

Alternatives::usage = "`alt1 | alt2 | ...` matches an expression if it matches any pattern in the list of alternatives.";
Attributes[Alternatives] = {Protected};
Tests`Alternatives = {
    ESimpleExamples[
        ESameTest[Alternatives[c,d], c | d],
        ESameTest[False, MatchQ[b, c | d]],
        ESameTest[True, MatchQ[c, c | d]],
        ESameTest[True, MatchQ[d, c | d]],
        ESameTest[{c, 1, 2}, Cases[{a, b, c, 1, 2}, c | _Integer]],
        ESameTest[(1 + List)[1 + a, 1 + b, 1 + c, 1., 3], {a, b, c, 1., 2} /. amatch_Symbol | amatch_Integer -> amatch + 1],
        ESameTest[{b, c, d, e}, Cases[{a, b, c, d, e, f}, b | c | d | e]],
        ESameTest[False, MatchQ[{a, b}, {a_, k | a_}]]
    ], ETests[
        ESameTest[False, MatchQ[c || a || Not[b], Or[___, a_, ___, Not[And[___, a_, ___] | a_], ___]]]
    ]
};

FreeQ::usage = "`FreeQ[e, var]` returns True if `e` is free from any occurences of `var`.";
FreeQ[expr_, val_] := expr === (expr /. val -> Internal`DummyReplace);
Attributes[FreeQ] = {Protected};
Tests`FreeQ = {
    ETests[
        ESameTest[False, FreeQ[{0, 1, 2}, 1]],
        ESameTest[True, FreeQ[{0, 1, 2}, 3]],
        ESameTest[False, FreeQ[{0, 1, 2}, _Integer]],
        ESameTest[True, FreeQ[{0, 1, 2}, _Real]],
        ESameTest[True, FreeQ[x^2, _Real]],
        ESameTest[False, FreeQ[x^2, _Integer]],
        ESameTest[False, FreeQ[x^2, 2]],
        ESameTest[True, FreeQ[x^2, 3]],
        ESameTest[True, FreeQ[x^2, y]],
        ESameTest[True, FreeQ[x^2, y]],
        ESameTest[False, FreeQ[x^2, x^_Integer]],
        ESameTest[True, FreeQ[x^2, y^_Integer]],
        ESameTest[False, FreeQ[5*foo[x], foo]],
        ESameTest[True, FreeQ[5*foo[x], bar]]
    ]
};

ReplaceList::usage = "`ReplaceList[expr, rule]` returns all the possible replacements using `rule` on `expr`.";
Attributes[ReplaceList] = {Protected};
Tests`ReplaceList = {
    ESimpleExamples[
        ESameTest[{{a, b}, {b, a}}, ReplaceList[a + b, x_ + y_ -> {x, y}]],
        ESameTest[{{b, a}}, ReplaceList[foo[a + b, b], foo[j_ + k_, j_] -> {j, k}]],
        ESameTest[{{a, b}, {b, a}}, ReplaceList[foo[a + b], foo[x_ + y_] -> {x, y}]],
        ESameTest[{{a, b, c}, {b, a, c}}, ReplaceList[bar[foo[a + b] + c], bar[foo[x_ + y_] + z_] -> {x, y, z}]],
        ESameTest[{{c, d, a, b}, {c, d, b, a}, {d, c, a, b}, {d, c, b, a}}, ReplaceList[bar[foo[a + b] + c + d], bar[w_ + x_ + foo[y_ + z_]] -> {w, x, y, z}]],
        ESameTest[{}, ReplaceList[foo[a + b, c], foo[j_ + k_, j_] -> {j, k}]]
    ], ETests[
        ESameTest[{{{a},{b}},{{b},{a}}}, ReplaceList[a+b,x__+y__->{{x},{y}}]],
        ESameTest[{{{},{a,b}},{{a},{b}},{{a,b},{}}}, ReplaceList[foo[a,b],foo[a___,b___]->{{a},{b}}]],
        ESameTest[{}, ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a:Repeated[b_,{2}],rest___]->{{a},{rest}}]],
        ESameTest[{{c}}, ReplaceList[foo[a,b,c],foo[___,a_]->{a}]],
        ESameTest[{{a+b+c}}, ReplaceList[a+b+c,a_->{a}]],
        ESameTest[{{{},{a,b},{},{b,c}},{{},{a,b},{b},{c}},{{},{a,b},{b,c},{}},{{a},{b},{},{b,c}},{{a},{b},{b},{c}},{{a},{b},{b,c},{}},{{a,b},{},{},{b,c}},{{a,b},{},{b},{c}},{{a,b},{},{b,c},{}}}, ReplaceList[foo[a,b,foo[b,c]],foo[a___,b___,foo[c___,d___]]->{{a},{b},{c},{d}}]],
        ESameTest[{{a+b+c},{b+c},{a+c},{a+b},{c},{b},{a}}, ReplaceList[a+b+c,___+a_->{a}]],
        ESameTest[{{{},{a,b}},{{a},{b}},{{b},{a}},{{a,b},{}}}, ReplaceList[a+b,x___+y___->{{x},{y}}]],
        ESameTest[{{{a},{b+c}},{{b},{a+c}},{{c},{a+b}},{{a+b},{c}},{{a+c},{b}},{{b+c},{a}}}, ReplaceList[a+b+c,a_+b_->{{a},{b}}]],
        ESameTest[{{{a},{b,c}},{{b},{a,c}},{{c},{a,b}},{{a,b},{c}},{{a,c},{b}},{{b,c},{a}}}, ReplaceList[a+b+c,a__+b__->{{a},{b}}]],
        ESameTest[{{{a},{b,c}},{{b},{a,c}},{{c},{a,b}},{{a,b},{c}},{{a,c},{b}},{{b,c},{a}}}, ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a__,b__]->{{a},{b}}]],
        ESameTest[{{{a,b},{c}},{{a,c},{b}},{{b,c},{a}}}, ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a:Repeated[_,{2}],rest___]->{{a},{rest}}]],
        ESameTest[{{{a,b},{c}},{{a,c},{b}},{{b,c},{a}}}, ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a:Repeated[_,{2}],rest___]->{{a},{rest}}]],
        ESameTest[{{{a,b},{c,d}},{{a,c},{b,d}},{{a,d},{b,c}},{{b,c},{a,d}},{{b,d},{a,c}},{{c,d},{a,b}}}, ReplaceList[ExpreduceOrderlessFn[a,b,c,d],ExpreduceOrderlessFn[a:Repeated[_,{2}],rest___]->{{a},{rest}}]],
        ESameTest[{{a+b+c},{b+c},{a+c},{a+b},{c},{b},{a}}, ReplaceList[a+b+c,___+a_->{a}]],
        ESameTest[{{{},{a,b}},{{a},{b}},{{b},{a}},{{a,b},{}}}, ReplaceList[ExpreduceOrderlessFn[a,b],ExpreduceOrderlessFn[a___,b___]->{{a},{b}}]],
        ESameTest[{{{a},{b},{c}},{{a},{c},{b}},{{b},{a},{c}},{{b},{c},{a}},{{c},{a},{b}},{{c},{b},{a}},{{a},{b+c},{}},{{b},{a+c},{}},{{c},{a+b},{}},{{a+b},{c},{}},{{a+c},{b},{}},{{b+c},{a},{}}}, ReplaceList[a+b+c,a_+b_+rest___->{{a},{b},{rest}}]],
        ESameTest[{{{},{a,b,c}},{{a},{b,c}},{{b},{a,c}},{{c},{a,b}},{{a,b},{c}},{{a,c},{b}},{{b,c},{a}},{{a,b,c},{}}}, ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a___,b___]->{{a},{b}}]],
        ESameTest[{{{a,a},{b,b,c}},{{b,b},{a,a,c}}}, ReplaceList[ExpreduceOrderlessFn[a,a,b,b,c],ExpreduceOrderlessFn[a:Repeated[b_,{2}],rest___]->{{a},{rest}}]],
        ESameTest[{{a,b,c},{b,c},{a,c},{a,b},{c},{b},{a},{}}, ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a___,rest___]->{rest}]],
        ESameTest[{{{},{a,b},{},{c,d}},{{},{a,b},{c},{d}},{{},{a,b},{d},{c}},{{},{a,b},{c,d},{}},{{a},{b},{},{c,d}},{{a},{b},{c},{d}},{{a},{b},{d},{c}},{{a},{b},{c,d},{}},{{b},{a},{},{c,d}},{{b},{a},{c},{d}},{{b},{a},{d},{c}},{{b},{a},{c,d},{}},{{a,b},{},{},{c,d}},{{a,b},{},{c},{d}},{{a,b},{},{d},{c}},{{a,b},{},{c,d},{}}}, ReplaceList[ExpreduceOrderlessFn[a,b,ExpreduceOrderlessFn[c,d]],ExpreduceOrderlessFn[a___,b___,ExpreduceOrderlessFn[c___,d___]]->{{a},{b},{c},{d}}]],
        ESameTest[{}, ReplaceList[a+b+c,___+a_+___->{a}]],
        ESameTest[{{{2},{x,y}}}, ReplaceList[ExpreduceFlOrOiFn[2,x,y],ExpreduceFlOrOiFn[c_Integer,e__]->{{c},{e}}]],
        ESameTest[{{{2},{x,y}}}, ReplaceList[ExpreduceFlOrOiFn[2,x,y],ExpreduceFlOrOiFn[c_?NumberQ,e__]->{{c},{e}}]]
    ], EKnownFailures[
         (*Orderless has issues. Flat seems to work fine. regular ordered matching seems perfect.*)
        ESameTest[{{a},{b},{c}}, ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[___,a_]->{a}]]
    ]
};

Repeated::usage = "`Repeated[p_]` matches a sequence of expressions that match the pattern `p`.";
Attributes[Repeated] = {Protected};
Tests`Repeated = {
    ETests[
        ESameTest[True, MatchQ[foo[a, a], foo[Repeated[a]]]],
        ESameTest[False, MatchQ[foo[a, b], foo[Repeated[a]]]],
        ESameTest[True, MatchQ[foo[a], foo[Repeated[a]]]],
        ESameTest[False, MatchQ[foo[], foo[Repeated[a]]]],
        ESameTest[True, MatchQ[foo[1, 2, 3], foo[Repeated[_Integer]]]],
        ESameTest[False, MatchQ[foo[1, 2, a], foo[Repeated[_Integer]]]],
        ESameTest[2, foo[1, 2, 3] /. foo[a : (Repeated[_Integer])] -> 2],
        ESameTest[matches[1, 2, 3], foo[1, 2, 3] /. foo[a : (Repeated[_Integer])] -> matches[a]],
        ESameTest[foo[1, 2, 3], foo[1, 2, 3] /. foo[a : (Repeated[k_Integer])] -> matches[a]],
        ESameTest[matches[1, 1, 1], foo[1, 1, 1] /. foo[a : (Repeated[k_Integer])] -> matches[a]],
        ESameTest[True, MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[a, Repeated[b, {3}]]]],
        ESameTest[False, MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[a, Repeated[b, {a}]]]],
        ESameTest[False, MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[a, Repeated[b, {4}]]]],
        ESameTest[False, MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[a, Repeated[b, {2}]]]],
        ESameTest[False, MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[a, Repeated[_Integer, {2}]]]],
        ESameTest[True, MatchQ[ExpreduceFlOrOiFn[a, 1, 2], ExpreduceFlOrOiFn[a, Repeated[_Integer, {2}]]]],
        ESameTest[False, MatchQ[ExpreduceFlOrOiFn[a, 1, 2], ExpreduceFlOrOiFn[a, Repeated[k_Integer, {2}]]]],
        ESameTest[True, MatchQ[ExpreduceFlOrOiFn[a, 2, 2], ExpreduceFlOrOiFn[a, Repeated[k_Integer, {2}]]]],
        ESameTest[True, MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[___, Repeated[_Integer, {0}]]]],
        ESameTest[False, MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[___, Repeated[_Integer, {-1}]]]],
        ESameTest[x, foo[x, x] /. foo[Repeated[a_, {2}]] -> a]
    ]
};

Optional::usage = "`Optional[pat, default]` attempts to match `pat` but uses `default` if not present.";
Attributes[Optional] = {Protected};
Tests`Optional = {
    ETests[
        ESameTest[foo[a], foo[a]/.foo[a,b_.]->{a,b}],
        ESameTest[{a,b}, foo[a,b]/.foo[a,b_.]->{a,b}],
        ESameTest[{a,c}, foo[a]/.foo[a,b_:c]->{a,b}],
        ESameTest[{a,b}, foo[a,b]/.foo[a,b_:c]->{a,b}],
        ESameTest[{{a},{b}}, foo[a,b]/.foo[a___,b_.]->{{a},{b}}],
        ESameTest[{{a},{b}}, foo[a,b]/.foo[a___,b_:c]->{{a},{b}}],
        ESameTest[{{},{a},{b}}, foo[a,b]/.foo[a___,b_:c,d_:e]->{{a},{b},{d}}],
        ESameTest[{{x},{y},{z}}, foo[x]/.foo[a_,b_:y,c_:z]->{{a},{b},{c}}],
        ESameTest[foo[], foo[]/.foo[a_,b_:y,c_:z]->{{a},{b},{c}}],
        ESameTest[{{x},{i},{j}}, foo[x,i,j]/.foo[a_,b_:y,c_:z]->{{a},{b},{c}}],
        ESameTest[a, a /. foo[a, c_.] -> {{c}}],
         (*This match succeeds because Plus has both a Default and has*)
         (*OneIdentity*)
        ESameTest[{{0}}, a /. a + c_. -> {{c}}],
        ESameTest[False, MatchQ[a,foo[a,c_.]]],
        ESameTest[True, MatchQ[a,a+c_.]],
        ESameTest[False, MatchQ[foo[a],a+c_.]],
        ESameTest[{{0},{0}}, a/.a+c_.+d_.->{{c},{d}}],
        ESameTest[{{0},{0}}, Cos[x]/.(_+c_.+d_.)->{{c},{d}}],
        ESameTest[{{5},{a}}, 5*a/.Optional[c1_?NumberQ]*a_->{{c1},{a}}],
        ESameTest[{{1},{a}}, a/.Optional[c1_?NumberQ]*a_->{{c1},{a}}],
        ESameTest[False, MatchQ[foo[a,b],foo[c1__?NumberQ]]],
        ESameTest[True, MatchQ[foo[1,2],foo[c1__?NumberQ]]],
        ESameTest[False, MatchQ[foo[1,2],foo[Optional[c1__?NumberQ]]]],
        ESameTest[True, MatchQ[foo[1],foo[Optional[c1__?NumberQ]]]],

         (*Ensure that we attempt to fill optionals before using the*)
         (*default.*)
        ESameTest[{{{a},{b,c}},{{5},{a,b,c}}}, ReplaceList[{a,b,c},{a_:5,b__}->{{a},{b}}]],
        ESameTest[{{{a},{b},{c}},{{a},{6},{b,c}},{{5},{a},{b,c}},{{5},{6},{a,b,c}}}, ReplaceList[{a,b,c},{a_:5,b_:6,c___}->{{a},{b},{c}}]],
        ESameTest[True, MatchQ[-x,p_.]],
        ESameTest[True, MatchQ[-x*a,p_.*a]],
        ESameTest[True, MatchQ[__, Optional[1]*a_]],
        ESameTest[True, MatchQ[x^x, x^Optional[exp_]]]
    ], EKnownFailures[
        ESameTest[foo[a,b], foo[a,b]/.foo[a___,b_.,d_.]->{{a},{b},{d}}],
        ESameTest[True, MatchQ[x^x, (x^x)^Optional[exp_]]],
        (*Disabled because issue #79*)
        ESameTest[{{0},{5}}, a/.a+c_.+d_:5->{{c},{d}}]
    ]
};

Verbatim::usage = "`Verbatim[expr]` matches `expr` exactly, even if it has patterns.";
Attributes[Verbatim] = {Protected};
Tests`Verbatim = {
    ETests[
        ESameTest[{{a,b},{b,c},{c,d}}, ReplaceList[a+b+c+d,Verbatim[Plus][___,x_,y_,___]->{x,y}]],
        ESameTest[{}, ReplaceList[a+b+c+d,Verbatim[Times][___,x_,y_,___]->{x,y}]],
        ESameTest[{}, ReplaceList[a+b*c+d,Verbatim[Times][___,x_,y_,___]->{x,y}]],
        ESameTest[{{a,b},{b,c},{c,d}}, ReplaceList[foo[a,b,c,d],Verbatim[foo][___,x_,y_,___]->{x,y}]],
        ESameTest[{{a,b},{b,c},{c,d}}, ReplaceList[(a+b)[a,b,c,d],Verbatim[a+b][___,x_,y_,___]->{x,y}]],
        ESameTest[{}, ReplaceList[(a+b)[a,b,c,d],Verbatim[a+_][___,x_,y_,___]->{x,y}]]
    ]
};

HoldPattern::usage = "`HoldPattern[expr]` leaves `expr` unevaluated but is seen as just `expr` for the purposes of pattern matching.";
Attributes[HoldPattern] = {HoldAll, Protected};
Tests`HoldPattern = {
    ESimpleExamples[
        ESameTest[False, MatchQ[2x+2y,2_+2_]],
        ESameTest[True, MatchQ[2x+2y,HoldPattern[2_+2_]]],
        ESameTest[True, MatchQ[2x+2y,HoldPattern[2_+HoldPattern[2_]]]]
    ]
};
