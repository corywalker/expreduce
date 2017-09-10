Function::usage = "`Function[inner]` defines a pure function where `inner` is evaluated with `Slot` parameters.

`Function[x, inner]` defines a pure function where `inner` is evaluated a single parameter `x`.";
Attributes[Function] = {HoldAll, Protected};
Tests`Function = {
    ESimpleExamples[
        ESameTest[1 + x, Function[1 + #][x]],
        ESameTest[1 + x + 2y, Function[1 + # + 2#2][x, y]],
        ESameTest[a^2, Function[x, x^2][a]],
        ESameTest[a^2, Function[x, x^2][a, b]],
        ESameTest[x^2, Function[x, x^2][x]],
        ESameTest[4, Function[x, x^2][-2]]
    ]
};

Slot::usage = "`#` serves as a pure function's first parameter.

`#n` serves as a pure function's `n`'th parameter.";
Attributes[Slot] = {NHoldAll, Protected};
Tests`Slot = {
    ESimpleExamples[
        ESameTest[1 + x, Function[1 + #][x]],
        ESameTest[1 + x + 2y, Function[1 + # + 2#2][x, y]],
        ESameTest[True, # === Slot[1]],
        ESameTest[True, #2 === Slot[2]],
        ESameTest[2a + 4b, (4 # + (2 # &)[a] &)[b]]
    ], ETests[
        ESameTest[foo[test, k], (foo[test, #] &) &[j][k]]
    ]
};

Apply::usage = "`Apply[f, e]` (`f@@e`) replaces the head of expression `e` with `f`.";
Attributes[Apply] = {Protected};
Tests`Apply = {
    ESimpleExamples[
        ESameTest[bar[syma, symb], Apply[bar, foo[syma, symb]]],
        ESameTest[bar[syma, symb], bar@@foo[syma, symb]],
        ESameTest[{syma, symb}, List@@(syma + symb)],
        EComment["`Apply` is useful in performing aggregations on `List`s:"],
        ESameTest[12, Times @@ {2, 6}],
        ESameTest[a b, Times @@ {a, b}]
    ], EFurtherExamples[
        EComment["`Apply` has no effect on atoms:"],
        ESameTest[1, foo @@ 1],
        ESameTest[bar, foo @@ bar]
    ], ETests[
        ESameTest[foo[a,b,c], Apply[foo, {a,b,c}]],
        ESameTest[foo[bar, buzz], Apply[foo, {bar, buzz}]],
        ESameTest[foo[bar, buzz], foo @@ {bar, buzz}],
        ESameTest[foo[1, 2], foo @@ {1, 2}]
    ]
};

Map::usage = "`Map[f, expr]` returns a new expression with the same head as `expr`, but with `f` mapped to each of the arguments.";
Attributes[Map] = {Protected};
Tests`Map = {
    ESimpleExamples[
        ESameTest[{foo[a], foo[b], foo[c]}, Map[foo, {a, b, c}]],
        ESameTest[{foo[a], foo[b], foo[c]}, foo /@ {a, b, c}],
        ESameTest[{2, 4, 9}, Times /@ {2, 4, 9}],
        ESameTest[{foo[{a, b}], foo[c]}, Map[foo, {{a, b}, c}]],
        ESameTest[Map[foo], Map[foo]],
        ESameTest[foo, Map[foo, foo]],
        ESameTest[Map[foo, foo, foo], Map[foo, foo, foo]],
        EComment["Pure functions are useful with `Map`:"],
        ESameTest[{4,16}, Function[x, x^2] /@ {2,4}],
        ESameTest[{4,16}, Function[#^2] /@ {2,4}]
    ]
};

FoldList::usage = "`FoldList[f, x, {a, b}] returns {x, f[x, a], f[f[x, a], b]}"
FoldList[f_, expr_] := FoldList[f, First[expr], Rest[expr]]
(* FoldList[f_][expr__] := FoldList[f, expr] When subvalues are allowed *)
Attributes[FoldList] = {Protected};
Tests`FoldList = {
    ESimpleExamples[
        ESameTest[{1, f[1, 2], f[f[1, 2], 3]}, FoldList[f, 1, {2, 3}]],
        ESameTest[{1, f[1, 2], f[f[1, 2], 3]}, FoldList[f, {1, 2, 3}]],
        (* ESameTest[{1, f[1, 2], f[f[1, 2], 3]}, FoldList[f][{1, 2, 3}]], *)
        ESameTest[{1, f[1, 2], f[f[1, 2], 3]}, FoldList[f][1, {2, 3}]],
        ESameTest[h[e1, f[e1, e2], f[f[e1, e2], e3], f[f[f[e1, e2], e3], e4]], FoldList[f, e1, h[e2, e3, e4]]],
        ESameTest[{h}, FoldList[f, h, {}]]
        EComment["Known problem: FoldList[f, , {1}] ? this is because Null is not handled correctly. Try evaluating e.g. f[,]"]
    ]
}

Fold::usage = "`Fold[f, x, {a, b}]` returns `f[f[x, a], b]`, and this nesting continues for lists of arbitrary length. `Fold[f, {a, b, c}]` returns `Fold[f, a, {b, c}]`. `Fold[f]` is an operator form that can be applied to expressions such as `{a, b, c}`."
Fold[f_, x_, expr_] := Last[FoldList[f, x, expr]]
Fold[f_, expr_] := Last[FoldList[f, First[expr], Rest[expr]]]
(* Fold[f_][expr__] := Last[FoldList[f, expr]] When subvalues are allowed *)
Attributes[Fold] = {Protected};
Tests`Fold = {
    ESimpleExamples[
        ESameTest[f[f[1, 2], 3], Fold[f, 1, {2, 3}]],
        ESameTest[f[f[1, 2], 3], Fold[f, {1, 2, 3}]],
        (* ESameTest[f[f[1, 2], 3], Fold[f][{1, 2, 3}]], *)
        ESameTest[f[f[1, 2], 3], Fold[f][1, {2, 3}]],
        ESameTest[f[f[f[e1, e2], e3], e4], Fold[f, e1, h[e2, e3, e4]]],
        ESameTest[h, Fold[f, h, {}]]
        EComment["Known problem: Fold[f, , {1}] ? this is because Null is not handled correctly. Try evaluating e.g. f[,]"]
    ]
}

NestList::usage = "`NestList[f, expr, n]` returns `f` wrapped around `expr` first once, then twice, and so on up to `n` times."
Attributes[NestList] = {Protected}
Tests`NestList = {
    ESimpleExamples[
        ESameTest[{x, f[x], f[f[x]], f[f[f[x]]]}, NestList[f, x, 3]],
        ESameTest[{{1, 2, 3}, {1, 4, 9}, {1, 16, 81}, {1, 256, 6561}}, NestList[#^2 &, {1, 2, 3}, 3]]
    ]
}

Nest::usage = "`Nest[f, expr, n]` returns `f` wrapped around `expr` `n` times."
Nest[f_, expr_, n_] := Last[NestList[f, expr, n]]
Attributes[Nest] = {Protected}
Tests`Nest = {
    ESimpleExamples[
        ESameTest[f[f[f[x]]], Nest[f, x, 3]],
        ESameTest[{1, 256, 6561}, Nest[#^2 &, {1, 2, 3}, 3]]
    ]
}

NestWhileList::usage = "`NestWhileList[f, expr, test, m, max, n]` applies `f` to `expr` until `test` does not return `True`.
It returns a list of all intermediate results. `test` is a function that takes as its argument the last `m` results.
`max` denotes the maximum number of applications of `f` and `n` denotes that `f` should be applied another `n` times after
`test` has terminated the recursion."
Attributes[NestWhileList] = {Protected}
Tests`NestWhileList = {
    ESimpleExamples[
        ESameTest[7, Length@NestWhileList[(# + 3/#)/2 &, 1.0, UnsameQ[#1, #2] &, 2]],
        ESameTest[{2, 4, 16, 256}, NestWhileList[#^2 &, 2, # < 256 &]],
        ESameTest[{1, 2, 3, 4, 5, 6, 7}, NestWhileList[#+1 &, 1, # + #4 < 10 &, 4]],
        ESameTest[{1, 2, 3, 4, 5}, NestWhileList[#+1 &, 1, True &, 1, 4]],
        ESameTest[{1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, NestWhileList[#+1 &, 1, True &, 1, 4, 5]]
    ]
}

NestWhile::usage = "`NestWhile[f, expr, test, m, max, n]` applies `f` to `expr` until `test` does not return `True`.
`test` is a function that takes as its argument the last `m` results. `max` denotes the maximum number of applications
of `f` and `n` denotes that `f` should be applied another `n` times after `test` has terminated the recursion."
Attributes[NestWhile] = {Protected}
NestWhile[args__] := Last[NestWhileList[args]]
Tests`NestWhile = {
    ESimpleExamples[
        ESameTest[256, NestWhile[#^2 &, 2, # < 256 &]],
        ESameTest[7, NestWhile[#+1 &, 1, # + #4 < 10 &, 4]],
        ESameTest[5, NestWhile[#+1 &, 1, True &, 1, 4]],
        ESameTest[10, NestWhile[#+1 &, 1, True &, 1, 4, 5]]
    ]
}

FixedPointList::usage = "`FixedPointList[f, expr]` applies `f` to `expr` until `UnsameQ` applied to the two most recent results
returns False. It returns a list of all intermediate results."
FixedPointList[f_, expr_] := NestWhileList[f, expr, UnsameQ, 2]
Tests`FixedPointList = {
    ESimpleExamples[
        ESameTest[7, Length@FixedPointList[(# + 3/#)/2 &, 1.0]],
        ESameTest[{x^3, 3 x^2, 6 x, 6, 0, 0}, FixedPointList[D[#, x] &, x^3]]
    ]
}

FixedPoint::usage = "`FixedPointList[f, expr]` applies `f` to `expr` until `UnsameQ` applied to the two most recent results
returns False."
FixedPoint[f_, expr_] := Last[NestWhileList[f, expr, UnsameQ, 2]]
Tests`FixedPoint = {
    ESimpleExamples[
        ESameTest[0, FixedPoint[D[#, x] &, x^3]]
    ]
}

Array::usage = "`Array[f, n]` creates a list of `f[i]`, with `i` = 1 to `n`.";
Attributes[Array] = {Protected};
Tests`Array = {
    ESimpleExamples[
        ESameTest[{f[1], f[2], f[3]}, Array[f, 3]],
        ESameTest[Null, mytest[x_] := 5],
        ESameTest[{5, 5, 5}, Array[mytest, 3]],
        ESameTest[{(a + b)[1], (a + b)[2], (a + b)[3]}, Array[a + b, 3]],
        ESameTest[Array[a, a], Array[a, a]]
    ]
};

Identity::usage = "`Identity[expr_]` returns `expr`.";
Identity[expr_] := expr;
Attributes[Identity] = {Protected};
Tests`Identity = {
    ESimpleExamples[
        ESameTest[5, Identity[5]],
        ESameTest[a, Identity[Identity[a]]]
    ]
};
