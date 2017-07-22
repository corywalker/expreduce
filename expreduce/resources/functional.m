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
