Head::usage = "`Head[expr]` returns the head of the expression.";
Attributes[Head] = {Protected};
Tests`Head = {
    ESimpleExamples[
        ESameTest[f, Head[f[x]]],
        ESameTest[Symbol, Head[x]],
        ESameTest[List, Head[{x}]],
        ESameTest[Plus, Head[a + b]],
        ESameTest[Integer, Head[1]],
        ESameTest[Real, Head[1.]],
        ESameTest[Rational, Head[2/7]],
        ESameTest[Rational, Head[1/7]],
        ESameTest[String, Head["1"]],
        ESameTest[Plus, Head[Head[(a + b)[x]]]]
    ]
};

Depth::usage = "`Depth[expr]` returns the depth of `expr`.";
Attributes[Depth] = {Protected};
Tests`Depth = {
    ESimpleExamples[
        ESameTest[1, Depth[foo]],
        ESameTest[2, Depth[{foo}]],
        ESameTest[2, Depth[bar[foo, bar]]],
        ESameTest[3, Depth[foo[foo[]]]],
        ESameTest[1, Depth[3]],
        ESameTest[1, Depth[3.5]],
        ESameTest[1, Depth[3/5]],
        ESameTest[2, Depth[foo[{{{}}}][]]]
    ]
};

Length::usage = "`Length[expr]` returns the length of `expr`.";
Attributes[Length] = {Protected};
Tests`Length = {
    ESimpleExamples[
        ESameTest[4, Length[{1,2,3,4}]],
        ESameTest[0, Length[{}]],
        ESameTest[1, Length[{5}]]
    ], EFurtherExamples[
        EComment["`expr` need not have a `List` head:"],
        ESameTest[2, Length[foo[1, 2]]],
        EComment["The length of an atomic expression is zero:"],
        ESameTest[0, Length[a]],
        ESameTest[0, Length[2.5]],
        ESameTest[0, Length["hello"]]
    ]
};

Sequence::usage = "`Sequence[e1, e2, ...]` holds a list of expressions to be automatically inserted into another function.";
Attributes[Sequence] = {Protected};
Tests`Sequence = {
    ESimpleExamples[
        EComment["Sequence arguments are automatically inserted into the parent functions:"],
        ESameTest[foo[a, 2, 3], foo[a, Sequence[2, 3]]],
        EComment["Outside of the context of functions, Sequence objects do not merge:"],
        ESameTest[Sequence[2, 3], Sequence[2, 3]],
        ESameTest[14, Sequence[2, 3] + Sequence[5, 4]],
        ESameTest[120, Sequence[2, 3]*Sequence[5, 4]]
    ], EFurtherExamples[
        EComment["Empty `Sequence[]` objects effectively disappear:"],
        ESameTest[foo[], foo[Sequence[]]]
    ], ETests[
        ESameTest[Sequence[2], Sequence[2]],
        ESameTest[Sequence[2, 3], Sequence[2, 3]],
        ESameTest[foo[2, 3], foo[Sequence[2, 3]]],
        ESameTest[foo[2], foo[Sequence[2]]],
        ESameTest[foo[14], foo[Sequence[2, 3] + Sequence[5, 4]]],
        ESameTest[foo[2, 3, 5, 4], foo[Sequence[2, 3], Sequence[5, 4]]],
        ESameTest[False, Sequence[2, 3] == Sequence[2, 3]],
        ESameTest[True, Sequence[2, 2] == Sequence[2]],
        ESameTest[False, Sequence[2, 3] === Sequence[2, 3]],
        ESameTest[True, Sequence[2, 2] === Sequence[2]]
    ]
};

Evaluate::usage = "`Evaluate[expr]` evaluates to an evaluated form of `expr`, even when under hold conditions.";
Attributes[Evaluate] = {Protected};
Tests`Evaluate = {
    ESimpleExamples[
        EStringTest["Hold[4, (2 + 1)]", "Hold[Evaluate[1 + 3], 2 + 1]"],
        EStringTest["Hold[foo[Evaluate[(1 + 1)]]]", "Hold[foo[Evaluate[1 + 1]]]"],
        EStringTest["Hold[4, 7, (2 + 1)]", "Hold[Evaluate[1 + 3, 5 + 2], 2 + 1]"],
        EStringTest["Hold[(1 + 3), (5 + 2), (2 + 1)]", "Hold[Sequence[1 + 3, 5 + 2], 2 + 1]"]
    ]
};

Hold::usage = "`Hold[expr]` prevents automatic evaluation of `expr`.";
Attributes[Hold] = {HoldAll, Protected};
Tests`Hold = {
    ESimpleExamples[
        EStringTest["Hold[5^3]", "Hold[Power[5, 3]]"],
        EStringTest["Hold[5.^3.]", "Hold[Power[5., 3.]]"]
    ]
};

HoldForm::usage = "`HoldForm[expr]` prevents automatic evaluation of `expr`. Prints as `expr`.";
Attributes[HoldForm] = {HoldAll, Protected};
Tests`HoldForm = {
    ESimpleExamples[
        EStringTest["5^3", "HoldForm[Power[5, 3]]"],
        EStringTest["5.^3.", "HoldForm[Power[5., 3.]]"]
    ]
};

Flatten::usage = "`Flatten[list]` flattens out lists in `list`.";
Attributes[Flatten] = {Protected};
Tests`Flatten = {
    ESimpleExamples[
        ESameTest[Flatten[1], Flatten[1]],
        EComment["Input must be nonatomic:"],
        ESameTest[{1}, Flatten[{1}]],
        ESameTest[{1}, Flatten[{{{{1}}}}]],
        ESameTest[{1, 2, 3}, Flatten[{{{{1}, 2}}, 3}]],
        ESameTest[{1, 2, 3, 4}, Flatten[{{{{1}, 2}}, 3, 4}]],
        ESameTest[{-1, 1, 2, 3, 4}, Flatten[{-1, {{{1}, 2}}, 3, 4}]],
        EComment["A level of zero means no change:"],
        ESameTest[{-1, {{{1}, 2}}, 3, 4}, Flatten[{-1, {{{1}, 2}}, 3, 4}, 0]],
        ESameTest[{-1, {{1}, 2}, 3, 4}, Flatten[{-1, {{{1}, 2}}, 3, 4}, 1]],
        ESameTest[{-1, {1}, 2, 3, 4}, Flatten[{-1, {{{1}, 2}}, 3, 4}, 2]],
        ESameTest[{-1, 1, 2, 3, 4}, Flatten[{-1, {{{1}, 2}}, 3, 4}, 3]],
        ESameTest[{-1, 1, 2, 3, 4}, Flatten[{-1, {{{1}, 2}}, 3, 4}, 4]],
        ESameTest[Flatten[{-1, {{{1}, 2}}, 3, 4}, a], Flatten[{-1, {{{1}, 2}}, 3, 4}, a]],
        ESameTest[{-1, foo[{{1}, 2}], 3, 4}, Flatten[{-1, {foo[{{1}, 2}]}, 3, 4}, 999]],
        ESameTest[{-1, foo[{{1}, 2}], 3, 4}, Flatten[{-1, {foo[{{1}, 2}]}, 3, 4}, 999]],
        ESameTest[{-1, 1[{{1}, 2}], 3, 4}, Flatten[{-1, {1[{{1}, 2}]}, 3, 4}, 999]]
    ]
};
