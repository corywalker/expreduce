Simplify::usage = "`Simplify[expr]` attempts to perform simplification operations on `expr`.";
booleanSimplify[exp_] := exp //. {
    (*a_ && a_  :> a,*)
    (*a_ || a_  :> a,*)

    !x_ || !y_  :> !(x && y),
    !x_ || !y_  || !z :> !(x && y && z),
    (*This is a generalization of the above rule, but causes issues*)
    (*This problem actually happens outside of Expreduce as well.*)
    (*The issue is that the Or with the pattern inside evaluates*)
    (*immediately to just the pattern, due to how Or works. This*)
    (*happens before pattern matching, causing all kinds of*)
    (*expressions, even outside Or expressions, to match.*)
    (*Or[match__?(AllTrue[#, (Head[#] == Not &)] &)] :> Not[(#[[1]] &) /@ match],*)

    (*a_ || (a_ && b_) :> a,*)
    (*a_ || !a_ && b_ :> a || b,*)

    (a_ || b_) && (a_ || c_) :> a || (b && c),
    (b_ || a_) && (c_ || a_) :> a || (b && c),
    Or[___, a_, ___, Not[And[___, a_, ___] | a_], ___] :> True,
    Or[___, Not[And[___, a_, ___] | a_], ___, a_, ___] :> True,
    Or[x1___, a_, x2___, And[x3___, a_, x4___], x5___] :> Or[a, x1, x2, x5],
    Or[x1___, And[x2___, a_, x3___], x4___, a_, x5___] :> Or[a, x1, x4, x5],
    Or[x1___, a_, x2___, a_, x3___] :> Or[a, x1, x2, x3],
    Or[x1___, a_, x2___, And[x3___, !a_, x4___], x5___] :> Or[a, x1, x2, And[x3, x4], x5],
    Or[x1___, And[x2___, !a_, x3___], x4___, a_, x5___] :> Or[a, x1, And[x2, x3], x4, x5],

    (*Dual of these rules.*)
    And[___, a_, ___, Not[Or[___, a_, ___] | a_], ___] :> False,
    And[___, Not[Or[___, a_, ___] | a_], ___, a_, ___] :> False,
    And[x1___, a_, x2___, Or[x3___, a_, x4___], x5___] :> And[a, x1, x2, x5],
    And[x1___, Or[x2___, a_, x3___], x4___, a_, x5___] :> And[a, x1, x4, x5],
    And[x1___, a_, x2___, a_, x3___] :> And[a, x1, x2, x3],
    And[x1___, a_, x2___, Or[x3___, !a_, x4___], x5___] :> And[a, x1, x2, Or[x3, x4], x5],
    And[x1___, Or[x2___, !a_, x3___], x4___, a_, x5___] :> And[a, x1, Or[x2, x3], x4, x5]
};
simplifyInner[exp_] := Module[{e = exp, tryVal},
    e = booleanSimplify[e];
    inferredPower = 1;
    If[MatchQ[e, s_Plus^n_Integer],
      inferredPower := Replace[e, s_Plus^n_Integer -> n]];
    If[inferredPower < 5,
      (*Similar to Expand, but not using ReplaceAll*)
      tryVal = FixedPoint[Replace[#, expandRules]&, e];
      If[LeafCount[tryVal] < LeafCount[e], e = tryVal];
    ];
    e = Replace[e, Sqrt[inner_] :> Sqrt[FactorTerms[inner]]];
    e
];
Simplify[exp_] := Map[simplifyInner, exp, {0, Infinity}];
Attributes[Simplify] = {Protected};
Tests`Simplify = {
    ESimpleExamples[
        EComment["`Simplify` can simplify some boolean expressions."],
        ESameTest[b, b && b // Simplify],
        ESameTest[False, a && b && !b // Simplify],
        ESameTest[a || (b && c), (a || b) && (a || c) // Simplify],
        ESameTest[a || b, a || ! a && b // Simplify],
        ESameTest[True, a || b || ! a || ! b // Simplify]
    ], ETests[
        (*Seems wrong, but this is the right behavior*)
        ESameTest[a, a || (a && Infinity) // Simplify],
        ESameTest[a || (b && c), (b || a) && (c || a) // Simplify],

        ESameTest[True, (a || b || c || Not[(a && b && c)]) // Simplify],
        ESameTest[True, (a || b || c || Not[(a && b && c && d)]) // Simplify],
        ESameTest[True, (a || b || c || d || Not[(a && b && c)]) // Simplify],
        ESameTest[True, (a || b || c || d || Not[a]) // Simplify],
        ESameTest[True, (az || b || cz || Not[(ay && b && cy && dy)]) // Simplify],

        ESameTest[a, a || (a && b && c && d) // Simplify],
        ESameTest[d, d || (a && b && c && d) // Simplify],
        ESameTest[d || e, d || e || (a && b && c && d) // Simplify],
        ESameTest[b || d, d || b || (a && b && c && d) // Simplify // Sort],
        ESameTest[True, d || b || (a && b && c && d) || ! b // Simplify],
        ESameTest[foo[True], foo[d || b || (a && b && c && d) || ! b] // Simplify],
        ESameTest[d || e || (a && b && c), d || e || (a && b && c) // Simplify],
        ESameTest[z, z || z // Simplify],
        ESameTest[a || z, z || a || z // Simplify // Sort],
        ESameTest[a, a || a && b // Simplify],
        ESameTest[a || b, a || !a && b // Simplify],
        ESameTest[a || b || c, a || c || ! a && b // Simplify // Sort],
        ESameTest[a || b || c, a || c || ! a && ! c && b // Simplify // Sort],
        ESameTest[a || c || !b, a || c || ! a && ! c && ! b // Simplify // Sort],
        ESameTest[a || c || (! b && d), a || c || ! a && ! c && ! b && d // Simplify // Sort],
        ESameTest[a || c || Not[b], c || a || Not[b] // Simplify // Sort],
        ESameTest[False, And[x1, a, x2, Not[Or[x3, a, x4]], x5] // Simplify],
        ESameTest[a && x1 && x2 && x5, And[x1, a, x2, Or[x3, a, x4], x5] // Simplify],
        ESameTest[a && b, a&&b&&a//Simplify],
        ESameTest[(-32+32 x-16 x^2)^9, (16 + 8 (-6 + 4 x - 2 x^2))^9 // Simplify],
    ]
};

FullSimplify::usage = "`FullSimplify[expr]` attempts to perform full simplification operations on `expr`.";
FullSimplify[e_] := Simplify[e] //. {
    E^(-x_Symbol)+E^x_Symbol:>2 Cosh[x]
};
Attributes[FullSimplify] = {Protected};
Tests`FullSimplify = {
    ESimpleExamples[
        ESameTest[2 Cosh[x], E^-x+E^x//FullSimplify],
    ]
};

