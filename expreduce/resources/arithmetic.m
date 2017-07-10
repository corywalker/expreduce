Abs[a_?NumberQ] := If[a<0,-a,a];
Abs[-a_] := Abs[a];
Attributes[Abs] = {Listable, NumericFunction, Protected, ReadProtected};
Tests`Abs = {
    ESimpleExamples[
        ESameTest[5.2, Abs[-5.2]],
        ESameTest[5, Abs[5]],
        EComment["Absolute values of unspecified inputs will be left unevaluated:"],
        ESameTest[Abs[a], Abs[a]],
        EComment["But sometimes simplifications can occur:"],
        ESameTest[Abs[Sin[x]], Abs[-Sin[x]]]
    ], ETests[
        ESameTest[0, Abs[0]],
        ESameTest[Abs[x^a], Abs[-x^a]],
        ESameTest[Abs[x^(a + b)], Abs[-x^(a + b)]]
    ]
};
