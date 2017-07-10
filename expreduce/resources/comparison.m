NumericQ::usage =  "`NumericQ[expr]` returns `True` if `expr` is a numeric quantity, `False` otherwise.";
NumericQ[e_] := If[NumberQ[N[e]], True, False];
Attributes[NumericQ] = {Protected};
Tests`NumericQ = {
    ESimpleExamples[
        ESameTest[True, NumericQ[5]],
        ESameTest[False, NumericQ[a]],
        ESameTest[False, NumericQ[Sin[a]]],
        ESameTest[True, NumericQ[Sin[2]]]
    ], ETests[
        ESameTest[True, NumericQ[Cos[2]]],
        ESameTest[False, NumericQ[Sqrt[a]]],
        ESameTest[False, NumericQ[Sqrt[Sin[2]]*Sqrt[Sin[x]]]]
    ], EKnownFailures[
        ESameTest[True, NumericQ[Sqrt[2]]]
    ]
};
