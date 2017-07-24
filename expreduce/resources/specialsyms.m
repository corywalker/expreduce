Infinity::usage = "`Infinity` represents the mathematical concept of infinity.";
Plus[Infinity, _, rest___] := Infinity + rest;
Plus[-Infinity, _, rest___] := -Infinity + rest;
Plus[Infinity, -Infinity, rest___] := Indeterminate + rest;
Attributes[Infinity] = {ReadProtected, Protected};
Tests`Infinity = {
    ESimpleExamples[
        ESameTest[Infinity, Infinity - 1],
        ESameTest[Infinity, Infinity - 990999999],
        ESameTest[Infinity, Infinity - 990999999.],
        ESameTest[Indeterminate, Infinity - Infinity],
        ESameTest[-Infinity, Infinity*-1],
        ESameTest[-Infinity, -Infinity + 1],
        ESameTest[-Infinity, -Infinity + 999],
        ESameTest[Infinity, -Infinity*-1],
        ESameTest[0, 1/Infinity]
    ], EKnownFailures[
        (*I can't simplify this type of infinity until I have ;/ rules*)
        ESameTest[Infinity, Infinity*2]
    ]
};

ComplexInfinity::usage = "`ComplexInfinity` represents an an infinite quantity that extends in an unknown direction in the complex plane.";
Attributes[ComplexInfinity] = {Protected};
Tests`ComplexInfinity = {
    ESimpleExamples[
        ESameTest[ComplexInfinity, 0^(-1)],
        ESameTest[ComplexInfinity, a/0],
        ESameTest[ComplexInfinity, ComplexInfinity * foo[x]],
        ESameTest[ComplexInfinity, Factorial[-1]]
    ]
};

Indeterminate::usage = "`Indeterminate` represents an indeterminate form.";
Attributes[Indeterminate] = {Protected};
Tests`Indeterminate = {
    ESimpleExamples[
        ESameTest[Indeterminate, 0/0],
        ESameTest[Indeterminate, Infinity - Infinity],
        ESameTest[Indeterminate, 0 * Infinity],
        ESameTest[Indeterminate, 0 * ComplexInfinity],
        ESameTest[Indeterminate, 0^0]
    ]
};

Pi::usage = "`Pi` is the constant of pi.";
N[Pi] := 3.141592653589793238462643383279502884197;
Times[Pi, a_Real, rest___] := N[Pi] * a * rest;
Attributes[Pi] = {ReadProtected, Constant, Protected};

E::usage = "`E` is the constant for the base of the natural logarithm.";
N[E] := 2.71828182845904523536028747135266249775724709370;
Times[E, a_Real, rest___] := N[E] * a * rest;
Attributes[E] = {ReadProtected, Constant, Protected};
