Rational::usage = "`Rational` is the head for the atomic rational type.";
Attributes[Rational] = {Protected};
Tests`Rational = {
    ESimpleExamples[
        EComment["Rationals are created from `Times` when a rational form is encountered:"],
        ESameTest[Rational, Times[5, 6^-1] // Head],
        EComment["Which is equivalent to typing them in directly:"],
        ESameTest[Rational, 5/6 // Head],
        EComment["Or being even more explicit:"],
        ESameTest[Rational, Rational[5, 6] // Head],
        EComment["Rationals simplify on evaluation:"],
        ESameTest[5/3, Rational[10, 6]],
        EComment["Which might include evaluating to an Integer:"],
        ESameTest[Integer, Rational[-100, 10] // Head],
        EComment["Rationals of non-Integer types are not allowed:"],
        EStringTest["Rational[0, n]", "Rational[0, n]"]
    ], EFurtherExamples[
        EComment["Undefined rationals are handled accordingly:"],
        EStringTest["Indeterminate", "Rational[0, 0]"],
        EStringTest["ComplexInfinity", "Rational[1, 0]"],
        EComment["Rational numbers have some special handling for pattern matching:"],
        ESameTest[2/3, test = Rational[2, 3]],
        ESameTest[True, MatchQ[test, 2/3]],
        ESameTest[True, MatchQ[test, Rational[a_Integer, b_Integer]]],
        ESameTest[{2, 3}, 2/3 /. Rational[a_Integer, b_Integer] -> {a, b}],
        ESameTest[2/3, 2/3 /. a_Integer/b_Integer -> {a, b}]
    ], ETests[
        ESameTest[10/7, Rational[10, 7]],
        EStringTest["Rational[x, 10]", "Rational[x, 10]"],
        EStringTest["10", "Rational[100, 10]"],
        ESameTest[-10, Rational[-100, 10]],
        EStringTest["10", "Rational[-100, -10]"],
        ESameTest[-5/3, Rational[-10, 6]],
        ESameTest[5/3, Rational[-10, -6]],
        EStringTest["0", "Rational[0, 5]"],
        EStringTest["Rational[0, n]", "Rational[0, n]"],
        EStringTest["ComplexInfinity", "Rational[-1, 0]"],
        EStringTest["ComplexInfinity", "Rational[-1, -0]"],
        EStringTest["Indeterminate", "Rational[-0, -0]"],
        EStringTest["Indeterminate", "Rational[-0, 0]"],
        ESameTest[buzz[bar], foo[bar, 1/2] /. foo[base_, 1/2] -> buzz[base]],
        ESameTest[buzz[bar], foo[bar, 1/2] /. foo[base_, Rational[1, 2]] -> buzz[base]],
        ESameTest[buzz[bar], foo[bar, Rational[1, 2]] /. foo[base_, 1/2] -> buzz[base]],
        ESameTest[buzz[bar], foo[bar, Rational[1, 2]] /. foo[base_, Rational[1, 2]] -> buzz[base]],
        ESameTest[True, MatchQ[1/2, Rational[1, 2]]],
        ESameTest[True, MatchQ[Rational[1, 2], 1/2]],
        ESameTest[False, Hold[Rational[1, 2]] === Hold[1/2]]
    ]
};

Complex::usage = "`Complex` is the head for the atomic rational type.";
(a : (_Integer|_Real|_Rational)) * Complex[real_, im_] * rest___ := Complex[a * real, a * im] * rest;
(a : (_Integer|_Real|_Rational)) + Complex[real_, im_] + rest___ := Complex[a + real, im] + rest;
Complex[x_,y_] + Complex[u_,v_] + rest___ := Complex[x+u,y+v] + rest;
Complex[x_,y_] * Complex[u_,v_] * rest___ := Complex[x*u-y*v,x*v+y*u] * rest;
Attributes[Complex] = {Protected};
Tests`Complex = {
    ESimpleExamples[
        ESameTest[Complex[-16, 28], (4 + 8I)(2 + 3I)]
    ]
};

String::usage = "`String` is the head for the atomic string type.";
Attributes[String] = {Protected};
Tests`String = {
    ESimpleExamples[
        ESameTest["Hello", "Hello"],
        ESameTest[True, "Hello" == "Hello"],
        ESameTest[False, "Hello" == "Hello world"],
        ESameTest[String, Head["Hello"]]
    ]
};

Real::usage = "`Real` is the head for the atomic floating point type.";
Attributes[Real] = {Protected};
Tests`Real = {
    ESimpleExamples[
        ESameTest[Real, Head[1.53]],
        EComment["One can force Real interperetation on an Integer by appending a decimal point:"],
        ESameTest[Real, Head[1.]],
        EComment["Real numbers are backed by arbitrary-precision floating points:"],
        EStringTest["10.", "10.^5000 / 10.^4999"]
    ], EFurtherExamples[
        ESameTest[True, MatchQ[1.53, _Real]]
    ]
};

Integer::usage = "`Integer` is the head for the atomic integer type.";
Attributes[Integer] = {Protected};
Tests`Integer = {
    ESimpleExamples[
        ESameTest[Integer, Head[153]],
        EComment["Integer numbers are backed by arbitrary-precision data structures:"],
        ESameTest[815915283247897734345611269596115894272000000000, Factorial[40]]
    ], EFurtherExamples[
        ESameTest[True, MatchQ[153, _Integer]]
    ]
};

IntegerQ::usage = "`IntegerQ[e]` returns True if `e` is an Integer, False otherwise.";
IntegerQ[e_] := Head[e] === Integer;
Attributes[IntegerQ] = {Protected};
Tests`IntegerQ = {
    ESimpleExamples[
        ESameTest[False, IntegerQ[a]],
        ESameTest[True, IntegerQ[1]],
        ESameTest[False, IntegerQ[2.]]
    ]
};

Im[x_Integer]  := 0;
Im[x_Real]     := 0;
Im[x_Rational] := 0;
Im[a_Integer * x_Integer?Positive^y_Rational] := 0;
Im[Complex[_,im_]] := im;

Re[x_Integer]  := x;
Re[x_Real]     := x;
Re[x_Rational] := x;
Re[Complex[re_,_]] := re;
