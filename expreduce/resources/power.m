Power::usage = "`base^exp` finds `base` raised to the power of `exp`.";
(*Simplify nested exponents*)
Power[Power[a_,b_Integer],c_Integer] := a^(b*c);
Power[Power[a_,b_Real],c_Integer] := a^(b*c);
Power[Power[a_,b_Symbol],c_Integer] := a^(b*c);
Power[Power[a_,b_Complex*c_Symbol],d_Integer] := a^(b*c*d);
Power[Power[a_,b_Rational],c_] := a^(b*c);
Power[Infinity, 0] := Indeterminate;
Power[-Infinity, 0] := Indeterminate;
Power[_, 0] := 1;
Power[Infinity, 0.] := Indeterminate;
Power[-Infinity, 0.] := Indeterminate;
Power[_, 0.] := 1;
Power[Infinity, -1] := 0;
Power[Indeterminate, _] := Indeterminate;
Power[_, Indeterminate] := Indeterminate;
Power[1, a_] := 1;
Power[b_?NumberQ, Infinity] := Which[
    b < -1,
    ComplexInfinity,
    b === -1,
    Indeterminate,
    b < 1,
    0,
    b === 1,
    Indeterminate,
    b > 1,
    Infinity,
    True,
    UnexpectedInfinitePowerBase
];
Power[b_, Infinity] := Indeterminate;
Power[b_?NumberQ, -Infinity] := Which[
    b < -1,
    0,
    b === -1,
    Indeterminate,
    b <= 0,
    ComplexInfinity,
    b < 1,
    Infinity,
    b === 1,
    Indeterminate,
    b > 1,
    0,
    True,
    UnexpectedInfinitePowerBase
];
(* Example: 3^(4/3) -> 3*3^(1/3) *)
Power[b_Integer, Rational[n_, d_]] := b^((n-Mod[n,d])/d) * b^(Mod[n,d]/d) /; Or[n > d, -n > d];
Power[b_, -Infinity] := Indeterminate;
(*Power definitions*)
(*Distribute any kind of power for numeric values in Times:*)
((first:(_Integer | _Real | _Rational)?((#!=-1)&)) * inner__)^pow_ := first^pow * Times[inner]^pow;
(*Otherwise, only distribute integer powers*)
(first_ * inner___)^pow_Integer := first^pow * Times[inner]^pow;
(*Rational simplifications*)
(*These take up time. Possibly convert to Upvalues.*)
Power[Rational[a_,b_], -1] := Rational[b,a];
Power[Rational[a_,b_], e_Integer?Positive] := Rational[a^e,b^e];
Power[-1, -1/2] := -I;
Power[-1, 1/2] := I;
Power[Rational[a_?Positive,b_?Positive], 1/2] := Power[a, 1/2] * Power[b, -1/2];
Power[Power[x_, y_Rational], -1] := Power[x, -y];
(*We may want to deprecate this in favor of the general definition.*)
Complex[0,1]^e_Integer := Switch[Mod[e, 4],
  0, 1,
  1, I,
  2, -1,
  3, -I];
Complex[re_,im_]^n_Integer := If[n===-1,
  Complex[re/(re^2+im^2), -(im/(re^2+im^2))],
  Module[{theta = ArcTan[re,im]}, Sqrt[re^2+im^2]^n*Complex[Cos[n*theta],Sin[n*theta]]]];
Complex[re_,im_]^n_Real := Module[{theta = ArcTan[re,im]}, Sqrt[re^2+im^2]^n*Complex[Cos[n*theta],Sin[n*theta]]];
Power[ComplexInfinity+_, -1] := 0;
_^ComplexInfinity := Indeterminate;
(*TODO(corywalker): Remove this as there should be a more general version.*)
E^pow_Real := N[E]^pow;
E^(Log[a_]+rest___) := a * E^rest;
E^Log[a_] := a;
E^(Complex[0, n_Integer]*Pi) := -(Mod[n, 2]*2 - 1);
a_Real ^ Complex[b_Real, c_Real] := Module[{inner},
  inner = b Arg[a]+1/2 c Log[a^2];
  (a^2)^(b/2) E^(-c Arg[a]) * Complex[Cos[inner], Sin[inner]]
];
Attributes[Power] = {Listable, NumericFunction, OneIdentity, Protected};
Tests`Power = {
    ESimpleExamples[
        EComment["Exponents of integers are computed exactly:"],
        ESameTest[-1/125, (-5)^-3],
        EComment["Floating point exponents are handled with floating point precision:"],
        EStringTest["1.99506e+3010", ".5^-10000."],
        EComment["Automatically apply some basic simplification rules:"],
        ESameTest[m^4., (m^2.)^2]
    ], EFurtherExamples[
        EComment["Expreduce handles problematic exponents accordingly:"],
        EStringTest["Indeterminate", "0^0"],
        ESameTest[ComplexInfinity, 0^(-1)]
    ], ETests[
        (*Test raising expressions to the first power*)
        ESameTest[1 + x, (x+1)^1],
        EStringTest["0", "0^1"],
        EStringTest["0.", "0.^1"],
        ESameTest[-5, -5^1],
        ESameTest[-5.5, -5.5^1],
        ESameTest[1 + x, (x+1)^1.],
        EStringTest["0", "0^1."],
        EStringTest["0.", "0.^1."],
        ESameTest[-5, (-5)^1.],
        ESameTest[-5.5, -5.5^1.],

        (*Test raising expressions to the zero power*)
        EStringTest["1", "(x+1)^0"],
        EStringTest["Indeterminate", "0^0"],
        EStringTest["Indeterminate", "0.^0"],
        ESameTest[-1, -5^0],
        EStringTest["1", "(-5)^0"],
        EStringTest["1", "(-5.5)^0"],
        EStringTest["1", "(x+1)^0."],
        EStringTest["Indeterminate", "0^0."],
        EStringTest["Indeterminate", "0.^0."],
        ESameTest[-1, -5^0.],
        EStringTest["1", "(-5.5)^0."],
        ESameTest[-1, -5^0],
        EStringTest["1", "99^0"],

        EStringTest["125", "5^3"],
        ESameTest[1/125, 5^-3],
        ESameTest[-125, (-5)^3],
        ESameTest[-1/125, (-5)^-3],

        EStringTest["2.97538e+1589", "39^999."],
        EStringTest["3.36092e-1590", "39^-999."],
        EStringTest["1.99506e+3010", ".5^-10000."],
        EStringTest["1.99506e+3010", ".5^-10000"],

        EStringTest["1", "1^1"],
        EStringTest["1", "1^2"],
        EStringTest["1", "1^0"],
        EStringTest["1", "1^-1"],
        EStringTest["1", "1^-2"],
        EStringTest["1", "1^99999992"],
        EStringTest["1.", "1^2."],
        EStringTest["1.", "1^99999992."],
        EStringTest["1.", "1.^30"],
        EStringTest["4.", "(1.*2*1.)^2"],
        ESameTest[-1, (-1)^1],
        EStringTest["1", "(-1)^2"],
        EStringTest["1", "(-1)^0"],
        EStringTest["1", "(-1)^0"],
        ESameTest[-1, (-1)^-1],
        EStringTest["1", "(-1)^-2"],
        EStringTest["1", "(-1)^99999992"],
        EStringTest["1.", "(-1.)^30"],
        EStringTest["4.", "(1.*2*-1.)^2"],
        ESameTest[-0.5, (1.*2*-1.)^(-1)],

        ESameTest[Rational, Power[2, -1] // Head],
        ESameTest[Integer, Power[1, -1] // Head],
        ESameTest[Integer, Power[2, 2] // Head],
        ESameTest[Rational, Power[-2, -1] // Head],
        ESameTest[Rational, Power[2, -2] // Head],

        (*Exponent simplifications*)
        ESameTest[m^4, m^2*m^2],
        ESameTest[m^4, (m^2)^2],
        ESameTest[(m^2)^2., (m^2)^2.],
        ESameTest[(m^2.)^2., (m^2.)^2.],
        ESameTest[m^4., (m^2.)^2],

        ESameTest[ComplexInfinity, 0^(-1)],

        ESameTest[{1}, ReplaceAll[a, a^p_. -> {p}]],

        ESameTest[0, 2^(-Infinity)],
        ESameTest[0, (-2)^(-Infinity)],
        ESameTest[Indeterminate, (-1)^(-Infinity)],
        ESameTest[Indeterminate, (1)^(-Infinity)],
        ESameTest[Indeterminate, (d)^(-Infinity)],
        ESameTest[Infinity, 2^(Infinity)],
        ESameTest[ComplexInfinity, (-2)^(Infinity)],
        ESameTest[Indeterminate, (-1)^(Infinity)],
        ESameTest[Indeterminate, (1)^(Infinity)],
        ESameTest[Indeterminate, (d)^(Infinity)],

        (* Test nth-root algorithm. *)
        ESameTest[2, 16^(1/4)],
        ESameTest[2., 16^(1/4.)],
        ESameTest[True, Head[101^(1/2)]=!=Integer],
        ESameTest[True, Head[99^(1/2)]=!=Integer],
        ESameTest[0, 0^(1/2)],
        ESameTest[8, 2^3],
        ESameTest[0, 0^(1/3)],
        ESameTest[0, 0^(1/4)],
        ESameTest[2, 8^(1/3)],
        ESameTest[Power, 7^(1/3)//Head],
        ESameTest[Power, 9^(1/3)//Head],
        ESameTest[1/2, 16^(-1/4)],
        ESameTest[ComplexInfinity, 0^(-1/3)],
        ESameTest[ComplexInfinity, 0^(-1/2)],
        ESameTest[1/3, 27^(-1/3)],
        ESameTest[Power, 7^(-1/3)//Head],
        ESameTest[Power, 9^(-1/3)//Head],
        ESameTest[27, 9^(3/2)],
        ESameTest[1/27, 9^(-3/2)],

        (* Test simplifying radicals *)
        ESameTest[4 2^(1/3), (128)^(1/3)],
        ESameTest[4 (-2)^(1/3), (-128)^(1/3)],
        ESameTest[15 7^(2/3) 57^(1/3), 9426375^(1/3)],
        ESameTest[15 7^(2/3) 57^(1/3), 9426375^(1/3)],
        ESameTest[3 3^(1/3), (3^4)^(1/3)],
        ESameTest[3 3^(1/3), (3)^(4/3)],
        ESameTest[15 7^(2/3) 57^(1/3), (3^(4/3)*5^(3/3)*7^(2/3)*19^(1/3))],
        ESameTest[15 7^(2/3) 57^(1/3), 5*3^(4/3)*7^(2/3)*19^(1/3)],
        ESameTest[3 3^(1/3), 3^(4/3)],
        ESameTest[3 3^(1/3), 3^(4/3)],
        ESameTest[a^(4/3), a^(4/3)],
        ESameTest[-(-1)^(1/3), (-1)^(4/3)],
        ESameTest[(-1)^(2/3), (-1)^(-4/3)],
        ESameTest[-(I/2), (-4)^(-1/2)],
        ESameTest[Indeterminate, (-1)^(-1/0)],
        ESameTest[1., (-1.)^0.5 // Im],
    ], EKnownFailures[
        ESameTest[(3+I Sqrt[29]) E^(-((2 I \[Pi])/3)), ((3 + I*Sqrt[29])^3)^(1/3)],
        ESameTest[{{-5,1/5^(1/3)},{-4,1/2^(2/3)},{-3,1/3^(1/3)},{-2,1/2^(1/3)},{-1,1},{0,ComplexInfinity},{1,-(-1)^(2/3)},{2,-((-1)^(2/3)/2^(1/3))},{3,-((-1)^(2/3)/3^(1/3))},{4,-(-(1/2))^(2/3)},{5,-((-1)^(2/3)/5^(1/3))}}, Table[{n, (-n)^(-1/3)}, {n, -5, 5}] // Quiet],
    ]
};

Log::usage = "`Log[e]` finds the natural logarithm of `e`.";
Log[n_Integer?Negative] := I*Pi + Log[-n];
Log[ComplexInfinity] := Infinity;
Log[Infinity] := Infinity;
Log[-ComplexInfinity] := Infinity;
Log[-Infinity] := Infinity;
Log[0] := -Infinity;
Log[1] := 0;
Log[E] := 1;
Log[E^p_?NumberQ] := p;
Log[Rational[1,b_]] := -Log[a];
Attributes[Log] = {Listable,NumericFunction,Protected};
Tests`Log = {
    ESimpleExamples[
        ESameTest[1, Log[E]],
        ESameTest[-2, Log[E^(-2)]],
        ESameTest[Log[2], Log[2]]
    ]
};

Sqrt::usage = "`Sqrt[e]` finds the square root of `e`.";
(*TODO: automatically simplify perfect squares*)
Attributes[Sqrt] = {Listable, NumericFunction, Protected};
Sqrt[a_Integer?Negative] := I*Sqrt[-a];
Sqrt[-a_?NumberQ] := I*Sqrt[a];
Sqrt[a_Integer*b_Plus] := Sqrt[Abs[a]]*Sqrt[(a/Abs[a])*b] /; a != 0;
Sqrt[a_Real?Positive] := a^.5;
Sqrt[x_] := Which[
    (*Normally we would define these directly, but right now "x_" is
    considered more specific than 0 or 1. *)
    x===0, 0,
    x===1, 1,
    True,  x^(1/2)
];
Tests`Sqrt = {
    ESimpleExamples[
        ESameTest[Sqrt[3], Sqrt[3]],
        ESameTest[I, Sqrt[-1]],
        ESameTest[I * Sqrt[3], Sqrt[-3]],
        ESameTest[1, Sqrt[1]],
        ESameTest[0, Sqrt[0]]
    ], ETests[
        ESameTest[Sqrt[2] Sqrt[-2-x^y], (-2)(x^y+2)//Sqrt],
    ]
};

I::usage = "`I` is the imaginary number representing `Sqrt[-1]`.";
I := Complex[0, 1];
Attributes[I] = {Locked, Protected, ReadProtected};
Tests`I = {
    ESimpleExamples[
        ESameTest[-1, I^2],
        ESameTest[1, I^4]
    ]
};

possibleExponents[n_Integer, m_Integer] :=
 Flatten[Permutations /@ ((PadRight[#, m]) & /@
     IntegerPartitions[n, m]), 1];
genVars[addends_List, exponents_List] := Times@@(addends ^ exponents);
genExpand[addends_List, exponents_List] :=
 Plus@@Table[(Multinomial @@ exponents[[ExpandUnique`i]])*
   genVars[addends, exponents[[ExpandUnique`i]]], {ExpandUnique`i, 1,
   Length[exponents]}];
expandRules := {
  s_Plus^n_Integer?Positive :>
    genExpand[List @@ s, possibleExponents[n, Length[s]]],
  c_*s_Plus :> ((c*#) &) /@ s
};
Expand::usage = "`Expand[expr]` attempts to expand `expr`.";
Expand[a_] := a //. expandRules;
Expand[a_, x_] := (Print["Expand does not support second argument."];Expand[a]);
Attributes[Expand] = {Protected};
Tests`Expand = {
    ESimpleExamples[
        ESameTest[a^3 + 3 a^2 * b + 3 a b^2 + b^3 + 3 a^2 * c + 6 a b c + 3 b^2 * c + 3 a c^2 + 3 b c^2 + c^3, Expand[(a + b + c)^3]],
        ESameTest[a c + b c + a d + b d + a e + b e, (a + b) * (c + d + e) // Expand],
        ESameTest[a d^2 + b d^2 + c d^2 + 2 a d e + 2 b d e + 2 c d e + a e^2 + b e^2 + c e^2, (a + b + c)*(d + e)^2 // Expand],
        ESameTest[a^(2 b) + 2 a^b * c^d + c^(2 d), Expand[(a^b + c^d)^2]],
        ESameTest[a/d + b/d + c/d, Expand[(a + b + c)/d]],
        ESameTest[1/d + (2 a)/d + a^2/d + b/d + c/d, Expand[((a + 1)^2 + b + c)/d]],
        ESameTest[2 + 2 a, 2*(a + 1) // Expand]
    ], ETests[
        ESameTest[Null, ((60 * c * a^2 * b^2) + (30 * c * a^2 * b^2) + (30 * c * a^2 * b^2) + a^5 + b^5 + c^5 + (5 * a * b^4) + (5 * a * c^4) + (5 * b * a^4) + (5 * b * c^4) + (5 * c * a^4) + (5 * c * b^4) + (10 * a^2 * b^3) + (10 * a^2 * c^3) + (10 * a^3 * b^2) + (10 * a^3 * c^2) + (10 * b^2 * c^3) + (10 * b^3 * c^2) + (20 * a * b * c^3) + (20 * a * c * b^3) + (20 * b * c * a^3));],
        ESameTest[1/3, ((1+I Sqrt[3]) (1/(2 2^(1/3))-(I Sqrt[3])/(2 2^(1/3))))/(3 2^(2/3))//Expand],
    ]
};

ExpandAll::usage = "`ExpandAll[expr]` attempts to expand `expr` at all levels.";
ExpandAll[a_] := Map[Expand, a, {0, Infinity}];
Attributes[ExpandAll] = {Protected};
Tests`ExpandAll = {
    ESimpleExamples[
        ESameTest[Log[-1+x^2], Log[(x+1)(x-1)]//ExpandAll],
    ]
};

PolynomialQ::usage =  "`PolynomialQ[e, var]` returns True if `e` is a polynomial in `var`.";
innerPolynomialQ[p_Plus, v_] :=
  AllTrue[List @@ p, (PolynomialQ[#, v]) &];
innerPolynomialQ[p_.*v_^Optional[exp_Integer], v_] :=
  If[FreeQ[p, v] && Positive[exp], True, False];
innerPolynomialQ[p_, v_] := If[FreeQ[p, v], True, False];
PolynomialQ[p_, v_] := innerPolynomialQ[p//Expand, v];
(*Seemingly undocumented version with no variable specification:*)
PolynomialQ[p_] := PolynomialQ[p, Variables[p]];
Attributes[PolynomialQ] = {Protected};
Tests`PolynomialQ = {
    ETests[
        ESameTest[True, PolynomialQ[2x^2-3x+2, x]],
        ESameTest[True, PolynomialQ[2x^2, x]],
        ESameTest[False, PolynomialQ[2x^2.5, x]],
        ESameTest[False, PolynomialQ[2x^-2, x]],
        ESameTest[True, PolynomialQ[2x^0, x]],
        ESameTest[False, PolynomialQ[2x^y, x]],
        ESameTest[True, PolynomialQ[-3x, x]],
        ESameTest[True, PolynomialQ[2, x]],
        ESameTest[True, PolynomialQ[2y^2, x]],
        ESameTest[True, PolynomialQ[-3y, x]],
        ESameTest[False, PolynomialQ[2x^2-3x+2+Cos[x], x]],
        ESameTest[False, PolynomialQ[Cos[x], x]],
        ESameTest[False, PolynomialQ[2x^2-3x+Cos[x], x]],
        ESameTest[False, PolynomialQ[2x^2-x*Cos[x], x]],
        ESameTest[True, PolynomialQ[2x^2-x*Cos[y], x]],
        ESameTest[True, PolynomialQ[2.5x^2-3x+2.5, 2.5]],
        ESameTest[True, PolynomialQ[2x^2-3x+2, "hello"]],
        ESameTest[True, PolynomialQ[2x^2-3x+2, y]],
        ESameTest[True, PolynomialQ[x, y]],
        ESameTest[True, PolynomialQ[y, y]],
        ESameTest[True, PolynomialQ[2*x, y]],
        ESameTest[False, PolynomialQ[2*x^Sin[y], x]],
        ESameTest[True, PolynomialQ[Sin[y]*x^2, x]],
        ESameTest[False, PolynomialQ[Sin[y]*x^2.5, x]],
        ESameTest[False, PolynomialQ[Sin[y]*x^y, x]],
        ESameTest[True, PolynomialQ[2*y, y]],
        ESameTest[True, PolynomialQ[y*x, y]],
        ESameTest[True, PolynomialQ[y*x, z]],
        ESameTest[True, PolynomialQ[y*Sin[x], z]],
        ESameTest[False, PolynomialQ[y^x, y]],
        ESameTest[False, PolynomialQ[x^y, y]],
        ESameTest[True, PolynomialQ[x^y, z]],
        ESameTest[True, PolynomialQ[2.5*x^2, 2.5]],
        ESameTest[True, PolynomialQ[2.5*x, 2.5]],
        ESameTest[False, PolynomialQ[2*x^2, 2]],
        ESameTest[True, PolynomialQ[2*x, 2]],
        ESameTest[True, PolynomialQ[x, 2]],
        ESameTest[True, PolynomialQ[Cos[x*y], Cos[x*y]]],
        ESameTest[True, PolynomialQ[x^2,2.]],
        ESameTest[False, PolynomialQ[x^a,a]],
        ESameTest[False, PolynomialQ[x^n,x]],
        ESameTest[True, PolynomialQ[-x*Cos[y],x]],
        ESameTest[True, PolynomialQ[x^y, 1]],
        ESameTest[True, PolynomialQ[(-280*c^4*d^2*x^2 + -315*c^6*d^2*x^4 + 9*c^2*(63*d^2 + 90*c^2*d^2*x^2 + 35*c^4*d^2*x^4))//Expand,x]],
        ESameTest[True, PolynomialQ[(-280*c^4*d^2*x^2 + -315*c^6*d^2*x^4 + 9*c^2*(63*d^2 + 90*c^2*d^2*x^2 + 35*c^4*d^2*x^4)),x]],
    ], EKnownFailures[
        ESameTest[True, PolynomialQ[2*x^2-3x+2, 2]],
        ESameTest[True, PolynomialQ[2*x^2-3x, 2]],
        ESameTest[False, PolynomialQ[x/y]]
    ]
};

Exponent::usage = "`Exponent[p, var]` returns the degree of `p` with respect to the variable `var`.";
Exponent[expr_/p_Plus, var_, head_] := Exponent[expr, var, head];
Exponent[expr_, var_, head_] := If[expr === 0, head[],
  Module[{e = expr, v = var, h = head, theCases, toCheck},
   toCheck = expr // Expand;
   toCheck = If[Head[toCheck] === Plus, toCheck, {toCheck}];
   theCases =
    Cases[toCheck, p_.*v^Optional[exp_] -> exp] // DeleteDuplicates;
   If[Length[theCases] =!= Length[toCheck], PrependTo[theCases, 0]];
   h @@ theCases
   ]];
Exponent[expr_, var_] := Exponent[expr, var, Max];
Attributes[Exponent] = {Listable, Protected};
Tests`Exponent = {
    ESimpleExamples[
        EComment["Find the degree of a polynomial:"],
        ESameTest[5, Exponent[3 + x^3 + k*x^5, x]]
    ], EFurtherExamples[
        EComment["Find the degree of a polynomial:"],
        ESameTest[{0,3,5}, Exponent[3 + x^3 + k*x^5, x, List]]
    ], ETests[
        (*Sorting of the input addition expression is off here, so we sort*)
        (*the result so it does match up.*)
        ESameTest[{0,3,5,x^x}, Exponent[3 + "hello" + x^3 + a*x^5 + x^x^x, x, List]//Sort],
        ESameTest[{0}, Exponent[1 + x^x^x, x^x, List]],
        ESameTest[{0}, Exponent[2 + a, x, List]],
        ESameTest[{0}, Exponent[a, x, List]],
        ESameTest[{2}, Exponent[x^2, x, List]],
        ESameTest[{1}, Exponent[x^2 - x*(a + x), x, List]],
        ESameTest[{0,1}, Exponent[(1 + x)/(3 + x), x, List]],
        ESameTest[{0,2}, Exponent[(1 + x^2)/(3 + x), x, List]],
        ESameTest[{0,1}, Exponent[(1 + x)/(3 + x^3), x, List]],
        ESameTest[{0}, Exponent[(3 + x^3)^(-1), x, List]],
        ESameTest[{-3}, Exponent[x^(-3), x, List]],
        ESameTest[{-3}, Exponent[a/x^3, x, List]],
        ESameTest[{-2}, Exponent[x^(-2), x, List]],
        ESameTest[{1}, Exponent[(a*x)/(3 + x^3), x, List]],
        ESameTest[{0,1}, Exponent[1 + b*x + x^2 - (x*(1 + a*x))/a, x, List]],
        ESameTest[{0,1}, Exponent[1 + x + x^2 - (x*(1 + 2*x))/2, x, List]],
        ESameTest[{}, Exponent[0, x, List]],
        ESameTest[{}, Exponent[0, x+2, List]],
        ESameTest[{}, Exponent[0, 0, List]]
    ], EKnownFailures[
        ESameTest[{0,1}, Exponent[1 + x^x^x, x^x^x, List]]
    ]
};

ExpreduceSingleCoefficient[inP_, inTerm_] :=
  Module[{p = inP, term = inTerm, pat},
   (*If[MatchQ[p,term],Return[1]];*)
   pat = If[term === 1, Print["Warning: term of 1 used"]; a_?NumberQ, Optional[a_]*term];
   (*pat=Optional[a_]*term;*)
   If[MatchQ[p, pat],
    (p) /. pat -> a, 0]
   ];
ExpreduceNonProp[inP_, inTerm_] :=
  Module[{p = inP, term = inTerm, toMatch, pat},
   toMatch = p // Expand;
   pat = Except[Optional[a_]*term^n_.];
   If[Head[toMatch] === Plus,
    Plus@@Cases[toMatch, pat],
    If[MatchQ[toMatch, pat], toMatch, 0]]
   ];
Coefficient::usage =  "`Coefficient[p, form]` returns the coefficient of form `form` in polynomial `p`.";
Coefficient[p_, var_, exp_] :=
    If[exp === 0,
        ExpreduceNonProp[p, var],
        Coefficient[p, var^exp]
    ];
Coefficient[inP_, inTerm_] :=
  Module[{p = inP, term = inTerm, toMatch},
   toMatch = p // Expand;
   If[Head[toMatch] === Plus,
    Map[ExpreduceSingleCoefficient[#, term] &, toMatch],
    ExpreduceSingleCoefficient[toMatch, term]]
   ];
Attributes[Coefficient] = {Listable, Protected};
Tests`Coefficient = {
    ESimpleExamples[
        ESameTest[3, Coefficient[(a + b)^3, a*b^2]]
    ], ETests[
        ESameTest[j, Coefficient[c + j*a + k*b, a]],
        ESameTest[a, Coefficient[c + k*x + a*x^3, x, 3]],
        ESameTest[24, Coefficient[2*b*(2*a + 3*b)*(1 + 2*a + 3*b), a*b^2]],
        ESameTest[29, Coefficient[(2 + x)^2 + (5 + x)^2, x, 0]],
        ESameTest[1, Coefficient[a + x, x]],
        ESameTest[4, Coefficient[2*b*(2*a + 3*b)*(1 + 2*a + 3*b), a*b]],
        ESameTest[1, Coefficient[x^2, x^2]],
        ESameTest[-a, Coefficient[x^2 - x*(a + x), x]],
        ESameTest[-(1/a)+b, Coefficient[1 + b*x + x^2 - (x*(1 + a*x))/a, x]],
        ESameTest[1/2, Coefficient[1 + x + x^2 - (x*(1 + 2*x))/2, x]],
        ESameTest[a, Coefficient[a,x,0]],
        ESameTest[a b, Coefficient[a*b,x,0]],
        ESameTest[a b+c^d, Coefficient[a*b+c^d,x,0]],
        ESameTest[a b+c^d, Coefficient[a*b+c^d+5x,x,0]],
        ESameTest[0, Coefficient[(a*b+c^d)*x^2+5x,x,0]]
    ]
};

CoefficientList::usage =  "`CoefficientList[p, var]` returns the list of coefficients associated with variable `var`.";
CoefficientList[p_, var_] :=
    Table[Coefficient[p,var,i],{i,0,Exponent[p,var]}];
Attributes[CoefficientList] = {Protected};
Tests`CoefficientList = {
    ESimpleExamples[
        ESameTest[{b,3,5}, CoefficientList[b+3x+5x^2,x]],
        ESameTest[{0,0,5}, CoefficientList[5x^2,x]],
        ESameTest[{-(a/b),1/b}, CoefficientList[(-a+x)/b,x]]
    ], ETests[
        ESameTest[{b,3,0,5}, CoefficientList[b+3x+5x^3,x]],
        ESameTest[{b+3 x+5 x^3}, CoefficientList[b+3x+5x^3,y]],
        ESameTest[{3 x+5 x^3,1}, CoefficientList[b+3x+5x^3,b]]
    ]
};

PolynomialQuotientRemainder::usage =  "`PolynomialQuotientRemainder[poly_, div_, var_]` returns the quotient and remainder of `poly` divided by `div` treating `var` as the polynomial variable.";
ExpreduceLeadingCoeff[p_, x_] := Coefficient[p, x^Exponent[p, x]];
PolynomialQuotientRemainder[inp_, inq_, v_] :=
  Module[{a = inp, b = inq, x = v, r, d, c, i, s, q, rExp},
   (*I should think carefully about when I use = vs := to avoid unwanted evaluation*)
   q = 0;
   r = a;
   d = Exponent[b, x];
   pow = x^d;
   (* This should happen any time that inq is free of v, or if inq === 1. *)
   If[pow === 1, Return[{a/b//Distribute, 0}]];
   c = Coefficient[b, pow];
   i = 1;
   While[rExp = Exponent[r, x]; rExp >= d && i < 20,
    (*Looks like we get the coefficient and the exponent of the leading term here. Perhaps we can just grab the leading term and get both at once. And maybe we can exploit the canonical ordering*)
    (*But all of this seems wrong. I think the slowness resides in the expreduce interpreter.*)
    (*TODO tomorrow: find out what 'power' function takes up the most time and optimize it by making kernel changes*)
    s = (Coefficient[r, x^rExp]/c)*x^(rExp - d);
    q = q + s;
    r = r - s*b;
    i = i + 1;
    ];
   {q, r} // Expand
   ];
Attributes[PolynomialQuotientRemainder] = {Protected};
PolynomialQuotient::usage =  "`PolynomialQuotient[poly_, div_, var_]` returns the quotient of `poly` divided by `div` treating `var` as the polynomial variable.";
PolynomialQuotient[inp_, inq_, v_] :=
  PolynomialQuotientRemainder[inp, inq, v][[1]];
Attributes[PolynomialQuotient] = {Protected};
PolynomialRemainder::usage =  "`PolynomialRemainder[poly_, div_, var_]` returns the remainder of `poly` divided by `div` treating `var` as the polynomial variable.";
PolynomialRemainder[inp_, inq_, v_] :=
  PolynomialQuotientRemainder[inp, inq, v][[2]];
Attributes[PolynomialRemainder] = {Protected};
Tests`PolynomialQuotientRemainder = {
    ESimpleExamples[
        ESameTest[{x^2/2,2}, PolynomialQuotientRemainder[2 + x^2 + x^3, 2 + 2*x, x]],
        ESameTest[{x^2-x y+y^2,-y^3}, PolynomialQuotientRemainder[x^3, x + y, x]],
        ESameTest[{x/a,1-x/a}, PolynomialQuotientRemainder[1 + x^3, 1 + a*x^2, x]]
    ], ETests[
        ESameTest[{b+a/x,0}, PolynomialQuotientRemainder[a+b*x,x,a]],
        ESameTest[{a+b x,0}, PolynomialQuotientRemainder[a+b*x,1,a]],
        ESameTest[{a/c+(b x)/c,0}, PolynomialQuotientRemainder[a+b*x,c,a]]
    ]
};
Tests`PolynomialQuotient = {
    ESimpleExamples[
        ESameTest[x^2/2, PolynomialQuotient[2 + x^2 + x^3, 2 + 2*x, x]],
        ESameTest[x^2-x y+y^2, PolynomialQuotient[x^3, x + y, x]],
        ESameTest[x/a, PolynomialQuotient[1 + x^3, 1 + a*x^2, x]]
    ]
};
Tests`PolynomialRemainder = {
    ESimpleExamples[
        ESameTest[2, PolynomialRemainder[2 + x^2 + x^3, 2 + 2*x, x]],
        ESameTest[-y^3, PolynomialRemainder[x^3, x + y, x]],
        ESameTest[1-x/a, PolynomialRemainder[1 + x^3, 1 + a*x^2, x]]
    ]
};

FactorTermsList::usage =  "`FactorTermsList[expr]` factors out the constant term of `expr` and puts the factored result into a `List`.";
ExpreduceConstantTerm[c_?NumberQ] := {c, 1};
ExpreduceConstantTerm[c_?NumberQ*e_] := {c, e};
ExpreduceConstantTerm[e_] := {1, e};
FactorTermsList[expr_] := Module[{e = expr, toFactor, cTerms, c},
   toFactor = e // Expand;
   If[Head[toFactor] =!= Plus,
    Return[ExpreduceConstantTerm[toFactor]]
    ];
   (* Parens are necessary due to precedence issue. *)
   cTerms = ((ExpreduceConstantTerm /@ (List @@ toFactor)) //
       Transpose)[[1]];
   c = GCD @@ cTerms;
   If[Last[cTerms] < 0, c = -c];
   {c, toFactor/c // Expand}
   ];
Attributes[FactorTermsList] = {Protected};
Tests`FactorTermsList = {
    ESimpleExamples[
        ESameTest[{2,Sin[8 k]}, FactorTermsList[2*Sin[8*k]]],
        ESameTest[{1/2,a+x}, FactorTermsList[a/2 + x/2]],
        ESameTest[{1,a+x}, FactorTermsList[a + x]]
    ], ETests[
        ESameTest[{1,1}, FactorTermsList[1]],
        ESameTest[{5,1}, FactorTermsList[5]],
        ESameTest[{5.,1}, FactorTermsList[5.]],
        ESameTest[{1,a}, FactorTermsList[a]],
        ESameTest[{1/2,a}, FactorTermsList[a/2]],
        ESameTest[{-(3/2),x}, FactorTermsList[(-3*x)/2]],
        ESameTest[{2,a+x}, FactorTermsList[2*a + 2*x]],
        ESameTest[{1/2,a/(2 b+2 c)+x/(2 b+2 c)}, FactorTermsList[(a/2 + x/2)/(2*b + 2*c)]],
        ESameTest[{1,2+x^2}, FactorTermsList[(8 + 4*x^2)/4]],
        ESameTest[{-(1/2),2+3 x+x^2}, FactorTermsList[(-4 - 6*x - 2*x^2)/4]],
        ESameTest[{-(1/2),-2+3 x+x^2}, FactorTermsList[(2 - 3*x - x^2)/2]],
        ESameTest[{-(1/2),-2-3 x+x^2}, FactorTermsList[(2 + 3*x - x^2)/2]],
        ESameTest[{1/2,2+3 x+x^2}, FactorTermsList[(2 + 3*x + x^2)/2]],
        ESameTest[{1/2,-2-3 x+x^2}, FactorTermsList[(-2 - 3*x + x^2)/2]],
        ESameTest[{5,2+3 x+x^2}, FactorTermsList[5*(1 + x)*(2 + x)]],
        ESameTest[{40,1+3 x+3 x^2+x^3}, FactorTermsList[5*(2 + 2*x)^3]],
        ESameTest[{-6,1+x}, FactorTermsList[(-12 - 12*x)/2]],
        ESameTest[{2/3,3+x}, FactorTermsList[(18 + 6*x)/9]],
        ESameTest[{-(2800301/67344500),1-2 x+x^3}, FactorTermsList[(-2800301/538756 + (2800301*x)/269378 - (2800301*x^3)/538756)/125]]
    ]
};

FactorTerms::usage =  "`FactorTerms[expr]` factors out the constant term of `expr`, if any.";
FactorTerms[expr_] := Module[{e = expr, factored},
    factored = FactorTermsList[e];
    If[factored[[1]] === 1,
      factored[[2]],
      Times@@factored
    ]
   ];
Attributes[FactorTerms] = {Protected};
Tests`FactorTerms = {
    ESimpleExamples[
        ESameTest[2*Sin[8 k], FactorTerms[2*Sin[8*k]]],
        ESameTest[(1/2)*(a+x), FactorTerms[a/2 + x/2]],
        ESameTest[a+x, FactorTerms[a + x]]
    ]
};

ExpreduceFactorConstant[p_Plus] := Module[{e = p, cTerms, c},
   (* Parens are necessary due to precedence issue. *)
   cTerms = ((ExpreduceConstantTerm /@ (List @@ e)) // Transpose)[[1]];
   c = GCD @@ cTerms;
   If[Last[cTerms] < 0, c = -c];
   c * Distribute[e/c]
   ];
ExpreduceFactorConstant[e_] := e;
Attributes[ExpreduceFactorConstant] = {Protected};

Variables::usage = "`Variables[expr]` returns the variables in `expr`.";
Variables[s_Symbol] := {s};
Variables[s_^p_Integer] := Variables[s];
Variables[s_^p_Rational] := Variables[s];
Variables[s_^p_Plus] :=
  If[NumericQ[s], {}, (((s^#) &) /@ p) // Variables];
Variables[s_^p_] := If[NumericQ[s], {}, {s^p}];
Variables[s_^p_Times] :=
  If[NumericQ[s], {}, {s^DeleteCases[p, _Integer]}];
Variables[e_] := (
   If[NumericQ[e] || Length[e] === 0, Return[{}]];
   If[MemberQ[{Plus, Times, List}, Head[e]],
    Return[Union @@ Variables /@ (List @@ e)]];
   If[Length[e] > 0, Return[{e}]];
   Unknown
   );
Attributes[Variables] = {Protected};
Tests`Variables = {
    ESimpleExamples[
        ESameTest[{x, y}, Variables[x + y + y^2]],
        ESameTest[{w^w, x^y, z}, Variables[w^w + x^y + z]],
        ESameTest[{a, b^c, b^d}, Variables[a^2*b^(2*c + 2*d)]]
    ], ETests[
        ESameTest[{x, y}, Variables[x*y]],
        ESameTest[{x, y}, Variables[x + y]],
        ESameTest[{x, y, y^2.5}, Variables[x + y + y^2.5]],
        ESameTest[{y}, Variables[y^2]],
        ESameTest[{x^y}, Variables[x^y]],
        ESameTest[{x^y, y^x}, Variables[x^y + y^x]],
        ESameTest[{x^y, z}, Variables[x^y + z]],
        ESameTest[{w, x^y, z}, Variables[w^2 + x^y + z]],
        ESameTest[{}, Variables[2^(x + y)]],
        ESameTest[{}, Variables[2^x]],
        ESameTest[{}, Variables[foo[]]],
        ESameTest[{foo[x]}, Variables[foo[x]]],
        ESameTest[{foo[x, y]}, Variables[foo[x, y]]],
        ESameTest[{foo[2]}, Variables[foo[2]]],
        ESameTest[{}, Variables[Sin[2]]],
        ESameTest[{Sin[x]}, Variables[Sin[x]]],
        ESameTest[{}, Variables[1]],
        ESameTest[{x}, Variables[{x}]],
        ESameTest[{}, Variables[{1}]],
        ESameTest[{x}, Variables[x]],
        ESameTest[{a, b, x, y, z}, Variables[a + (a + b)^2 + x*y^3 + 2*z]],
        ESameTest[{a, b}, Variables[(a + b)^2]],
        ESameTest[{a, b}, Variables[(a + 2*b)^2]],
        ESameTest[{a, b^c, b^d}, Variables[(a + b^(c + d))^2]],
        ESameTest[{a, b^c, b^d}, Variables[a + b^(c + d)]],
        ESameTest[{(a*b^(c + d))^e}, Variables[(a*b^(c + d))^e]],
        ESameTest[{(a + b)^c}, Variables[(a + b)^c]],
        ESameTest[{(a + b)^c, (a + b)^d}, Variables[(a + b)^(c + d)]],
        ESameTest[{}, Variables[2^(c + d)]],
        ESameTest[{Log[b]}, Variables[Log[b]]],
        ESameTest[{a^b, a^c}, Variables[a^(b + c)]],
        ESameTest[{b^c, b^d}, Variables[b^(2*c + 2*d)]],
        ESameTest[{b^(c*d)}, Variables[b^(2*c*d)]],
        ESameTest[{b^(c*d)}, Variables[b^(c*d)]],
        ESameTest[{b^(2.5*c*d)}, Variables[b^(2.5*c*d)]],
        ESameTest[{(a + b)^2.5}, Variables[(a + b)^2.5]],
        ESameTest[{(a + b)^(2.5*a)}, Variables[(a + b)^(2.5*a)]],
        ESameTest[{(a + b)^2.5, (a + b)^a}, Variables[(a + b)^(2.5 + a)]],
        ESameTest[{}, Variables[5.656854249492381]],
        ESameTest[{}, Variables[{}]],
        ESameTest[{a^"Hello"}, Variables[a^"Hello"]],
        ESameTest[{}, Variables[2^"Hello"]],
        ESameTest[{}, Variables[2^"Hello"^2]],
        ESameTest[{a^"Hello"^2}, Variables[a^"Hello"^2]],

        ESameTest[{}, Variables[Pi^y]],
        ESameTest[{a, Log[b]}, Variables[Sqrt[a] + Log[b]]],
        ESameTest[{a}, Variables[Sqrt[a]]]
    ], EKnownFailures[
        (*I think these have to do with NumericQ.*)
        ESameTest[{(a*b)^c, (a*b)^d}, Variables[(a*b)^(c + d)]]
    ]
};

PolynomialGCD::usage = "`PolynomialGCD[a, b]` calculates the polynomial GCD of `a` and `b`.";
PolySubresultantGCD[inA_, inB_, inX_] :=
  Module[{u = inA, v = inB, x = inX, h, delta, beta, newU, newV, i},
   h = 1;
   i = 1;
   While[v =!= 0 && i < 20,
    uEx = Exponent[u, x];
    vEx = Exponent[v, x];
    delta = uEx - vEx;
    beta = (-1)^(delta + 1)*uEx*h^delta;
    h = h*(vEx/h)^delta;
    newU := v;
    newV = PolynomialRemainder[u, v, x]/beta;
    u = newU;
    v = newV;
    i = i + 1;
    ];
   If[Exponent[u, x] == 0, 1, u]
   ];
(* doesn't work with rational functions yet. *)
(* Looks like prefactored inputs remain factored. *)
PolynomialGCD[inA_, inB_] :=
  FactorTermsList[
    PolySubresultantGCD[inA, inB, Variables[inA][[1]]]][[2]];
Attributes[PolynomialGCD] = {Listable, Protected};
Tests`PolynomialGCD = {
    ESimpleExamples[
        ESameTest[5+a, PolynomialGCD[15+13 a+2 a^2,10+7 a+a^2]],
        ESameTest[5+a+a^2, PolynomialGCD[15+13 a+5 a^2+2 a^3,10+7 a+3 a^2+a^3]],
        ESameTest[-5-a+a^2, PolynomialGCD[15+13 a-a^2-2 a^3,5+a-a^2]]
    ]
};

SquareFreeQ::usage = "`SquareFreeQ[expr]` returns True if `expr` is a square-free polynomial.";
(*only works for univariate polynomials, does not support numbers *)
SquareFreeQ[ex_] := Module[{f = ex, expF, polyvar, fprime},
   If[Length[Variables[f]] != 1, Return[False]];
   expF = Expand[f];
   polyvar = Variables[expF][[1]];
   If[! PolynomialQ[expF, polyvar], Return[False]];
   fprime = D[expF, polyvar];
   PolynomialGCD[expF, fprime] === 1];
Attributes[SquareFreeQ] = {Protected, ReadProtected};
Tests`SquareFreeQ = {
    ESimpleExamples[
        ESameTest[False, SquareFreeQ[(x+1)(x+2)^2//Expand]],
        ESameTest[True, SquareFreeQ[(x + 1) (x + 2)]],
        ESameTest[True, SquareFreeQ[(2 x + 3) (x + 2) // Expand]],
        ESameTest[False, SquareFreeQ[(2 x + 3)^2]]
    ]
};

PSimplify[expr_] := expr;
PSimplify[p_?PolynomialQ/q_?PolynomialQ] :=
  If[Length[Variables[p]] === 1 && Variables[p] === Variables[q],
   PolynomialQuotient[p, q, Variables[p][[1]]], p/q];
Tests`PSimplify = {
    ESimpleExamples[
        ESameTest[-1 + x^2, PSimplify[(1 - 2*x^2 + x^4)/(-1 + x^2)]],
        ESameTest[4*x, PSimplify[(-4*x + 4*x^3)/(-1 + x^2)]],
        ESameTest[-1 - x + x^3 + x^4, PSimplify[(1 - x^2 - x^3 + x^5)/(-1 + x)]],
        ESameTest[2*x + 5*x^2 + 5*x^3, PSimplify[(-2*x - 3*x^2 + 5*x^4)/(-1 + x)]],
        ESameTest[-6 + 11*x - 6*x^2 + x^3, PSimplify[(18 - 39*x + 29*x^2 - 9*x^3 + x^4)/(-3 + x)]],
        ESameTest[13 - 15*x + 4*x^2, PSimplify[(-39 + 58*x - 27*x^2 + 4*x^3)/(-3 + x)]],
        ESameTest[-3 - x + 3*x^2 + x^3, PSimplify[(-9 - 6*x + 8*x^2 + 6*x^3 + x^4)/(3 + x)]],
        ESameTest[-2 + 6*x + 4*x^2, PSimplify[(-6 + 16*x + 18*x^2 + 4*x^3)/(3 + x)]]
    ], ETests[
        ESameTest[12 + 4*x - 15*x^2 - 5*x^3 + 3*x^4 + x^5, PSimplify[(-108 - 108*x + 207*x^2 + 239*x^3 - 81*x^4 - 153*x^5 - 27*x^6 + 21*x^7 + 9*x^8 + x^9)/(-9 - 6*x + 8*x^2 + 6*x^3 + x^4)]],
        ESameTest[12 - 54*x - 33*x^2 + 18*x^3 + 9*x^4, PSimplify[(-108 + 414*x + 717*x^2 - 324*x^3 - 765*x^4 - 162*x^5 + 147*x^6 + 72*x^7 + 9*x^8)/(-9 - 6*x + 8*x^2 + 6*x^3 + x^4)]]
    ],
};

myFactorCommonTerms[a_] := a;
allTimes[p_Plus] := AllTrue[p, (Head[#] === Times) &];
myFactorCommonTerms[a_Plus] := Module[{commonTerms},
   If[! allTimes[a], Return[a]];
   commonTerms = Intersection @@ a;
   commonTerms ((a/commonTerms) // Expand)
   ];

FactorSquareFree::usage = "`FactorSquareFree[poly]` computes the square free factorization of `poly`.";
FactorSquareFree[poly_] :=
  Module[{f = poly, a, b, nb, c, d, i, res, fprime, polyvar, vars},
   vars = Variables[f];
   If[Length[vars] != 1, Return[f//myFactorCommonTerms]];
   polyvar = vars[[1]];
   If[! PolynomialQ[f, polyvar], Return[f]];
   fprime = D[f, polyvar];
   a = PolynomialGCD[f, fprime];
   res = If[SquareFreeQ[a], a, a // FactorSquareFree];
   nb = PolynomialQuotient[f,a,polyvar];
   c = PolynomialQuotient[fprime,a,polyvar];
   d = c - D[nb, polyvar];
   i = 1;
   b = nb;
   While[b =!= 1 && i < 20,
    a = PolynomialGCD[b, d];
    nb = PolynomialQuotient[b,a,polyvar];
    c = PolynomialQuotient[d,a,polyvar];
    res = res*If[SquareFreeQ[a], a, a // FactorSquareFree];
    i = i + 1;
    b = nb;
    d = c - D[b, polyvar]
    (*Print[{Subscript[a, i-1],Subscript[b, i],Subscript[c, i],
    Subscript[d, i]}]*)];
   res
   ];
Attributes[FactorSquareFree] = {Listable, Protected};
Tests`FactorSquareFree = {
    ESimpleExamples[
        ESameTest[(-1 + x^2)^2, FactorSquareFree[1 - 2*x^2 + x^4]],
        ESameTest[(-1 + x)^2*(1 + 2*x + 2*x^2 + x^3), FactorSquareFree[1 - x^2 - x^3 + x^5]],
        ESameTest[(-3 + x)^2*(2 - 3*x + x^2), FactorSquareFree[18 - 39*x + 29*x^2 - 9*x^3 + x^4]],
        ESameTest[(3 + x)^3*(-4 + x^2)*(-1 + x^2)^2, FactorSquareFree[-108 - 108*x + 207*x^2 + 239*x^3 - 81*x^4 - 153*x^5 - 27*x^6 + 21*x^7 + 9*x^8 + x^9]]
    ], ETests[
        ESameTest[a (b+c), FactorSquareFree[a b+a c]],
    ]
};

Factor::usage = "`Factor[poly]` factors `poly`.";
Factor[poly_] := poly;
Attributes[Factor] = {Listable, Protected};
Tests`Factor = {
    ETests[
        ESameTest[a, Factor[a]],
    ]
};

PowerExpand[exp_] := exp //. {
  Log[x_ y_]:>Log[x]+Log[y],
  Log[x_^k_]:>k Log[x],
  Sqrt[-a_]:>I*Sqrt[a],
  Sqrt[a_^2]:>a,
  Sqrt[a_/b_]:>Sqrt[a]/Sqrt[b],
  (a_^b_Integer)^c_Rational:>a^(b*c)
};
Attributes[PowerExpand] = {Protected};
Tests`PowerExpand = {
    ESimpleExamples[
        EComment["`PowerExpand` can expand nested log expressions:"],
        ESameTest[Log[a] + e (Log[b] + d Log[c]), PowerExpand[Log[a (b c^d)^e]]],
        ESameTest[{I Sqrt[a],a,Sqrt[a]/Sqrt[b]}, {Sqrt[-a],Sqrt[a^2],Sqrt[a/b]}//PowerExpand]
    ]
};

Arg::usage = "`Arg[x]` computes the argument of `x`.";
Attributes[Arg] = {Listable, NumericFunction, Protected};
Arg[a_?NumberQ] := ArcTan[Re[a], Im[a]];
Arg[a_] := ArcTan[Re[a], Im[a]] ;/ (FreeQ[ReIm[a], Re] && FreeQ[ReIm[a], Im]);
Tests`Arg = {
    ESimpleExamples[
        ESameTest[Pi/4, Arg[1/2 E^(I*Pi/4)]],
    ]
};

Conjugate::usage = "`Conjugate[x]` computes the complex conjugate of `x`.";
Conjugate[a_] := a - 2 Im[a] I ;/ (FreeQ[Im[a], Re] && FreeQ[Im[a], Im]);
Attributes[Conjugate] = {Listable, NumericFunction, Protected, ReadProtected};
Tests`Conjugate = {
    ESimpleExamples[
        ESameTest[4-4I, Conjugate[4+4I]],
        ESameTest[-4I, Conjugate[4I]],
        ESameTest[4, Conjugate[4]],
    ]
};

ComplexExpand::usage = "`ComplexExpand[e]` returns a complex expansion of `e`.";
Attributes[ComplexExpand] = {Protected};
complexExpandInner[e_] := e;
complexExpandInner[(a_Integer?Negative)^b_Rational] :=
  Module[{coeff, inner},
   coeff = ((a^2)^(b/2));
   inner = b*Arg[a];
   coeff*Cos[inner] + I*coeff*Sin[inner]];
complexExpandInner[E^((a_ + I*b_)*c_)] := E^(a c) Cos[b c]+I E^(a c) Sin[b c];
complexExpandInner[E^(Complex[a_, b_]*c_)] := E^(a c) Cos[b c]+I E^(a c) Sin[b c];
ComplexExpand[exp_] :=
  Map[complexExpandInner, exp, {0, Infinity}] // Expand;
Tests`ComplexExpand = {
    ESimpleExamples[
        ESameTest[a, ComplexExpand[a]],
        ESameTest[1, ComplexExpand[1]],
        ESameTest[a b+a c, ComplexExpand[a*(b+c)]],
        ESameTest[1/2+(I Sqrt[3])/2, ComplexExpand[(-1)^(1/3)]],
        ESameTest[-(1/2)-(I Sqrt[3])/2, ComplexExpand[(-1)^(4/3)]],
        ESameTest[2 2^(1/3), ComplexExpand[(2)^(4/3)]],
        ESameTest[-1+I Sqrt[3], ComplexExpand[(-1)^(1/3) (1+I Sqrt[3])]],
        ESameTest[d E^(a c) Cos[b c]+d I E^(a c) Sin[b c], ComplexExpand[d*E^((a+I*b)*c)]],
        ESameTest[(1/2 + I/2)/Sqrt[2], ComplexExpand[1/2 E^(\[ImaginaryJ]*\[Pi]/4)]],
    ], EKnownFailures[
        ESameTest[-2^(1/3)-I 2^(1/3) Sqrt[3], ComplexExpand[(-2)^(4/3)]],
    ]
};

Exp::usage = "`Exp[x]` returns the exponential of `x`.";
Attributes[Exp] = {Listable, NumericFunction, Protected, ReadProtected};
Exp[x_] := E^x;
Tests`Exp = {
    ESimpleExamples[
        ESameTest[Simplify[Exp[x] * Exp[y] == Exp[x + y]], True],
    ]
};