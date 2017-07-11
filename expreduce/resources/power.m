possibleExponents[n_Integer, m_Integer] := 
 Flatten[Permutations /@ ((PadRight[#, m]) & /@ 
     IntegerPartitions[n, m]), 1];
genVars[addends_List, exponents_List] := 
 Product[addends[[ExpandUnique`i]]^
   exponents[[ExpandUnique`i]], {ExpandUnique`i, 1, Length[addends]}];
genExpand[addends_List, exponents_List] := 
 Sum[(Multinomial @@ exponents[[ExpandUnique`i]])*
   genVars[addends, exponents[[ExpandUnique`i]]], {ExpandUnique`i, 1, 
   Length[exponents]}];
Expand::usage = "`Expand[expr]` attempts to expand `expr`.";
Expand[a_] := a //. {
    s_Plus^n_Integer?Positive :> 
     genExpand[List @@ s, possibleExponents[n, Length[s]]],
    c_*s_Plus :> ((c*#) &) /@ s
    };
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
    ], EKnownDangerous[
        (*The following tests should not take 10 seconds*)
        ESameTest[Null, ((60 * c * a^2 * b^2) + (30 * c * a^2 * b^2) + (30 * c * a^2 * b^2) + a^5 + b^5 + c^5 + (5 * a * b^4) + (5 * a * c^4) + (5 * b * a^4) + (5 * b * c^4) + (5 * c * a^4) + (5 * c * b^4) + (10 * a^2 * b^3) + (10 * a^2 * c^3) + (10 * a^3 * b^2) + (10 * a^3 * c^2) + (10 * b^2 * c^3) + (10 * b^3 * c^2) + (20 * a * b * c^3) + (20 * a * c * b^3) + (20 * b * c * a^3));]
    ]
};

PolynomialQ::usage =  "`PolynomialQ[e, var]` returns True if `e` is a polynomial in `var`.";
PolynomialQ[p_Plus, v_] :=
  AllTrue[List @@ p, (PolynomialQ[#, v]) &];
PolynomialQ[p_.*v_^Optional[exp_Integer], v_] :=
  If[FreeQ[p, v] && Positive[exp], True, False];
PolynomialQ[p_, v_] := If[FreeQ[p, v], True, False];
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
        ESameTest[True, PolynomialQ[x^y, 1]]
    ], EKnownFailures[
        ESameTest[True, PolynomialQ[2*x^2-3x+2, 2]],
        ESameTest[True, PolynomialQ[2*x^2-3x, 2]]
    ]
};

Exponent::usage = "`Exponent[p, var]` returns the degree of `p` with respect to the variable `var`.";
Exponent[expr_/p_Plus, var_, head_] := Exponent[expr, var, head];
Exponent[expr_, var_, head_] :=
  Module[{e = expr, v = var, h = head, theCases, toCheck},
   toCheck = expr // Expand;
   toCheck = If[Head[toCheck] === Plus, toCheck, {toCheck}];
   theCases =
    Cases[toCheck, p_.*v^Optional[exp_] -> exp] // DeleteDuplicates;
   If[Length[theCases] =!= Length[toCheck], PrependTo[theCases, 0]];
   h @@ theCases
   ];
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
        ESameTest[{0,1}, Exponent[1 + x + x^2 - (x*(1 + 2*x))/2, x, List]]
    ], EKnownFailures[
        ESameTest[{0,1}, Exponent[1 + x^x^x, x^x^x, List]]
    ]
};

ExpreduceSingleCoefficient[inP_, inTerm_] :=
  Module[{p = inP, term = inTerm, pat},
   (*If[MatchQ[p,term],Return[1]];*)
   pat = If[term === 1, a_?NumberQ, Optional[a_]*term];
   (*pat=Optional[a_]*term;*)
   If[MatchQ[p, pat],
    (p) /. pat -> a, 0]
   ];
Coefficient::usage =  "`Coefficient[p, form]` returns the coefficient of form `form` in polynomial `p`.";
Coefficient[p_, var_, exp_] := Coefficient[p, var^exp];
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
        ESameTest[1/2, Coefficient[1 + x + x^2 - (x*(1 + 2*x))/2, x]]
    ]
};

PolynomialQuotientRemainder::usage =  "`PolynomialQuotientRemainder[poly_, div_, var_]` returns the quotient and remainder of `poly` divided by `div` treating `var` as the polynomial variable.";
ExpreduceLeadingCoeff[p_, x_] := Coefficient[p, x^Exponent[p, x]];
PolynomialQuotientRemainder[inp_, inq_, v_] :=
  Module[{a = inp, b = inq, x = v, r, d, c, i, s, q},
   q = 0;
   r = a;
   d = Exponent[b, x];
   c = ExpreduceLeadingCoeff[b, x];
   i = 1;
   While[Exponent[r, x] >= d && i < 20,
    s = (ExpreduceLeadingCoeff[r, x]/c)*x^(Exponent[r, x] - d);
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

Varibles::usage = "`Variables[expr]` returns the variables in `expr`.";
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
        ESameTest[{a^"Hello"^2}, Variables[a^"Hello"^2]]
    ], EKnownFailures[
        (*I think these have to do with NumericQ.*)
        ESameTest[{a, Log[b]}, Variables[Sqrt[a] + Log[b]]],
        ESameTest[{a}, Variables[Sqrt[a]]],
        ESameTest[{(a*b)^c, (a*b)^d}, Variables[(a*b)^(c + d)]],
        ESameTest[{}, Variables[Pi^y]]
    ]
};

PolynomialGCD::usage = "`PolynomialGCD[a, b]` calculates the polynomial GCD of `a` and `b`.";
PolySubresultantGCD[inA_, inB_, inX_] := 
  Module[{u = inA, v = inB, x = inX, h, delta, beta, newU, newV, i},
   h = 1;
   i = 1;
   While[v =!= 0 && i < 20,
    delta = Exponent[u, x] - Exponent[v, x];
    beta = (-1)^(delta + 1)*Exponent[u, x]*h^delta;
    h = h*(Exponent[v, x]/h)^delta;
    newU = v;
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
