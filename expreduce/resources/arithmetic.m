Plus::usage = "`(e1 + e2 + ...)` computes the sum of all expressions in the function.";
(*{"Verbatim[Plus][beg___, Optional[c1_?NumberQ]*a_, Optional[c2_?NumberQ]*a_, end___]", "beg+(c1+c2)*a+end"},*)
 (*The world is not ready for this madness.*)
(*{"Verbatim[Plus][beg___, Verbatim[Times][Optional[c1_?NumberQ],a__], Verbatim[Times][Optional[c2_?NumberQ],a__], end___]", "beg+(c1+c2)*a+end"},*)
Attributes[Plus] = {Flat, Listable, NumericFunction, OneIdentity, Orderless, Protected};
Tests`Plus = {
    ESimpleExamples[
        ESameTest[2, 1 + 1],
        EComment["If Reals are present, other Integers are demoted to Reals:"],
        ESameTest[0., (5.2 - .2) - 5],
        EComment["Plus automatically combines like terms:"],
        ESameTest[a+6*b^2, a + b^2 + 5*b^2],
        ESameTest[((5 * c^a) + (3 * d)), (a+b)-(a+b)+c-c+2*c^a+2*d+5*d+d-5*d+3*c^a],
        ESameTest[-3 a b c d e f, 4*a*b*c*d*e*f + -7*a*b*c*d*e*f]
    ], ETests[
        (*Test automatic expansion*)
        EStringTest["(a + b)", "1*(a + b)"],
        EStringTest["(1.*(a + b))", "1.*(a + b)"],
        EStringTest["(2.*(a + b))", "2.*(a + b)"],
        EStringTest["(a + b)", "(a + b)/1"],
        EStringTest["(1.*(a + b))", "(a + b)/1."],
        EStringTest["(2*(a + b))", "2*(a + b)"],
        EStringTest["(a*(b + c))", "a*(b + c)"],
        EStringTest["(-a - b)", "-1*(a + b)"],
        EStringTest["(-a - b)", "-(a + b)"],
        EStringTest["((-1.)*(a + b))", "-1.*(a + b)"],
        EStringTest["(-a - b)", "(a + b)/-1"],
        EStringTest["((-1.)*(a + b))", "(a + b)/-1."],

        (*Test that we do not delete all the addends*)
        ESameTest[0., (5.2 - .2) - 5],
        ESameTest[0, 0 + 0],

        (*Test empty Plus expressions*)
        ESameTest[0, Plus[]],

        (*Test proper accumulation of Rationals*)
        EStringTest["(47/6 + sym)", "Rational[5, 2] + Rational[7, 3] + 3 + sym"],
        EStringTest["(17/6 + sym)", "Rational[5, -2] + Rational[7, 3] + 3 + sym"],
        EStringTest["(-19/6 + sym)", "Rational[5, -2] + Rational[7, 3] - 3 + sym"],
        EStringTest["(-47/6 + sym)", "Rational[5, -2] + Rational[-7, 3] - 3 + sym"],

        (*Test combining monomials of degree 1*)
        ESameTest[a+7*b, a + 2*b + 5*b],

        (*Test a more general version*)
        ESameTest[a+7*b, a + 2*b + 5*b],
        ESameTest[a+7*b^2, a + 2*b^2 + 5*b^2],
        ESameTest[a+3*b^2, a - 2*b^2 + 5*b^2],

        (*Test using terms without a coefficient*)
        ESameTest[a+6*b^2, a + b^2 + 5*b^2],

        (*Test additive identity*)
        ESameTest[a, a+0],
        ESameTest[a+b, (a+b)+0],

        (*Test additive inverse*)
        ESameTest[0, a-a],
        ESameTest[0, -a + a],
        ESameTest[0, (a+b)-(a+b)],
        ESameTest[0, -(a+b)+(a+b)],
        ESameTest[0, (a+b)-(a+b)],
        ESameTest[0, -(a+b)+(a+b)],

        (*Test basic simplifications*)
        ESameTest[d, (a+b)-(a+b)+c-c+d],
        ESameTest[((5 * c^a) + (3 * d)), (a+b)-(a+b)+c-c+2*c^a+2*d+5*d+d-5*d+3*c^a],
        ESameTest[87.5 + 3 * x, ((x + 80. + 3. + x) + 2. + x + 2.5)],
        ESameTest[87.5 + (7. * x), ((x + 80. + 3. + x) + 2. + (x * 2. * 2.) + (0. * 3. * x) + x + 2.5)],
        ESameTest[50*a, a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a],

        (*More complicated term combining*)
        ESameTest[-3 * m - 10 * n, -9 * n - n - 3 * m],
        ESameTest[7*a * b - 2*a * c, 3*a*b - 2*a*c + 4*a*b],
        ESameTest[-3*a - 2*b + 3*a*b, 2*a - 4*b + 3*a*b - 5*a + 2*b],
        ESameTest[7*x - 11*y + x*y, 8*x - 9*y - 3*x*y - 2*y - x + 4*x*y],
        ESameTest[-3*a*b*c*d*e*f, 4*a*b*c*d*e*f + -7*a*b*c*d*e*f],
        ESameTest[-3*a*b*c*d*e*f, a*b*c*4*d*e*f + -a*b*c*d*e*f*7],
        ESameTest[-3*a*b*c*d*e*f, a*b*2*c*2*d*e*f + -a*b*c*d*e*f*7],
        ESameTest[2 r + 2 t, 2 r - 3 s - t + 3 t + 3 s],
        ESameTest[3 (x - 2 y) - 4 x y + 2 (-1 + x y), 2 (x*y - 1) + 3 (x - 2 y) - 4 x*y],
        ESameTest[-4 s + 4 r s - 3 (1 + r s), 4 r*s - 2 s - 3 (r*s + 1) - 2 s],
        ESameTest[7 y - z + 3 y z, 8 y - 2 z - (y - z) + 3 y*z]
    ]
};

Sum::usage = "`Sum[expr, n]` returns the sum of `n` copies of `expr`.

`Sum[expr, {sym, n}]` returns the sum of `expr` evaluated with `sym` = 1 to `n`.

`Sum[expr, {sym, m, n}]` returns the sum of `expr` evaluated with `sym` = `m` to `n`.";
Attributes[Sum] = {HoldAll, ReadProtected, Protected};
Sum[i_Symbol, {i_Symbol, 0, n_Integer}] := 1/2*n*(1 + n);
Sum[i_Symbol, {i_Symbol, 1, n_Integer}] := 1/2*n*(1 + n);
Sum[i_Symbol, {i_Symbol, end_}]         := 1/2*end*(1 + end);
Sum[i_Symbol, {i_Symbol, 0, n_Symbol}]  := 1/2*n*(1 + n);
Sum[i_Symbol, {i_Symbol, 1, n_Symbol}]  := 1/2*n*(1 + n);
(* Infinite series *)
Sum[i_Symbol^(-2), {i_Symbol, 1, Infinity}] := Pi^2/6;
Sum[num_/(i_Symbol^2), {i_Symbol, 1, Infinity}] := num * Pi^2/6;
Tests`Sum = {
    ESimpleExamples[
        ESameTest[45, Sum[i, {i, 5, 10}]],
        ESameTest[55, Sum[i, {i, 1, 10}]],
        ESameTest[55, Sum[i, {i, 0, 10}]],
        ESameTest[450015000, Sum[i, {i, 1, 30000}]],
        ESameTest[450015000, Sum[i, {i, 0, 30000}]],
        ESameTest[1/2*n*(1 + n), Sum[i, {i, 0, n}]],
        ESameTest[1/2*n*(1 + n), Sum[i, {i, 1, n}]],
        ESameTest[30, Sum[a + b, {a, 0, 2}, {b, 0, 3}]],
        ESameTest[b+c+d+e, Sum[a, {a, {b, c, d, e}}]],
        ESameTest[b g + c g + d g + e g + b h + c h + d h + e h, Sum[a*f, {a, {b, c, d, e}}, {f, {g, h}}]],
        ESameTest[25 n (1 + 50 n), Sum[i, {i, n*50}]],
    ], ETests[
        ESameTest[Sum[1/(n^2), {n, 1, Infinity}], Pi^2/6],
        ESameTest[Sum[n^-2, {n, 1, Infinity}], Pi^2/6],
        ESameTest[Sum[6/(n^2), {n, 1, Infinity}], Pi^2],
    ]
};

Times::usage = "`(e1 * e2 * ...)` computes the product of all expressions in the function.";
(* This is likely the most compute-intensive rule in the system. Modify with
care. *)
Verbatim[Times][beg___, a_^Optional[m_], a_^Optional[n_], end___] := beg*a^(m+n)*end /; (!NumberQ[a] || !NumberQ[m] || !NumberQ[n]);
(*Verbatim[Times][a_Integer, mid___, b_Integer^n_, end___] := mid*-(b^(n+1))*end /; (a == -b);*)
a_Integer^c_Rational*b_Integer^c_Rational*rest___ := (a*b)^c*rest;
(*Verbatim[Times][beg___, a_^Optional[m_], a_^Optional[n_], end___] := beg*a^(m+n)*end;*)
(* This qualifier is so that the simplification for 3^(4/3) -> 3*3^(1/3) does not produce an infinite evaluation loop *)
wouldntBeLessThanNegOne[x_] := ((x - 1) < -1) =!= True;
Verbatim[Times][Rational[1, a_Integer], inner___, a_Integer^n_?wouldntBeLessThanNegOne, end___] := inner*a^(n-1)*end;
Times[den_Integer^-1, num_Integer, rest___] := Rational[num,den] * rest;
Times[ComplexInfinity, rest___] := ComplexInfinity;
a_Integer?Negative^b_Rational*c_Integer^d_Rational*rest___ := (-1)^b*rest /; (a == -c && b == -d);
Verbatim[Times][beg___, a_Integer^m_Rational, a_Integer^n_Rational, end___] := beg*a^(m+n)*end;
Times[c : (Rational[_Integer, d_Integer] |
     Complex[_Integer, Rational[_Integer, d_Integer]]),
  Power[a_Integer, Rational[1, r_Integer]], rest___] :=
 Times[c*a, a^(1/r - 1), rest] /; (Mod[d, a] === 0 && a > 1)
Sin[x_]*Cos[x_]^(-1)*rest___ := Tan[x]*rest;
Cos[x_]*Sin[x_]^(-1)*rest___ := Cot[x]*rest;
Attributes[Times] = {Flat, Listable, NumericFunction, OneIdentity, Orderless, Protected};
Tests`Times = {
    ESimpleExamples[
        EComment["Simplification rules apply automatically:"],
        ESameTest[3/2, (3 + (x^2 * 0)) * 2^-1],
        ESameTest[a^(2+c), a^2*a^c],
        ESameTest[a/(b*c*d), a/b/c/d]
    ], EFurtherExamples[
        EComment["Rational numbers are suppported (explicit rational declaration added for clarity):"],
        ESameTest[-2/3, Rational[1, -2]*Rational[-2, 3]*-2],
        EComment["The product of nothing is defined to be one:"],
        ESameTest[1, Times[]]
    ], ETests[
        (*Test that we do not delete all the multiplicands*)
        ESameTest[1, 1*1],
        ESameTest[1, 5*1/5*1],

        (*Test empty Times expressions*)
        ESameTest[1, Times[]],

        (*Test fraction simplification*)
        ESameTest[25, 50/2],
        ESameTest[50, 100/2],
        ESameTest[50, 1/2*100],
        ESameTest[5/4, 1/2*5/2],
        ESameTest[1/4, 1/2*1/2],
        ESameTest[a/(b*c*d), a/b/c/d],

        (*Test Rational detection*)
        EStringTest["10", "40/2^2"],
        EStringTest["10", "40/4"],
        ESameTest[40/3, 40/3],
        ESameTest[20/3, 40/6],
        EStringTest["10", "1/4*40"],
        EStringTest["10", "1/(2^2)*40"],

        (*Test proper accumulation of Rationals*)
        EStringTest["(2*sym)", "sym*Rational[1,2]*Rational[2,3]*6"],
        ESameTest[-2/3, Rational[1, -2]*Rational[-2, 3]*-2],
        EStringTest["Rational", "Rational[1, -2]*Rational[-2, 3]*-2 // Head"],

        (*Test multiplicative identity*)
        EStringTest["5", "5*1"],
        EStringTest["a", "1*a"],
        EStringTest["(1.*a)", "1.*a"],

        (*Test multiplicative inverse*)
        EStringTest["1", "8*1/8"],
        EStringTest["1", "a*1/a"],
        EStringTest["1", "1/a*a"],

        (*Test multiplicative property of zero*)
        ESameTest[3/2, (3 + (x^2 * 0)) * 2^-1],

        (*Simplifications with Power*)
        ESameTest[a^(2+c), a^2*a^c],
        ESameTest[a^(2-c), a^2/a^c],
        ESameTest[m^2, m*m],
        ESameTest[1, m/m],
        ESameTest[1, m^2/m^2],
        ESameTest[Times[Power[2,Rational[-1,2]],a], (1/2)*a*2^(1/2)],

        (*Conversion of exact numeric functions to reals*)
        ESameTest[True, MatchQ[Sqrt[2*Pi]*.1, _Real]],

        ESameTest[(-1)^(1/3) a b c, (-2)^(1/3)*2^(-1/3)*a*b*c],
        ESameTest[1/12, (1/12)*2^(-2/3)*2^(2/3)],
        ESameTest[I/(4 Sqrt[3]), (0+I/12) Sqrt[3]],
        (* 1/12*Sqrt[3]===1/12*3^(1/2)===12^-1*3^(1/2)===(2*2*3)^-1*3^(1/2)===(2*2)^-1*3^-1*3^(1/2)===(2*2)^-1*3^(1/2-1)===1/4*3^(-1/2)===1/(4 Sqrt[3]) *)
        ESameTest[1/(4 Sqrt[3]), 1/12*Sqrt[3]],
        ESameTest[-(I/(4 Sqrt[3])), (0-I/4) 1/Sqrt[3]],
        ESameTest[-(1/(4 Sqrt[3])), Times[-1/12,Sqrt[3]]],
        ESameTest[-(5/(4 Sqrt[3])), Times[-5/12,Sqrt[3]]],
        ESameTest[(3+I/4)/Sqrt[3], Times[1+1/12 I,Sqrt[3]]],
        ESameTest[(I Sqrt[3])/4, Times[3/12 I,Sqrt[3]]],
        ESameTest[-(I/(2 Sqrt[3])), Times[-2/12 I,Sqrt[3]]],
        ESameTest[-(I/(2 Sqrt[3])), Times[2/-12 I,Sqrt[3]]],
        ESameTest[(3+(5 I)/4)/Sqrt[3], Times[1+5/12 I,Sqrt[3]]],
        ESameTest[I/(2 Sqrt[3] a^2), (0+1/6*I)*3^(1/2)*a^(-2)],
        (* Test wouldntBeLessThanNegOne. *)
        ESameTest[(1/3)*3^(-1/2), (1/3)*3^(-1/2)],

        ESameTest[Sqrt[2/\[Pi]], Sqrt[2]*Sqrt[1/Pi]],
        ESameTest[Sqrt[3/(2 \[Pi])], Sqrt[3/2]*Sqrt[1/Pi]],
    ], EKnownFailures[
        ESameTest[-2^(1/3), (-2)*2^(-2/3)],
        ESameTest[-2^(1+a), (-2)*2^(a)],
    ]
};

Product::usage = "`Product[expr, n]` returns the product of `n` copies of `expr`.

`Product[expr, {sym, n}]` returns the product of `expr` evaluated with `sym` = 1 to `n`.

`Product[expr, {sym, m, n}]` returns the product of `expr` evaluated with `sym` = `m` to `n`.";
Attributes[Product] = {HoldAll, ReadProtected, Protected};
Tests`Product = {
    ESimpleExamples[
        ESameTest[120, Product[a, {a, 1, 5}]],
        ESameTest[f[1] * f[2] * f[3] * f[4] * f[5], Product[f[a], {a, 1, 5}]],
        ESameTest[576, Product[a^2, {a, 4}]],
        ESameTest[1440, Product[a + b, {a, 1, 2}, {b, 1, 3}]]
    ]
};

Abs::usage = "`Abs[expr]` calculates the absolute value of `expr`.";
Abs[a_?NumberQ] := If[a<0,-a,a];
Abs[Infinity] := Infinity;
Abs[ComplexInfinity] := Infinity;
Abs[-a_] := Abs[a];
Abs[a_?((!FreeQ[#,I|_Complex])&)] := Sqrt[Total[ReIm[a]^2]] ;/ (FreeQ[ReIm[a], Re] && FreeQ[ReIm[a], Im]);
Attributes[Abs] = {Listable, NumericFunction, Protected, ReadProtected};
Tests`Abs = {
    ESimpleExamples[
        ESameTest[5, Abs[-5]],
        ESameTest[5, Abs[5]],
        EComment["Absolute values of unspecified inputs will be left unevaluated:"],
        ESameTest[Abs[a], Abs[a]],
        EComment["But sometimes simplifications can occur:"],
        ESameTest[Abs[Sin[x]], Abs[-Sin[x]]]
    ], ETests[
        ESameTest[True, Abs[-5.2] > 0],
        ESameTest[0, Abs[0]],
        ESameTest[Abs[x^a], Abs[-x^a]],
        ESameTest[Abs[x^(a + b)], Abs[-x^(a + b)]],
        ESameTest[1/2, Abs[1/2 E^(\[ImaginaryJ]*\[Pi]/4)]],
    ]
};

Divide::usage = "`Divide[a, b]` computes `a/b`.";
Divide[a_,b_] := a/b;
Attributes[Divide] = {Listable, NumericFunction, Protected};
Tests`Divide = {
    ESimpleExamples[
        ESameTest[2, Divide[10, 5]]
    ]
};

Increment::usage = "`Increment[a]` adds 1 to `a` and returns the original value.";
Increment[a_] := (a = a + 1; a - 1);
Attributes[Increment] = {HoldFirst, Protected, ReadProtected};
Tests`Increment = {
    ESimpleExamples[
        ESameTest[3, toModify = 3],
        ESameTest[3, toModify++],
        ESameTest[4, toModify]
    ]
};

Decrement::usage = "`Decrement[a]` subtracts 1 from `a` and returns the original value.";
Decrement[a_] := (a = a - 1; a + 1);
Attributes[Decrement] = {HoldFirst, Protected, ReadProtected};
Tests`Decrement = {
    ESimpleExamples[
        ESameTest[3, toModify = 3],
        ESameTest[3, toModify--],
        ESameTest[2, toModify]
    ]
};

PreIncrement::usage = "`PreIncrement[a]` adds 1 to `a` and returns the new value.";
PreIncrement[a_] := (a = a + 1);
Attributes[PreIncrement] = {HoldFirst, Protected, ReadProtected};
Tests`PreIncrement = {
    ESimpleExamples[
        ESameTest[3, toModify = 3],
        ESameTest[4, ++toModify],
        ESameTest[4, toModify]
    ]
};

PreDecrement::usage = "`PreDecrement[a]` subtracts 1 from `a` and returns the new value.";
PreDecrement[a_] := (a = a - 1);
Attributes[PreDecrement] = {HoldFirst, Protected, ReadProtected};
Tests`PreDecrement = {
    ESimpleExamples[
        ESameTest[3, toModify = 3],
        ESameTest[2, --toModify],
        ESameTest[2, toModify]
    ]
};

AddTo::usage = "`AddTo[a, b]` adds `b` to `a` and returns the new value.";
AddTo[a_, b_] := (a = a + b);
Attributes[AddTo] = {HoldFirst, Protected};
Tests`AddTo = {
    ESimpleExamples[
        ESameTest[3, toModify = 3],
        ESameTest[5, toModify += 2],
        ESameTest[5, toModify]
    ]
};

SubtractFrom::usage = "`SubtractFrom[a, b]` subtracts `b` from `a` and returns the new value.";
SubtractFrom[a_, b_] := (a = a - b);
Attributes[SubtractFrom] = {HoldFirst, Protected};
Tests`SubtractFrom = {
    ESimpleExamples[
        ESameTest[3, toModify = 3],
        ESameTest[1, toModify -= 2],
        ESameTest[1, toModify]
    ]
};
