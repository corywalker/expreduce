D::usage = "`D[f, x]` finds the partial derivative of `f` with respect to `x`.";
D[x_,x_] := 1;
D[a_,x_] := 0 /; FreeQ[a,x];
D[a_+b_,x_] := D[a,x]+D[b,x];
D[a_ b_,x_] := D[a,x]*b + a*D[b,x];
(*Chain rule*)
(*Prime notation would be nicer here*)
D[f_[g_[x_Symbol]], x_Symbol] := (Evaluate[D[f[#], #]] &)[g[x]]*D[g[x],x];
(*The times operator is needed here. Whitespace precedence is messed up*)
D[a_^(b_), x_] := a^b*(D[b,x] Log[a]+D[a,x]/a*b);
D[Log[a_], x_] := D[a, x]/a;
D[Sin[a_], x_] := D[a,x] Cos[a];
D[Cos[a_], x_] := -D[a,x] Sin[a];
Attributes[D] = {ReadProtected, Protected};
Tests`D = {
    ESimpleExamples[
        ESameTest[Sqrt[x] + x^(3/2), D[2/3*x^(3/2) + 2/5*x^(5/2), x]],
        ESameTest[2/x, D[Log[5 x^2], x]],
        ESameTest[-(Sin[Log[x]]/x), D[Cos[Log[x]], x]]
    ], ETests[
        ESameTest[1, D[x,x]],
        ESameTest[1, D[foo,foo]],
        ESameTest[0, D[foo,bar]],
        ESameTest[2, D[bar+foo+bar,bar]],
        ESameTest[2x, D[x^2,x]],
        ESameTest[2x+3x^2, D[x^2+x^3,x]],
        ESameTest[-4x^3, D[-x^4,x]],
        ESameTest[-n x^(-1 - n) + n x^(-1 + n), D[x^n+x^(-n),x]],
        ESameTest[4 x (1 + x^2), D[(x^2 + 1)^2, x]],
        ESameTest[((1 + x + (1/6 * x^3) + (1/2 * x^2))), D[1 + x + 1/2*x^2 + 1/6*x^3 + 1/24*x^4, x]],
        ESameTest[-10*Power[x,-3] - 7*Power[x,-2], D[1 + 7/x + 5/(x^2), x]],
        ESameTest[-2 Sin[2 x], D[Cos[2 x], x]],
        ESameTest[Cos[x]/x - Sin[x]*Power[x,-2], D[(Sin[x]*x^-1), x]],
        ESameTest[-((2 Cos[x])*Power[x,-2]) + (2 Sin[x])*Power[x,-3] - Sin[x]/x, D[D[(Sin[x]*x^-1), x], x]],
        ESameTest[-((2 Cos[x])*Power[x,-2]) + (2 Sin[x])*Power[x,-3] - Sin[x]/x, D[D[(Sin[x]*x^-1+Sin[y]), x], x]],
        ESameTest[-Cos[Cos[x]] Sin[x], D[Sin[Cos[x]],x]],
        ESameTest[Cos[Log[x]]/x, D[Sin[Log[x]],x]],
        ESameTest[-(Sin[Log[x]]/x), D[Cos[Log[x]],x]],
        ESameTest[1-(1+Cot[x]) Sin[x+Log[Sin[x]]], D[Cos[Log[Sin[x]]+x]+x,x]]
    ]
};

Integrate::usage = "`Integrate[f, x]` finds the indefinite integral of `f` with respect to `x`.

!!! warning \"Under development\"
    This function is under development, and as such will be incomplete and inaccurate.";
Integrate[a_,{x_Symbol,start_,end_}] := 
    ReplaceAll[Integrate[a, x],x->end] - ReplaceAll[Integrate[a, x],x->start];
Integrate[a_Integer,x_Symbol] := a*x;
Integrate[a_*b_,x_Symbol] := a*Integrate[b,x] /; FreeQ[a,x];
Integrate[a_+b_,x_Symbol] := Integrate[a,x]+Integrate[b,x];

(*Basic power integrals*)
Integrate[a_Symbol,x_Symbol] := If[a===x, x^2/2, a*x];
Integrate[x_Symbol^e_, x_Symbol] := x^(e+1)/(e+1) /; FreeQ[e, x];
Integrate[a_^(b_*x_Symbol),x_Symbol] := a^(b x)/(b Log[a]) /; (FreeQ[a, x] && FreeQ[b, x]);
Integrate[1/x_Symbol,x_Symbol] := Log[Abs[x]];
Integrate[Log[x_Symbol],x_Symbol] := -x + x Log[x];
Integrate[x_Symbol*Log[x_Symbol],x_Symbol] := -((x^2)/4) + (1/2)*(x^2)*Log[x];

(*Trig functions*)
Integrate[Sin[x_Symbol],x_Symbol] := -Cos[x];
Integrate[Cos[x_Symbol],x_Symbol] := Sin[x];
Integrate[Tan[x_Symbol],x_Symbol] := -Log[Cos[x]];
Integrate[Sec[x_Symbol]^2,x_Symbol] := Tan[x];
Integrate[Csc[x_Symbol]^2,x_Symbol] := -Cot[x];
Integrate[Sec[x_Symbol]Tan[x_Symbol],x_Symbol] := Sec[x];
Integrate[Csc[x_Symbol]Cot[x_Symbol],x_Symbol] := -Csc[x];
Integrate[Sqrt[1-x_Symbol^2]^(-1),x_Symbol] := ArcSin[x];
Integrate[(1+x_Symbol^2)^(-1),x_Symbol] := ArcTan[x];

(*This may not always reduce. Look into this*)
(*Integrate[u_Symbol*v_, u_Symbol] := u*Integrate[v, u] - Integrate[Integrate[v, u], u];*)

Attributes[Integrate] = {ReadProtected, Protected};
Tests`Integrate = {
    ESimpleExamples[
        ESameTest[2 x + (3 x^(5/3))/5 + (3 x^2)/2, Integrate[x^(2/3) + 3 x + 2, x]],
        ESameTest[-((3 x^2)/4) + (1/2) (x^2) Log[x] - Sin[x], Integrate[Integrate[Sin[x] + Log[x], x], x]],
        ESameTest[1/3, Integrate[x^2, {x, 0, 1}]],
        ESameTest[True, (Integrate[x^2, {x, 0.5, 1.}] - 0.29166667) < .00001],
        (*ESameTest[-(E^(3 x)/9)+1/3 E^(3 x) x, Integrate[E^(3*x)*x, x]//Expand],*)
        ESameTest[E^(3*x)/3, Integrate[E^(3*x), x]],
        ESameTest[x^(1 + a + b)/(1 + a + b), Integrate[x^(a + b), x]],
        ESameTest[n^3/3, Integrate[x^2, {x, 0, n}]],
        ESameTest[x^3/3, Integrate[x^2, {x, 0, x}]]
    ], ETests[
        (*Test some trig definitions*)
        ESameTest[Tan[x], Integrate[Sec[x]^2,x]],
        ESameTest[-Cot[x], Integrate[Csc[x]^2,x]],
        ESameTest[Sec[x], Integrate[Sec[x]Tan[x],x]],
        ESameTest[-Csc[x], Integrate[Csc[x]Cot[x],x]],
        ESameTest[ArcSin[x], Integrate[1/Sqrt[1-x^2],x]],
        ESameTest[ArcTan[x], Integrate[1/(1+x^2),x]]
    ], EKnownFailures[
        ESameTest[Log[x] - 1/2 Log[1 + 2 x^2], Integrate[1/(2 x^3 + x), x]]
    ]
};
