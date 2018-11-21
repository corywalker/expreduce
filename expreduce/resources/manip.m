ExpreduceDistributeMultiply[e_, multiplicand_] :=
  If[Head[e] === Plus, (#*multiplicand) & /@ e, e*multiplicand];

Together::usage = "`Together[e]` attempts to put the terms in `e` under the same denominator.";

(*Factor out some operations*)
ExpreduceTogether[a_Plus*b_] := ExpreduceTogether[a]*b;
ExpreduceTogether[e_^p_?NumberQ] := ExpreduceTogether[e]^p;

(*Process any denominator*)
ExpreduceTogether[c_.*1/d_ + rest_] := ExpreduceTogether[(c+Expand[ExpreduceDistributeMultiply[rest, d]])/d];
(*Rationals have denominators too. Rational denominators are integers, and
thus automatically distributed through Plus, so no need for the distribute
function.*)
ExpreduceTogether[c_.*Rational[n_,d_] + rest_] := ExpreduceTogether[(c n+Expand[rest d])/d];
ExpreduceTogether[c_.*Complex[0, Rational[n_,d_]] + rest_] := ExpreduceTogether[(I c n+Expand[rest d])/d];

ExpreduceTogether[e_] := e;
Together[e_] := ExpreduceFactorConstant[ExpreduceTogether[e]];

Attributes[Together] = {Listable, Protected};
Tests`Together = {
    ESimpleExamples[
        ESameTest[(6+a)/(2 a), 1/2+3/a//Together],
        ESameTest[(1/2+3/a)^c, (1/2+3/a)^c//Together],
        ESameTest[(6+a)^2/(4 a^2), (1/2+3/a)^2//Together]
    ], ETests[
        ESameTest[(c+a d+b d)/d, a+b+c/d//Together],
        ESameTest[(a+b+c+d)/((a+b) (c+d)), 1/(a+b)+1/(c+d)//Together],
        ESameTest[(a+b+c-a^2*c-a b c+d-a^2*d-a b d)/((a+b) (c+d)), 1/(a+b)+1/(c+d)-a//Together],
        (*Only for when we have Cancel:*)
        (*ESameTest[-(a/(2+a)), Together[a/(-2+a+a^2)-a^2/(-2+a+a^2)]],*)
        ESameTest[(a+b c)/b, a/b+c//Together],
        ESameTest[(b c+a d)/(b d), (a+(b c)/d)/b//Together],
        ESameTest[(b c+a d)/d, a+(b c)/d//Together],
        ESameTest[(c+a d+b d)/d, Together[(c + a*d + b*d)/d]],
        ESameTest[(6+a+2 b)/(2 a), (3+a/2+b)/a//Together],
        ESameTest[a/(b e), (a/b)/e//Together],
        ESameTest[(12+a)/(4 a), (3 + a*1/4)/a//Together],
        ESameTest[(1/2) (6+foo[a]), 3 + foo[a]*2/4//Together],
        ESameTest[(6+a)/(2 a), 1/2 + 3/a//Together],
        ESameTest[(a+b c)/(a b), (c+ a/b)/a//Together],
        ESameTest[(a+b c+b e)/(b d), (c+e+ a/b)/d//Together],
        ESameTest[(4 a^2*b+36 c+12 a c+a^2*c)/(4 a^2*c), Together[(1/2 + 3/a)^2+b/c]],
        ESameTest[(6+a)/(2 a), (3 + a/2)/a//Together],
        ESameTest[(a b+c rest)/(c d), (rest + a*b/c)/d//Together],
        ESameTest[(1+a c+b c)/(a+b), 1/(a+b)+c//Together],
        ESameTest[(c+a d+b d)/d, Together[(c + a*d + b*d)/d]],
        ESameTest[(6+a+2 b)/(2 a), (3+a/2+b)/a//Together],
        ESameTest[a/(b e), (a/b)/e//Together],
        ESameTest[(a+a^2*c+a b c+a d+b d)/(a (a+b)), Together[1/(a + b) + c+d/a]],
        ESameTest[(a+b) (c+d), (a+b)(c+d)//Together],
        ESameTest[(a+b+c+d)/((a+b) (c+d)), 1/(a + b)+1/(c+d)//Together],
        ESameTest[1/(a+b), 1/(a + b)//Together],
        ESameTest[(a+b c e f)/(b c), a/(b*c)+(e*f)//Together],
        ESameTest[(a+b+c-a^2*c-a b c+d-a^2*d-a b d)/((a+b) (c+d)), Together[1/(a + b) + 1/(c + d) - a]],
        ESameTest[(a+b)/(a b), 1/a+1/b//Together],
        ESameTest[(a+b+a b c)/(a b), 1/a+1/b+c//Together],
        ESameTest[(1+c d)/c, 1/c+d//Together],
        ESameTest[1/2*(1+2 a), 1/2+a//Together],
        ESameTest[(a+b+c+d)/((a+b) (c+d)), (1+a/(c+d)+b/(c+d))/(a+b)//Together],
        ESameTest[(a+b+a b c+a b d)/(a b), 1/a+1/b+c+d//Together],
        ESameTest[2(a+b), 2a+2b//Together],
    ], EKnownFailures[
        ESameTest[(I (a-b))/(2 Subscript[\[Omega], 0]), (I a)/(2 Subscript[\[Omega], 0])-(I b)/(2 Subscript[\[Omega], 0])//Together],
    ]
};

Numerator::usage = "`Numerator[e]` returns the numerator of `e`.";
denPattern := b_^n_?Negative | b_^(n : (-_Symbol));
Numerator[prod_Times] := Times@@Cases[prod, Except[denPattern]];
Numerator[Rational[n_,d_]] := n;
Numerator[e_] := e;
Attributes[Numerator] = {Listable, Protected};
Tests`Numerator = {
    ESimpleExamples[
        ESameTest[a, Numerator[a/b]],
        ESameTest[a^2 b, Numerator[a^2*b]],
        ESameTest[a^2, Numerator[a^2*b^-2]],
        ESameTest[a^2 c, Numerator[a^2*b^-a*c]],
        ESameTest[2, Numerator[2/3]]
    ]
};

Denominator::usage = "`Denominator[e]` returns the denominator of `e`.";
Denominator[prod_Times] := Times@@Cases[prod, denPattern -> b^(-n)];
Denominator[Rational[n_,d_]] := d;
Denominator[e_] := 1;
Attributes[Denominator] = {Listable, Protected};
Tests`Denominator = {
    ESimpleExamples[
        ESameTest[b c, Denominator[a/(b*c)]],
        ESameTest[1, Denominator[a^2*b]],
        ESameTest[b^2 c^3, Denominator[a^2*b^-2*c^-3]],
        ESameTest[b^a c^d, Denominator[a^2*b^-a*c^-d]],
        ESameTest[3, Denominator[2/3]]
    ]
};

Apart::usage = "`Apart[e]` attempts to break apart the terms in `e`. Warning: not fully implemented.";
termsWithout[dTerms_, i_] :=
  Product[If[index === i, 1, dTerms[[index]]], {index,
    Length[dTerms]}];
getPowerApartForm[base_, exp_, denTerms_] :=
  Module[{b = base, n = exp, holders, form, dTerms = denTerms,
    unDivForm, finalForm},
   holders = Table[Unique[], n//Evaluate];
   finalForm = Sum[(holders[[i]]/b^i), {i, n}];
   form = Sum[(holders[[i]]/b^i)*Times @@ dTerms, {i, n}];
   {finalForm, form, holders}
   ];
getApartForm[denTerms_, iVar_] :=
  Module[{dTerms = denTerms, i = iVar, holder, powerPattern},
   powerPattern := b_^n_Integer;
   If[MatchQ[dTerms[[i]], powerPattern],
    Replace[dTerms[[i]],
     powerPattern :> getPowerApartForm[b, n, dTerms]],
    holder = Unique[];
    {holder/dTerms[[i]],
     holder*If[Length[dTerms] === 1, dTerms[[1]],
       termsWithout[dTerms, i]], {holder}}]
   ];
myLinearApart[num_, denTerms_, var_] :=
  Module[{n = num, dTerms = denTerms, v = var, lhs, rhs, coeffs,
    apartForm, coeffHolders, tmp, toSolve, finalForm},
   coeffHolders = {};
   apartForm = {};
   finalForm = {};
   Do[
    tmp = getApartForm[dTerms, i];
    coeffHolders = Join[coeffHolders, tmp[[3]]];
    AppendTo[apartForm, tmp[[2]]];
    AppendTo[finalForm, tmp[[1]]];
    , {i, Length[dTerms]}];
   apartForm = Plus @@ apartForm;

   lhs = CoefficientList[apartForm, v];
   rhs = PadRight[CoefficientList[n, v], Length[lhs]];
   toSolve = Table[lhs[[i]] == rhs[[i]], {i, Length[lhs]}];
   (*Print[toSolve, coeffHolders];*)
   coeffs = Solve[toSolve, coeffHolders];
   If[Length[coeffs] === 0 || Head[coeffs] === Solve,
    num/(Times @@ denTerms),
    Plus @@ (finalForm /. coeffs[[1]])
    ]
   ];
ClearAll[denTerms];
getDenTerms[den_Times] := List @@ den;
getDenTerms[den_] := {den};
validDenTermQ[t_, x_] :=
  MatchQ[t, (Optional[a_?((FreeQ[#, x]) &)]*
      x^Optional[n_Integer]) | (Optional[a_?((FreeQ[#, x]) &)]*x +
       Optional[b_?((FreeQ[#, x]) &)])^Optional[n_?((FreeQ[#, x]) &)]];
myApartUnexpanded[expr_Times, var_] :=
  Module[{e = expr, v = var, denTerms, num, den, divRes},
   num = Numerator[e];
   den = Denominator[e];
   If[Exponent[num, v] > Exponent[den, v], Return[
     divRes = PolynomialQuotientRemainder[num, den, v];
     divRes[[1]] + myApartUnexpanded[divRes[[2]]/den, v]
     ]];
   denTerms = getDenTerms[den];
   (*If[Length[denTerms]<2,Return[e]];*)

   If[! AllTrue[denTerms, validDenTermQ[#, v] &], Return[e]];
   myLinearApart[num, denTerms, v]
   ];
myApartUnexpanded[expr_, var_] := expr;

Apart[expr_, var_] := myApartUnexpanded[expr, var] // Expand;
Apart[e_] := Expand[e];

Attributes[Apart] = {Listable, Protected};
Tests`Apart = {
    ESimpleExamples[
        ESameTest[a^3+3 a^2 b+3 a b^2+b^3, Apart[(a + b)^3]],
        ESameTest[7/(6 (-5+x))+11/(6 (1+x)), Apart[(3x-8)/((x+1)*(x-5)),x]],
        (*ESameTest[13/(10 (-1+x))-5/(6 (1+x))-7/(15 (4+x)), Apart[(4x+9)/((-1+x) (1+x) (4+x)),x]],*)
        (*ESameTest[1/b-a/(b (a+b x)), Apart[(x/(a+(b*x))),x]],*)
        ESameTest[(5 a^4)/b^6-(4 a^3 x)/b^5+(3 a^2 x^2)/b^4-(2 a x^3)/b^3+x^4/b^2+a^6/(b^6 (a+b x)^2)-(6 a^5)/(b^6 (a+b x)), Apart[(x^6/((a+(b*x))*(a+(b*x)))),x]],
        ESameTest[(5 a^4)/b^6-(4 a^3 x)/b^5+(3 a^2 x^2)/b^4-(2 a x^3)/b^3+x^4/b^2+a^6/(b^6 (a+b x)^2)-(6 a^5)/(b^6 (a+b x)), Apart[(x^6*(a+(b*x))^-2),x]],
        (*ESameTest[2/(27 (-2+x))+1/(3 (1+x)^3)+7/(9 (1+x)^2)-2/(27 (1+x)), Apart[(x^2-2)/((x-2)(x+1)^3),x]]*)
    ]
};

Distribute::usage = "`Distribute[e]` distributes the function over the `Plus` expressions.";
Distribute[e_] := Distribute[e, Plus];
Attributes[Distribute] = {Protected};
Tests`Distribute = {
    ESimpleExamples[
        ESameTest[a c+b c+a d+b d, Distribute[(a+b)*(c+d)]],
        ESameTest[a c+b c, Distribute[(a+b)*c]],
        ESameTest[foo[a,c]+foo[b,c], Distribute[foo[(a+b),c]]],
        ESameTest[foo[a,b], Distribute[foo[a,b]]],
        ESameTest[foo[c]+foo[a,b], Distribute[foo[a,b]+foo[c]]],
        ESameTest[a+(a+b) c, Distribute[(a+b)*(c)+a]],
        ESameTest[(a+b) c e+d e+(a+b) c f+d f, Distribute[((a+b)*(c)+d)*(e+f)]],
        ESameTest[test[foo[a,b]], Distribute[foo[a,b],test]],
        ESameTest[test[foo[a,b],foo[a,c]], Distribute[foo[a,test[b,c]],test]],
        ESameTest[test[foo[a,b,d],foo[a,b,e],foo[a,c,d],foo[a,c,e]], Distribute[foo[a,test[b,c],test[d,e]],test]],
        ESameTest[test[foo[a,b,d,bar[a]],foo[a,b,e,bar[a]],foo[a,c,d,bar[a]],foo[a,c,e,bar[a]]], Distribute[foo[a,test[b,c],test[d,e],bar[a]],test]],
        ESameTest[a, Distribute[a,test]],
        ESameTest[1[a+b], Distribute[a+b,1]],
        ESameTest[test[bar[a,b,d],bar[a,b,e],bar[a,c,d],bar[a,c,e]], Distribute[bar[a,test[b,c],test[d,e]],test]],
        ESameTest[test[test[f,g][a,b,d],test[f,g][a,b,e],test[f,g][a,c,d],test[f,g][a,c,e]], Distribute[test[f,g][a,test[b,c],test[d,e]],test]],
        ESameTest[test[foo[]], Distribute[foo[],test]],
        ESameTest[test[][foo[]], Distribute[foo[],test[]]],
        ESameTest[foo, Distribute[foo,test]]
    ]
};
