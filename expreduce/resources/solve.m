Solve::usage = "`Solve[eqn, var]` solves `eqn` for `var`.";

countVar[expr_, var_Symbol] := 
  If[expr === var, 1, Count[expr, var, -1]];

containsOneOccurrence[eqn_Equal, var_Symbol] := 
  Count[eqn, var, -1] == 1;
containsZeroOccurrences[eqn_Equal, var_Symbol] := 
  Count[eqn, var, -1] == 0;

checkedConditionalExpression[e_, c_] := 
  Module[{nextC = 1, res, reps, newC = -1},
   While[True, If[Count[e, C[nextC], -1] > 0, nextC++, Break[]]];
   res = ConditionalExpression[e, c];
   reps = {};
   While[True,
    If[Count[res, C[newC], -1] > 0,
     AppendTo[reps, C[newC] -> C[-newC]]; newC--,
     Break[]]];
   res = res /. C[n_Integer?Positive] :> C[n + Length[reps]];
   res /. reps];

applyInverse[lhs_Plus -> rhs_, var_Symbol] := Module[{nonVarParts},
   nonVarParts = Select[lhs, (countVar[#, var] === 0) &];
   varParts    = Select[lhs, (countVar[#, var] =!= 0) &];
   {varParts -> rhs - nonVarParts}];
applyInverse[lhs_Times -> rhs_, var_Symbol] := Module[{nonVarParts},
   nonVarParts = Select[lhs, (countVar[#, var] === 0) &];
   varParts    = Select[lhs, (countVar[#, var] =!= 0) &];
   {varParts -> rhs / nonVarParts}];
applyInverse[base_^pow_ -> rhs_, var_Symbol] := If[countVar[base, var] =!= 0,
  (* var in base *)
  Switch[pow,
    -1,              {base -> 1/rhs},
    2,               {base -> -Sqrt[rhs]//PowerExpand, base -> Sqrt[rhs]//PowerExpand},
    3,               {base->rhs^(1/3),base->-(-1)^(1/3) rhs^(1/3),base->(-1)^(2/3) rhs^(1/3)},
    4,               {base->-rhs^(1/4),base->-I rhs^(1/4),base->I rhs^(1/4),base->rhs^(1/4)},
    5,               {base->rhs^(1/5),base->-(-1)^(1/5) rhs^(1/5),base->(-1)^(2/5) rhs^(1/5),base->-(-1)^(3/5) rhs^(1/5),base->(-1)^(4/5) rhs^(1/5)},
    (* Not implemented yet *)
    _Integer,        SolveError,
    (* Similar to the general case but without the message.*)
    Rational[1, n_], {base -> rhs ^ (1/pow)},
    _,               Message[Solve::ifun, Solve];{base -> rhs ^ (1/pow)}
  ],
  (* else, var in power *)
  If[rhs === 0,
    {},
    Switch[base,
      _Integer,
        {pow->
          ConditionalExpression[
            If[base > 0,
              (2 I Pi C[1])/Log[base]+Log[rhs]/Log[base],
              ((2 I Pi C[1])+Log[rhs])/Log[base],
            ],
            C[1]\[Element]Integers
          ]
        },
      E, If[MatchQ[rhs, _Real],
            {pow -> Log[rhs]},
            {pow -> ConditionalExpression[2 I Pi C[1] + Log[rhs], 
              C[1] \[Element] Integers]},
           ],
      _, Message[Solve::ifun, Solve];{pow -> Log[rhs]/Log[base]}
    ]]
];
applyInverse[Log[lhs_] -> rhs_, var_Symbol] :=
  {lhs -> ConditionalExpression[E^rhs, -Pi < Im[rhs] <= Pi]};
applyInverse[Abs[lhs_] -> rhs_, var_Symbol] :=
  (Message[Solve::ifun, Solve];{lhs -> -rhs, lhs -> rhs});
(* Trig inverses *)
applyInverse[Sin[lhs_] -> rhs_, var_Symbol] :=
  {lhs->checkedConditionalExpression[Pi-ArcSin[rhs]+2 Pi C[-1],C[-1]\[Element]Integers],
   lhs->checkedConditionalExpression[ArcSin[rhs]+2 Pi C[-1],C[-1]\[Element]Integers]};
applyInverse[Cos[lhs_] -> rhs_, var_Symbol] :=
  {lhs->checkedConditionalExpression[-ArcCos[rhs]+2 Pi C[-1],C[-1]\[Element]Integers],
   lhs->checkedConditionalExpression[ArcCos[rhs]+2 Pi C[-1],C[-1]\[Element]Integers]};
applyInverse[Tan[lhs_] -> rhs_, var_Symbol] :=
  {lhs -> ConditionalExpression[ArcTan[rhs] + Pi C[1], 
         C[1] \[Element] Integers]};
applyInverse[Cot[lhs_] -> rhs_, var_Symbol] :=
  {lhs -> ConditionalExpression[ArcCot[rhs] + Pi C[1], 
         C[1] \[Element] Integers]};
applyInverse[Sec[lhs_] -> rhs_, var_Symbol] :=
  {lhs -> ConditionalExpression[-ArcCos[1/rhs] + 2 Pi C[1], 
         C[1] \[Element] Integers], lhs -> 
               ConditionalExpression[ArcCos[1/rhs] + 2 Pi C[1], 
                  C[1] \[Element] Integers]};
applyInverse[Csc[lhs_] -> rhs_, var_Symbol] :=
  {lhs -> ConditionalExpression[Pi - ArcSin[1/rhs] + 2 Pi C[1], 
         C[1] \[Element] Integers], lhs -> 
               ConditionalExpression[ArcSin[1/rhs] + 2 Pi C[1], 
                  C[1] \[Element] Integers]};
(* Inverses for inverse trig functions *)
applyInverse[ArcSin[lhs_] -> rhs_, var_Symbol] :=
  {lhs -> ConditionalExpression[
         Sin[rhs], (Re[rhs] == -(Pi/2) && Im[rhs] >= 0) || -(Pi/2) < 
              Re[rhs] < Pi/2 || (Re[rhs] == Pi/2 && Im[rhs] <= 0)]};
applyInverse[ArcCos[lhs_] -> rhs_, var_Symbol] :=
  {lhs -> ConditionalExpression[
         Cos[rhs], (Re[rhs] == 0 && Im[rhs] >= 0) || 
             0 < Re[rhs] < Pi || (Re[rhs] == Pi && Im[rhs] <= 0)]};
applyInverse[ArcTan[lhs_] -> rhs_, var_Symbol] :=
  {lhs -> ConditionalExpression[
         Tan[rhs], (Re[rhs] == -(Pi/2) && Im[rhs] < 0) || -(Pi/2) < 
              Re[rhs] < Pi/2 || (Re[rhs] == Pi/2 && Im[rhs] > 0)]};
applyInverse[Cosh[lhs_] -> rhs_, var_Symbol] :=
  {lhs -> ConditionalExpression[-ArcCosh[rhs] + 2 I \[Pi] C[1], 
   C[1] \[Element] Integers], lhs -> 
  ConditionalExpression[ArcCosh[rhs] + 2 I \[Pi] C[1], 
   C[1] \[Element] Integers]}

(* Base case: *)

isolate[var_Symbol -> rest_, var_Symbol] := {var -> rest};
isolate[lhs_ -> rhs_, var_Symbol] := Module[{inverseApplied},
   (* Switch sides if needed to get var on LHS: *)

   If[(countVar[rhs, var] === 1) && (countVar[lhs, var] === 0), 
    Return[isolate[rhs -> lhs, var]]];

   (* Assert var occurs only once in the LHS: *)

   If[!((countVar[lhs, var] === 1) && (countVar[rhs, var] === 0)),
    Return[$Failed]];

   inverseApplied = applyInverse[lhs -> rhs, var];
   If[Head[inverseApplied] =!= List, 
    Print["Solve error: Finding inverse failed for ", lhs -> rhs, 
     ", var: ", var]; Return[SolveFailed]];

   allIsolated = isolate[#, var]& /@ inverseApplied;
   Join[Sequence @@ allIsolated]
   ];
checkSolution[eqn_Equal, sol_] := Module[{checkRes},
    checkRes = eqn /. sol // Simplify;
    checkRes =!= False
];
isolateInEqn[eqn_Equal, var_Symbol] := Module[{isolated},
  isolated = {#}& /@ isolate[Rule @@ eqn, var];
  (*Check that the isolate procedure returned sane results.*)
  If[!AllTrue[isolated, (Head[#[[1]]] == Rule)&], Return[SolveFailed]];
  (*Canonicalize solutions.*)
  isolated = isolated//Simplify//Sort;
  isolated = Select[isolated, checkSolution[eqn, #]&];
  isolated
];

collect[eqn_Equal, var_Symbol] := Module[{toTry, collected, continue, foundSimpler, toTryFns},
  collected = eqn;
  continue = True;
  While[continue,
    foundSimpler = False;
    toTryFns = {
      (#[[1]]-#[[2]]==0)&,
      (Expand[#])&,
      (ExpandAll[#])&
    };
    Do[
      toTry = toTryFn[collected];
      If[Not[foundSimpler] && countVar[toTry, var] < countVar[collected, var],
        collected = toTry;
        foundSimpler = True;
      ];
    , {toTryFn, toTryFns}];
    continue = foundSimpler;
  ];
  collected
];

solveQuadratic[a_, b_, c_, x_] := {{x->(-b-Sqrt[b^2-4 a c])/(2 a)},{x->(-b+Sqrt[b^2-4 a c])/(2 a)}};
solveQuadratic[a_.*x_^2 + b_.*x_ + c_., x_] := solveQuadratic[a,b,c,x]/;FreeQ[{a,b,c},x];
solveCubic[d_,c_,b_,a_,x_] := {{x->-(c/(3 d))-(2^(1/3) (-c^2+3 b d))/(3 d (-2 c^3+9 b c d-27 a d^2+Sqrt[4 (-c^2+3 b d)^3+(-2 c^3+9 b c d-27 a d^2)^2])^(1/3))+(-2 c^3+9 b c d-27 a d^2+Sqrt[4 (-c^2+3 b d)^3+(-2 c^3+9 b c d-27 a d^2)^2])^(1/3)/(3 2^(1/3) d)},{x->-(c/(3 d))+((1+I Sqrt[3]) (-c^2+3 b d))/(3 2^(2/3) d (-2 c^3+9 b c d-27 a d^2+Sqrt[4 (-c^2+3 b d)^3+(-2 c^3+9 b c d-27 a d^2)^2])^(1/3))-(1/(6 2^(1/3) d))(1-I Sqrt[3]) (-2 c^3+9 b c d-27 a d^2+Sqrt[4 (-c^2+3 b d)^3+(-2 c^3+9 b c d-27 a d^2)^2])^(1/3)},{x->-(c/(3 d))+((1-I Sqrt[3]) (-c^2+3 b d))/(3 2^(2/3) d (-2 c^3+9 b c d-27 a d^2+Sqrt[4 (-c^2+3 b d)^3+(-2 c^3+9 b c d-27 a d^2)^2])^(1/3))-(1/(6 2^(1/3) d))(1+I Sqrt[3]) (-2 c^3+9 b c d-27 a d^2+Sqrt[4 (-c^2+3 b d)^3+(-2 c^3+9 b c d-27 a d^2)^2])^(1/3)}};
solveCubic[d_.*x_^3 + c_.*x_^2 + b_.*x_ + a_., x_] := solveCubic[d,c,b,a,x]/;FreeQ[{a,b,c,d},x];
solveCubic[d_.*x_^3 + c_.*x_^2 + a_., x_] := solveCubic[d,c,0,a,x]/;FreeQ[{a,c,d},x];
solveQuartic[e_.*x_^4 + d_.*x_^3 + c_.*x_^2 + b_.*x_ + a_., x_] := {{x->-(d/(4 e))-1/2 \[Sqrt](d^2/(4 e^2)-(2 c)/(3 e)+(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))+(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3)))-1/2 \[Sqrt](d^2/(2 e^2)-(4 c)/(3 e)-(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))-(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))-(-(d^3/e^3)+(4 c d)/e^2-(8 b)/e)/(4 \[Sqrt](d^2/(4 e^2)-(2 c)/(3 e)+(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+\[Sqrt](-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2))^(1/3))+(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+\[Sqrt](-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2))^(1/3)))))},{x->-(d/(4 e))-1/2 \[Sqrt](d^2/(4 e^2)-(2 c)/(3 e)+(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))+(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3)))+1/2 \[Sqrt](d^2/(2 e^2)-(4 c)/(3 e)-(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))-(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))-(-(d^3/e^3)+(4 c d)/e^2-(8 b)/e)/(4 \[Sqrt](d^2/(4 e^2)-(2 c)/(3 e)+(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+\[Sqrt](-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2))^(1/3))+(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+\[Sqrt](-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2))^(1/3)))))},{x->-(d/(4 e))+1/2 \[Sqrt](d^2/(4 e^2)-(2 c)/(3 e)+(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))+(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3)))-1/2 \[Sqrt](d^2/(2 e^2)-(4 c)/(3 e)-(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))-(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))+(-(d^3/e^3)+(4 c d)/e^2-(8 b)/e)/(4 \[Sqrt](d^2/(4 e^2)-(2 c)/(3 e)+(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+\[Sqrt](-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2))^(1/3))+(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+\[Sqrt](-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2))^(1/3)))))},{x->-(d/(4 e))+1/2 \[Sqrt](d^2/(4 e^2)-(2 c)/(3 e)+(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))+(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3)))+1/2 \[Sqrt](d^2/(2 e^2)-(4 c)/(3 e)-(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))-(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+Sqrt[-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2])^(1/3))+(-(d^3/e^3)+(4 c d)/e^2-(8 b)/e)/(4 \[Sqrt](d^2/(4 e^2)-(2 c)/(3 e)+(2^(1/3) (c^2-3 b d+12 a e))/(3 e (2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+\[Sqrt](-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2))^(1/3))+(1/(3 2^(1/3) e))((2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e+\[Sqrt](-4 (c^2-3 b d+12 a e)^3+(2 c^3-9 b c d+27 a d^2+27 b^2 e-72 a c e)^2))^(1/3)))))}}/;FreeQ[{a,b,c,d,e},x];

(* Solve using u-substitution for polynomial-like forms.*)
uSubstitute::usage = 
  "uSubstitute[eqn, var] takes a non-polynomial `eqn` and attempts a \
u-substitution such that `eqn` takes a polynomial form. If the \
substitution succeeds, the function returns `{transformed, uValue}`. \
The `transformed` equation will include the `uPlaceholder` symbol as \
the u symbol. The function returns an error symbol if the \
substitution fails to produce a polynomial form.";
uSubstitute[theEqn_, theVar_Symbol] := 
  Module[{eqn = theEqn, var = theVar, expGcd, uValue, transformed, 
    exponents},
   (* Attempt to extract exponents of polynomial-like equations. 
   We wish to ignore any zero-valued exponents. *)
   
   exponents = DeleteCases[Exponent[eqn, var, List], 0];
   (* Find the signed GCD of the exponents. 
   This seems to work for many of the problem cases, 
   but may not yield a useful polynomial form for all equations. *)
  
    expGcd = GCD @@ exponents*Sign[exponents[[1]]];
   uValue = var^expGcd;
   (* Rewrite the variable with our u-value. *)
   
   transformed = 
    eqn /. var -> uPlaceholder^(1/expGcd) // PowerExpand;
   (* If our transformed equation is polynomial, we have succeeded. *)

      If[PolynomialQ[transformed, var], {transformed, uValue}, $Failed]
   ];

uSubstitutionSolve::usage = 
  "uSubstitutionSolve[eqn, var] takes a non-polynomial `eqn` and \
attempts a u-substitution such that `eqn` takes a polynomial form in \
order to solve the equation. The function returns the solve result or \
`$Failed` in case of an issue.";
uSubstitutionSolve[theEqn_, theVar_Symbol] := 
  Module[{eqn = theEqn, var = theVar, transformed, uSolved, solved},
   transformed = uSubstitute[eqn, var];
   (* If the u-
   substitution fails to produce a polynomial form and instead \
returns an error symbol, fail this solution attempt. *)
Print[transformed];
   
   If[Head[transformed] =!= List, Return[$Failed]];
   (* Find the roots of the equation that was transformed into a \
polynomial form. *)
   
   uSolved = Solve[transformed[[1]] == 0, uPlaceholder];
   (* For each of the roots, solve for the original variable. *)
Print[uSolved];
   If[Head[uSolved] =!= List, Return[$Failed]];
   
   solved = 
    Map[Solve[transformed[[2]] == #[[1, 2]], var] &, uSolved];
   (* There may be some roots that have no solution for the original \
variable. Throw these out. *)
Print[solved];
   
   solved = Select[solved, (Length[#] >= 1) &];
   (* No way to handle multiple solutions yet. *)
   
   If[AnyTrue[solved, (Length[#] != 1) &], Return[$Failed]];
   (* Collect the unique solutions of eqn and return. *)
   
Print[solved];
   Map[First, solved] // DeleteDuplicates // Sort
   ];

(* Following method described in: *)
(*Sterling, L, Bundy, A, Byrd, L, O'Keefe, R & Silver, B 1982, Solving Symbolic Equations with PRESS. in*)
(*Computer Algebra - Lecture Notes in Computer Science. vol. 7. DOI: 10.1007/3-540-11607-9_13*)
(* Available at: http://www.research.ed.ac.uk/portal/files/413486/Solving_Symbolic_Equations_%20with_PRESS.pdf *)
Solve[eqn_Equal, var_Symbol] := Module[{degree, collected, fullSimplified, poly},
   If[containsZeroOccurrences[eqn, var], Return[{}]];
   (* Attempt isolation *)
   If[containsOneOccurrence[eqn, var], Return[isolateInEqn[eqn, var]]];

   (* Attempt polynomial solve *)
   poly = eqn[[1]]-eqn[[2]];
   If[PolynomialQ[poly, var],
    degree = Exponent[poly, var];
    If[degree === 2, Return[solveQuadratic[poly//Expand, var]//Simplify//Sort]];
    If[degree === 3, Return[solveCubic[poly//Expand, var]//Simplify//Sort]];
    If[degree === 4, Return[solveQuartic[poly//Expand, var]//Simplify//Sort]];
   ];

   collected = collect[eqn, var];
   If[containsOneOccurrence[collected, var], Return[isolateInEqn[collected, var]]];

   (*Try FullSimplify then solve.*)
   fullSimplified = eqn // FullSimplify;
   If[fullSimplified =!= eqn, Return[Solve[fullSimplified, var]]];

   Print["Solve found no solutions"];
   SolveFailed
   ];
solveMultOrdered[eqns_List, vars_List] := 
  Module[{firstSol, secondSol, toSolve},
   If[Length[eqns] =!= 2 || Length[vars] =!= 2, Return[SolveFailed]];
   firstSol = Solve[eqns[[1]], vars[[1]]];
   Print[firstSol];
   If[Length[firstSol] =!= 1, Return[TooManySols1]];
   toSolve := eqns[[2]] /. firstSol[[1, 1]];
   secondSol = Solve[toSolve, vars[[2]]];
   Print[secondSol];
   If[Length[secondSol] =!= 1, Return[TooManySols2]];
   firstSol = firstSol /. secondSol[[1]];
   {{firstSol[[1, 1]], secondSol[[1, 1]]}}
   ];
Solve[eqn_Equal, vars_List] := Solve[eqn, vars[[Length[vars]]]];
Solve[eqns_List, vars_List] := Module[{res, currVarOrder},
   res = Do[
     res = solveMultOrdered[eqns, currVarOrder];
     If[Head[res] === List, Return[res]];
     , {currVarOrder, Permutations[vars]}];
   If[res === Null, NoneFound, res]
   ];

(* Special cases for Solve: *)
Solve[False, _] := {};
Solve[True, _] := {{}};
Solve[{}, _] := {{}};
Solve[x_Symbol+a_.*E^x_Symbol==0, x_Symbol] := {{x->-ProductLog[a]}};
(* Currently needed for Apart: *)
(*Orderless matching would be nice here*)
Solve[{a_.*x_Symbol+b_.*y_Symbol==c_,d_.*x_Symbol+e_.*y_Symbol==f_},{x_Symbol,y_Symbol}] := {{x->-((c e-b f)/(b d-a e)),y->-((-c d+a f)/(b d-a e))}} /;FreeQ[{a,b,c,d,e,f},x]&&FreeQ[{a,b,c,d,e,f},y]
Solve[{a_.*x_Symbol+b_.*y_Symbol==c_,d_.*x_Symbol==f_},{x_Symbol,y_Symbol}] := {{x->f/d,y->-((-c d+a f)/(b d))}}/;FreeQ[{a,b,c,d,f},x]&&FreeQ[{a,b,c,d,f},y]

Attributes[Solve] = {Protected};
normSol[s_List] := 
  Sort[(# /. 
             ConditionalExpression[e_, a_And] :> 
                     ConditionalExpression[e, a // Sort]) & /@ s];
Tests`Solve = {
    ESimpleExamples[
        ESameTest[{{x->Log[y]/Log[a+b]}}, Solve[(a+b)^x==y,x]],
        ESameTest[{{x -> -Sqrt[-3 + y]}, {x -> Sqrt[-3 + y]}}, Solve[y == x^2 + 3, x]],
        ESameTest[{{y->1-Sqrt[-2+2 x-x^2]},{y->1+Sqrt[-2+2 x-x^2]}}, Solve[2==x^2+y^2+(x-2)^2+(y-2)^2,y]],
        (*ESameTest[{{x -> (-b - Sqrt[b^2 - 4 a c])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c])/(2 a)}}, Solve[a*x^2 + b*x + c == 0, x]],*)
        (*ESameTest[{{x -> (-b - Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}}, Print[a,b,c,d,x];Solve[a*x^2 + b*x + c == d, x]]*)
    ], ETests[
        (* BASIC ISOLATION *)

        (* Sanity checks *)
        ESameTest[{{x -> 0}}, Solve[x == 0, x]],
        ESameTest[{{x -> b}}, Solve[x == b, x]],
        (* Inverses of addition *)
        ESameTest[{{a -> 1.5}}, Solve[a + 1.5 == 3, a]],
        (* Inverses of multiplication/division *)
        ESameTest[{{x -> b/a}}, Solve[x*a == b, x]],
        ESameTest[{{x -> a b}}, Solve[x/a == b, x]],
        ESameTest[{{x -> -(b/m)}}, Solve[m*x + b == 0, x]],
        ESameTest[{{x -> (-b + c)/m}}, Solve[m*x + b == c, x]],
        (* Inverse of exponentiation, var in base *)
        ESameTest[{{x -> -Sqrt[a]}, {x -> Sqrt[a]}}, Solve[x^2 == a, x]],
        ESameTest[{{x->b^(1/a)}}, Solve[x^a==b,x]],
        ESameTest[{{x -> -Sqrt[-3 + y]}, {x -> Sqrt[-3 + y]}}, Solve[y == x^2 + 3, x]],
        ESameTest[{{x->2^(1/(5 y+Sin[y]))}}, Solve[x^(5y+Sin[y])==2,x]],
        ESameTest[{{a->-b},{a->b}}, Solve[a^2==b^2,a]],
        ESameTest[{}, Solve[x^(1/2)==-1,x]],
        (* Inverse of exponentiation, var in base: To a fractional power *)
        ESameTest[{{x->y^2}}, Solve[Sqrt[x]==y,x]],
        ESameTest[{{x->y^9}}, Solve[x^(1/9)==y,x]],
        (* Inverse of exponentiation, var in power *)
        ESameTest[{{x->Log[y]/Log[a+b]}}, Solve[(a+b)^x==y,x]],
        ESameTest[{{x->ConditionalExpression[1/2 (2 I Pi C[1]+Log[5/4]),C[1]\[Element]Integers]}}, Solve[4E^(2x)==5,x]],
        ESameTest[{{x->ConditionalExpression[2 I Pi C[1]+Log[5],C[1]\[Element]Integers]}}, Solve[E^x==5,x]],
        ESameTest[{}, Solve[E^x==0,x]],
        ESameTest[{{x->ConditionalExpression[2 I Pi C[1],C[1]\[Element]Integers]}}, Solve[E^x==1,x]],
        (*ESameTest[{{x->2.4663 Log[y]}}, Solve[1.5^x==y,x]],*)
        ESameTest[{{x->ConditionalExpression[(2 I Pi C[1])/Log[3]+Log[y]/Log[3],C[1]\[Element]Integers]}}, Solve[3^x == y, x]],
        ESameTest[{{x->ConditionalExpression[(2 I Pi C[1])/Log[2]+Log[y]/Log[2],C[1]\[Element]Integers]}}, Solve[2^x == y, x]],
        ESameTest[{{x->ConditionalExpression[(2 I Pi C[1]+Log[y])/(I Pi+Log[2]),C[1]\[Element]Integers]}}, Solve[(-2)^x == y, x]],
        ESameTest[{{x->ConditionalExpression[(2 I Pi C[1]+Log[y])/(I Pi+Log[3]),C[1]\[Element]Integers]}}, Solve[(-3)^x == y, x]],
        (* Inverse of log *)
        ESameTest[{{x->ConditionalExpression[E^(b+y-z)-y,-Pi<Im[b+y-z]<=Pi]}}, Solve[y+b==Log[x+y]+z,x]],
        ESameTest[{{x->ConditionalExpression[Pi-ArcSin[E^y]+2 Pi C[1],C[1]\[Element]Integers&&-Pi<Im[y]<=Pi]},{x->ConditionalExpression[ArcSin[E^y]+2 Pi C[1],C[1]\[Element]Integers&&-Pi<Im[y]<=Pi]}}//Sort, Solve[Log[Sin[x]]==y,x]],
        (* Inverse of Abs *)
        ESameTest[{{a->-2-b},{a->2-b}}, Solve[Abs[a+b]==2,a]],
        (* Inverse of Sin *)
        ESameTest[{{x->ConditionalExpression[-b-ArcSin[c-d]+2 Pi C[1],C[1]\[Element]Integers]},{x->ConditionalExpression[-b+Pi+ArcSin[c-d]+2 Pi C[1],C[1]\[Element]Integers]}}, Solve[Sin[x+b]+c==d,x]],
        (* Inverse of Cos *)
        ESameTest[{{a->ConditionalExpression[-b-ArcCos[2]+2 Pi C[1],C[1]\[Element]Integers]},{a->ConditionalExpression[-b+ArcCos[2]+2 Pi C[1],C[1]\[Element]Integers]}}, Solve[Cos[a+b]==2,a]],
        (* Solve nested trig functions *)
        ESameTest[{{x->ConditionalExpression[-ArcSin[ArcCos[y]-2 Pi C[2]]+2 Pi C[1],C[2]\[Element]Integers&&C[1]\[Element]Integers]},{x->ConditionalExpression[Pi+ArcSin[ArcCos[y]-2 Pi C[2]]+2 Pi C[1],C[2]\[Element]Integers&&C[1]\[Element]Integers]},{x->ConditionalExpression[Pi-ArcSin[ArcCos[y]+2 Pi C[2]]+2 Pi C[1],C[2]\[Element]Integers&&C[1]\[Element]Integers]},{x->ConditionalExpression[ArcSin[ArcCos[y]+2 Pi C[2]]+2 Pi C[1],C[2]\[Element]Integers&&C[1]\[Element]Integers]}}//normSol, Solve[Cos[Sin[x]]==y,x]//normSol],
        (* Solve combination of Sin and ArcSin *)
        ESameTest[{{x->-b+y}}, Solve[Sin[ArcSin[x+b]]==y,x]],
        ESameTest[{{x->ConditionalExpression[Pi-ArcSin[Sin[y]]+2 Pi C[1],((Re[y]==-(Pi/2)&&Im[y]>=0)||-(Pi/2)<Re[y]<Pi/2||(Re[y]==Pi/2&&Im[y]<=0))&&C[1]\[Element]Integers]},{x->ConditionalExpression[ArcSin[Sin[y]]+2 Pi C[1],((Re[y]==-(Pi/2)&&Im[y]>=0)||-(Pi/2)<Re[y]<Pi/2||(Re[y]==Pi/2&&Im[y]<=0))&&C[1]\[Element]Integers]}}//normSol, Solve[ArcSin[Sin[x]]==y,x]//normSol],
        (* Solve a problem involving a PDF *)
        EStringTest["{{x -> -1.66352}, {x -> 1.66352}}", "Solve[PDF[NormalDistribution[0, 1], x] == .1, x]"],

        (* POLYNOMIALS *)
        ESameTest[{{x->(-b-Sqrt[b^2-4 a c])/(2 a)},{x->(-b+Sqrt[b^2-4 a c])/(2 a)}}, Solve[a*x^2==-b*x-c,x]],
        ESameTest[Solve[a x^2==-b x-foo[x],x], Solve[a*x^2==-b*x-foo[x],x]],
        ESameTest[{{x->-((I Sqrt[c])/Sqrt[a])},{x->(I Sqrt[c])/Sqrt[a]}}, Solve[a*x^2==-c,x]],
        ESameTest[{{x->-I Sqrt[c]},{x->I Sqrt[c]}}, Solve[x^2==-c,x]],

        (* COLLECTION *)
        ESameTest[{{x->4}}, Solve[3x+1==2x+5,x]],
        ESameTest[{{x->17/15}}, Solve[5(4x-3)+4 (6 x+1)==7 (2 x+3)+2,x]],
    ], EKnownFailures[
        ESameTest[{{x->-2 I},{x->-2 I-2 y}}//normSol, Solve[Abs[x+2I+y]==y,x]//normSol],
    ],
};

ExpreduceTestSolve[fn_] := Module[{testproblems, testi, runSolveTest, testp, res, nCorrect, isCorrect},
    testproblems = ReadList[fn];
    testproblems = Select[testproblems, (MatchQ[#[[2]],_Symbol])&];
    Print[Length[testproblems]];

    testi = 1;
    nCorrect = 0;

    runSolveTest[thei_Integer] := (
        testp = testproblems[[thei]];
        res = Solve[testp[[1]], testp[[2]]] // Timing;
        isCorrect = res[[2]] === testp[[3]];
        Print[{testp[[1]], testp[[2]], testp[[3]], res[[2]], res[[1]], isCorrect}];
        If[isCorrect, nCorrect++];
    );

    While[testi <= Length[testproblems],
        Print[{testi, testproblems[[testi]]}];
        runSolveTest[testi];
        testi = testi+1;
    ];
    Print[nCorrect];
];

ConditionalExpression::usage = "`ConditionalExpression[expr, conditions]` represents `expr` which is conditional on `conditions`.";
Attributes[ConditionalExpression] = {Protected};
ConditionalExpression[e_, True] := e;
ConditionalExpression[e_, False] := Undefined;
ConditionalExpression[ConditionalExpression[a_, b_], c_] :=
  ConditionalExpression[a, c && b];
