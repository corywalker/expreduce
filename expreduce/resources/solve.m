Solve::usage = "`Solve[eqn, var]` solves `eqn` for `var`.";

countVar[expr_, var_Symbol] := 
  If[expr === var, 1, Count[expr, var, -1]];

containsOneOccurrence[eqn_Equal, var_Symbol] := 
  Count[eqn, var, -1] == 1;

(* Return a function that can help isolate var from expr: *)

applyInverse[lhs_Plus -> rhs_, var_Symbol] := Module[{nonVarParts},
   nonVarParts = Select[lhs, (countVar[#, var] === 0) &];
   varParts    = Select[lhs, (countVar[#, var] =!= 0) &];
   {varParts -> rhs - nonVarParts}];
applyInverse[lhs_Times -> rhs_, var_Symbol] := Module[{nonVarParts},
   nonVarParts = Select[lhs, (countVar[#, var] === 0) &];
   varParts    = Select[lhs, (countVar[#, var] =!= 0) &];
   {varParts -> rhs/nonVarParts}];
(* TODO: add support for returning multiple equations. *)
applyInverse[1/lhs_ -> rhs_, var_Symbol] := {lhs -> 1/rhs};
applyInverse[lhs_^2 -> rhs_, var_Symbol] :=
   {lhs -> -Sqrt[rhs], lhs -> Sqrt[rhs]};
applyInverse[Log[lhs_] -> rhs_, var_Symbol] := {lhs -> ConditionalExpression[E^rhs, -Pi < Im[rhs] <= Pi]};
applyInverse[lhs_^Rational[1, n_] -> rhs_, var_Symbol] := {lhs -> rhs^n};

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

(* Following method described in: *)
(*Sterling, L, Bundy, A, Byrd, L, O'Keefe, R & Silver, B 1982, Solving Symbolic Equations with PRESS. in*)
(*Computer Algebra - Lecture Notes in Computer Science. vol. 7. DOI: 10.1007/3-540-11607-9_13*)
(* Available at: http://www.research.ed.ac.uk/portal/files/413486/Solving_Symbolic_Equations_%20with_PRESS.pdf *)
Solve[eqn_Equal, var_Symbol] := Module[{isolated},
   If[containsOneOccurrence[eqn, var],
    isolated = isolate[Rule @@ eqn, var];
    If[AllTrue[isolated, (Head[#] == Rule)&], Return[{#}& /@ isolated]];
    Print["isolation procedure failed"];
    Return[isolated]];
   Print["Solve found no solutions"];
   {}
   ];

(* Special cases for Solve: *)

(* Currently needed for Apart: *)
(*Orderless matching would be nice here*)
Solve[{a_.*x_Symbol+b_.*y_Symbol==c_,d_.*x_Symbol+e_.*y_Symbol==f_},{x_Symbol,y_Symbol}] := {{x->-((c e-b f)/(b d-a e)),y->-((-c d+a f)/(b d-a e))}} /;FreeQ[{a,b,c,d,e,f},x]&&FreeQ[{a,b,c,d,e,f},y]
Solve[{a_.*x_Symbol+b_.*y_Symbol==c_,d_.*x_Symbol==f_},{x_Symbol,y_Symbol}] := {{x->f/d,y->-((-c d+a f)/(b d))}}/;FreeQ[{a,b,c,d,f},x]&&FreeQ[{a,b,c,d,f},y]

Attributes[Solve] = {Protected};
Tests`Solve = {
    ESimpleExamples[
        ESameTest[{{x -> 0}}, Solve[x == 0, x]],
        ESameTest[{{x -> b}}, Solve[x == b, x]],
        ESameTest[{{x -> a b}}, Solve[x/a == b, x]],
        ESameTest[{{x -> b/a}}, Solve[x*a == b, x]],
        ESameTest[{{x -> -(b/m)}}, Solve[m*x + b == 0, x]],
        ESameTest[{{x -> (-b + c)/m}}, Solve[m*x + b == c, x]],
        ESameTest[{{x -> -Sqrt[a]}, {x -> Sqrt[a]}}, Solve[x^2 == a, x]],
        ESameTest[{{a -> 1.5}}, Solve[a + 1.5 == 3, a]],
        ESameTest[{{x -> -Sqrt[-3 + y]}, {x -> Sqrt[-3 + y]}}, Solve[y == x^2 + 3, x]],
        (*ESameTest[{{x -> (-b - Sqrt[b^2 - 4 a c])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c])/(2 a)}}, Solve[a*x^2 + b*x + c == 0, x]],*)
        (*ESameTest[{{x -> (-b - Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}}, Print[a,b,c,d,x];Solve[a*x^2 + b*x + c == d, x]]*)
    ]
};
