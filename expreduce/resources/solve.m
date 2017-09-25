Solve::usage = "`Solve[eqn, var]` solves `eqn` for `var`.";
Solve[x_ == expr_, x_] := {{x -> expr}};
Solve[x_ * exprB__ == exprA_, x_] := {{x -> exprA / Times[exprB]}};
Solve[x_ * exprB__ + exprC_ == exprA_, x_] := {{x -> (exprA-exprC) / Times[exprB]}};
Solve[a_.*x_^2 + b_.*x_ + c_ == d_, x_] := {{x -> (-b - Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}};
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
        (*ESameTest[{{x -> (-b - Sqrt[b^2 - 4 a c])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c])/(2 a)}}, Solve[a*x^2 + b*x + c == 0, x]],*)
        (*ESameTest[{{x -> (-b - Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}}, Print[a,b,c,d,x];Solve[a*x^2 + b*x + c == d, x]]*)
    ]
};
