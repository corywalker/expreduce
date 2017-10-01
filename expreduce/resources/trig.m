Sin::usage = "`Sin[x]` is the sine of `x`.";
Sin[0] := 0;
Sin[-x_] := -Sin[x];
Sin[p_Plus] := -Sin[-p] /; (MatchQ[p[[1]], -_] || p[[1]] < 0);
Sin[x_Integer?Negative] := -Sin[-x];
Sin[Pi] := 0;
Sin[n_Integer*Pi] := 0;
Sin[I*a_] := I*Sinh[a];
Sin[Indeterminate] := Indeterminate;
Attributes[Sin] = {Listable, NumericFunction, Protected};

Cos::usage = "`Cos[x]` is the cosine of `x`.";
Cos[0] := 1;
Cos[Pi] := -1;
Cos[n_Integer?EvenQ*Pi] := 1;
Cos[n_Integer?OddQ*Pi] := -1;
Cos[I*a_] := Cosh[a];
Cos[-x_] := Cos[x];
Cos[x_Integer?Negative] := Cos[-x];
Cos[inner : Verbatim[Plus][Repeated[_*I]]] := Cosh[-I*inner // Distribute]
Cos[Indeterminate] := Indeterminate;
Attributes[Cos] = {Listable, NumericFunction, Protected};

Tan::usage = "`Tan[x]` is the tangent of `x`.";
1/Tan[x_] := Cot[x];
Tan[a_+Pi/2] := Cot[-a];
(*Tan[a_-Pi/2] := (Print[a];-Cot[a]);*)
Attributes[Tan] = {Listable, NumericFunction, Protected};

Cot::usage = "`Cot[x]` is the cotangent of `x`.";
1/Cot[x_] := Tan[x];
Cot[Verbatim[Plus][-1*a_, b___]] := -Cot[a-b];
Attributes[Cot] = {Listable, NumericFunction, Protected};

Csc[inner : Verbatim[Plus][Repeated[_*I]]] := -I*Csch[-I*inner // Distribute]

Cosh[a_]*Csch[a_]^(b_Integer?Positive)*rest___ := Coth[a]*Csch[a]^(b - 1)*rest

TrigExpand[Cos[2*a_]] := Cos[a]^2-Sin[a]^2;
TrigExpand[Cos[a_]] := Cos[a];
TrigExpand[a_] := (Print["Unsupported call to TrigExpand", a];a);
Attributes[TrigExpand] = {Protected};

TrigReduce[a_] := (Print["Unsupported call to TrigReduce", a];a);
Attributes[TrigReduce] = {Protected};
