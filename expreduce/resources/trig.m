Sin::usage = "`Sin[x]` is the sine of `x`.";
Sin[0] := 0;
Sin[-x_] := -Sin[x];
Sin[x_Integer?Negative] := -Sin[-x];
Sin[Pi] := 0;
Sin[n_Integer*Pi] := 0;
Sin[I*a_] := I*Sinh[a];
Attributes[Sin] = {Listable, NumericFunction, Protected};

Cos::usage = "`Cos[x]` is the cosine of `x`.";
Cos[0] := 1;
Cos[Pi] := -1;
Cos[n_Integer?EvenQ*Pi] := 1;
Cos[n_Integer?OddQ*Pi] := -1;
Cos[I*a_] := Cosh[a];
Cos[-x_] := Cos[x];
Cos[x_Integer?Negative] := Cos[-x];
Attributes[Cos] = {Listable, NumericFunction, Protected};

Tan::usage = "`Tan[x]` is the tangent of `x`.";
Attributes[Tan] = {Listable, NumericFunction, Protected};
