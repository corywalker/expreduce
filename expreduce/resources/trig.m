Sin::usage = "`Sin[x]` is the sine of `x`.";
Sin[0] := 0;
Sin[-x_] := -Sin[x];
Sin[p_Plus] := -Sin[-p] /; (MatchQ[p[[1]], -_] || p[[1]] < 0);
Sin[x_Integer?Negative] := -Sin[-x];
Sin[Pi] := 0;
Sin[n_Integer*Pi] := 0;
Sin[I*a_] := I*Sinh[a];
Sin[(-5/2)*Pi] := -1;
Sin[(-3/2)*Pi] := 1;
Sin[(-2/3)*Pi] := -Sqrt[3]/2;
Sin[(-1/2)*Pi] := -1;
Sin[(-1/3)*Pi] := -(Sqrt[3]/2);
Sin[(1/4)*Pi] := 1/Sqrt[2];
Sin[(1/3)*Pi] := Sqrt[3]/2;
Sin[(1/2)*Pi] := 1;
Sin[(2/3)*Pi] := Sqrt[3]/2;
Sin[(3/2)*Pi] := -1;
Sin[(5/2)*Pi] := 1;
Sin[Indeterminate] := Indeterminate;
Sin[ArcSin[a_]] := a;
Sin[ArcTan[1/2]] := 1/Sqrt[5];
Attributes[Sin] = {Listable, NumericFunction, Protected};

Cos::usage = "`Cos[x]` is the cosine of `x`.";
Cos[0] := 1;
Cos[Pi] := -1;
Cos[n_Integer?EvenQ*Pi] := 1;
Cos[n_Integer?OddQ*Pi] := -1;
Cos[(-5/2)*Pi] := 0;
Cos[(-3/2)*Pi] := 0;
Cos[(-1/2)*Pi] := 0;
Cos[(-1/3)*Pi] := 1/2;
Cos[(1/4)*Pi] := 1/Sqrt[2];
Cos[(1/3)*Pi] := 1/2;
Cos[(1/2)*Pi] := 0;
Cos[(2/3)*Pi] := -1/2;
Cos[(3/2)*Pi] := 0;
Cos[(5/2)*Pi] := 0;
Cos[I*a_] := Cosh[a];
Cos[-x_] := Cos[x];
Cos[x_Integer?Negative] := Cos[-x];
Cos[inner : Verbatim[Plus][Repeated[_*I]]] := Cosh[-I*inner // Distribute]
Cos[Indeterminate] := Indeterminate;
Cos[ArcCos[a_]] := a;
Cos[ArcTan[1/2]] := 2/Sqrt[5];
Attributes[Cos] = {Listable, NumericFunction, Protected};

Tan::usage = "`Tan[x]` is the tangent of `x`.";
Tan[x_]^(-1) := Cot[x];
Tan[a_+Pi/2] := Cot[-a];
(*Tan[a_-Pi/2] := (Print[a];-Cot[a]);*)
Tan[ArcTan[a_]] := a;
Attributes[Tan] = {Listable, NumericFunction, Protected};

Cot::usage = "`Cot[x]` is the cotangent of `x`.";
Cot[x_]^(-1) := Tan[x];
Cot[x_ + Pi/2] := -Tan[x];
Cot[Verbatim[Plus][-1*a_, b___]] := -Cot[a-b];
Attributes[Cot] = {Listable, NumericFunction, Protected};

Sec[x_ - Pi/2] := Csc[x];
Attributes[Sec] = {Listable, NumericFunction, Protected};

Csc[inner : Verbatim[Plus][Repeated[_*I]]] := -I*Csch[-I*inner // Distribute]
Attributes[Csc] = {Listable, NumericFunction, Protected};

Cosh[a_]*Csch[a_]^(b_Integer?Positive)*rest___ := Coth[a]*Csch[a]^(b - 1)*rest
Attributes[Cosh] = {Listable, NumericFunction, Protected};

ArcSin[p_Plus] := -ArcSin[-p] /; (MatchQ[p[[1]], -_] || p[[1]] < 0);
ArcSin[-x_] := -ArcSin[x];
ArcSin[0] := 0;
Attributes[ArcSin] = {Listable, NumericFunction, Protected, ReadProtected};

Attributes[ArcCos] = {Listable, NumericFunction, Protected, ReadProtected};

ArcTan[-1] := -Pi/4;
ArcTan[0] := 0;
ArcTan[1] := Pi/4;
ArcTan[x_,y_] := Which[
    x > 0, ArcTan[y/x],
    x < 0 && y >= 0, ArcTan[y/x] + Pi,
    x < 0 && y < 0, ArcTan[y/x] - Pi,
    x == 0 && y > 0, Pi/2,
    x == 0 && y < 0, -Pi/2,
    True, Indeterminate];
Attributes[ArcTan] = {Listable, NumericFunction, Protected, ReadProtected};

TrigExpand[Cos[2*a_]] := Cos[a]^2-Sin[a]^2;
TrigExpand[Cos[a_]] := Cos[a];
TrigExpand[a_] := (Print["Unsupported call to TrigExpand", a];a);
Attributes[TrigExpand] = {Protected};

TrigReduce[a_] := (Print["Unsupported call to TrigReduce", a];a);
Attributes[TrigReduce] = {Protected};

TrigToExp[n_Integer] := n;
TrigToExp[Cos[sym_Symbol]] := E^(-I sym)/2 + E^(I sym)/2;
TrigToExp[Sin[sym_Symbol]] := E^(-I sym)/2 + E^(I sym)/2;
TrigToExp[a_] := (Print["Unsupported call to TrigToExp", a];a);
Attributes[TrigToExp] = {Listable, Protected};
