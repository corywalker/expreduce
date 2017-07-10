(* Eventually we should not need the rest___ term. GCD is Flat. *)
GCD[Rational[a_, b_], Rational[c_, d_], rest___] := 
  GCD[GCD[a*d, c*b]/(b*d), rest];
GCD[Rational[a_, b_], c_Integer, rest___] := 
  GCD[GCD[a, c*b]/b, rest];
(*This deviates from how it should be done*)
GCD[a_Rational] := Abs[a];

LCM[a_?NumberQ, b_?NumberQ] := (a/GCD[a, b])*b;
LCM[a_?NumberQ, b_?NumberQ, rest__?NumberQ] := 
  LCM[LCM[a, b], rest];
Attributes[LCM]={Flat,Listable,OneIdentity,Orderless,Protected};
