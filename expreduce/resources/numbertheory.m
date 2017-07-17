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

EvenQ::usage = "`EvenQ[n]` returns True if `n` is an even integer.";
EvenQ[n_Integer] := Mod[n,2]===0;
Attributes[EvenQ] = {Listable, Protected};
Tests`EvenQ = {
    ESimpleExamples[
        ESameTest[True, EvenQ[6]],
        ESameTest[True, EvenQ[-2]],
        ESameTest[False, EvenQ[1]],
        ESameTest[EvenQ[2.], EvenQ[2.]],
        ESameTest[EvenQ[a], EvenQ[a]]
    ]
};

OddQ::usage = "`OddQ[n]` returns True if `n` is an odd integer.";
OddQ[n_Integer] := Mod[n,2]===1;
Attributes[OddQ] = {Listable, Protected};
Tests`OddQ = {
    ESimpleExamples[
        ESameTest[False, OddQ[6]],
        ESameTest[False, OddQ[-2]],
        ESameTest[True, OddQ[1]],
        ESameTest[OddQ[2.], OddQ[2.]],
        ESameTest[OddQ[a], OddQ[a]]
    ]
};
