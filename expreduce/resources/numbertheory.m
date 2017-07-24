PrimeQ::usage = "`PrimeQ[n]` returns True if `n` is prime, False otherwise.";
Attributes[PrimeQ] = {Listable, Protected};
Tests`PrimeQ = {
    ESimpleExamples[
        ESameTest[True, PrimeQ[5]],
        ESameTest[False, PrimeQ[100]],
        ESameTest[True, PrimeQ[982451653]],
        ESameTest[True, PrimeQ[-2]]
    ], EFurtherExamples[
        EComment["`PrimeQ` only works for Integers:"],
        ESameTest[False, PrimeQ[5.]]
    ], ETests[
        ESameTest[False, PrimeQ[0]],
        ESameTest[False, PrimeQ[1]],
        ESameTest[False, PrimeQ[-1]],
        ESameTest[False, PrimeQ[0.5]]
    ]
};

GCD::usage = "`GCD[n1, n2, ...]` finds the greatest common denominator of the integer inputs.";
(* Eventually we should not need the rest___ term. GCD is Flat. *)
GCD[Rational[a_, b_], Rational[c_, d_], rest___] := 
  GCD[GCD[a*d, c*b]/(b*d), rest];
GCD[Rational[a_, b_], c_Integer, rest___] := 
  GCD[GCD[a, c*b]/b, rest];
(*This deviates from how it should be done*)
GCD[a_Rational] := Abs[a];
Attributes[GCD] = {Flat, Listable, OneIdentity, Orderless, Protected};
Tests`GCD = {
    ESimpleExamples[
        ESameTest[3, GCD[9, 6]],
        ESameTest[5, GCD[100, 30, 15]]
    ], ETests[
        ESameTest[1, GCD[9, 2]],
        ESameTest[10, GCD[100, 0, 10]],
        ESameTest[3, GCD[9, 3]],
        ESameTest[10, GCD[100, 30, 10]],
        ESameTest[10, GCD[100, 30]],
        ESameTest[1, GCD[100, 30, -1]],
        ESameTest[10, GCD[100, 30, -60]],
        ESameTest[60, GCD[-60, -60, -60]],
        ESameTest[GCD[-60, -60, -0.5], GCD[-60, -60, -0.5]],
        ESameTest[GCD[0.5], GCD[0.5]],
        ESameTest[GCD[1, a], GCD[1, a]],
        ESameTest[GCD[a, a], GCD[a, a]],
        ESameTest[0, GCD[]],
        ESameTest[1, GCD[1]],
        ESameTest[GCD[a], GCD[a]],
        ESameTest[1000, GCD[1000]],
        ESameTest[5, GCD[5, 15]],
        ESameTest[5, GCD[5, 15, 30]],
        ESameTest[5, GCD[10, 20, 25]],
        ESameTest[1, GCD[5, 14]],
        ESameTest[5/2, GCD[5/2, 15/2]],
        ESameTest[5/3, GCD[5/3, 5]],
        ESameTest[GCD[5/3,a], GCD[5/3, a]],
        ESameTest[GCD[a,b,c], GCD[a, b, c]],
        ESameTest[0, GCD[0]],
        ESameTest[0, GCD[0, 0]],
        ESameTest[99, GCD[-99]],
        ESameTest[5/2, GCD[-5/2]],
        ESameTest[5, GCD[10, -20, 25]],
        ESameTest[1, GCD[5, -14]],
        ESameTest[5/2, GCD[5/2, -15/2]],
        ESameTest[5/2, GCD[5/2, -15/2, -15/2]],
        ESameTest[5/3, GCD[-5/3, -5]],
        ESameTest[5/3, GCD[-5/3, -5]],
        ESameTest[GCD[-(5/3),a], GCD[-5/3, a]]
    ]
};

LCM::usage = "`LCM[n1, n2, ...]` finds the least common multiple of the inputs.";
LCM[a_?NumberQ, b_?NumberQ] := (a/GCD[a, b])*b;
LCM[a_?NumberQ, b_?NumberQ, rest__?NumberQ] := 
  LCM[LCM[a, b], rest];
Attributes[LCM]={Flat,Listable,OneIdentity,Orderless,Protected};
Tests`LCM = {
    ESimpleExamples[
        ESameTest[70, LCM[5, 14]],
        ESameTest[2380, LCM[5, 14, 68]],
        ESameTest[2/3, LCM[2/3, 1/3]],
        ESameTest[10/3, LCM[2/3, 1/3, 5/6]],
        ESameTest[30, LCM[2/3, 1/3, 5/6, 3]],
        ESameTest[{2/3,10/3,6}, LCM[2/3, {1/3, 5/6, 3}]]
    ], ETests[
        ESameTest[{10/3,10/3,30}, LCM[2/3, {1/3, 5/6, 3}, 5/6]],
        ESameTest[LCM[a,b], LCM[a, b]],
        ESameTest[LCM[a,b,c], LCM[a, b, c]],
        ESameTest[LCM[5,6,c], LCM[5, 6, c]]
    ]
};

Mod::usage = "`Mod[x, y]` finds the remainder when `x` is divided by `y`.";
(* Factor out numeric constants like Pi: *)
Mod[a_Integer*c_?NumericQ,b_Integer*c_?NumericQ] := c * Mod[a,b];
Attributes[Mod] = {Listable, NumericFunction, ReadProtected, Protected};
Tests`Mod = {
    ESimpleExamples[
        ESameTest[2, Mod[5,3]],
        ESameTest[0, Mod[0,3]],
        ESameTest[Indeterminate, Mod[2,0]],
        ESameTest[Pi, Mod[-2 Pi,3 Pi]]
    ], ETests[
        ESameTest[1, Mod[-5,3]],
        ESameTest[Mod[a,3], Mod[a,3]],
        ESameTest[Indeterminate, Mod[0,0]],
        ESameTest[Mod[2,a], Mod[2,a]],
        ESameTest[Mod[0,a], Mod[0,a]]
    ], EKnownFailures[
        ESameTest[1.5, Mod[1.5,3]],
        ESameTest[0., Mod[2,0.5]]
    ]
};

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
