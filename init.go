package cas

func InitCAS(es *EvalState) {
	// Set Attributes
	EvalInterp("Attributes[MemberQ] = {Protected}", es)
	EvalInterp("Attributes[Attributes] = {HoldAll, Listable, Protected}", es)
	EvalInterp("Attributes[Times] = {Orderless}", es)
	EvalInterp("Attributes[Plus] = {Orderless}", es)
	EvalInterp("Attributes[Set] = {HoldFirst}", es)
	EvalInterp("Attributes[Pattern] = {HoldFirst}", es)
	EvalInterp("Attributes[SetDelayed] = {HoldAll}", es)
	EvalInterp("Attributes[Table] = {HoldAll}", es)
	EvalInterp("Attributes[Clear] = {HoldAll}", es)
	EvalInterp("Attributes[Timing] = {HoldAll}", es)
	EvalInterp("Attributes[Hold] = {HoldAll}", es)
	EvalInterp("Attributes[_] = List[]", es)

	// Define functions
	EvalInterp("Total[lmatch__List] := Apply[Plus, lmatch]", es)
	EvalInterp("Mean[lmatch__List] := Total[lmatch]/Length[lmatch]", es)
	EvalInterp("Table[amatch_, bmatch_Integer] := Table[amatch, {i, 1, bmatch}]", es)
	EvalInterp("RandomReal[{minmatch_, maxmatch_}] := RandomReal[]*(maxmatch - minmatch) + minmatch", es)
	EvalInterp("RandomReal[maxmatch_] := RandomReal[]*maxmatch", es)
	EvalInterp("PowerExpand[expmatch_] := expmatch //. {Log[x_ y_]:>Log[x]+Log[y],Log[x_^k_]:>k Log[x]}", es)
	EvalInterp("Multinomial[seqmatch___] := Factorial[Apply[Plus, {seqmatch}]] / Apply[Times, Map[Factorial, {seqmatch}]]", es)

	// Calculus
	EvalInterp("D[x_,x_]:=1", es)
	EvalInterp("D[a_,x_]:=0", es)
	EvalInterp("D[a_+b__,x_]:=D[a,x]+D[Plus[b],x]", es)
	EvalInterp("D[a_ b__,x_]:=D[a,x] b+a D[Times[b],x]", es)
	// The times operator is needed here. Whitespace precedence is messed up
	EvalInterp("D[a_^(b_), x_]:= a^b*(D[b,x] Log[a]+D[a,x]/a*b)", es)
	EvalInterp("D[Log[a_], x_]:= D[a, x]/a", es)
	EvalInterp("D[Sin[a_], x_]:= D[a,x] Cos[a]", es)
	EvalInterp("D[Cos[a_], x_]:=-D[a,x] Sin[a]", es)

	// Might need to be implemented in code. Try running Integrate[-10x, {x, 1, 5}]
	// with this
	//EvalInterp("Integrate[a_,{x_Symbol,start_Integer,end_Integer}]:=ReplaceAll[Integrate[a, x],x->end] - ReplaceAll[Integrate[a, x],x->start]", es)
	EvalInterp("Integrate[a_Integer,x_Symbol]:=a*x", es)
	EvalInterp("Integrate[a_Integer*b_,x_Symbol]:=a*Integrate[b,x]", es)
	// An outstanding bug is requiring me to write this as amatch and bmatch
	// instead of a and b, because doing the latter causes issues with
	// Integrate[a+b+c,x]
	EvalInterp("Integrate[amatch_+bmatch__,x_Symbol]:=Integrate[amatch,x]+Integrate[Plus[bmatch],x]", es)
	EvalInterp("Integrate[x_Symbol^n_Integer, x_Symbol]:=x^(n+1)/(n+1)", es)
	EvalInterp("Integrate[x_Symbol^n_Rational, x_Symbol]:=x^(n+1)/(n+1)", es)

	// Define function simplifications
	EvalInterp("Sum[imatch_Symbol, {imatch_Symbol, 0, nmatch_Integer}] := 1/2*nmatch*(1 + nmatch)", es)
	EvalInterp("Sum[imatch_Symbol, {imatch_Symbol, 1, nmatch_Integer}] := 1/2*nmatch*(1 + nmatch)", es)
	EvalInterp("Sum[imatch_Symbol, {imatch_Symbol, 0, nmatch_Symbol}] := 1/2*nmatch*(1 + nmatch)", es)
	EvalInterp("Sum[imatch_Symbol, {imatch_Symbol, 1, nmatch_Symbol}] := 1/2*nmatch*(1 + nmatch)", es)

	// Simplify expressions with Infinity
	EvalInterp("Plus[Infinity, _Integer, rest___] := Infinity + rest", es)
	EvalInterp("Plus[Infinity, _Real, rest___] := Infinity + rest", es)
	EvalInterp("Plus[-Infinity, _Integer, rest___] := -Infinity + rest", es)
	EvalInterp("Plus[-Infinity, _Real, rest___] := -Infinity + rest", es)
	EvalInterp("Plus[Infinity, -Infinity, rest___] := Indeterminate + rest", es)
	EvalInterp("(1/Infinity) := 0", es)

	// Multiplication definitions
	EvalInterp("Times[a_, a_, rest___] := a^2 * rest", es)
	EvalInterp("Times[a_^n_, a_, rest___] := a^(n+1) * rest", es)
	EvalInterp("Times[a_^n_, a_^m_, rest___] := a^(n+m) * rest", es)
	EvalInterp("Times[den_Integer^(-1), num_Integer, rest___] := Rational[num,den] * rest", es)
	EvalInterp("Times[a_, Power[a_, -1], rest___] := rest", es)
	EvalInterp("Times[a_^b_, Power[a_, -1], rest___] := a^(b-1) * rest", es)
	//EvalInterp("Times[a_^b_, Power[a_^c_, -1], rest___] := a^(b-c) * rest", es)
	//EvalInterp("Times[a_^b_, Power[a_, Power[c_, -1]], rest___] := a^(b-c) * rest", es)

	// Addition definitions
	//EvalInterp("(amatch_ - amatch_) := 0", es)
	//EvalInterp("((c1match_Integer*matcha_) + (c2match_Integer*matcha_)) := (c1match+c2match)*matcha", es)
	//EvalInterp("((c1match_Integer*matcha_) + matcha_) := (c1match+1)*matcha", es)
	//EvalInterp("(matcha_ + matcha_) := 2*matcha", es)
	//EvalInterp("((c1match_Integer*matcha_) + matcha_) := (c1match+1)*matcha", es)
	//EvalInterp("((c1match_Real*matcha_) + (c2match_Integer*matcha_)) := (c1match+c2match)*matcha", es)

	// Simplify nested exponents
	//EvalInterp("((matcha_^matchb_Integer)^matchc_Integer) := matcha^(matchb*matchc)", es)
	//EvalInterp("((matcha_^matchb_Real)^matchc_Integer) := matcha^(matchb*matchc)", es)

	// Power definitions
	EvalInterp("Power[Times[Except[_Symbol, first_], inner___], pow_] := first^pow*Power[Times[inner],pow]", es)
	EvalInterp("Power[Times[first_, inner___], Except[_Symbol, pow_]] := first^pow*Power[Times[inner],pow]", es)
	EvalInterp("(matcha_^matchb_ / matcha_^matchc_) := matcha^(matchb-matchc)", es)

	// System initialization
	EvalInterp("SeedRandom[UnixTime[]]", es)
}
