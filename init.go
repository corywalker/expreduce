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
	// The following line hangs with: D[bar+foo+bar,bar]
	EvalInterp("D[a_+b__,x_]:=D[a,x]+D[Plus[b],x]", es)
	EvalInterp("D[a_ b__,x_]:=D[a,x] b+a D[Times[b],x]", es)
	// The times operator is needed here. Whitespace precedence is messed up
	EvalInterp("D[a_^(b_), x_]:= a^b*(D[b,x] Log[a]+D[a,x]/a*b)", es)
	EvalInterp("D[Log[a_], x_]:= D[a, x]/a", es)
	EvalInterp("D[Sin[a_], x_]:= D[a,x] Cos[a]", es)
	EvalInterp("D[Cos[a_], x_]:=-D[a,x] Sin[a]", es)

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

	//EvalInterp("Times[a_, a_, rest___] := a^2 + rest", es)

	// System initialization
	EvalInterp("SeedRandom[UnixTime[]]", es)
}
