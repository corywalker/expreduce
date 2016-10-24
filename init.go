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

	// Define function simplifications
	EvalInterp("Sum[imatch_Symbol, {imatch_Symbol, 0, nmatch_Integer}] := 1/2*nmatch*(1 + nmatch)", es)
	EvalInterp("Sum[imatch_Symbol, {imatch_Symbol, 1, nmatch_Integer}] := 1/2*nmatch*(1 + nmatch)", es)
	EvalInterp("Sum[imatch_Symbol, {imatch_Symbol, 0, nmatch_Symbol}] := 1/2*nmatch*(1 + nmatch)", es)
	EvalInterp("Sum[imatch_Symbol, {imatch_Symbol, 1, nmatch_Symbol}] := 1/2*nmatch*(1 + nmatch)", es)

	// System initialization
	EvalInterp("SeedRandom[UnixTime[]]", es)
}
