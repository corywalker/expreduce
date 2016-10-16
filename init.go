package cas

func InitCAS(es *EvalState) {
	EvalInterp("Total[lmatch__List] := Apply[Plus, lmatch]", es)
	EvalInterp("Mean[lmatch__List] := Total[lmatch]/Length[lmatch]", es)
	// Serious problems lurk here.
	EvalInterp("Table[amatch_, bmatch_Integer] := Table[amatch, {i, 1, bmatch}]", es)

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
}
