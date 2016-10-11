package cas

func InitCAS(es *EvalState) {
	EvalInterp("Total[lmatch__List] := Apply[Plus, lmatch]", es)
	EvalInterp("Mean[lmatch__List] := Total[lmatch]/Length[lmatch]", es)
	// Serious problems lurk here.
	//EvalInterp("Table[amatch_, bmatch_Integer] := Table[amatch, {i, 1, bmatch}]", es)

	EvalInterp("Attributes[MemberQ] = {Protected}", es)
	EvalInterp("Attributes[Attributes] = {HoldAll, Listable, Protected}", es)
	EvalInterp("Attributes[_] = List[]", es)
}
