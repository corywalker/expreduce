package cas

func InitCAS(es *EvalState) {
	// System initialization
	EvalInterp("SeedRandom[UnixTime[]]", es)
}
