package expreduce

func getStatsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{Name: "NormalDistribution"})
	defs = append(defs, Definition{Name: "LogNormalDistribution"})
	defs = append(defs, Definition{Name: "PDF"})
	return
}
