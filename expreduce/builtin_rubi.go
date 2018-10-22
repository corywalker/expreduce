package expreduce

func getRubiDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:              "LoadRubi",
		expreduceSpecific: true,
	})
	return
}
