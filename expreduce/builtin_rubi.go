package expreduce

func GetRubiDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "LoadRubi",
		ExpreduceSpecific: true,
	})
	return
}
