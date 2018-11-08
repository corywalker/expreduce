package expreduce

func getTestsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:              "ExpreduceMiscTests",
		OmitDocumentation: true,
		expreduceSpecific: true,
	})
	return
}
