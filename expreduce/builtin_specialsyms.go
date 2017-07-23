package expreduce

func getSpecialSymsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Infinity",
	})
	defs = append(defs, Definition{
		Name: "ComplexInfinity",
	})
	defs = append(defs, Definition{
		Name: "Indeterminate",
	})
	defs = append(defs, Definition{
		Name: "Pi",
	})
	defs = append(defs, Definition{
		Name: "E",
	})
	return
}
