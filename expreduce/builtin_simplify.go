package expreduce

func GetSimplifyDefinitions() (defs []Definition) {
	defs = append(defs, Definition{Name: "Simplify"})
	defs = append(defs, Definition{
		Name: "FullSimplify",
		OmitDocumentation: true,
	})
	return
}
