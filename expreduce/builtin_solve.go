package expreduce

func GetSolveDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Solve",
		Details: "!!! warning \"Under development\"\n" +
			"	This function is under development, and as such will be incomplete and inaccurate. The function currently only knows how to solve a few example forms of equations.",
	})
	defs = append(defs, Definition{Name: "ConditionalExpression"})
	return
}
