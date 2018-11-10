//go:generate go run ../utils/gensnapshots/gensnapshots.go -rubi_snapshot_location=./rubi_snapshot.expred

package expreduce

func getRubiDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:              "LoadRubi",
		expreduceSpecific: true,
	})
	defs = append(defs, Definition{
		Name:              "LoadRubiSnapshot",
		expreduceSpecific: true,
	})
	defs = append(defs, Definition{
		Name:              "SaveRubiSnapshot",
		expreduceSpecific: true,
	})
	return
}
