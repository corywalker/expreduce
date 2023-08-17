//go:generate go run ../utils/gensnapshots/gensnapshots.go -rubi_snapshot_location=./rubi_snapshot/rubi_snapshot.expred
//go:generate go-bindata -pkg rubi_snapshot -o rubi_snapshot/rubi_resources.go -nocompress -nometadata rubi_snapshot/rubi_snapshot.expred

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
		Name:              "LoadRubiBundledSnapshot",
		expreduceSpecific: true,
	})
	defs = append(defs, Definition{
		Name:              "SaveRubiSnapshot",
		expreduceSpecific: true,
	})
	return
}
