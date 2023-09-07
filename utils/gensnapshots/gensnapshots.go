package main

import (
	"flag"

	"github.com/corywalker/expreduce/expreduce"
	"github.com/corywalker/expreduce/expreduce/atoms"
)

var rubiSnapshotLocation = flag.String(
	"rubi_snapshot_location",
	"/tmp/theRubiSnapshot.expred",
	"the location to write the Rubi snapshot",
)

func main() {
	flag.Parse()

	es := expreduce.NewEvalState()

	es.Eval(atoms.E(
		atoms.S("LoadRubi"),
	))
	res := es.Eval(atoms.E(
		atoms.S("SaveRubiSnapshot"),
		atoms.NewString(*rubiSnapshotLocation),
	))
	if !atoms.IsSameQ(res, atoms.S("Null")) {
		panic("Unexpected response from SaveRubiSnapshot[]!")
	}
}
