package atoms

import "encoding/gob"

// RegisterGobAtoms performs gob registration for the atoms package.
func RegisterGobAtoms() {
	gob.RegisterName("E", &Expression{})
	gob.RegisterName("S", &Symbol{})
	gob.RegisterName("C", &Complex{})
	gob.RegisterName("I", &Integer{})
	gob.RegisterName("R", &Rational{})
	gob.RegisterName("F", &Flt{})
	gob.RegisterName("T", &String{})
}
