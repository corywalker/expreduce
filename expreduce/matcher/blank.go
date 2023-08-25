package matcher

import (
	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func isBlankTypeOnly(e expreduceapi.Ex) bool {
	asPattern, patternOk := atoms.HeadAssertion(e, "System`Pattern")
	if patternOk {
		_, blankOk := atoms.HeadAssertion(
			asPattern.GetParts()[2],
			"System`Blank",
		)
		_, bsOk := atoms.HeadAssertion(
			asPattern.GetParts()[2],
			"System`BlankSequence",
		)
		_, bnsOk := atoms.HeadAssertion(
			asPattern.GetParts()[2],
			"System`BlankNullSequence",
		)
		if blankOk || bsOk || bnsOk {
			return true
		}
	}
	_, blankOk := atoms.HeadAssertion(e, "System`Blank")
	_, bsOk := atoms.HeadAssertion(e, "System`BlankSequence")
	_, bnsOk := atoms.HeadAssertion(e, "System`BlankNullSequence")
	if blankOk || bsOk || bnsOk {
		return true
	}
	return false
}

func isBlankTypeCapturing(
	e expreduceapi.Ex,
	target expreduceapi.Ex,
	head expreduceapi.Ex,
	pm *PDManager,
	cl expreduceapi.LoggingInterface,
) (bool, *PDManager) {
	// Similar to IsBlankType, but will capture target into es.patternDefined
	// if there is a valid match.
	asPattern, patternOk := atoms.HeadAssertion(e, "System`Pattern")
	if patternOk {
		asBlank, blankOk := atoms.HeadAssertion(
			asPattern.GetParts()[2],
			"System`Blank",
		)
		asBS, bsOk := atoms.HeadAssertion(
			asPattern.GetParts()[2],
			"System`BlankSequence",
		)
		asBNS, bnsOk := atoms.HeadAssertion(
			asPattern.GetParts()[2],
			"System`BlankNullSequence",
		)
		if blankOk || bsOk || bnsOk {
			parts := []expreduceapi.Ex{}
			if blankOk {
				parts = asBlank.GetParts()
			} else if bsOk {
				parts = asBS.GetParts()
			} else if bnsOk {
				parts = asBNS.GetParts()
			}
			//if len(parts) < 2 {
			//return true, pm
			//}
			cl.Debugf("%v %v", parts, len(parts))
			var matchesHead bool
			if len(parts) < 2 {
				matchesHead = true
			} else {
				matchesHead = atoms.IsSameQ(head, parts[1])
			}
			cl.Debugf("%v", matchesHead)
			if matchesHead {
				sAsSymbol, sAsSymbolOk := asPattern.GetParts()[1].(*atoms.Symbol)
				if sAsSymbolOk {
					// TODO: we should handle matches with BlankSequences
					// differently here.
					toMatch, ispd := pm.patternDefined[sAsSymbol.Name]
					if !ispd {
						toMatch = target
						pm.lazyMakeMap()
						pm.patternDefined[sAsSymbol.Name] = target
					}
					if !atoms.IsSameQ(toMatch, target) {
						return false, pm
					}
				}
				return true, pm
			}
			return false, pm
		}
	}
	asBlank, blankOk := atoms.HeadAssertion(e, "System`Blank")
	asBS, bsOk := atoms.HeadAssertion(e, "System`BlankSequence")
	asBNS, bnsOk := atoms.HeadAssertion(e, "System`BlankNullSequence")
	if blankOk || bsOk || bnsOk {
		parts := []expreduceapi.Ex{}
		if blankOk {
			parts = asBlank.GetParts()
		} else if bsOk {
			parts = asBS.GetParts()
		} else if bnsOk {
			parts = asBNS.GetParts()
		}
		if len(parts) < 2 {
			return true, pm
		}
		return atoms.IsSameQ(head, parts[1]), pm
	}
	return false, pm
}

func blankNullSequenceToBlank(
	bns expreduceapi.ExpressionInterface,
) expreduceapi.ExpressionInterface {
	if len(bns.GetParts()) < 2 {
		return atoms.NewExpression(
			[]expreduceapi.Ex{atoms.NewSymbol("System`Blank")},
		)
	}
	return atoms.NewExpression(
		[]expreduceapi.Ex{atoms.NewSymbol("System`Blank"), bns.GetParts()[1]},
	)
}

func blankSequenceToBlank(
	bs expreduceapi.ExpressionInterface,
) expreduceapi.ExpressionInterface {
	if len(bs.GetParts()) < 2 {
		return atoms.NewExpression(
			[]expreduceapi.Ex{atoms.NewSymbol("System`Blank")},
		)
	}
	return atoms.NewExpression(
		[]expreduceapi.Ex{atoms.NewSymbol("System`Blank"), bs.GetParts()[1]},
	)
}
