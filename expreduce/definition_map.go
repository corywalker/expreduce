package expreduce

type definitionMapInternal map[string]Def

type definitionMap struct {
	internalMap	definitionMapInternal
}

func newDefinitionMap() definitionMap {
	var dm definitionMap
	dm.internalMap = make(definitionMapInternal)
	return dm
}

func (dm definitionMap) Set(key string, value Def) {
	dm.internalMap[key] = value
}

func (dm definitionMap) Get(key string) (Def, bool) {
	value, ok := dm.internalMap[key]
	return value, ok
}

func (dm definitionMap) GetDef(key string) Def {
	value, ok := dm.Get(key)
	if !ok {
		panic("Reading missing value in GetDef()!")
	}
	return value
}

func (dm definitionMap) CopyDefs() definitionMap {
	out := newDefinitionMap()
	for k, v := range dm.internalMap {
		newDef := Def{}
		for _, dv := range v.downvalues {
			newDv := DownValue{
				rule:        dv.rule.DeepCopy().(*Expression),
				specificity: dv.specificity,
			}
			newDef.downvalues = append(newDef.downvalues, newDv)
		}
		out.Set(k, newDef)
	}
	return out
}
