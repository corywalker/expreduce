package expreduce

import (
	"github.com/orcaman/concurrent-map"
)

type definitionMap struct {
	internalMap	cmap.ConcurrentMap
}

func newDefinitionMap() definitionMap {
	var dm definitionMap
	dm.internalMap = cmap.New()
	return dm
}

func (dm definitionMap) Set(key string, value Def) {
	dm.internalMap.Set(key, value)
}

func (dm definitionMap) Get(key string) (Def, bool) {
	if !dm.internalMap.Has(key) {
		return Def{}, false
	}
	value, ok := dm.internalMap.Get(key)
	return value.(Def), ok
}

func (dm definitionMap) GetDef(key string) Def {
	value, ok := dm.Get(key)
	if !ok {
		panic("Reading missing value in GetDef()!")
	}
	return value
}

func (dm definitionMap) LockKey(key string) {
	shard := dm.internalMap.GetShard(key)
	shard.Lock()
}

func (dm definitionMap) UnlockKey(key string) {
	shard := dm.internalMap.GetShard(key)
	shard.Unlock()
}

func (dm definitionMap) CopyDefs() definitionMap {
	out := newDefinitionMap()
	for mapTuple := range dm.internalMap.IterBuffered() {
		k, v := mapTuple.Key, mapTuple.Val.(Def)
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
