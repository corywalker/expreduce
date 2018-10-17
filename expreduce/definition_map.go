package expreduce

import (
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"github.com/orcaman/concurrent-map"
)

type ThreadSafeDefinitionMap struct {
	internalMap cmap.ConcurrentMap
}

func newDefinitionMap() ThreadSafeDefinitionMap {
	var dm ThreadSafeDefinitionMap
	dm.internalMap = cmap.New()
	return dm
}

func (dm ThreadSafeDefinitionMap) Set(key string, value expreduceapi.Def) {
	dm.internalMap.Set(key, value)
}

func (dm ThreadSafeDefinitionMap) Get(key string) (expreduceapi.Def, bool) {
	if !dm.internalMap.Has(key) {
		return expreduceapi.Def{}, false
	}
	value, ok := dm.internalMap.Get(key)
	return value.(expreduceapi.Def), ok
}

func (dm ThreadSafeDefinitionMap) GetDef(key string) expreduceapi.Def {
	value, ok := dm.Get(key)
	if !ok {
		panic("Reading missing value in GetDef()!")
	}
	return value
}

func (dm ThreadSafeDefinitionMap) LockKey(key string) {
	shard := dm.internalMap.GetShard(key)
	shard.Lock()
}

func (dm ThreadSafeDefinitionMap) UnlockKey(key string) {
	shard := dm.internalMap.GetShard(key)
	shard.Unlock()
}

func (dm ThreadSafeDefinitionMap) CopyDefs() expreduceapi.DefinitionMap {
	out := newDefinitionMap()
	for mapTuple := range dm.internalMap.IterBuffered() {
		k, v := mapTuple.Key, mapTuple.Val.(expreduceapi.Def)
		newDef := expreduceapi.Def{}
		for _, dv := range v.downvalues {
			newDv := DownValue{
				rule:        dv.rule.DeepCopy().(*expreduceapi.Expression),
				specificity: dv.specificity,
			}
			newDef.downvalues = append(newDef.downvalues, newDv)
		}
		out.Set(k, newDef)
	}
	return out
}
