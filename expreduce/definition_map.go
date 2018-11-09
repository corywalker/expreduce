package expreduce

import (
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"github.com/orcaman/concurrent-map"
)

type threadSafeDefinitionMap struct {
	internalMap cmap.ConcurrentMap
}

func newDefinitionMap() *threadSafeDefinitionMap {
	var dm threadSafeDefinitionMap
	dm.internalMap = cmap.New()
	return &dm
}

func (dm threadSafeDefinitionMap) Set(key string, value expreduceapi.Def) {
	dm.internalMap.Set(key, value)
}

func (dm threadSafeDefinitionMap) Get(key string) (expreduceapi.Def, bool) {
	if !dm.internalMap.Has(key) {
		return expreduceapi.Def{}, false
	}
	value, ok := dm.internalMap.Get(key)
	return value.(expreduceapi.Def), ok
}

func (dm threadSafeDefinitionMap) GetDef(key string) expreduceapi.Def {
	value, ok := dm.Get(key)
	if !ok {
		panic("Reading missing value in GetDef()!")
	}
	return value
}

func (dm threadSafeDefinitionMap) LockKey(key string) {
	shard := dm.internalMap.GetShard(key)
	shard.Lock()
}

func (dm threadSafeDefinitionMap) UnlockKey(key string) {
	shard := dm.internalMap.GetShard(key)
	shard.Unlock()
}

func (dm threadSafeDefinitionMap) Keys() []string {
	return dm.internalMap.Keys()
}

func (dm threadSafeDefinitionMap) CopyDefs() expreduceapi.DefinitionMap {
	out := newDefinitionMap()
	for mapTuple := range dm.internalMap.IterBuffered() {
		k, v := mapTuple.Key, mapTuple.Val.(expreduceapi.Def)
		newDef := expreduceapi.Def{}
		for _, dv := range v.Downvalues {
			newDv := expreduceapi.DownValue{
				Rule:        dv.Rule.DeepCopy().(expreduceapi.ExpressionInterface),
				Specificity: dv.Specificity,
			}
			newDef.Downvalues = append(newDef.Downvalues, newDv)
		}
		out.Set(k, newDef)
	}
	return out
}
