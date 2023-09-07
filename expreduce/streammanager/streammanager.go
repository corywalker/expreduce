// Package streammanager keeps track of open streams and allows for reading/writing to them.
package streammanager

import (
	"io"
	"os"
	"sort"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type streamKey struct {
	id   int64
	name string
}
type streamMap map[streamKey]io.Writer

type streamManagerImpl struct {
	openStreams streamMap
}

// NewStreamManager returns an object that can keep track of open streams.
func NewStreamManager() expreduceapi.StreamManager {
	sm := streamManagerImpl{}
	sm.openStreams = make(streamMap)
	sm.openStreams[streamKey{id: 1, name: "stdout"}] = os.Stdout
	sm.openStreams[streamKey{id: 2, name: "stderr"}] = os.Stderr
	return &sm
}

func (sm streamManagerImpl) fillMissingIndex(key *streamKey) {
	if key.id == -1 {
		if key.name == "stdout" {
			key.id = 1
		} else if key.name == "stdin" {
			key.id = 2
		}
	}
}

// WriteString writes the toWrite string into the stream defined by streamName and streamIndex.
func (sm streamManagerImpl) WriteString(
	streamName string,
	streamIndex int64,
	toWrite string,
) bool {
	key := streamKey{id: streamIndex, name: streamName}
	sm.fillMissingIndex(&key)
	writer, hasWriter := sm.openStreams[key]
	if !hasWriter {
		return false
	}
	_, err := writer.Write([]byte(toWrite))
	return err == nil
}

func (sm streamManagerImpl) AsExpr() expreduceapi.Ex {
	res := atoms.E(atoms.S("List"))

	keys := make([]streamKey, 0)
	for k := range sm.openStreams {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(i, j int) bool {
		return keys[i].id < keys[j].id
	})

	for _, k := range keys {
		res.AppendEx(atoms.E(
			atoms.S("OutputStream"),
			atoms.NewString(k.name),
			atoms.NewInt(k.id),
		))
	}

	return res
}
