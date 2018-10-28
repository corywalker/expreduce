// Package streammanager keeps track of open streams and allows for reading/writing to them.
package streammanager

import (
	"io"
	"os"

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

// WriteString writes the toWrite string into the stream defined by streamName and streamIndex.
func (sm streamManagerImpl) WriteString(streamName string, streamIndex int64, toWrite string) bool {
	key := streamKey{id: streamIndex, name: streamName}
	writer, hasWriter := sm.openStreams[key]
	if !hasWriter {
		return false
	}
	writer.Write([]byte(toWrite))
	return true
}
