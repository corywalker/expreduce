package logging

import (
	"os"
	"sync"

	gologging "github.com/op/go-logging"
)

var format = gologging.MustStringFormatter(
	`%{color}%{time:15:04:05.000} %{callpath} ▶ %{id:03x}%{color:reset} %{message}`,
)
var goLoggingMutex = &sync.Mutex{}

// CASLogger keeps track of logging state for the language.
type CASLogger struct {
	_log        *gologging.Logger
	leveled     gologging.LeveledBackend
	debugState  bool
	isProfiling bool
}

// Debugf logs a debug-level message.
func (cl *CASLogger) Debugf(fmt string, args ...interface{}) {
	if cl.debugState {
		//cl._log.Debugf(cl.pre() + fmt, args...)
		cl._log.Debugf(fmt, args...)
	}
}

// Infof logs an info-level message.
func (cl *CASLogger) Infof(fmt string, args ...interface{}) {
	if cl.debugState {
		//cl._log.Infof(cl.pre() + fmt, args...)
		cl._log.Infof(fmt, args...)
	}
}

// Errorf logs an error-level message.
func (cl *CASLogger) Errorf(fmt string, args ...interface{}) {
	cl._log.Errorf(fmt, args...)
}

// DebugOn turns on debug features.
func (cl *CASLogger) DebugOn(level gologging.Level) {
	cl.leveled.SetLevel(level, "")
	cl.debugState = true
	cl.SetProfiling(true)
}

// DebugOff turns off debug features.
func (cl *CASLogger) DebugOff() {
	cl.leveled.SetLevel(gologging.ERROR, "")
	cl.debugState = false
	cl.SetProfiling(false)
}

// SetDebugState turns the ability to log off and on.
func (cl *CASLogger) SetDebugState(newState bool) {
	cl.debugState = newState
}

// IsProfiling returns if the interpreter should be profiling.
func (cl *CASLogger) IsProfiling() bool {
	return cl.isProfiling
}

// SetProfiling sets if the interpreter should be profiling.
func (cl *CASLogger) SetProfiling(profiling bool) {
	cl.isProfiling = profiling
}

// SetUpLogging initializes this logging state.
func (cl *CASLogger) SetUpLogging() {
	// go-logging appears to not be thread safe, so we have a mutex when
	// configuring the logging.
	goLoggingMutex.Lock()
	cl._log = gologging.MustGetLogger("example")
	backend := gologging.NewLogBackend(os.Stderr, "", 0)
	formatter := gologging.NewBackendFormatter(backend, format)
	cl.leveled = gologging.AddModuleLevel(formatter)
	gologging.SetBackend(cl.leveled)
	goLoggingMutex.Unlock()
}
