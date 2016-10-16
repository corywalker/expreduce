go tool pprof cas.test cpu.prof
go test -cpuprofile cpu.prof -memprofile mem.prof -bench .
