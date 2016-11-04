set -e

go test -cpuprofile cpu.prof -memprofile mem.prof -bench . -run Syst
go tool pprof cas.test cpu.prof
