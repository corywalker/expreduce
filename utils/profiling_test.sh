set -e

go test -cpuprofile cpu.prof -memprofile mem.prof -bench .
go tool pprof expreduce.test cpu.prof
