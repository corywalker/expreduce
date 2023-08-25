set -e

echo "Generating files..."
go generate expreduce/builtin.go
echo "Running lint..."
golangci-lint run
echo "Running tests..."
go test -v ./...
go test -v -race ./... -run Concurrency
echo "SUCCESS!"