#!/bin/bash

set -e

go generate
go test
