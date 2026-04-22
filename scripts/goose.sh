#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "$DIR/.."

go tool perennial-cli goose --config goose-kubernetes.toml
go tool perennial-cli goose --config goose-kubernetes-model.toml
go tool perennial-cli goose --config goose-controllers.toml
