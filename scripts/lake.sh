#!/bin/sh
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
export ELAN_HOME="$project_dir/.tooling/elan"
cd "$project_dir"
exec lake "$@"
