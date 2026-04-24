#!/usr/bin/env bash

FWDIR="$(
  cd "$(dirname "$0")"/.. || exit
  pwd
)"
DATE=$(date +%Y-%m-%dT%H:%M:%S%z)

cd "$FWDIR"

lake build
lake build Tests

cd "$FWDIR/Tests"
sbt compile
