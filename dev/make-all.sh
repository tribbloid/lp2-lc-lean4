#!/usr/bin/env bash

FWDIR="$(
  cd "$(dirname "$0")"/.. || exit
  pwd
)"
DATE=$(date +%Y-%m-%dT%H:%M:%S%z)

cd "$FWDIR"

rm -R ".metals" # Windows/Linux build cache are not mutually compatible

lake build Lp2lc Tests Docs && \
sbt --server compile
