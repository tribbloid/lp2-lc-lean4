#!/bin/bash

lake update && lake build # && lake test

if command -v markdownlint >/dev/null 2>&1; then markdownlint '**/*.md'; fi
