#!/usr/bin/env bash
set -euo pipefail

lake build

if grep -RInE --include='*.lean' '(^|[^[:alnum:]_])(sorry|admit|axiom|unsafe)([^[:alnum:]_]|$)' Spinor Spinor.lean; then
  echo "Forbidden proof-hole token found in Lean source." >&2
  exit 1
fi
