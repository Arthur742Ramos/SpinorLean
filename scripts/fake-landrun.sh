#!/usr/bin/env bash
set -euo pipefail

# Explicitly opt-in local fallback for macOS, whose kernel does not provide
# Landlock. This is not a security boundary and is never used by GitHub CI or
# Palomar's Linux verifier.
while [ "$#" -gt 0 ] && [ "$1" != "--" ]; do
  shift
done

if [ "$#" -eq 0 ]; then
  echo "error: fake Landrun received no command" >&2
  exit 2
fi

shift
exec "$@"
