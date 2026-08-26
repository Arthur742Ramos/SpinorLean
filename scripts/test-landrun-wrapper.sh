#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
wrapper="$repository_root/scripts/landrun-wrapper.sh"
fake="$repository_root/scripts/fake-landrun.sh"

PALOMAR_LANDRUN_BIN="$fake" "$wrapper" --ro "$repository_root" sh -c 'exit 0'

set +e
rejected_output=$(PALOMAR_LANDRUN_BIN="$fake" "$wrapper" --unrestricted-net sh -c 'exit 0' 2>&1)
rejected_status=$?
set -e
if [ "$rejected_status" -ne 2 ] || [[ "$rejected_output" != *"switches off part of the sandbox"* ]]; then
  echo "error: Landrun wrapper accepted an unrestricted option" >&2
  exit 1
fi

set +e
missing_value_output=$(PALOMAR_LANDRUN_BIN="$fake" "$wrapper" --ro 2>&1)
missing_value_status=$?
set -e
if [ "$missing_value_status" -ne 2 ] || [[ "$missing_value_output" != *"missing its value"* ]]; then
  echo "error: Landrun wrapper accepted a missing option value" >&2
  exit 1
fi

echo "Landrun wrapper policy checks passed."
