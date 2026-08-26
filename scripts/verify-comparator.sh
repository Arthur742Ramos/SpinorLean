#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$repository_root/.cache/palomar-comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

# These are the current Palomar verifier pins. The Lean4Export revision is the
# exact commit behind the v4.30.0-rc1 release tag, which is this repository's
# pinned Lean toolchain. Keeping the commit explicit makes local replay and CI
# evidence reproducible even if a moving branch changes later.
comparator_commit=68a064109f01c08f47c8edc9f51d6a2bbffaa188
lean4export_commit=fb517af7d71065b28c256348afdf764308acc369
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required_command in cargo git go lake python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done

if [ "$(uname -s)" != "Linux" ] && [ "${PALOMAR_ALLOW_UNSANDBOXED_LOCAL:-}" != "1" ]; then
  echo "error: real Landrun requires Linux Landlock" >&2
  echo "set PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 for an explicit local proof replay without a sandbox" >&2
  exit 1
fi

python3 - "$repository_root/comparator.json" <<'PY'
import json
import pathlib
import sys

config_path = pathlib.Path(sys.argv[1])
try:
    config = json.loads(config_path.read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {config_path}: {error}", file=sys.stderr)
    raise SystemExit(1)

required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
allowed = required | {"definition_names", "enable_nanoda"}
if not isinstance(config, dict) or set(config) - allowed or not required <= set(config):
    print(f"error: {config_path}: Comparator keys are not the Palomar contract", file=sys.stderr)
    raise SystemExit(1)
if config.get("enable_nanoda") is not True:
    print(
        f"error: {config_path}: enable_nanoda must be exactly true; the NanoDa replay is required",
        file=sys.stderr,
    )
    raise SystemExit(1)
if not isinstance(config["theorem_names"], list) or not config["theorem_names"]:
    print(f"error: {config_path}: theorem_names must be nonempty", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config["permitted_axioms"], list) or not set(config["permitted_axioms"]) <= {
    "propext", "Quot.sound", "Classical.choice"
}:
    print(f"error: {config_path}: unsupported permitted axiom", file=sys.stderr)
    raise SystemExit(1)
PY

mkdir -p "$cache_root" "$bin_dir"

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"

if [ ! -f "$lean4export_dir/lean-toolchain" ]; then
  echo "error: pinned Lean4Export revision has no lean-toolchain file" >&2
  exit 1
fi

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$lean4export_toolchain" ]; then
  echo "error: project toolchain $project_toolchain does not match Lean4Export $lean4export_toolchain" >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"

GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"

(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$repository_root"
lake exe cache get

comparator_landrun="$repository_root/scripts/landrun-wrapper.sh"
landrun_binary="$bin_dir/landrun"
if [ "$(uname -s)" != "Linux" ]; then
  landrun_binary="$repository_root/scripts/fake-landrun.sh"
  echo "warning: using the explicit unsandboxed macOS fallback; GitHub CI must provide real Landrun" >&2
fi

PALOMAR_LANDRUN_BIN="$landrun_binary" \
COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
COMPARATOR_LANDRUN="$comparator_landrun" \
  lake env "$comparator_dir/.lake/build/bin/comparator" comparator.json
