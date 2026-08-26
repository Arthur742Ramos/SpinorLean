#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_file in \
  lean-toolchain lake-manifest.json formalization.yaml Challenge.lean Solution.lean comparator.json LICENSE; do
  if [ ! -f "$required_file" ] || [ -L "$required_file" ]; then
    echo "error: required Palomar file is missing or not regular: $required_file" >&2
    exit 1
  fi
done

python3 - "$repository_root" <<'PY'
import json
import pathlib
import re
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
lakefiles = [
    name for name in ("lakefile.toml", "lakefile.lean")
    if (root / name).exists()
]
if len(lakefiles) != 1:
    raise SystemExit(f"error: project root must contain exactly one Lakefile; found {lakefiles}")

license_pattern = re.compile(
    r"^(?:licen[cs]e|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?$", re.I
)
licenses = [
    path for path in root.iterdir()
    if path.is_file()
    and not path.is_symlink()
    and license_pattern.fullmatch(path.name)
]
if len(licenses) != 1:
    raise SystemExit(
        f"error: project root must contain exactly one conventional license; found {licenses}"
    )

try:
    listed = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        cwd=root,
    ).decode().split("\0")
except subprocess.CalledProcessError as error:
    raise SystemExit(f"error: could not enumerate the repository snapshot: {error}")

artifact_suffixes = {
    ".a", ".bc", ".dll", ".dylib", ".ilean", ".ir", ".o", ".obj",
    ".olean", ".so", ".trace",
}
total_bytes = 0
for relative in filter(None, listed):
    path = root / relative
    if path.is_symlink():
        raise SystemExit(f"error: Palomar snapshot contains a symlink: {relative}")
    if not path.is_file():
        continue
    if path.suffix in artifact_suffixes or path.name.endswith(
        (".olean.private", ".olean.server")
    ):
        raise SystemExit(f"error: compiled artifact is in the Palomar snapshot: {relative}")
    total_bytes += path.stat().st_size
if total_bytes > 500 * 1024 * 1024:
    raise SystemExit(
        f"error: Palomar snapshot is {total_bytes} bytes, above the 500 MiB limit"
    )

challenge = root / "Challenge.lean"
challenge_text = challenge.read_text(encoding="utf-8")
if challenge.stat().st_size > 100 * 1024 or len(challenge_text.splitlines()) > 1000:
    raise SystemExit("error: Challenge.lean exceeds Palomar's 100 KiB or 1,000-line limit")
imports = [
    line.split()[1]
    for line in challenge_text.splitlines()
    if line.startswith("import ")
]
if any(not module.startswith("Mathlib.") for module in imports):
    raise SystemExit(f"error: Challenge.lean imports outside Mathlib: {imports}")

try:
    comparator = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    raise SystemExit(f"error: comparator.json is not valid JSON: {error}")
required_keys = {
    "challenge_module", "solution_module", "theorem_names", "permitted_axioms"
}
allowed_keys = required_keys | {"definition_names", "enable_nanoda"}
if (
    not isinstance(comparator, dict)
    or set(comparator) - allowed_keys
    or not required_keys <= set(comparator)
):
    raise SystemExit("error: comparator.json has an invalid key set")
if comparator["challenge_module"] == comparator["solution_module"]:
    raise SystemExit("error: Challenge and Solution module names must differ")
if not isinstance(comparator["theorem_names"], list) or not comparator["theorem_names"]:
    raise SystemExit("error: comparator.json theorem_names must be nonempty")
if comparator.get("enable_nanoda") is not True:
    raise SystemExit("error: comparator.json must enable NanoDa for local/CI parity")
if not set(comparator["permitted_axioms"]) <= {
    "propext", "Quot.sound", "Classical.choice"
}:
    raise SystemExit("error: comparator.json contains an unpermitted axiom")

solution_text = (root / "Solution.lean").read_text(encoding="utf-8")
if re.search(
    r"(^|[^A-Za-z0-9_])(sorry|admit|axiom|unsafe)([^A-Za-z0-9_]|$)",
    solution_text,
):
    raise SystemExit("error: Solution.lean contains a forbidden proof-hole token")
print(
    f"Palomar package shape passed: {total_bytes} snapshot bytes; "
    f"Challenge {challenge.stat().st_size} bytes"
)
PY

ruby -ryaml - "$repository_root/formalization.yaml" <<'RUBY'
path = ARGV.fetch(0)
data = YAML.safe_load(File.read(path), aliases: false)
abort "error: formalization.yaml must contain one top-level mapping" unless data.is_a?(Hash)
project = data["project"]
classification = data["classification"]
abort "error: formalization.yaml project is incomplete" unless project.is_a?(Hash)
abort "error: project.name is missing" unless project["name"].is_a?(String) && !project["name"].strip.empty?
abort "error: project.description is missing" unless project["description"].is_a?(String) && !project["description"].strip.empty?
abort "error: project.authors must be a nonempty list" unless project["authors"].is_a?(Array) && !project["authors"].empty?
abort "error: project.responsible_maintainers must be a nonempty list" unless project["responsible_maintainers"].is_a?(Array) && !project["responsible_maintainers"].empty?
abort "error: project.license must be Apache-2.0" unless project["license"] == "Apache-2.0"
abort "error: classification is incomplete" unless classification.is_a?(Hash) && classification["arxiv"].is_a?(Array) && !classification["arxiv"].empty? && classification["msc2020"].is_a?(Array)
sources = data["sources"]
abort "error: sources must be nonempty" unless sources.is_a?(Array) && !sources.empty? && sources.all? { |source| source.is_a?(Hash) && source["title"].is_a?(String) && source["relationship"].is_a?(String) }
automation = data["automation"]
abort "error: automation.methods must be nonempty" unless automation.is_a?(Hash) && automation["methods"].is_a?(Array) && !automation["methods"].empty?
review = data["review"]
abort "error: review.status is missing" unless review.is_a?(Hash) && review["status"].is_a?(String) && !review["status"].strip.empty?
puts "formalization.yaml shape passed."
RUBY

bash scripts/verify.sh
bash scripts/test-landrun-wrapper.sh
