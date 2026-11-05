#!/usr/bin/env bash
# Records the reflection, JNI and resource accesses that the GraalVM native
# image needs (see scripts/build-native-image.sh), by running the JVM build
# of the inox command line under GraalVM's tracing agent. native-image keeps
# only what it can reach statically, so anything Inox looks up by name must
# be listed in reachability-metadata.json, and an access that no run below
# exercises is missing from the binary. The runs cover every TIP regression
# file with each solver back end, and the same problems in the binary format.
#
# Usage: scripts/record-native-image-metadata.sh <dir>
#   writes <dir>/reachability-metadata.json, with its entries sorted so that
#   two recordings can be compared with diff. It also builds the assembly
#   jar that scripts/build-native-image.sh compiles.
#
# Needs GraalVM 25 or later (java on the PATH, or GRAALVM_HOME set), sbt,
# and z3 on the PATH.
set -euo pipefail
cd "$(dirname "$0")/.."

if [ $# -ne 1 ]; then
  echo "Usage: $0 <dir>" >&2
  exit 1
fi
out=$1

java=java
if [ -n "${GRAALVM_HOME:-}" ]; then java="$GRAALVM_HOME/bin/java"; fi

tips=src/it/resources/regression/tip
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# ForallAssoc.scala-0.tip takes minutes and ignores --timeout.
files=$(ls "$tips"/{SAT,UNSAT,UNKNOWN}/*.tip | grep -v ForallAssoc.scala-0.tip)
# shellcheck disable=SC2086
sbt -batch assembly "Test/runMain inox.utils.WriteBinaryInputs $work/binary $(echo $files)"
jar=$(ls -t target/scala-*/inox-assembly-*.jar | head -n 1)

recorded=$work/recorded
mkdir -p "$recorded" "$work/tmp"

# Runs inox on the given files in a single JVM (starting a JVM under the
# agent takes seconds). A run stops at the first file that crashes or times
# out, so it restarts after that file until every file has been tried. The
# fresh temporary directory makes the first native Z3 run unpack the Z3
# libraries, so that their resources are recorded. The first argument holds
# the options, separated by spaces.
run() {
  local opts
  read -r -a opts <<< "$1"; shift
  local todo=("$@")
  while [ ${#todo[@]} -gt 0 ]; do
    local log
    log=$(timeout 600 "$java" -agentlib:native-image-agent=config-merge-dir="$recorded" \
      -Djava.io.tmpdir="$work/tmp" -jar "$jar" --timeout=5 "${opts[@]}" "${todo[@]}" 2>&1 || true)
    local rest=() started=false
    for f in "${todo[@]}"; do
      if $started; then rest+=("$f")
      elif ! grep -qF "$f =>" <<< "$log"; then
        started=true
        echo "  no answer for $f, continuing after it"
      fi
    done
    todo=("${rest[@]+"${rest[@]}"}")
  done
}

# These compare functions, which the default semantics rejects (as in TipTestSuite).
comparing='Injective.scala-0.tip|LambdaEquality2.scala-1.tip|Streams.scala-0.tip|inline-lambdas.scala-0.tip'
intensional=--function-equality=intensional

# Runs the given files with the options in $1, under intensional function
# equality for those that compare functions.
run_all() {
  local opts=$1; shift
  # shellcheck disable=SC2046
  run "$opts" $(printf '%s\n' "$@" | grep -vE "$comparing")
  # shellcheck disable=SC2046
  run "$opts $intensional" $(printf '%s\n' "$@" | grep -E "$comparing")
}

for solver in smt-z3 nativez3; do
  echo "Running the TIP files with $solver"
  # shellcheck disable=SC2086
  run_all --solvers="$solver" $files
done
# Princess ignores --timeout on these two (samarion/inox#65).
echo "Running the TIP files with princess"
# shellcheck disable=SC2046
run_all --solvers=princess $(echo "$files" | grep -vE '/SAT/AbstractRefinementMap.scala-0.tip|/UNSAT/BinarySearchTreeQuant2.scala-0.tip')
echo "Running the binary files"
run_all --format=binary:goal "$work"/binary/*.inoxb

mkdir -p "$out"
python3 - "$recorded/reachability-metadata.json" "$out/reachability-metadata.json" <<'PY'
import json, sys

# Sorts the entries by the type, resource or member they are about. Lists of
# names, such as parameter types, keep their order.
def key(value):
    name = value
    if isinstance(value, dict):
        name = next((value[k] for k in ("type", "glob", "bundle", "name") if k in value), "")
    return (json.dumps(name, sort_keys=True), json.dumps(value, sort_keys=True))

def canonical(value):
    if isinstance(value, dict):
        return {k: canonical(v) for k, v in sorted(value.items())}
    if isinstance(value, list):
        items = [canonical(v) for v in value]
        return sorted(items, key=key) if all(isinstance(v, dict) for v in items) else items
    return value

data = canonical(json.load(open(sys.argv[1])))
with open(sys.argv[2], "w") as f:
    json.dump(data, f, indent=2)
    f.write("\n")
PY
echo "Wrote $out/reachability-metadata.json"
