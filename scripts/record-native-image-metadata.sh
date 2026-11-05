#!/usr/bin/env bash
# Records the reflection, JNI and resource accesses that the GraalVM native
# image needs (see scripts/build-native-image.sh), by running the JVM build
# of the inox command line under GraalVM's tracing agent. native-image keeps
# only what it can reach statically, so anything Inox looks up by name must
# be listed in reachability-metadata.json, and an access that no run below
# exercises is missing from the binary. The runs cover every TIP regression
# file with each solver back end, and the same problems in the binary format.
#
# Usage:
#   scripts/record-native-image-metadata.sh          merge new accesses into
#                                                    the committed metadata
#   scripts/record-native-image-metadata.sh --check  fail if the runs reach
#                                                    something it doesn't list
#
# Needs GraalVM 25 or later (java on the PATH, or GRAALVM_HOME set), sbt,
# and z3 on the PATH.
set -euo pipefail
cd "$(dirname "$0")/.."

check=false
if [ "${1:-}" = --check ]; then check=true; fi

java=java
if [ -n "${GRAALVM_HOME:-}" ]; then java="$GRAALVM_HOME/bin/java"; fi

metadata=src/main/resources/META-INF/native-image/ch.epfl.lara/inox
tips=src/it/resources/regression/tip
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# ForallAssoc.scala-0.tip takes minutes and ignores --timeout.
files=$(ls "$tips"/{SAT,UNSAT,UNKNOWN}/*.tip | grep -v ForallAssoc.scala-0.tip)
# shellcheck disable=SC2086
sbt -batch assembly "Test/runMain inox.utils.WriteBinaryInputs $work/binary $(echo $files)"
jar=$(ls -t target/scala-*/inox-assembly-*.jar | head -n 1)

if $check; then out=$work/recorded; else out=$metadata; fi
mkdir -p "$out" "$work/tmp"

# Runs inox on the given files in a single JVM (starting a JVM under the
# agent takes seconds). A run stops at the first file that crashes or times
# out, so it restarts after that file until every file has been tried. The
# fresh temporary directory makes the first native Z3 run unpack the Z3
# libraries, so that their resources are recorded.
run() {
  local opt=$1; shift
  local todo=("$@")
  while [ ${#todo[@]} -gt 0 ]; do
    local log
    log=$(timeout 600 "$java" -agentlib:native-image-agent=config-merge-dir="$out" \
      -Djava.io.tmpdir="$work/tmp" -jar "$jar" --timeout=5 "$opt" "${todo[@]}" 2>&1 || true)
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

for solver in smt-z3 nativez3; do
  echo "Running the TIP files with $solver"
  # shellcheck disable=SC2086
  run --solvers="$solver" $files
done
# Princess ignores --timeout on these two (samarion/inox#65).
echo "Running the TIP files with princess"
# shellcheck disable=SC2086
run --solvers=princess $(echo "$files" | grep -vE '/SAT/AbstractRefinementMap.scala-0.tip|/UNSAT/BinarySearchTreeQuant2.scala-0.tip')
echo "Running the binary files"
run --format=binary:goal "$work"/binary/*.inoxb

if $check; then
  python3 - "$metadata/reachability-metadata.json" "$out/reachability-metadata.json" <<'PY'
import fnmatch, json, sys

def accesses(path):
    data = json.load(open(path))
    found = set()
    for section, entries in data.items():
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            key = entry.get("type", entry.get("glob", entry.get("bundle")))
            key = json.dumps(key, sort_keys=True)
            found.add((section, key, ""))
            for member, value in entry.items():
                if member in ("type", "glob", "bundle", "condition", "module"):
                    continue
                for item in value if isinstance(value, list) else [value]:
                    found.add((section, key, member + " " + json.dumps(item, sort_keys=True)))
    return found

committed = accesses(sys.argv[1])
globs = [json.loads(key) for section, key, _ in committed if section == "resources"]

def covered(access):
    section, key, _ = access
    if access in committed:
        return True
    # A resource is also covered by a glob in the committed metadata.
    return section == "resources" and any(
        isinstance(g, str) and fnmatch.fnmatchcase(json.loads(key), g) for g in globs)

missing = sorted(a for a in accesses(sys.argv[2]) if not covered(a))
for section, key, member in missing:
    print(f"missing in {section}: {key}" + (f" {member}" if member else ""))
if missing:
    print("Run scripts/record-native-image-metadata.sh to update the metadata.")
    sys.exit(1)
print("The committed metadata covers every recorded access.")
PY
fi
