#!/usr/bin/env bash
# Smoke test for a native build of the inox command line: runs it on the TIP
# regression files and fails if an answer contradicts the file's category
# (SAT reported for an UNSAT file or the other way around), or if the binary
# crashes. UNKNOWN is accepted, since it depends on timeouts.
#
# ForallAssoc.scala-0.tip is skipped: it takes minutes and ignores --timeout
# with the SMT-LIB back ends (TipTestSuite moves it to native Z3 for that).
#
# The files that compare functions run under intensional function equality,
# since `none` rejects them (as in TipTestSuite).
#
# Usage: scripts/check-native-binary.sh <binary> [inox options...]
set -uo pipefail
cd "$(dirname "$0")/.."

bin=$1; shift
dir=src/it/resources/regression/tip
failures=0
total=0

for expected in SAT UNSAT; do
  for f in "$dir/$expected"/*.tip; do
    case "$(basename "$f")" in ForallAssoc.scala-0.tip) continue ;; esac
    total=$((total + 1))
    semantics=()
    case "$(basename "$f")" in
      Injective.scala-0.tip|LambdaEquality2.scala-1.tip|Streams.scala-0.tip|inline-lambdas.scala-0.tip)
        semantics=(--function-equality=intensional) ;;
    esac
    out=$(timeout 120 "$bin" --timeout=10 "${semantics[@]}" "$@" "$f" 2>&1)
    answers=$(echo "$out" | grep -oE '=> (SAT|UNSAT|UNKNOWN)' | cut -d' ' -f2 | sort -u)
    if [ "$expected" = SAT ]; then wrong=UNSAT; else wrong=SAT; fi
    if [ -z "$answers" ]; then
      echo "FAIL $f: no answer"; echo "$out" | grep -vE '^\s+at ' | tail -n 10; failures=$((failures + 1))
    elif echo "$answers" | grep -qx "$wrong"; then
      echo "FAIL $f: expected $expected, got $wrong"; failures=$((failures + 1))
    else
      echo "ok   $f: $(echo $answers)"
    fi
  done
done

echo "$failures of $total files failed"
[ "$failures" -eq 0 ]
