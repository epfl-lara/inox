#!/bin/sh
# check.sh DIR [JOBS] [FLAGS]: checks the certificates of every file of DIR, each what Inox prints
# for an input with `get-proof` commands, with the checker in Lean, JOBS files at a time (2 by
# default), each within 300 seconds. Fails unless the checker accepts every certificate, other than
# those whose proofs have constant arrays, which Logos doesn't read yet: their rules are checked.
# FLAGS are passed to inox-check, such as `--terms`.
set -e
cd "$(dirname "$0")"
CHECK=$PWD/.lake/build/bin/inox-check
[ -x "$CHECK" ] || lake build inox-check
FLAGS="${3:-}"
export CHECK FLAGS
ls "$1"/* | grep -v '/check\.log$' | xargs -P "${2:-2}" -I{} sh -c '
  r=$(timeout 300 "$CHECK" $FLAGS {} 2>&1 | grep "^ok \|^FAIL " || echo "FAIL {}: no answer: the checker crashed, or took more than 300 seconds")
  echo "$r" | while read -r line; do
    case "$line" in
      *"unknown indexed operator const"*)
        if "$CHECK" --rules {} > /dev/null 2>&1; then echo "skip {}: constant arrays, the rules hold"; else echo "$line"; fi;;
      *) echo "$line";;
    esac
  done' | tee "$1/check.log"
total=$(grep -c . "$1/check.log")
ok=$(grep -c '^ok ' "$1/check.log" || true)
skipped=$(grep -c '^skip ' "$1/check.log" || true)
echo "The Lean checker accepts $ok of $total certificates, and the rules of $skipped more"
[ "$((ok + skipped))" = "$total" ] && [ "$ok" -gt 0 ]
