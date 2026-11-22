#!/bin/sh
# check.sh DIR [JOBS]: checks every CPC proof in DIR with Ethos, with cvc5's
# signature, JOBS at a time (2 by default), each within 300 seconds and 4 GB.
# ETHOS names the Ethos binary and CPC the file Cpc.eo (get-ethos.sh prints
# both). Fails unless Ethos says `correct` of every proof.
#
# The signature includes cvc5's expert one (expert/CpcExpert.eo, next to
# Cpc.eo), which has the constant arrays of Inox's maps and bags.
set -e
: "${ETHOS:?ETHOS must name the Ethos binary}" "${CPC:?CPC must name Cpc.eo}"
EXPERT=$(dirname "$CPC")/expert/CpcExpert.eo
export ETHOS CPC EXPERT
ls "$1"/*.cpc | xargs -P "${2:-2}" -I{} sh -c '
  r=$( (ulimit -v 4000000; timeout 300 "$ETHOS" --include="$CPC" --include="$EXPERT" {} 2>&1) | grep -v "^$" | tail -1)
  if [ "$r" = correct ]; then echo "ok   {}"; else echo "FAIL {}: $(echo "$r" | cut -c1-300)"; fi' |
  tee "$1/check.log"
total=$(grep -c . "$1/check.log")
ok=$(grep -c '^ok ' "$1/check.log" || true)
echo "Ethos accepts $ok of $total proofs"
[ "$ok" = "$total" ]
