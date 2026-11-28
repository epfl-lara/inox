#!/bin/sh
# get-ethos.sh DIR: downloads and builds Ethos, and cvc5's CPC signature, at the
# versions in solvers.json, into DIR: DIR/ethos/build/src/ethos and DIR/cpc/Cpc.eo.
# Needs cmake, a C++ compiler and GMP (libgmp-dev). It prints the two paths
# on standard output, as ETHOS=... and CPC=..., and the build on standard error.
#
# The Ethos commit is the one named by cvc5's contrib/get-ethos-checker.
set -e
MANIFEST="$(dirname "$0")/../../solvers.json"
CVC5=cvc5-$(jq -er '.cvc5.version' "$MANIFEST")
ETHOS=$(jq -er '.cvc5.ethosCommit' "$MANIFEST")
mkdir -p "$1"
cd "$1"
if [ ! -x ethos/build/src/ethos ]; then
  rm -rf ethos
  git init -q ethos
  git -C ethos fetch -q --depth 1 https://github.com/cvc5/ethos "$ETHOS"
  git -C ethos checkout -q FETCH_HEAD
  (cd ethos && ./configure.sh release && cd build && make -j"$(nproc)") >&2
fi
if [ ! -f cpc/Cpc.eo ]; then
  rm -rf cpc cvc5
  git init -q cvc5
  git -C cvc5 sparse-checkout set proofs/eo/cpc
  git -C cvc5 fetch -q --depth 1 --filter=blob:none https://github.com/cvc5/cvc5 "$CVC5"
  git -C cvc5 checkout -q FETCH_HEAD
  mv cvc5/proofs/eo/cpc cpc
  rm -rf cvc5
fi
echo "ETHOS=$(pwd)/ethos/build/src/ethos"
echo "CPC=$(pwd)/cpc/Cpc.eo"
