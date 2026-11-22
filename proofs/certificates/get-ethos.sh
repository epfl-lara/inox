#!/bin/sh
# get-ethos.sh DIR: downloads and builds Ethos, and cvc5's CPC signature, at the
# versions pinned below, into DIR: DIR/ethos/build/src/ethos and DIR/cpc/Cpc.eo.
# Needs cmake, a C++ compiler and GMP (libgmp-dev). It prints the two paths
# on standard output, as ETHOS=... and CPC=..., and the build on standard error.
#
# The pins move together: CVC5 is the cvc5 that the tests run (CVC5_VER in
# .github/workflows), and ETHOS the Ethos commit that its
# contrib/get-ethos-checker names.
set -e
CVC5=cvc5-1.4.2
ETHOS=08e4aa40c4f8a6e00833f10e8d8985777e424027
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
