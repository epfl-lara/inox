#!/usr/bin/env bash
# Decides which Stainless tests the Stainless downstream CI skips.
#
# An Inox change that breaks Stainless until Stainless is updated for it says
# so with lines like these in one of its commit messages:
#
#   Stainless: skip                                  skip all Stainless tests
#   Stainless: skip verification/valid/Foo.scala     skip some benchmarks: paths
#   Stainless: skip termination/valid/Bar*.scala     or globs under Stainless's
#                                                    frontends/benchmarks,
#                                                    separated by spaces
#
# A line applies for as long as Stainless main pins an Inox commit that doesn't
# contain it: the lines come from the Inox commits in
# <Stainless's inox submodule>..HEAD. The Stainless change that bumps Inox past
# that commit turns them off, with nothing to revert in Inox, and several Inox
# pull requests can land before it. Unrelated Stainless commits don't.
#
# Inputs, from the environment:
#   STAINLESS_REPO  the Stainless repository (default epfl-lara/stainless)
#   STAINLESS_REF   its branch (default main)
#
# Writes `stainless` (the Stainless commit it looked at, for the tests to use),
# `all=true|false` and `benchmarks` (one glob per line) to $GITHUB_OUTPUT, or
# prints them.
set -euo pipefail

STAINLESS_REPO="${STAINLESS_REPO:-epfl-lara/stainless}"
STAINLESS_REF="${STAINLESS_REF:-main}"
out="${GITHUB_OUTPUT:-/dev/stdout}"

# The Inox commit that Stainless pins, from its tree without checking it out.
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
git clone -q --depth 1 --filter=blob:none --no-checkout --branch "$STAINLESS_REF" \
  "https://github.com/$STAINLESS_REPO.git" "$tmp/stainless"
stainless="$(git -C "$tmp/stainless" rev-parse HEAD)"
pinned="$(git -C "$tmp/stainless" ls-tree HEAD inox | awk '$2 == "commit" { print $3 }')"
if [ -z "$pinned" ]; then
  echo "::error::Couldn't find the Inox submodule of $STAINLESS_REPO@$STAINLESS_REF."
  exit 1
fi
if ! git cat-file -e "$pinned^{commit}" 2> /dev/null && ! git fetch -q origin "$pinned"; then
  echo "::error::$STAINLESS_REPO@$STAINLESS_REF pins Inox commit $pinned, which isn't in this repository."
  exit 1
fi
echo "::notice::$STAINLESS_REPO@$STAINLESS_REF ($stainless) pins Inox commit $pinned."

all=false
benchmarks=()
while read -r commit; do
  while read -r filter; do
    if [ -z "$filter" ]; then
      all=true
      echo "::warning::Skipping all Stainless tests, as commit $commit says, until Stainless bumps Inox past it."
    else
      read -ra globs <<< "$filter"
      for glob in "${globs[@]}"; do
        if [[ "$glob" == /* || "$glob" == *..* ]]; then
          echo "::error::Invalid 'Stainless: skip $glob' in commit $commit: expected a path under frontends/benchmarks."
          exit 1
        fi
      done
      benchmarks+=("${globs[@]}")
      echo "::warning::Skipping the Stainless benchmarks $filter, as commit $commit says, until Stainless bumps Inox past it."
    fi
  done < <(git log -1 --format=%B "$commit" | tr -d '\r' |
           sed -n -E 's/^[[:space:]]*[Ss]tainless:[[:space:]]*skip([[:space:]]+(.*[^[:space:]]))?[[:space:]]*$/\2/p')
done < <(git log --format=%H "$pinned..HEAD")

{
  echo "stainless=$stainless"
  echo "all=$all"
  echo "benchmarks<<EOF_BENCHMARKS"
  if [ "${#benchmarks[@]}" -gt 0 ]; then
    printf '%s\n' "${benchmarks[@]}"
  fi
  echo "EOF_BENCHMARKS"
} >> "$out"
