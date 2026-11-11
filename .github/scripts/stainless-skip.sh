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
# The line must start the line in the commit message, so indented examples
# (like the ones above, in a commit message) don't count.
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
#   INOX_REVS       the Inox revisions whose commits are read, separated by
#                   spaces (default HEAD)
#   INOX_BASE       optional: the revision of Inox main, so that the report
#                   tells the commits of a pull request from those on main
#   SKIP_REPORT     optional: a file to which a Markdown warning is appended
#                   when tests are skipped, naming them and the commits that
#                   skip them (for the job summary and the pull request comment)
#
# Writes `stainless` (the Stainless commit it looked at, for the tests to use),
# `all=true|false` and `benchmarks` (one glob per line) to $GITHUB_OUTPUT, or
# prints them.
set -euo pipefail

STAINLESS_REPO="${STAINLESS_REPO:-epfl-lara/stainless}"
STAINLESS_REF="${STAINLESS_REF:-main}"
INOX_REVS="${INOX_REVS:-HEAD}"
INOX_BASE="${INOX_BASE:-}"
SKIP_REPORT="${SKIP_REPORT:-}"
out="${GITHUB_OUTPUT:-/dev/stdout}"
server="${GITHUB_SERVER_URL:-https://github.com}"
inox_repo="${GITHUB_REPOSITORY:-epfl-lara/inox}"

# The Inox commit that Stainless pins, from its tree without checking it out.
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
git clone -q --depth 1 --filter=blob:none --no-checkout --branch "$STAINLESS_REF" \
  "$server/$STAINLESS_REPO.git" "$tmp/stainless"
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
all_commits=()      # the commits that skip all tests
benchmarks=()       # the globs of the benchmarks to skip
glob_commits=()     # the commit of each glob
read -ra revs <<< "$INOX_REVS"
while read -r commit; do
  while read -r filter; do
    if [ -z "$filter" ]; then
      all=true
      all_commits+=("$commit")
      echo "::warning::Skipping all Stainless tests, as commit $commit says, until Stainless bumps Inox past it."
    else
      read -ra globs <<< "$filter"
      for glob in "${globs[@]}"; do
        if [[ "$glob" == /* || "$glob" == *..* ]]; then
          echo "::error::Invalid 'Stainless: skip $glob' in commit $commit: expected a path under frontends/benchmarks."
          exit 1
        fi
        benchmarks+=("$glob")
        glob_commits+=("$commit")
      done
      echo "::warning::Skipping the Stainless benchmarks $filter, as commit $commit says, until Stainless bumps Inox past it."
    fi
  done < <(git log -1 --format=%B "$commit" | tr -d '\r' |
           sed -n -E 's/^[Ss]tainless:[[:space:]]*skip([[:space:]]+(.*[^[:space:]]))?[[:space:]]*$/\2/p')
done < <(git log --format=%H "${revs[@]}" "^$pinned")

{
  echo "stainless=$stainless"
  echo "all=$all"
  echo "benchmarks<<EOF_BENCHMARKS"
  if [ "${#benchmarks[@]}" -gt 0 ]; then
    printf '%s\n' "${benchmarks[@]}"
  fi
  echo "EOF_BENCHMARKS"
} >> "$out"

if [ -z "$SKIP_REPORT" ] || { [ "$all" = false ] && [ "${#benchmarks[@]}" -eq 0 ]; }; then
  exit 0
fi

# The report quotes commit messages, which come from pull requests: keep them
# in code spans, so that they can't mention anyone or add Markdown.
code() { printf '`%s`' "$(printf '%s' "$1" | tr -d '`\r\n' | cut -c 1-100)"; }
commit_ref() {
  local where=""
  if [ -n "$INOX_BASE" ]; then
    if git merge-base --is-ancestor "$1" "$INOX_BASE"; then
      where=", on \`main\` and not in this pull request"
    else
      where=", in this pull request"
    fi
  fi
  printf 'commit [`%s`](%s/%s/commit/%s) %s%s' "${1:0:7}" "$server" "$inox_repo" "$1" \
    "$(code "$(git log -1 --format=%s "$1")")" "$where"
}
stainless_ref="[\`${stainless:0:7}\`]($server/$STAINLESS_REPO/commit/$stainless)"
pinned_ref="[\`${pinned:0:7}\`]($server/$inox_repo/commit/$pinned)"
until_msg="> The skip lines apply until Stainless bumps Inox past their commits: \`$STAINLESS_REF\` of $STAINLESS_REPO, at $stainless_ref, pins Inox $pinned_ref."

{
  echo "> [!WARNING]"
  if [ "$all" = true ]; then
    echo "> **The Stainless downstream CI skips all Stainless tests**, because of a \`Stainless: skip\` line in:"
    for commit in "${all_commits[@]}"; do
      echo "> - $(commit_ref "$commit")"
    done
    echo ">"
    echo "$until_msg"
  else
    # Match the globs against Stainless's benchmarks, as the tests job does,
    # on empty files with the same names.
    mkdir -p "$tmp/tree"
    git -C "$tmp/stainless" ls-tree -r --name-only HEAD frontends/benchmarks |
      (cd "$tmp/tree" && while read -r path; do mkdir -p "$(dirname "$path")" && : > "$path"; done)
    skipped=()
    lines=()
    shopt -s nullglob
    for i in "${!benchmarks[@]}"; do
      matches=()
      if [ -d "$tmp/tree/frontends/benchmarks" ]; then
        # shellcheck disable=SC2206 # the glob is meant to expand
        matches=($(cd "$tmp/tree/frontends/benchmarks" && for m in ${benchmarks[$i]}; do
                     if [ -d "$m" ]; then find "$m" -type f; else echo "$m"; fi
                   done))
      fi
      skipped+=("${matches[@]}")
      case "${#matches[@]}" in
        0) count="matches no benchmark" ;;
        1) count="1 benchmark" ;;
        *) count="${#matches[@]} benchmarks" ;;
      esac
      lines+=("> - $(code "${benchmarks[$i]}"): $count, from $(commit_ref "${glob_commits[$i]}")")
    done
    shopt -u nullglob
    mapfile -t skipped < <(if [ "${#skipped[@]}" -gt 0 ]; then printf '%s\n' "${skipped[@]}" | sort -u; fi)
    n="${#skipped[@]}"
    echo "> **The Stainless downstream CI skips $n Stainless benchmark$([ "$n" -eq 1 ] || echo s)**, because of \`Stainless: skip\` lines:"
    printf '%s\n' "${lines[@]}"
    echo ">"
    echo "$until_msg"
    if [ "$n" -gt 0 ]; then
      echo
      echo "<details><summary>Skipped benchmarks</summary>"
      echo
      for path in "${skipped[@]:0:300}"; do
        echo "- $(code "$path")"
      done
      if [ "$n" -gt 300 ]; then
        echo "- and $((n - 300)) more"
      fi
      echo
      echo "</details>"
    fi
  fi
} >> "$SKIP_REPORT"
