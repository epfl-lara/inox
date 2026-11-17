#!/usr/bin/env bash
# Compares the test durations of a pull request build with those of main, for
# the pull request comment. Called by the coverage comment workflow.
#
# usage: test-timings-comment.sh <workflow file> <run id> <artifact prefix> <mode> <title> <out.md>
#
# The build's artifacts named <artifact prefix>* hold the timings collected by
# scripts/test_timings.py, with the files that say what was tested (pr-number,
# pr-head-sha, base-sha, tested-sha, merged-prs). With mode `per-artifact`,
# each artifact is compared separately (the jobs of Inox CI run the same tests
# on different runners). With mode `merged`, the artifacts are merged first
# (the jobs of the Stainless downstream CI run different tests).
#
# The build is compared with the build of main at the commit it was merged
# into (or else the latest build of main), and earlier builds of main give the
# variation between builds of the same code. Builds of main are those that
# tested main without merging pull requests into it.
#
# Writes nothing when the build has no timings. Prints the pull request
# number and head commit that the build tested, if any, to stdout.
set -euo pipefail

workflow=$1 run=$2 prefix=$3 mode=$4 title=$5 out=$6
work=$(mktemp -d)
: > "$out"

# The artifacts come from pull request builds: only read plain files.
read_meta() { [ -f "$1" ] && head -c 200 "$1" | tr -cd '0-9a-f \n' | head -n 1 || true; }

download() {  # <run id> <dir>
  gh run download "$1" --repo "$GITHUB_REPOSITORY" --pattern "$prefix*" --dir "$2" 2>/dev/null &&
    [ -n "$(ls -A "$2" 2>/dev/null)" ]
}

# Combines the artifacts of a build into one timings file per group.
groups() {  # <dir>
  local dir=$1
  if [ "$mode" = merged ]; then
    python3 scripts/test_timings.py merge "$dir/all.timings" "$dir"/"$prefix"*/timings.json
  else
    for a in "$dir"/"$prefix"*/; do
      a=${a%/}
      [ -f "$a/timings.json" ] && cp "$a/timings.json" "$dir/${a##*/}.timings"
    done
  fi
}

download "$run" "$work/head" || { echo "No test timings in run $run" >&2; exit 0; }
meta=$(ls -d "$work/head/$prefix"*/ | head -n 1)
pr=$(read_meta "$meta/pr-number")
pr_head=$(read_meta "$meta/pr-head-sha")
base_sha=$(read_meta "$meta/base-sha")
groups "$work/head"

# Builds of main, newest first: the one at base_sha is the base, and up to 6
# others are the history.
base_run= history_runs=()
while read -r id; do
  [ "$id" = "$run" ] && continue
  dir="$work/main-$id"
  download "$id" "$dir" || continue
  m=$(ls -d "$dir/$prefix"*/ | head -n 1)
  # Only builds of main itself, without pull requests merged into it.
  if [ -n "$(read_meta "$m/pr-number")" ] || [ -n "$(read_meta "$m/merged-prs" | tr -d ' ')" ]; then
    continue
  fi
  groups "$dir"
  if [ -z "$base_run" ] && [ "$(read_meta "$m/tested-sha")" = "$base_sha" ]; then
    base_run=$id
  else
    history_runs+=("$id")
  fi
  [ -n "$base_run" ] && [ "${#history_runs[@]}" -ge 6 ] && break
done < <(gh run list --repo "$GITHUB_REPOSITORY" --workflow "$workflow" --branch main --status completed \
           --limit 20 --json databaseId --jq '.[].databaseId')

if [ -z "$base_run" ]; then
  # The latest build of main, compared with the others.
  if [ "${#history_runs[@]}" -eq 0 ]; then
    { echo "### $title"; echo; echo "_No build of \`main\` with test durations to compare with._"; } > "$out"
    echo "$pr $pr_head"
    exit 0
  fi
  base_run=${history_runs[0]}
  history_runs=("${history_runs[@]:1}")
  note="_Compared with the latest build of \`main\` (none at this build's base), so later changes to \`main\` count too._"
else
  note=
fi

groups="$work/groups.tsv"
: > "$groups"
for head in "$work/head"/*.timings; do
  name=$(basename "$head" .timings)
  base="$work/main-$base_run/$name.timings"
  [ -f "$base" ] || continue
  if [ "$mode" = merged ]; then
    label="Stainless downstream CI"
  else
    label=$(echo "${name#"$prefix"}" | sed 's/-jdk/, JDK /')
  fi
  line="$label"$'\t'"$head"$'\t'"$base"
  for id in "${history_runs[@]}"; do
    [ -f "$work/main-$id/$name.timings" ] && line+=$'\t'"$work/main-$id/$name.timings"
  done
  echo "$line" >> "$groups"
done
# The Stainless downstream CI tests the Stainless main of the day.
head_stainless=$(read_meta "$meta/stainless-sha")
base_stainless=$(read_meta "$(ls -d "$work/main-$base_run/$prefix"*/ | head -n 1)/stainless-sha")
if [ -n "$head_stainless" ] && [ "$head_stainless" != "$base_stainless" ]; then
  note="${note:+$note }_The two builds tested different Stainless commits, so Stainless changes count too._"
fi
echo "$note" > "$work/note.md"
python3 scripts/test_timings.py section "$title" "$groups" "$work/note.md" > "$out"
echo "$pr $pr_head"
