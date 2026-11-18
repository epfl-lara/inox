#!/usr/bin/env bash
# Updates sections of the CI comment on a pull request (see scripts/pr_comment.py),
# creating the comment if needed.
#
# usage: update-pr-comment.sh <pr number> <head sha> <section> <content> [<section> <content>]...
#
# Does nothing when the pull request has moved on from <head sha>, the commit
# that the build tested, since a newer build will update the comment.
#
# Several workflows update the comment, each as soon as it completes, and two
# of them can do so at the same time: the one that writes last would drop the
# other's sections. So after writing, this reads the comment again and writes
# its sections again if they are missing.
set -euo pipefail

pr=$1 head_sha=$2
shift 2
[[ "$pr" =~ ^[0-9]+$ ]] || { echo "Invalid pull request number"; exit 1; }
[[ "$head_sha" =~ ^[0-9a-f]{40}$ ]] || { echo "Invalid head commit"; exit 1; }
if [ "$(gh pr view "$pr" --repo "$GITHUB_REPOSITORY" --json headRefOid --jq .headRefOid)" != "$head_sha" ]; then
  echo "Pull request #$pr has moved on from $head_sha"
  exit 0
fi
updates=("$@")
marker="<!-- inox-coverage -->"

comment_ids() {  # The comments of this script, oldest first.
  gh api "repos/$GITHUB_REPOSITORY/issues/$pr/comments" --paginate \
    --jq ".[] | select(.user.login == \"github-actions[bot]\" and (.body | startswith(\"$marker\"))) | .id"
}
first_comment() { local ids; ids=$(comment_ids); echo "${ids%%$'\n'*}"; }

# Prints the comment `$1` (or an empty one) with the updates applied.
updated() {
  local body next
  body=$(mktemp)
  if [ -n "$1" ]; then
    gh api "repos/$GITHUB_REPOSITORY/issues/comments/$1" --jq .body > "$body"
  fi
  set -- "${updates[@]}"
  while [ $# -ge 2 ]; do
    next=$(mktemp)
    python3 scripts/pr_comment.py "$body" "$1" "$2" > "$next"
    body=$next
    shift 2
  done
  cat "$body"
}

# Whether two comment bodies are the same, up to line endings.
same() { [ "$(tr -d '\r' < "$1")" = "$(tr -d '\r' < "$2")" ]; }

for attempt in 1 2 3 4; do
  id=$(first_comment)
  new=$(mktemp)
  updated "$id" > "$new"
  if [ -n "$id" ]; then
    current=$(mktemp)
    gh api "repos/$GITHUB_REPOSITORY/issues/comments/$id" --jq .body > "$current"
    # Up to date: written by this script, or by an earlier attempt.
    if [ "$attempt" -gt 1 ] && same "$current" "$new"; then
      exit 0
    fi
    gh api -X PATCH "repos/$GITHUB_REPOSITORY/issues/comments/$id" -F body=@"$new" > /dev/null
  else
    gh pr comment "$pr" --repo "$GITHUB_REPOSITORY" --body-file "$new"
  fi
  # Another workflow may be writing at the same time: check again in a while.
  sleep $((5 + RANDOM % 10))
  # Two workflows may also both have created a comment: keep the oldest.
  ids=$(comment_ids)
  for extra in $(echo "$ids" | tail -n +2); do
    gh api -X DELETE "repos/$GITHUB_REPOSITORY/issues/comments/$extra" > /dev/null || true
  done
  id=$(first_comment)
  [ -n "$id" ] || continue
  current=$(mktemp)
  gh api "repos/$GITHUB_REPOSITORY/issues/comments/$id" --jq .body > "$current"
  check=$(mktemp)
  updated "$id" > "$check"
  if same "$current" "$check"; then
    exit 0
  fi
  echo "The comment changed meanwhile: updating it again"
done
echo "::warning::Couldn't update the comment, which kept changing."
