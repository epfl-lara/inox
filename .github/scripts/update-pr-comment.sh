#!/usr/bin/env bash
# Updates sections of the CI comment on a pull request (see scripts/pr_comment.py),
# creating the comment if needed.
#
# usage: update-pr-comment.sh <pr number> <head sha> <section> <content.md> [<section> <content.md>]...
#
# Does nothing when the pull request has moved on from <head sha>, the commit
# that the build tested, since a newer build will update the comment.
set -euo pipefail

pr=$1 head_sha=$2
shift 2
[[ "$pr" =~ ^[0-9]+$ ]] || { echo "Invalid pull request number"; exit 1; }
[[ "$head_sha" =~ ^[0-9a-f]{40}$ ]] || { echo "Invalid head commit"; exit 1; }
if [ "$(gh pr view "$pr" --repo "$GITHUB_REPOSITORY" --json headRefOid --jq .headRefOid)" != "$head_sha" ]; then
  echo "Pull request #$pr has moved on from $head_sha"
  exit 0
fi

marker="<!-- inox-coverage -->"
id=$(gh api "repos/$GITHUB_REPOSITORY/issues/$pr/comments" --paginate \
       --jq ".[] | select(.user.login == \"github-actions[bot]\" and (.body | startswith(\"$marker\"))) | .id" | head -n 1)
body=$(mktemp)
if [ -n "$id" ]; then
  gh api "repos/$GITHUB_REPOSITORY/issues/comments/$id" --jq .body > "$body"
fi
while [ $# -ge 2 ]; do
  next=$(mktemp)
  python3 scripts/pr_comment.py "$body" "$1" "$2" > "$next"
  body=$next
  shift 2
done
if [ -n "$id" ]; then
  gh api -X PATCH "repos/$GITHUB_REPOSITORY/issues/comments/$id" -F body=@"$body" > /dev/null
else
  gh pr comment "$pr" --repo "$GITHUB_REPOSITORY" --body-file "$body"
fi
