#!/usr/bin/env bash
# Requires curl, jq, unzip and shasum.
set -euo pipefail
manifest="$(cd "$(dirname "$0")/.." && pwd)/solvers.json"
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) platform=linux-x86_64 ;;
  Darwin-arm64) platform=macos-arm64 ;;
  *) echo "Unsupported solver platform: $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac
[[ $# -ge 1 && $# -le 2 ]] || { echo "Usage: $0 DEST [CACHE]" >&2; exit 1; }
dest=$1
cache=${2:-${XDG_CACHE_HOME:-$HOME/.cache}/inox/solvers}
mkdir -p "$cache" "$dest"
work=$(mktemp -d "$cache/.fetch.XXXXXX")
trap 'rm -rf "$work"' EXIT
pins=$(jq -er --arg p "$platform" 'to_entries[] |
  [.key, .value.version, .value.platforms[$p].url, .value.platforms[$p].sha256,
   (.value.platforms[$p].member // "-")] | @tsv' "$manifest")
while IFS=$'\t' read -r solver version url hash member; do
  archive="$cache/$hash"
  if [[ ! -f "$archive" ]]; then
    echo "Downloading $solver $version for $platform"
    curl -fsSL --retry 5 --retry-delay 5 --retry-all-errors "$url" -o "$work/download"
    archive="$work/download"
  fi
  actual=$(shasum -a 256 "$archive")
  [[ ${actual%% *} == "$hash" ]] || {
    echo "SHA-256 mismatch for $solver: expected $hash, got ${actual%% *} ($archive)" >&2
    exit 1
  }
  echo "Verified $solver $version: $hash"
  [[ "$archive" == "$cache/$hash" ]] || mv "$archive" "$cache/$hash"
  if [[ "$member" == "-" ]]; then
    cp "$cache/$hash" "$work/$solver"
  else
    unzip -p "$cache/$hash" "$member" > "$work/$solver"
  fi
  chmod +x "$work/$solver"
  mv -f "$work/$solver" "$dest/$solver"
done <<< "$pins"
