#!/usr/bin/env python3
"""Builds the pull request comment that the coverage comment workflow posts.

The comment holds one section per workflow that reports on pull requests:
test coverage (Inox CI) and the GraalVM reachability metadata (Native
builds). Each workflow updates its own section and keeps the others.

usage:
  pr_comment.py splice <body.md> <section> <content.md>
      Prints the comment `body.md` (possibly empty) with its section
      `section` replaced by `content.md`.
  pr_comment.py metadata <head.json> [<base.json> <base description>]
      Prints the metadata section: the accesses that `head.json` adds to or
      removes from `base.json`, collapsed, or a note when there is nothing
      to compare with.
"""

import json
import re
import sys

MARKER = "<!-- inox-coverage -->"
SECTIONS = ["coverage", "native-metadata"]
MAX_DIFF_LINES = 400


def section_re(name):
    return re.compile(rf"<!-- inox:{name} -->\n(.*?)\n<!-- /inox:{name} -->", re.S)


def splice(body, name, content):
    if name not in SECTIONS:
        sys.exit(f"Unknown section {name}")
    sections = {}
    for other in SECTIONS:
        m = section_re(other).search(body)
        if m:
            sections[other] = m.group(1)
    # Comments from before sections only held the coverage.
    if not sections and body.startswith(MARKER) and body[len(MARKER):].strip():
        sections["coverage"] = body[len(MARKER):].strip()
    # The coverage summary starts with the marker that identifies the comment.
    content = content.strip()
    if content.startswith(MARKER):
        content = content[len(MARKER):].strip()
    sections[name] = content
    parts = [MARKER]
    for other in SECTIONS:
        if other in sections:
            parts.append(f"<!-- inox:{other} -->\n{sections[other]}\n<!-- /inox:{other} -->")
    return "\n\n".join(parts) + "\n"


def accesses(path):
    """The accesses that a metadata file lists, one line each: the type or
    resource, followed by a member for the members of a type."""
    # The files come from pull request builds: only read valid JSON.
    data = json.load(open(path))
    found = set()
    for section, entries in data.items():
        for entry in entries if isinstance(entries, list) else []:
            if not isinstance(entry, dict):
                continue
            key = entry.get("type", entry.get("glob", entry.get("bundle")))
            key = key if isinstance(key, str) else json.dumps(key, sort_keys=True)
            found.add(f"{section} {key}")
            for member, value in entry.items():
                if member in ("type", "glob", "bundle", "condition", "module"):
                    continue
                for item in value if isinstance(value, list) else [value]:
                    if isinstance(item, dict) and set(item) == {"name"}:
                        item = item["name"]
                    elif not isinstance(item, str):
                        item = json.dumps(item, sort_keys=True)
                    found.add(f"{section} {key} {member.rstrip('s')} {item}")
    return found


def metadata(head_path, base_path=None, base_desc=None):
    title = "GraalVM reachability metadata"
    head = accesses(head_path)
    if base_path is None:
        return f"_{title}: no recording from `main` to compare with._"
    base = accesses(base_path)
    diff = sorted([("+", a) for a in head - base] + [("-", a) for a in base - head], key=lambda d: (d[1], d[0]))
    if not diff:
        return f"_{title}: no changes compared with {base_desc}._"
    added = sum(1 for sign, _ in diff if sign == "+")
    shown = [f"{sign} {a}" for sign, a in diff[:MAX_DIFF_LINES]]
    # A fence longer than any run of backticks in the diff.
    fence = "`" * max(3, 1 + max((len(r) for r in re.findall(r"`+", "\n".join(shown))), default=0))
    out = [f"<details><summary>{title}: {added} accesses added and {len(diff) - added} removed, "
           f"compared with {base_desc}</summary>", "", f"{fence}diff", *shown, fence]
    if len(diff) > len(shown):
        out += ["", f"_{len(diff) - len(shown)} more in the `graalvm-reachability-metadata` artifact._"]
    out += ["", "</details>"]
    return "\n".join(out)


def main(args):
    if len(args) == 4 and args[0] == "splice":
        body = open(args[1]).read()
        content = open(args[3]).read()
        sys.stdout.write(splice(body, args[2], content))
    elif len(args) in (2, 4) and args[0] == "metadata":
        print(metadata(*args[1:]))
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
