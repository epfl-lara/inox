#!/usr/bin/env python3
"""Updates one section of the CI comment on a pull request.

usage: pr_comment.py <body.md> <section> <content>

Prints the comment body `body.md` (empty or missing for a new comment) with
the given section replaced by the contents of the file `content` (or removed
when it is empty). The comment collects the results of several workflows,
which each update their own sections as soon as they complete:

  stainless-skip     Markdown: the Stainless tests that the downstream CI skips
  coverage           Markdown: the coverage, compared with main
  timings-coverage   test durations of the Inox coverage workflow
  timings-inox       test durations of Inox CI
  timings-stainless  test durations of the Stainless downstream CI

The test durations are JSON (see `scripts/test_timings.py section`), and the
comment shows those of all workflows in one table. The JSON is kept in the
comment, hidden, for the next updates.
"""

import base64
import json
import re
import sys
import zlib

from test_timings import MIN_FACTOR, MIN_SECONDS

MARKER = "<!-- inox-coverage -->"
MARKDOWN = ["stainless-skip", "coverage"]
TIMINGS = ["timings-coverage", "timings-inox", "timings-stainless"]
SECTIONS = MARKDOWN + TIMINGS


def encode(data):
    return base64.b64encode(zlib.compress(json.dumps(data).encode())).decode()


def decode(s):
    return json.loads(zlib.decompress(base64.b64decode(s)))


def parse(body):
    sections = {}
    for m in re.finditer(r"<!-- begin:([\w-]+) -->\n(.*?)<!-- end:\1 -->", body, re.S):
        if m.group(1) in MARKDOWN:
            sections[m.group(1)] = m.group(2).strip("\n")
    for m in re.finditer(r"<!-- data:([\w-]+) ([A-Za-z0-9+/=]+) -->", body):
        if m.group(1) in TIMINGS:
            try:
                sections[m.group(1)] = decode(m.group(2))
            except (ValueError, zlib.error):
                pass
    if not sections and body.startswith(MARKER) and "<!-- begin:" not in body and "<!-- data:" not in body:
        # A comment from before the sections, which only held the coverage.
        old = body[len(MARKER):].strip("\n")
        if old:
            sections["coverage"] = old
    return sections


def timings_table(sections):
    parts = [sections[s] for s in TIMINGS if s in sections]
    if not parts:
        return ""
    rows = [r for p in parts for r in p.get("rows", [])]
    details = [d for p in parts for d in p.get("details", [])]
    changed = sum(p.get("changed", 0) for p in parts)
    notes = []
    for p in parts:
        for n in p.get("notes", []):
            if n not in notes:
                notes.append(n)
    out = ["### Test durations", ""]
    if rows:
        out += ["| Job | `main` | This PR | Change (95%) | Tests changed |",
                "|---|---:|---:|---:|---|", *rows, ""]
    if details:
        out += [f"<details><summary>Tests that changed significantly ({changed})</summary>", "",
                "\n\n".join(details), "",
                f"Other tests changed within the noise between builds, or by less than "
                f"{MIN_FACTOR:g}× or {MIN_SECONDS:g} s. "
                "Intervals are 95%, and significance accounts for the number of tests (Bonferroni). "
                "See `scripts/test_timings.py`.", "", "</details>", ""]
    if notes:
        out.append("<sub>" + " ".join(n.strip("_") for n in notes) + "</sub>")
    return "\n".join(out).strip("\n")


def render(sections):
    parts = [MARKER]
    for s in MARKDOWN:
        if s in sections:
            parts.append(f"<!-- begin:{s} -->\n{sections[s]}\n<!-- end:{s} -->")
    table = timings_table(sections)
    if table:
        parts.append(table)
    for s in TIMINGS:
        if s in sections:
            parts.append(f"<!-- data:{s} {encode(sections[s])} -->")
    return "\n\n".join(parts)


def main(args):
    if len(args) != 3 or args[1] not in SECTIONS:
        sys.exit(__doc__)
    try:
        body = open(args[0]).read()
    except FileNotFoundError:
        body = ""
    sections = parse(body)
    content = open(args[2]).read().strip("\n")
    if not content:
        sections.pop(args[1], None)
    elif args[1] in TIMINGS:
        sections[args[1]] = json.loads(content)
    else:
        sections[args[1]] = content
    print(render(sections))


if __name__ == "__main__":
    main(sys.argv[1:])
