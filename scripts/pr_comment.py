#!/usr/bin/env python3
"""Updates one section of the CI comment on a pull request.

usage: pr_comment.py <body.md> <section> <content.md>

Prints the comment body `body.md` (empty or missing for a new comment) with
the given section replaced by the contents of `content.md` (or removed when
it is empty). The comment collects the results of several workflows, which
each update their own sections, in this order:
"""

import re
import sys

MARKER = "<!-- inox-coverage -->"
SECTIONS = ["stainless-skip", "coverage", "inox-timings", "stainless-timings"]
__doc__ += "".join(f"  {s}\n" for s in SECTIONS)


def parse(body):
    sections = {}
    for m in re.finditer(r"<!-- begin:([\w-]+) -->\n(.*?)<!-- end:\1 -->", body, re.S):
        if m.group(1) in SECTIONS:
            sections[m.group(1)] = m.group(2).strip("\n")
    # A comment from before the sections only held the coverage, which its
    # workflow posts again.
    return sections


def main(args):
    if len(args) != 3 or args[1] not in SECTIONS:
        sys.exit(__doc__)
    try:
        body = open(args[0]).read()
    except FileNotFoundError:
        body = ""
    sections = parse(body)
    content = open(args[2]).read().strip("\n")
    if content:
        sections[args[1]] = content
    else:
        sections.pop(args[1], None)
    parts = [MARKER]
    for s in SECTIONS:
        if s in sections:
            parts.append(f"<!-- begin:{s} -->\n{sections[s]}\n<!-- end:{s} -->")
    print("\n\n".join(parts))


if __name__ == "__main__":
    main(sys.argv[1:])
