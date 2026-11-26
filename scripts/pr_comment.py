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

from test_timings import (MAJOR_FACTOR, MAJOR_NEW_SECONDS, MAJOR_SECONDS, MAX_LISTED, MIN_FACTOR,
                          MIN_SECONDS, MIN_SECONDS_SINGLE, factor, interval, seconds, show)

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


# GitHub refuses comments longer than 65,536 characters.
MAX_LENGTH = 60000


# A test that only one job runs (or a job's own tests) is only listed when the
# job has at least this many earlier builds of main to estimate the noise of
# each test from.
MIN_HISTORY = 3


def timings_table(sections, with_details=True):
    """The table of test durations, one row per job, and the tests that
    changed, collapsed. A test's change is only listed when it is confirmed:
    the jobs of a group (the word their labels start with, such as Inox) run
    the same tests on different runners, and noise rarely makes the same test
    slower, or faster, in two of them. A group with a single job needs enough
    history for its tests' noise to be estimated well. Major slowdowns are
    too large for noise, and are shown first, in every job that has them."""
    parts = [sections[s] for s in TIMINGS if s in sections]
    if not parts:
        return ""
    jobs = [j for p in parts for j in p.get("jobs", [])]
    if not jobs:
        # No job has timings to compare yet: an empty table would only be a header.
        return ""
    notes = []
    for p in parts:
        for n in p.get("notes", []):
            if n not in notes:
                notes.append(n)
    groups = {}
    for j in jobs:
        groups.setdefault(j["label"].split(" ", 1)[0], []).append(j)

    def short(j):
        return j["label"].split(" ", 1)[1] if " " in j["label"] else j["label"]

    # Confirmed changes, per test: [(job, test)] in the jobs that saw them.
    listed = {1: [], -1: []}
    unconfirmed = 0
    for group, gj in groups.items():
        seen = {}
        for j in gj:
            for t in j.get("tests", []):
                seen.setdefault((t["key"], 1 if t["rel"] > 0 else -1), []).append((j, t))
        for (key, sign), occ in seen.items():
            single = (len(gj) == 1 and gj[0].get("history", 0) >= MIN_HISTORY
                      and abs(occ[0][1]["head"] - occ[0][1]["base"]) >= MIN_SECONDS_SINGLE)
            if len(gj) >= 2 and len(occ) >= 2 or single:
                listed[sign].append(occ)
            else:
                unconfirmed += 1
    def gained(t):
        return t["head"] - t["base"]

    for sign in listed:
        listed[sign].sort(key=lambda occ: -max(gained(t) * sign for _, t in occ))
    # Major slowdowns, per test: [(job, test)].
    major = {}
    for j in jobs:
        for t in j.get("major", []):
            major.setdefault(t["key"], []).append((j, t))
    major = sorted(major.values(), key=lambda occ: -max(t["head"] - (t["base"] or 0) for _, t in occ))
    counts = {}
    for sign in listed:
        for occ in listed[sign]:
            for j, _ in occ:
                counts.setdefault(id(j), {1: 0, -1: 0})[sign] += 1

    out = ["### Test durations", ""]
    if major:
        out += [f"**Much slower** (by {MAJOR_FACTOR:g}× and {MAJOR_SECONDS:g} s or more, "
                f"or new and over {MAJOR_NEW_SECONDS:g} s):", ""]
        for occ in major[:MAX_LISTED]:
            j, t = max(occ, key=lambda jt: jt[1]["head"])
            others = [short(o) for o, _ in occ if o is not j]
            change = (f"{seconds(t['base'])} → {seconds(t['head'])}, {factor(t['rel'])}"
                      if t.get("base") is not None else f"new, {seconds(t['head'])}")
            out.append(f"- {show(t['key'])}: {change} on {short(j)}"
                       + (f"; also on {', '.join(others)}" if others else ""))
        if len(major) > MAX_LISTED:
            out.append(f"- and {len(major) - MAX_LISTED} more")
        out.append("")
    out += ["| Job | Total time | Tests |", "|---|---:|---|"]
    for j in jobs:
        if not j.get("enough"):
            out.append(f"| {j['label']} | too few tests | |")
            continue
        if j.get("ci"):
            lo, hi = j["ci"]
            total = f"{factor(j['total'])} ({interval(lo, hi)})"
            if lo > 0 or hi < 0:
                total = f"<b>{total}</b>"
        else:
            total = "–"
        c = counts.get(id(j), {1: 0, -1: 0})
        tests = ", ".join(f"{c[sign]} {what}" for sign, what in ((1, "slower"), (-1, "faster")) if c[sign])
        if j.get("major"):
            tests = ", ".join(x for x in (f"<b>{len(j['major'])} much slower</b>", tests) if x)
        out.append(f"| {j['label']} | {total} | {tests or '–'} |")
    out.append("")

    n = len(listed[1]) + len(listed[-1])
    lines = []
    for sign, what in ((1, "Slower"), (-1, "Faster")):
        if not listed[sign]:
            continue
        lines += [f"{what}:", ""]
        for occ in listed[sign][:MAX_LISTED]:
            j, t = max(occ, key=lambda jt: abs(jt[1]["rel"]))
            others = [short(o) for o, _ in occ if o is not j]
            lines.append(f"- {show(t['key'])}: {seconds(t['base'])} → {seconds(t['head'])}, "
                         f"{factor(t['rel'])} ({interval(t['lo'], t['hi'])}) on {short(j)}"
                         + (f"; also on {', '.join(others)}" if others else ""))
        if len(listed[sign]) > MAX_LISTED:
            lines.append(f"- and {len(listed[sign]) - MAX_LISTED} more")
        lines.append("")
    explain = (f"Changes are relative to each job's median test, which absorbs the runners' speed. "
               f"A test is listed when its change is significant (Bonferroni) and at least "
               f"{MIN_FACTOR:g}× and {MIN_SECONDS:g} s in two jobs, or, for a single job, once "
               f"{MIN_HISTORY} earlier builds of `main` give each test's own noise and the change "
               f"is of {MIN_SECONDS_SINGLE:g} s or more.")
    if unconfirmed:
        explain += f" {unconfirmed} change{'s' if unconfirmed > 1 else ''} seen in a single job only {'were' if unconfirmed > 1 else 'was'} left out."
    if n and with_details:
        out += [f"<details><summary>Tests that changed ({n})</summary>", "", *lines, explain, "", "</details>", ""]
    elif n:
        out += [f"_{n} tests changed: too many to list here._", ""]
    if any(j.get("enough") and not j.get("ci") for j in jobs):
        notes.insert(0, "A total is shown once 2 earlier builds of `main` give its interval.")
    if notes:
        out.append("<sub>" + " ".join(x.strip("_") for x in notes) + "</sub>")
    return "\n".join(out).strip("\n")


def render(sections, with_details=True):
    parts = [MARKER]
    for s in MARKDOWN:
        if s in sections:
            parts.append(f"<!-- begin:{s} -->\n{sections[s]}\n<!-- end:{s} -->")
    table = timings_table(sections, with_details)
    if table:
        parts.append(table)
    for s in TIMINGS:
        if s in sections:
            parts.append(f"<!-- data:{s} {encode(sections[s])} -->")
    body = "\n\n".join(parts)
    if len(body) > MAX_LENGTH and with_details:
        return render(sections, with_details=False)
    return body


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
