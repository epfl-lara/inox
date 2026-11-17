#!/usr/bin/env python3
"""Collects test durations from JUnit XML reports and compares two builds.

usage:
  test_timings.py collect <out.json> <dir>...
      Reads the JUnit XML reports (TEST-*.xml) under each directory and writes
      the duration and outcome of every test case.
  test_timings.py merge <out.json> <in.json>...
      Merges collected timings, for builds that ran their tests in several jobs.
  test_timings.py section <title> <groups.tsv> [<note.md>]
      Prints a Markdown section that compares the test durations of pull
      request builds with those of main: a table with one row per suite, then
      a collapsed block per job. Each line of `groups.tsv` describes a job:
      its label (or nothing), then, separated by tabs, the timings of the
      pull request build (head), of the build of main (base), and of earlier
      builds of main (history), used to estimate how much the durations of
      two builds vary without any change to the code. `note.md` is printed
      after the jobs.

Test durations on CI runners vary a lot between builds of the same code, as a
whole, because runners differ in speed and load, and test by test. The
comparison accounts for both:

- The change of the total duration is given with an interval estimated from
  the history: it is the change between head and base, plus or minus what
  builds of main differ by from the base. Without at least two earlier builds
  of main, there is no interval.
- Each test's change is measured relative to the build's overall speed (the
  median change over all tests), so that a slower runner doesn't make every
  test look slower. The spread of these relative changes, among tests of
  similar durations, gives each test's 95% interval: since most tests are
  unaffected by a change, this spread is the noise between the two builds.
  With at least 3 earlier builds of main, a test's own variation between
  them bounds its noise from below, for tests that vary more than others.
  Tests are only listed when the change is significant after a Bonferroni
  correction for the number of tests compared, and changes the duration by
  at least 50% and 1 s.
"""

import json
import math
import os
import re
import statistics
import sys
import xml.etree.ElementTree as ET

# Added to every duration before taking logarithms, so that tests of a few
# milliseconds, whose durations are mostly noise, don't dominate the ratios.
EPSILON = 0.05
# Tests shorter than this in both builds don't take part in the estimates.
MIN_DURATION = 0.2
# Durations (in seconds, in the base build) that delimit the groups of tests
# whose noise is estimated separately.
BUCKETS = [0.2, 1, 5, 30]
# Listed tests change by at least this factor, and this many seconds.
MIN_FACTOR = 1.5
MIN_SECONDS = 1.0
# Suites are shown in bold when their change is significant and at least this factor.
SUITE_MIN_FACTOR = 1.2
MAX_LISTED = 15

NORMAL = statistics.NormalDist()


def test_key(classname, name):
    # The tests of `inox.TestSuite` are numbered, and the numbers shift when
    # tests are added: keep only the name and options.
    name = re.sub(r"^\s*\d+: ", "", name or "")
    return f"{classname} :: {name}"


def collect(out, dirs):
    tests = {}
    # sbt writes the reports of integration tests to both `it-reports` and
    # `test-reports`: read each suite's report once.
    reports = {}
    for d in dirs:
        for root, dirnames, files in os.walk(d):
            dirnames.sort()
            for f in sorted(files):
                if f.startswith("TEST-") and f.endswith(".xml"):
                    reports.setdefault(f, os.path.join(root, f))
    for _, path in sorted(reports.items()):
        try:
            suite = ET.parse(path).getroot()
        except ET.ParseError:
            continue
        for case in suite.iter("testcase"):
            if case.find("skipped") is not None:
                status = "skipped"
            elif case.find("failure") is not None or case.find("error") is not None:
                status = "failed"
            else:
                status = "passed"
            key = test_key(case.get("classname") or suite.get("name"), case.get("name"))
            n, k = 1, key
            while k in tests:
                n += 1
                k = f"{key} #{n}"
            try:
                time = float(case.get("time") or 0)
            except ValueError:
                time = 0.0
            tests[k] = {"time": time, "status": status}
    json.dump({"tests": tests}, open(out, "w"), indent=0, sort_keys=True)


def merge(out, ins):
    tests = {}
    for path in ins:
        tests.update(load(path))
    json.dump({"tests": tests}, open(out, "w"), indent=0, sort_keys=True)


def load(path):
    return json.load(open(path)).get("tests", {})


def passed(tests):
    return {k: v["time"] for k, v in tests.items()
            if v.get("status") == "passed" and isinstance(v.get("time"), (int, float))}


def log_ratio(h, b):
    return math.log(h + EPSILON) - math.log(b + EPSILON)


def total_log_ratio(head, base):
    common = head.keys() & base.keys()
    th, tb = sum(head[k] for k in common), sum(base[k] for k in common)
    return math.log(th / tb) if th > 0 and tb > 0 else None


def mad_sigma(xs):
    m = statistics.median(xs)
    return 1.4826 * statistics.median(abs(x - m) for x in xs)


def bucket(t):
    return sum(t >= b for b in BUCKETS)


def ratio(x):
    # Large speedups read better as fractions: ×1/1200 rather than ×0.00.
    v = math.exp(x)
    return f"{v:.2f}" if v >= 0.1 else f"1/{1 / v:,.0f}"


def factor(x):
    return f"×{ratio(x)}"


def interval(lo, hi):
    return f"×{ratio(lo)}–{ratio(hi)}"


def seconds(t):
    return f"{t:,.1f} s" if t < 100 else f"{t:,.0f} s"


SAFE = re.compile(r"[^\w .,:;=+\-/()\[\]#@!?*'\"<>&{}~^%$]")


def show(key):
    # Test names come from pull request builds: keep them inert in Markdown.
    # The suite's package is left out, for brevity.
    if " :: " in key:
        suite, name = key.split(" :: ", 1)
        key = f"{suite.rsplit('.', 1)[-1]} :: {name}"
    s = SAFE.sub("?", key)[:150]
    s = s.replace("<", "‹").replace(">", "›").replace("&", "+")
    return f"`{s}`"


def suite_of(key):
    # `<classname> :: <name>`: the suite's class, without its package.
    return key.split(" :: ", 1)[0].rsplit(".", 1)[-1]


class Comparison:
    """The comparison of one job's build with the build of main."""

    def __init__(self, label, head_path, base_path, history_paths):
        self.label = label
        head, base = passed(load(head_path)), passed(load(base_path))
        history = [passed(load(p)) for p in history_paths]
        self.head, self.base = head, base
        common = sorted(head.keys() & base.keys())
        self.common = common
        self.enough = len(common) >= 10
        if not self.enough:
            return

        self.th, self.tb = sum(head[k] for k in common), sum(base[k] for k in common)
        self.total = math.log(self.th / self.tb) if self.th > 0 and self.tb > 0 else 0.0
        # What builds of main differ by, in total, from the base build.
        noise = [r for r in (total_log_ratio(h, base) for h in history) if r is not None]
        self.total_ci = None
        if len(noise) >= 2:
            # The difference between two builds of the same code has the
            # spread of the history's differences: a t interval with
            # len(noise) - 1 degrees of freedom, centered on the observed change.
            sd = math.sqrt(sum(r * r for r in noise) / len(noise))
            q = t_quantile(0.975, len(noise))
            self.total_ci = (self.total - q * sd, self.total + q * sd)

        # Relative changes, test by test.
        measured = [k for k in common if max(head[k], base[k]) >= MIN_DURATION]
        self.measured = measured
        self.per_test = len(measured) >= 10
        if not self.per_test:
            return
        d = {k: log_ratio(head[k], base[k]) for k in measured}
        speed = self.speed = statistics.median(d.values())
        rel = self.rel = {k: d[k] - speed for k in measured}
        pooled = mad_sigma(list(rel.values()))
        sigma_of_bucket = {}
        for b in range(len(BUCKETS) + 1):
            xs = [rel[k] for k in measured if bucket(base[k]) == b]
            sigma_of_bucket[b] = mad_sigma(xs) if len(xs) >= 20 else pooled
        # Some tests vary much more than others of similar durations, such as
        # the first test of a suite, which warms up the JIT. With enough
        # history, a test's own variation between builds of main bounds its
        # noise from below.
        hist_rel = []
        for h in history:
            hk = [k for k in measured if k in h]
            if len(hk) >= 10:
                hd = {k: log_ratio(h[k], base[k]) for k in hk}
                m = statistics.median(hd.values())
                hist_rel.append((h, m, {k: hd[k] - m for k in hk}))

        def own_sigma(k):
            xs = [r[k] for _, _, r in hist_rel if k in r]
            # Each history difference involves the noise of two builds, as
            # does the difference between this build and the base.
            return math.sqrt(sum(x * x for x in xs) / len(xs)) if len(xs) >= 3 else 0.0

        sigma = self.sigma = {k: max(sigma_of_bucket[bucket(base[k])], own_sigma(k), 0.01)
                              for k in measured}
        z_crit = NORMAL.inv_cdf(1 - 0.05 / (2 * len(measured)))

        def significant(k, sign):
            r, s = rel[k] * sign, sigma[k]
            return (r / s > z_crit and r > math.log(MIN_FACTOR)
                    and abs(head[k] - base[k]) >= MIN_SECONDS)

        self.listed = {sign: sorted((k for k in measured if significant(k, sign)),
                                    key=lambda k: -rel[k] * sign)
                       for sign in (1, -1)}

        # Each suite's change, relative to the median test like the tests'.
        # Its noise combines those of its tests, weighted by their durations,
        # and is at least the suite's own variation between builds of main.
        self.suites = {}
        by_suite = {}
        for k in common:
            by_suite.setdefault(suite_of(k), []).append(k)
        for suite, ks in by_suite.items():
            sb, sh = sum(base[k] for k in ks), sum(head[k] for k in ks)
            ms = [k for k in ks if k in sigma]
            if not ms or sb <= 0:
                continue
            r = log_ratio(sh, sb) - speed
            var = sum((base[k] / sb) ** 2 * sigma[k] ** 2 for k in ms)
            hs = []
            for h, m, _ in hist_rel:
                if all(k in h for k in ks):
                    hs.append(log_ratio(sum(h[k] for k in ks), sb) - m)
            if len(hs) >= 3:
                var = max(var, sum(x * x for x in hs) / len(hs))
            self.suites[suite] = (sb, sh, r, max(math.sqrt(var), 0.01))
        # The tests of a suite share the load of the runner while they run, so
        # their noise doesn't average out as if independent: the spread of the
        # suites' changes, since most suites are unaffected by a change,
        # bounds each suite's noise from below.
        big = [v[2] for v in self.suites.values() if v[0] >= MIN_SECONDS]
        if len(big) >= 8:
            floor = mad_sigma(big)
            self.suites = {k: (sb, sh, r, max(sg, floor)) for k, (sb, sh, r, sg) in self.suites.items()}

    def summary(self):
        prefix = f"<b>{self.label}</b>: " if self.label else ""
        if not self.enough:
            return f"{prefix}too few tests passed in both builds to compare them."
        ci = f" ({interval(*self.total_ci)})" if self.total_ci else ""
        s = f"{prefix}total {factor(self.total)}{ci}"
        if not self.per_test:
            return s
        counts = ", ".join(f"{len(self.listed[sign])} test{'s' if len(self.listed[sign]) != 1 else ''} {what}"
                           for sign, what in ((1, "slower"), (-1, "faster")) if self.listed[sign])
        return f"{s}, {counts or 'no test changed significantly'}"

    def details(self):
        totals = (f"{len(self.common):,} tests took {seconds(self.th)}, against {seconds(self.tb)} on `main`"
                  + ("" if self.total_ci else " (no interval yet: fewer than 2 earlier builds of `main`)") + ".")
        if not self.per_test:
            return totals
        out = [f"{totals} The median test took {factor(self.speed)} as long, mostly from the runners' "
               f"speed: changes are relative to it, with 95% intervals.\n"]
        z95 = NORMAL.inv_cdf(0.975)
        for sign, what in ((1, "Slower"), (-1, "Faster")):
            ks = self.listed[sign]
            if not ks:
                continue
            out.append(f"{what}:\n")
            for k in ks[:MAX_LISTED]:
                r, sg = self.rel[k], self.sigma[k]
                out.append(f"- {show(k)}: {seconds(self.base[k])} → {seconds(self.head[k])}, "
                           f"{factor(r)} ({interval(r - z95 * sg, r + z95 * sg)})")
            if len(ks) > MAX_LISTED:
                out.append(f"- and {len(ks) - MAX_LISTED} more")
            out.append("")
        return "\n".join(out).rstrip("\n")


def suite_table(comparisons):
    """One row per suite: its duration on main and its change relative to the
    median test, combining the jobs (weighted by the inverse of their noise)."""
    rows = {}
    for c in comparisons:
        for suite, (sb, sh, r, sg) in getattr(c, "suites", {}).items():
            rows.setdefault(suite, []).append((sb, sh, r, sg))
    rows = {s: v for s, v in rows.items() if statistics.mean(x[0] for x in v) >= MIN_SECONDS}
    if not rows:
        return ""
    z95 = NORMAL.inv_cdf(0.975)
    stats = {}
    for suite, v in rows.items():
        w = [1 / (sg * sg) for *_, sg in v]
        r = sum(wi * x[2] for wi, x in zip(w, v)) / sum(w)
        sg = 1 / math.sqrt(sum(w))
        stats[suite] = (statistics.mean(x[0] for x in v), statistics.mean(x[1] for x in v), r, sg)
    z_crit = NORMAL.inv_cdf(1 - 0.05 / (2 * len(stats)))
    jobs = len(comparisons)
    out = ["| Suite | `main` | This PR | Change (95%) |", "|---|---:|---:|---:|"]
    for suite, (sb, sh, r, sg) in sorted(stats.items(), key=lambda kv: -kv[1][2]):
        ch = f"{factor(r)} ({interval(r - z95 * sg, r + z95 * sg)})"
        if abs(r) / sg > z_crit and abs(r) > math.log(SUITE_MIN_FACTOR):
            ch = f"<b>{ch}</b>"
        out.append(f"| {show(suite)} | {seconds(sb)} | {seconds(sh)} | {ch} |")
    note = (f"Suites that take at least {MIN_SECONDS:g} s, largest slowdowns first"
            + (f", averaged over the {jobs} jobs" if jobs > 1 else "")
            + ". Changes are relative to the median test, and in bold when significant.")
    return "\n".join(out) + f"\n\n<sub>{note}</sub>"


def section(title, groups_path, note_path=None):
    """Prints the section of the comment: the suites' table, then one
    collapsed block per job. Each line of `groups_path` holds a job's label
    (or nothing), then its head, base and history timings, separated by tabs."""
    comparisons = []
    for line in open(groups_path):
        fields = line.rstrip("\n").split("\t")
        if len(fields) >= 3:
            comparisons.append(Comparison(fields[0], fields[1], fields[2], fields[3:]))
    if not comparisons:
        return
    print(f"### {title}\n")
    table = suite_table(comparisons)
    if table:
        print(table + "\n")
    for c in comparisons:
        if c.enough:
            print(f"<details><summary>{c.summary()}</summary>\n\n{c.details()}\n\n</details>\n")
        else:
            print(c.summary() + "\n")
    if note_path:
        note = open(note_path).read().strip()
        if note:
            print(note + "\n")
    print(f"<sub>Tests are listed when their change, relative to the median test, is significant "
          f"after a Bonferroni correction and is at least {MIN_FACTOR:g}× and {MIN_SECONDS:g} s. "
          f"See `scripts/test_timings.py`.</sub>")


def t_quantile(p, df):
    # Quantiles of Student's t distribution, for the few degrees of freedom of
    # the history, and the normal quantile beyond.
    table = {1: 12.706, 2: 4.303, 3: 3.182, 4: 2.776, 5: 2.571, 6: 2.447, 7: 2.365,
             8: 2.306, 9: 2.262, 10: 2.228, 12: 2.179, 15: 2.131, 20: 2.086, 30: 2.042}
    assert p == 0.975
    for k in sorted(table, reverse=True):
        if df >= k:
            return table[k] if df <= 30 else NORMAL.inv_cdf(p)
    return table[1]


def main(args):
    if len(args) >= 3 and args[0] == "collect":
        collect(args[1], args[2:])
    elif len(args) >= 3 and args[0] == "merge":
        merge(args[1], args[2:])
    elif len(args) in (3, 4) and args[0] == "section":
        section(*args[1:])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
