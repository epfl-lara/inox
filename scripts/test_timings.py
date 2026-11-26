#!/usr/bin/env python3
"""Collects test durations from JUnit XML reports and compares two builds.

usage:
  test_timings.py collect <out.json> <dir>...
      Reads the JUnit XML reports (TEST-*.xml) under each directory and writes
      the duration and outcome of every test case.
  test_timings.py merge <out.json> <in.json>...
      Merges collected timings, for builds that ran their tests in several jobs.
  test_timings.py section <groups.tsv> [<note.md>]
      Prints, as JSON, the results for the comment's table of test durations of
      the jobs of a workflow, and the tests that changed significantly. Each
      line of `groups.tsv` describes a job: its label, then, separated by
      tabs, the timings of the pull request build (head), of the build of
      main (base), and of earlier builds of main (history), used to estimate
      how much the durations of two builds vary without any change to the
      code. The notes of `note.md` are shown below the table.

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
  at least 50% and 5 s. Shorter tests often move by a few seconds between
  runners, which isn't worth reporting.
- A test that becomes slower by at least 5× and 30 s, or a new test of more
  than 2 minutes, is a major slowdown: no runner noise accounts for it, so it
  is reported on its own, ahead of the other changes, without the statistics.
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
MIN_SECONDS = 5.0
# Major slowdowns: tests that become slower by at least this factor and this
# many seconds (relative to the build's overall speed), and new tests that
# take at least this long.
MAJOR_FACTOR = 5.0
MAJOR_SECONDS = 30.0
MAJOR_NEW_SECONDS = 120.0
MAX_LISTED = 15
# The changed tests of each job kept in the comment's data.
MAX_STORED = 40

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


class Comparison:
    """The comparison of one job's build with the build of main."""

    def __init__(self, label, head_path, base_path, history_paths):
        # Labels come from artifact names, which pull request builds choose.
        self.label = SAFE.sub("?", label)[:60].replace("<", "‹").replace(">", "›").replace("&", "+")
        head, base = passed(load(head_path)), passed(load(base_path))
        history = [passed(load(p)) for p in history_paths]
        self.head, self.base = head, base
        common = sorted(head.keys() & base.keys())
        self.common = common
        self.major = []
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

        self.history = len(hist_rel)

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

        # The time a test gains or loses, at the head build's speed.
        def gained(k):
            return head[k] - base[k] * math.exp(speed)

        def major(k):
            return rel[k] > math.log(MAJOR_FACTOR) and gained(k) >= MAJOR_SECONDS

        self.major = sorted((k for k in measured if major(k)), key=lambda k: -gained(k))
        self.major += sorted((k for k in head.keys() - base.keys() if head[k] >= MAJOR_NEW_SECONDS),
                             key=lambda k: -head[k])
        # Major slowdowns are reported apart, and the others by the time they
        # gain or lose: a test that is 3 minutes slower matters more than one
        # that is 10 times slower by a few seconds.
        self.listed = {sign: sorted((k for k in measured if significant(k, sign) and k not in self.major),
                                    key=lambda k: -gained(k) * sign)
                       for sign in (1, -1)}

    def data(self):
        """The job's results, for the comment (see scripts/pr_comment.py)."""
        job = {"label": self.label, "enough": self.enough, "history": 0, "tests": []}
        if not self.enough:
            return job
        job.update(total=self.total, base=self.tb, head=self.th, count=len(self.common),
                   ci=list(self.total_ci) if self.total_ci else None)
        if not self.per_test:
            return job
        job.update(history=self.history, speed=self.speed)
        job["major"] = [{"key": k, "base": self.base.get(k), "head": self.head[k],
                         "rel": round(self.rel[k], 4) if k in self.rel else None}
                        for k in self.major[:MAX_STORED]]
        z95 = NORMAL.inv_cdf(0.975)
        for sign in (1, -1):
            for k in self.listed[sign][:MAX_STORED]:
                r, sg = self.rel[k], self.sigma[k]
                job["tests"].append({"key": k, "rel": round(r, 4), "lo": round(r - z95 * sg, 4),
                                     "hi": round(r + z95 * sg, 4), "base": self.base[k], "head": self.head[k]})
        return job


def section(groups_path, note_path=None):
    """Prints, as JSON, the results of the jobs of a workflow for the comment's
    table of test durations (see scripts/pr_comment.py, which shows those of
    all workflows together). Each line of `groups_path` holds a job's label,
    then its head, base and history timings, separated by tabs."""
    comparisons = []
    for line in open(groups_path):
        fields = line.rstrip("\n").split("\t")
        if len(fields) >= 3:
            comparisons.append(Comparison(fields[0], fields[1], fields[2], fields[3:]))
    notes = []
    if note_path:
        note = open(note_path).read().strip()
        if note:
            notes.append(note)
    json.dump({"jobs": [c.data() for c in comparisons], "notes": notes}, sys.stdout, ensure_ascii=False)
    print()


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
    elif len(args) in (2, 3) and args[0] == "section":
        section(*args[1:])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
