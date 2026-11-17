#!/usr/bin/env python3
"""Collects test durations from JUnit XML reports and compares two builds.

usage:
  test_timings.py collect <out.json> <dir>...
      Reads the JUnit XML reports (TEST-*.xml) under each directory and writes
      the duration and outcome of every test case.
  test_timings.py merge <out.json> <in.json>...
      Merges collected timings, for builds that ran their tests in several jobs.
  test_timings.py compare <title> <head.json> <base.json> [<history.json>...]
      Prints a Markdown section that compares the test durations of the build
      in `head.json` with those of `base.json`. Each `history.json` is another
      build of the same code base as `base.json` (earlier builds of main),
      used to estimate how much the durations of two builds vary without any
      change to the code.

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


def factor(x):
    return f"×{math.exp(x):.2f}"


def interval(lo, hi):
    return f"×{math.exp(lo):.2f} to ×{math.exp(hi):.2f}"


def seconds(t):
    return f"{t:,.1f} s" if t < 100 else f"{t:,.0f} s"


SAFE = re.compile(r"[^\w .,:;=+\-/()\[\]#@!?*'\"<>&{}~^%$]")


def show(key):
    # Test names come from pull request builds: keep them inert in Markdown.
    s = SAFE.sub("?", key)[:150]
    s = s.replace("<", "‹").replace(">", "›").replace("&", "+")
    return f"`{s}`"


def compare(title, head_path, base_path, history_paths):
    head, base = passed(load(head_path)), passed(load(base_path))
    history = [passed(load(p)) for p in history_paths]
    common = sorted(head.keys() & base.keys())

    print(f"### {title}\n")
    if len(common) < 10:
        print("_Too few tests passed in both builds to compare their durations._")
        return

    th, tb = sum(head[k] for k in common), sum(base[k] for k in common)
    total = math.log(th / tb) if th > 0 and tb > 0 else 0.0
    # What builds of main differ by, in total, from the base build.
    noise = [r for r in (total_log_ratio(h, base) for h in history) if r is not None]
    if len(noise) >= 2:
        # The difference between two builds of the same code has the spread of
        # the history's differences: a t interval with len(noise) - 1 degrees
        # of freedom, centered on the observed change.
        sd = math.sqrt(sum(r * r for r in noise) / len(noise))
        q = t_quantile(0.975, len(noise))
        total_ci = f"{interval(total - q * sd, total + q * sd)}"
    else:
        total_ci = "no interval: fewer than 2 earlier builds of `main`"

    print("| | `main` | This PR | Change (95% interval) |")
    print("|---|---:|---:|---:|")
    print(f"| Total duration of the {len(common):,} tests that passed in both | {seconds(tb)} | {seconds(th)} | "
          f"{factor(total)} ({total_ci}) |")

    # Relative changes, test by test.
    measured = [k for k in common if max(head[k], base[k]) >= MIN_DURATION]
    if len(measured) < 10:
        print("\n_Too few tests take long enough to compare them one by one._")
        return
    d = {k: log_ratio(head[k], base[k]) for k in measured}
    speed = statistics.median(d.values())
    rel = {k: d[k] - speed for k in measured}
    pooled = mad_sigma(list(rel.values()))
    sigma_of_bucket = {}
    for b in range(len(BUCKETS) + 1):
        xs = [rel[k] for k in measured if bucket(base[k]) == b]
        sigma_of_bucket[b] = mad_sigma(xs) if len(xs) >= 20 else pooled
    sigma = {k: max(sigma_of_bucket[bucket(base[k])], 0.01) for k in measured}
    z_crit = NORMAL.inv_cdf(1 - 0.05 / (2 * len(measured)))
    z95 = NORMAL.inv_cdf(0.975)

    def significant(k, sign):
        r, s = rel[k] * sign, sigma[k]
        return (r / s > z_crit and r > math.log(MIN_FACTOR)
                and abs(head[k] - base[k]) >= MIN_SECONDS)

    print(f"\nThis build ran {factor(speed)} as long as `main` on the median test, which is mostly "
          f"the difference in speed between the two runners. Relative to that, "
          f"two builds' durations of a test typically differ by {factor(pooled)} "
          f"(one standard deviation, over {len(measured):,} tests of at least {MIN_DURATION} s).")

    for sign, what in ((1, "slower"), (-1, "faster")):
        ks = sorted((k for k in measured if significant(k, sign)), key=lambda k: -rel[k] * sign)
        if not ks:
            print(f"\nNo test got significantly {what} relative to the others.")
            continue
        print(f"\n<details{' open' if sign == 1 else ''}><summary><b>{len(ks)} test{'s' if len(ks) > 1 else ''} "
              f"got significantly {what}</b> relative to the others</summary>\n")
        print("| Test | `main` | This PR | Relative change (95% interval) |")
        print("|---|---:|---:|---:|")
        for k in ks[:MAX_LISTED]:
            lo, hi = rel[k] - z95 * sigma[k], rel[k] + z95 * sigma[k]
            print(f"| {show(k)} | {seconds(base[k])} | {seconds(head[k])} | {factor(rel[k])} ({interval(lo, hi)}) |")
        if len(ks) > MAX_LISTED:
            print(f"\n_And {len(ks) - MAX_LISTED} more._")
        print("\n</details>")

    print("\n<sub>Tests are listed when their change relative to the build's median is significant "
          "after a Bonferroni correction for the number of tests, and changes their duration by at least "
          f"{MIN_FACTOR:g}× and {MIN_SECONDS:g} s. See `scripts/test_timings.py`.</sub>")


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
    elif len(args) >= 4 and args[0] == "compare":
        compare(args[1], args[2], args[3], args[4:])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
