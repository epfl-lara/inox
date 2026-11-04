#!/usr/bin/env python3
"""Summarizes scoverage XML reports.

usage:
  coverage_summary.py report <scoverage.xml>
      Prints a Markdown summary, with per-package statement coverage.
  coverage_summary.py json <scoverage.xml> <out.json>
      Writes the overall and per-package coverage rates as JSON.
  coverage_summary.py compare <head.json> [<base.json>]
      Prints a Markdown table of the coverage in `head.json`, with the
      difference to `base.json` when it is given.
"""

import json
import re
import sys
import xml.etree.ElementTree as ET

MARKER = "<!-- inox-coverage -->"


def summarize(path):
    root = ET.parse(path).getroot()
    return {
        "statements": float(root.get("statement-rate")),
        "branches": float(root.get("branch-rate")),
        "statement-count": int(root.get("statement-count")),
        "statements-invoked": int(root.get("statements-invoked")),
        "packages": {
            pkg.get("name"): float(pkg.get("statement-rate"))
            for pkg in root.iter("package")
        },
    }


def report(path):
    s = summarize(path)
    print("## Test coverage\n")
    print(f"**Statements: {s['statements']:.1f}%** "
          f"({s['statements-invoked']} / {s['statement-count']}), "
          f"**branches: {s['branches']:.1f}%**\n")
    print("| Package | Covered |")
    print("|---|---:|")
    for name, rate in sorted(s["packages"].items()):
        print(f"| `{name}` | {rate:.1f}% |")


def delta(head, base):
    if base is None:
        return "n/a"
    d = head - base
    if abs(d) < 0.05:
        return "±0.0"
    return f"{'+' if d > 0 else '−'}{abs(d):.1f}"


def compare(head_path, base_path=None):
    head = json.load(open(head_path))
    base = json.load(open(base_path)) if base_path else None
    get = lambda key: base[key] if base else None

    print(MARKER)
    print("### Test coverage\n")
    print("| | Coverage | Δ vs `main` |")
    print("|---|---:|---:|")
    print(f"| Statements | {head['statements']:.1f}% | {delta(head['statements'], get('statements'))} |")
    print(f"| Branches | {head['branches']:.1f}% | {delta(head['branches'], get('branches'))} |")

    if base:
        changed = []
        names = set(head["packages"]) | set(base["packages"])
        # The JSON comes from pull request builds: only print plausible package names.
        for name in sorted(n for n in names if re.fullmatch(r"[\w.]+", n)):
            h, b = head["packages"].get(name), base["packages"].get(name)
            if h is None or b is None or abs(h - b) >= 0.05:
                changed.append((name, h, b))
        if changed:
            print("\n<details><summary>Packages with changed statement coverage</summary>\n")
            print("| Package | Coverage | Δ vs `main` |")
            print("|---|---:|---:|")
            for name, h, b in changed:
                cov = f"{h:.1f}%" if h is not None else "removed"
                d = delta(h, b) if h is not None and b is not None else "new" if b is None else "n/a"
                print(f"| `{name}` | {cov} | {d} |")
            print("\n</details>")
    else:
        print("\n_No coverage data from `main` to compare with._")


def main(args):
    if len(args) == 2 and args[0] == "report":
        report(args[1])
    elif len(args) == 3 and args[0] == "json":
        json.dump(summarize(args[1]), open(args[2], "w"), indent=2, sort_keys=True)
    elif len(args) in (2, 3) and args[0] == "compare":
        compare(*args[1:])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
