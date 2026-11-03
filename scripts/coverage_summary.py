#!/usr/bin/env python3
"""Prints a Markdown summary of an scoverage XML report.

usage: coverage_summary.py <scoverage.xml>
"""

import sys
import xml.etree.ElementTree as ET


def main(path):
    root = ET.parse(path).getroot()
    print("## Test coverage\n")
    print(f"**Statements: {float(root.get('statement-rate')):.1f}%** "
          f"({root.get('statements-invoked')} / {root.get('statement-count')}), "
          f"**branches: {float(root.get('branch-rate')):.1f}%**\n")
    print("| Package | Statements | Covered |")
    print("|---|---:|---:|")
    for pkg in sorted(root.iter("package"), key=lambda p: p.get("name")):
        print(f"| `{pkg.get('name')}` | {pkg.get('statement-count')} "
              f"| {float(pkg.get('statement-rate')):.1f}% |")


if __name__ == "__main__":
    main(sys.argv[1])
