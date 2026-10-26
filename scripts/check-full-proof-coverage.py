#!/usr/bin/env python3
"""Ensure the whole mathematical tree is included in lake check's root target.

The Comparator checks independently written headline statements separately.
This script checks only module reachability, not proofs or theorem equivalence.
"""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent.parent
entry = root / "SpectralGeometry.lean"
math_dir = root / "SpectralGeometry"
source_files = sorted(p for p in math_dir.rglob("*.lean") if p.is_file())
expected = {p.relative_to(root).with_suffix("").as_posix().replace("/", ".") for p in source_files}
contents = entry.read_text(encoding="utf-8")
actual = set(re.findall(r"^public import (SpectralGeometry\.[A-Za-z0-9_.']+)\s*$", contents, re.MULTILINE))
missing = sorted(expected - actual)
surplus = sorted(actual - expected)
issues = []
if not contents.lstrip().startswith("module"):
    issues.append("SpectralGeometry.lean is missing its module header")
if missing:
    issues.append("Modules absent from the full-project entry target: " + ", ".join(missing))
if surplus:
    issues.append("Unknown imported modules: " + ", ".join(surplus))
lakefile = (root / "lakefile.toml").read_text(encoding="utf-8")
if not re.search(r'^defaultTargets\s*=\s*\["SpectralGeometry"\]\s*$', lakefile, re.MULTILINE):
    issues.append('For whole-project lake check, defaultTargets must be ["SpectralGeometry"] (exclude the intentional Challenge sorry).')
if issues:
    for issue in issues:
        print("COVERAGE ERROR:", issue, file=sys.stderr)
    sys.exit(1)
print(f"Whole-project audit covers {len(source_files)} mathematical Lean files via the SpectralGeometry default target.")
print("This is a reachability audit; full proof checking requires: lake check --paranoid")
