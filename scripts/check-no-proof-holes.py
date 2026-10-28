#!/usr/bin/env python3
"""Guard against unfinished proof holes or new axioms in substantive modules.

The independent statement module Challenge intentionally contains sorry
placeholders and is not scanned here. This textual check
supplements, not replaces, Lean's kernel and Comparator.
"""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent.parent
files = [root / "SpectralGeometry.lean", *sorted((root / "SpectralGeometry").rglob("*.lean"))]
errors = []
for path in files:
    for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if re.search(r"\b(?:sorry|admit|axiom)\b", line):
            errors.append(f"{path.relative_to(root)}:{n}: forbidden proof-source token")
if errors:
    print("\n".join(errors), file=sys.stderr)
    sys.exit(1)
print(f"No sorry, admit or axiom tokens in {len(files)} substantive proof modules.")
