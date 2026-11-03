#!/usr/bin/env python3
"""Check that one auditable Mathlib-only Challenge backs the single Palomar config.

This is only a static packaging gate: Lean and Comparator perform the actual
type checking, independent statement comparison, and kernel verification.
"""
import json
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parent.parent
errors = []
challenge = root / "Challenge.lean"
solution = root / "Solution.lean"
config_path = root / "comparator.json"
try:
    statement = challenge.read_text(encoding="utf-8")
    config = json.loads(config_path.read_text(encoding="utf-8"))
    solution_text = solution.read_text(encoding="utf-8")
except (OSError, UnicodeError, ValueError) as error:
    print(f"Comparator packaging error: {error}", file=sys.stderr)
    sys.exit(1)

if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
    errors.append("Comparator must use root Challenge and Solution modules")
expected = [
    "SpectralGeometry.infiniteLocalMatchingFullEigenspace_finiteDimensional",
    "SpectralGeometry.AmmannBeenker.mate_involutive",
    "SpectralGeometry.AmmannBeenker.finite_norm_sublevel",
    "SpectralGeometry.AmmannBeenker.potential_proper",
    "SpectralGeometry.AmmannBeenker.exists_nine_level_fullProducts"
]
names = config.get("theorem_names")
if names != expected:
    errors.append("This Palomar candidate must select the geometric full-product response and its four supporting witness lemmas")
if config.get("definition_names") != []:
    errors.append("Concrete model definitions must be compared by body, with no definition holes")
for key in ("theorem_names", "definition_names"):
    names = config.get(key)
    if not isinstance(names, list) or not all(isinstance(n, str) for n in names):
        errors.append(f"{key} must be a list of qualified names")
    elif len(names) != len(set(names)) or (key == "theorem_names" and not names):
        errors.append(f"{key} has duplicates or an empty selection")

headers = re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", statement, re.MULTILINE)
if headers != ["Mathlib"]:
    errors.append(f"Challenge must import exactly Mathlib, got {headers!r}")
if "import SpectralGeometry" in statement:
    errors.append("Challenge must never import substantive SpectralGeometry proofs")
if "public import SpectralGeometry" not in solution_text:
    errors.append("Solution must import the substantive mathematical source")
if len(statement.splitlines()) > 1000 or len(statement.encode("utf-8")) > 100 * 1024:
    errors.append("Challenge exceeds Palomar's 1000-line/100-KiB limits")

decls = {"theorem": set(), "definition": set()}
pattern = r"^\s*(?:@\[expose\]\s+)?(?:noncomputable\s+)?(theorem|def|abbrev|structure)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
namespaces = []
for line in statement.splitlines():
    namespace = re.fullmatch(r"namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", line.strip())
    if namespace:
        namespaces.append(namespace.group(1))
    elif namespaces and line.strip() == "end " + namespaces[-1]:
        namespaces.pop()
    declaration = re.match(pattern, line)
    if declaration:
        kind, name = declaration.groups()
        decls["theorem" if kind == "theorem" else "definition"].add(".".join(namespaces + [name]))
for key, kind in (("theorem_names", "theorem"), ("definition_names", "definition")):
    for name in config.get(key, []) if isinstance(config.get(key), list) else []:
        if name not in decls[kind]:
            errors.append(f"{name}: missing standalone {kind} declaration in Challenge")

files = sorted(path.name for path in root.glob("comparator*.json"))
if files != ["comparator.json"]:
    errors.append(f"Expected one root Comparator config, found {files}")

for error in errors:
    print("Comparator coverage error:", error, file=sys.stderr)
if errors:
    sys.exit(1)
print(f"Single Mathlib-only Challenge: {len(statement.splitlines())} lines, "
      f"{len(statement.encode('utf-8'))} bytes; "
      f"{len(config['theorem_names'])} selected theorem(s) and "
      f"{len(config['definition_names'])} selected definitions.")
