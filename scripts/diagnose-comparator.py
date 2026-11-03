#!/usr/bin/env python3
"""Print source/Challenge declaration differences after a Comparator failure.

This diagnostic only reads built modules. It neither changes the declarations
nor determines whether the independent comparison passes.
"""
import difflib
import json
from pathlib import Path
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent
config = json.loads((root / "comparator.json").read_text())
targets = set(config["theorem_names"])
namespaces = []
names = []
for line in (root / "Challenge.lean").read_text().splitlines():
    namespace = re.fullmatch(r"namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", line.strip())
    if namespace:
        namespaces.append(namespace.group(1))
    elif namespaces and line.strip() == "end " + namespaces[-1]:
        namespaces.pop()
    declaration = re.match(
        r"^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?"
        r"(?:def|abbrev|structure|theorem)\s+([A-Za-z_][A-Za-z0-9_']*)", line
    )
    if declaration:
        name = ".".join(namespaces + [declaration.group(1)])
        if name not in targets:
            names.append(name)

with tempfile.TemporaryDirectory(prefix="comparator-diagnostic-", dir=root / ".lake") as tmp:
    outputs = {}
    for module in (config["challenge_module"], config["solution_module"]):
        commands = [f"import {module}", "set_option pp.all true"]
        for name in names:
            commands.extend([
                f'#eval IO.println "BEGIN {name}"',
                f"#print {name}",
                "run_meta do",
                f"  let info ← Lean.getConstInfo `{name}",
                '  Lean.logInfo m!"levels: {info.levelParams}; height: {info.hints.getHeightEx}"',
                f'#eval IO.println "END {name}"',
            ])
        path = Path(tmp) / f"{module}Declarations.lean"
        path.write_text("\n".join(commands) + "\n")
        result = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=root,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
        outputs[module] = result.stdout
    for name in names:
        blocks = []
        for module, output in outputs.items():
            block = output.split(f"BEGIN {name}\n", 1)[1].split(f"END {name}\n", 1)[0]
            blocks.append(block.splitlines(keepends=True))
        if blocks[0] != blocks[1]:
            print(f"Declaration difference: {name}")
            print("".join(difflib.unified_diff(
                blocks[1], blocks[0], fromfile="Solution", tofile="Challenge"
            )))
