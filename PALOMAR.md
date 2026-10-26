# Palomar submission preparation (draft)

This branch stages a comparator-ready **canonical-product** slice of the
Jules Spectral Geometry project. It does not yet establish successful
Palomar verification or an independently assessed research contribution.

## Statement and proof boundary

- `Challenge.lean` imports only Mathlib and independently declares three
  paired-product definitions, an admissibility structure and six theorem
  statements; its `sorry` terms are intentional statement placeholders.
- `Solution.lean` imports the existing substantive canonical-product proofs.
- `comparator.json` compares six theorems and three explicit definitions.
- `formalization.yaml` records provenance and the narrow scope.
- `lake-manifest.json` pins Mathlib and transitive dependencies to commits.
- This branch includes a module-system port of existing Lean files, which
  must pass a fresh Lake build and Comparator check before it is usable.

## Limitations

The canonical product's prescribed zero line is a consequence of its paired
factors, not a theorem about the zeros of the Riemann zeta function.
The spectral-operator results elsewhere in this repository are NOT audited
by this Comparator configuration. Connecting eigenvalues from the concrete
geometric model with these product levels remains a separate goal.

## Required checks

```sh
python3 scripts/check-palomar-layout.py
lake exe cache get
lake build
bash scripts/verify-comparator.sh
```

The shell script needs Bubblewrap and the independent kernels bundled with
an appropriate Lean toolchain. Inspect actual CI conclusions: compilation
alone does not establish Comparator equivalence.

## Publication decisions the maintainer must make

1. This branch proposes **Apache-2.0** as a repository licence, which must
   be explicitly reviewed before merging or publishing. No licence was
   present on `main` when this branch was created.
2. `alexodas/jules` is currently PRIVATE. Palomar requires a PUBLIC
   repository at the full submitted SHA. This branch does not change visibility.
3. Verify the metadata authors, credits, source provenance and research
   interest; no novelty or independent scientific review is claimed.
4. No Palomar submission, release, or merge is performed automatically.

## Coverage: two different verification guarantees

The Palomar `comparator.json` still compares six independent canonical-product
statements (and three definitions) from the standalone Mathlib-only
`Challenge.lean` with their proofs imported by `Solution.lean`. That is a
**statement-fidelity check**, not an enumeration of every theorem in Jules.

For **all** existing mathematical modules, CI separately executes
`lake check --paranoid`, which sandbox-builds and exports the default Lake
target `SpectralGeometry`, including every source module it imports, and
replays its declarations using the built-in and bundled independent kernels.
The `scripts/check-full-proof-coverage.py` gate fails if any Lean source
under `SpectralGeometry/` is not imported by `SpectralGeometry.lean`.

The default Lake target intentionally excludes `Challenge`, because the six
`sorry` placeholders are a trusted statement surface and must not be treated
as proved declarations. Ordinary CI compiles all three targets explicitly;
Comparator judges Challenge separately. This whole-project check is **not**
identical to comparing every theorem against a separately authored statement.
A genuinely independent statement comparison for each theorem would require
substantially more audited Challenge material and cannot be inferred from a
green `lake check` result. The project must not claim that Palomar Comparator
has compared the statements of every theorem.
