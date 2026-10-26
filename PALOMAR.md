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
bash scripts/verify-comparator.sh comparator-finite.json
```

The shell script needs Bubblewrap and the independent kernels bundled with
an appropriate Lean toolchain. Inspect actual CI conclusions: compilation
alone does not establish Comparator equivalence.

## Publication decisions the maintainer must make

1. This branch proposes **Apache-2.0** as a repository licence, which must
   be explicitly reviewed before merging or publishing. No licence was
   present on `main` when this branch was created.
2. Confirm that `alexodas/jules` is PUBLIC at the submitted SHA; this
   branch does not change repository visibility.
3. Verify the metadata authors, credits, source provenance and research
   interest; no novelty or independent scientific review is claimed.
4. No Palomar submission, release, or merge is performed automatically.

## Coverage: two different verification guarantees

The Palomar `comparator.json` still compares six independent canonical-product
statements (and three definitions) from the standalone Mathlib-only
`Challenge.lean` with their proofs imported by `Solution.lean`. That is a
**statement-fidelity check**, not an enumeration of every theorem in Jules.

CI compiles **all** existing mathematical modules with `lake build`.
The expensive global `lake check` was removed: both with and without
`--paranoid` it replayed hundreds of thousands of imported Mathlib declarations
for hours, although project compilation and Palomar Comparator had passed.
Independent statement comparison still runs via `comparator.json`; this is
not the same as independently checking every theorem in the project.
The `scripts/check-full-proof-coverage.py` gate fails if any Lean source
under `SpectralGeometry/` is not imported by `SpectralGeometry.lean`.

The default Lake target intentionally excludes `Challenge`, because the six
`sorry` placeholders are a trusted statement surface and must not be treated
as proved declarations. Ordinary CI compiles the mathematical root and all Challenge/Solution pairs explicitly;
Comparator judges Challenge separately. This whole-project check is **not**
identical to comparing every theorem against a separately authored statement.
A genuinely independent statement comparison for each theorem would require
substantially more audited Challenge material and cannot be inferred from a
green `lake check` result. The project must not claim that Palomar Comparator
has compared the statements of every theorem.

## Additional independent statement suite: finite geometry

CI independently compares the original six canonical-product theorems and
three definitions through the Palomar root `comparator.json`, as before.

The separate `comparator-finite.json` additionally compares **13 theorems**
and **three definitions** from the four finite-geometry source modules
(`FinitePerturbation`, `FinitePositiveEnergy`, `FiniteGeometricEnergy`,
`FiniteStrictPositivity`). `ChallengeFinite.lean` imports **only Mathlib**
and spells out these statements independently of the proof development.
`SolutionFinite.lean` imports the original, unmodified proofs.
Both suites use the toolchain-bundled Lean, NanoDa and con-ron checks.

The new suite is a **local/CI verification**, not an automatic expansion of
the root Palomar registry entry; the canonical-product `comparator.json`
and its `formalization.yaml` remain unchanged. Independent comparisons of the full interacting
infinite-operator spectrum remain future work.

The CI also runs `scripts/check-no-proof-holes.py` to reject textual
`sorry`, `admit` or `axiom` tokens in substantive project proof files.
This supplemental scan is not a replacement for Lean's proof checking.

## Independent infinite-onsite spectral Comparator suite

The third local/CI suite, `comparator-onsite.json`, independently checks
**14 theorems and three definitions** on the (possibly unbounded) real ℓ²
onsite multiplication operator. These cover the natural domain and its
density, point eigenvalue localization and positivity, and growth hypotheses
for inverse-square summability.

`ChallengeOnsite.lean` imports Mathlib only, with separate statement
signatures and deliberate `sorry` placeholders. `SolutionOnsite.lean`
imports the existing unchanged proofs. Lean, NanoDa and con-ron verify
this suite independently of the canonical-product and finite-geometry ones.

The preliminary isolated run
[40403327946](https://github.com/alexodas/jules/actions/runs/40403327946)
passed. Its separate Comparator step has a 15-minute timeout, so the
full Mathlib-wide `lake check` is not reintroduced.

Altogether CI compares **33 theorem statements and nine definitions**
across three suites; the root Palomar submission still advertises only
the canonical-product suite. Statements for the full interacting
unbounded operator require further independent formalization.
