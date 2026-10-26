# Palomar submission preparation — unified Comparator (draft)

This branch prepares **one Palomar submission candidate** for the Jules
SpectralGeometry Lean 4 development. One root `comparator.json` compares
**48 theorem statements and 14 definitions** between `Challenge.lean` and
`Solution.lean`, including canonical products, finite geometric energy,
infinite onsite operators, finite low-energy sectors, and finite-edge
interactions in an infinite Hilbert space.

## One independent statement boundary

- `Challenge.lean` imports **Mathlib only**. Its explicit definitions,
  structure and 48 theorem statements are independent of the project proofs.
  The 48 `sorry` terms deliberately mark the proposed theorem statements;
  they are not part of the proved library.
- `Solution.lean` imports existing, unchanged substantive source modules.
  No theorem body is copied into it.
- `comparator.json` is the **only Comparator configuration** and lists all
  48 theorems and 14 definition names. A single Palomar submission can point
  to this file, after maintainer approval and registry review.
- `formalization.yaml` describes the full selected scope and provenance.
- `lake-manifest.json` and `lean-toolchain` pin the verifier environment.
- The Challenge contains approximately **614 physical lines** (under the
  Palomar limits of 1,000 lines / 100 KiB).

### Scope of the checked results

| Mathematical topic | Theorems |
|---|---:|
| Canonical paired products and prescribed-line zeros | 6 |
| Finite geometric matrices, energy and eigenvalues | 13 |
| Infinite onsite multiplication, domain, eigenvalues and growth | 14 |
| Finite low-energy onsite sectors and point-eigenvalue bounds | 4 |
| Finite-edge interactions on an infinite Hilbert space | 5 |
| Onsite + finite-edge + bounded perturbation | 6 |
| **Total** | **48** |

These results have **conditional hypotheses** as stated in Lean. In
particular, the infinite interaction suite handles *finitely many active
edges* in an arbitrary (possibly infinite) tile space. It does **not**
verify the spectral completeness or compact-resolvent results for the full
infinite matching-family operator against independently authored statements.
The canonical product's zero line is fixed **by construction**; no theorem
about the zeros of the Riemann zeta function follows. A mathematical reader
must still review the statements, research significance and fidelity.

## Reproducible checks

From the repository root, with the pinned Lean toolchain, Linux Bubblewrap,
and pinned Mathlib dependencies:

```sh
python3 scripts/check-palomar-layout.py
python3 scripts/check-lean-sources.py
python3 scripts/check-unified-comparator.py
python3 scripts/check-full-proof-coverage.py
python3 scripts/check-no-proof-holes.py
ruby scripts/validate-formalization.rb
lake exe cache get
lake build SpectralGeometry Challenge Solution
bash scripts/verify-comparator.sh
```

CI builds all existing mathematical modules and then runs **one Comparator**
with Lean, NanoDa and con-ron from the toolchain. This preserves the
independently audited statement boundary without invoking the expensive
`lake check` that recursively replayed hundreds of thousands of Mathlib
declarations for hours. The static audits are not kernel checks.

The isolated unified proof test passed on
[GitHub Actions run 40406964723](https://github.com/alexodas/jules/actions/runs/40406964723)
in under five minutes for all 48 theorems. The final PR commit must
independently pass its own CI before it can be considered verified.

## Maintainer decisions before publication

1. Review the proposed **Apache-2.0** root license; none was present on
   `main` when this PR was prepared.
2. Confirm the repository is public at the precise submitted commit SHA,
   as required by Palomar; no visibility change is performed here.
3. Review authorship, source provenance, automation credits, research
   classification, conditional hypotheses and claimed mathematical scope.
   Passing Comparator is not a novelty assessment or peer review.
4. Submit only after a responsible maintainer authorizes it. This draft
   branch is not automatically merged, published, or submitted.
