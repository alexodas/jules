# Palomar candidate — one low-energy eigenspace multiplicity theorem

This repository develops 46 substantive Lean modules on canonical products and
finite/infinite spectral geometry. The current **Palomar selection**, distinct
from the larger proved development, consists of **one** full-interacting-operator
result and the definitions needed to state it independently.

## Mathematical question and result

For the infinite real Hilbert space of square-summable tile amplitudes,
consider `H=M_V+B` on the natural (possibly proper) domain of multiplication
by `V`. The bounded correction `B` comprises the finite-color infinite
matching-family Laplacian, a bounded perturbation, and an optional scalar shift.

The selected theorem
[`SpectralGeometry.infiniteLocalMatching_full_eigenspace_finrank_le_lowEnergyTiles`](SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean)
shows, under its explicit hypotheses, that

```math
\lambda<R-\|B\|,\quad\lambda\ne a
\quad\Longrightarrow\quad
\dim E_{\lambda}(H)\le\#\{t:V(t)\le R\}.
```

The assumptions include finite onsite sublevel sets, the unit-gap condition
`V(t)-a≥1`, and `‖B ∘ R_a‖<1` ensuring the specified shifted inverse.
The result bounds the multiplicity of **one** real eigenspace, not the total
number of eigenvalues below `R`. It does not show the index-wise min–max
comparison, any inverse-square spectral summability, a specific aperiodic
tiling, or the Riemann hypothesis.

**Proof architecture:** the form inequality on vectors supported outside
the low-onsite sector rules out a nonzero eigenvector below `R-‖B‖` with
all low-energy coordinates zero. The eigenspace-to-coordinate restriction
is therefore injective. Its domain is finite-dimensional via the compact
resolvent proved in earlier Lean modules, and the codomain is a finite
coordinate space, giving the claimed rank bound.

This is a concrete result about the full interacting operator, unlike the
finite-edge/onsite-only results previously selected. Nevertheless the
observation is close to standard variational arguments: **scientific novelty
and Palomar-level research interest are not asserted or guaranteed.**

## Source provenance

`formalization.yaml` records the specific selected statement as
`type: original-proof`, `relationship: other`: this names the present
Jules formalization as the first identified presentation of this formulation.
It does **not** assert that the underlying inequality is new to mathematics.
T. Kato's *Perturbation Theory for Linear Operators* is identified strictly
as **background** in operator perturbation theory, and Mathlib is separately
identified as **background software/formal foundations**, never as the
source adapted for this result. If a published earlier occurrence of the
exact statement is identified, provenance must be revised to its actual
source-based relation before submitting.

The earlier Palomar attempt mechanically passed its independent comparison,
but editorial review rejected its weak research motivation and inaccurate
Mathlib provenance. This new candidate deliberately isolates those issues.

## Independent statement and mechanical verification

- `Challenge.lean` imports only Mathlib; it reproduces the selected
  statement and its necessary definitions without importing project proofs.
  Deliberate `sorry` terms there are Challenge-only placeholders.
- `Solution.lean` imports
  `SpectralGeometry.InfiniteLocalFullLowEnergyCounting`, containing the
  genuine, previously proved declaration and its full dependency closure.
- The **only** `comparator.json` selects one theorem and its 16 supporting
  definitions and type abbreviations. The other Lean theorems remain compiled through
  `SpectralGeometry.lean`, but are not independently compared here.
- `lean-toolchain` and `lake-manifest.json` pin the environment; the
  source proof modules remain unchanged.

From the repository root:

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

CI runs Lean/Mathlib and one Comparator; a green build is a prerequisite,
not evidence of novelty or a prediction of acceptance. Never submit a
moving branch: use the full immutable SHA of a verified public commit
only after maintainer review and authorization.
