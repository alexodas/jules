# Palomar candidate — low-energy multiplicity of an infinite interacting operator

The candidate **mathematical result** is one theorem from the 46-module
Lean 4 project, not a count of formalized lemmas. Comparator selects
`SpectralGeometry.infiniteLocalMatching_full_eigenspace_finrank_le_lowEnergyTiles`
in [`SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean`](SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean).
The theorem was proved in the source development before this packaging work.

## Research question

When an infinite collection of geometric sites carries an unbounded onsite
energy `V` together with bounded interactions, how much of a **complete
low-energy eigenspace** can be observed in the finitely many sites where
the onsite potential is small? Can the dimension of that eigenspace be
bounded even when the ambient Hilbert space has infinitely many coordinates?

Let `H = M_V + B` on the natural multiplication domain in the real
Hilbert space `ℓ²(Tile)`. Here `B` is the full bounded correction: a
finite-color matching-family interaction on the *infinite* tile space,
a bounded perturbation and an optional scalar shift.

The compared Lean theorem states the following necessary-condition bound,
retaining all its explicit hypotheses:

```math
\lambda<R-\|B\|,\quad \lambda\ne a
\quad\Longrightarrow\quad
\dim E_\lambda(H)\le\#\{t:V(t)\le R\}.
```

We assume that every onsite sublevel set is finite, `V(t)-a≥1`
for every site, and `‖B ∘ R_a‖ < 1` for the onsite resolvent `R_a`.
These conditions identify a bounded compact shifted inverse and ensure
that the eigenspace of the full operator on its natural domain has a
well-defined finite geometric multiplicity. The theorem does **not**
assume that the bounded correction is symmetric or self-adjoint.
In the Lean statement `E_λ(H)` is represented by the equivalent
eigenspace of the compact shifted resolvent, with the equality to
natural-domain eigenvectors proved in the source development.

## Why this particular result may interest researchers

**Finite-coordinate observability.** Even in an infinite Hilbert space,
restriction to the finite set `{t : V(t) ≤ R}` is injective on the
*entire eigenspace at one sufficiently low spectral level*, not just
nonzero on one eigenvector. Thus its geometric multiplicity has an
explicit upper bound in terms of a geometric/potential sublevel count.

**Robustness under bounded interactions.** The threshold has an explicit
perturbation penalty `‖B‖`. The operator includes infinitely many
geometric interaction edges represented by a finite family of bounded
matching operators, not only the finitely many active edges treated in
our earlier Comparator selection. The proof applies without assuming
the bounded correction is symmetric. Its conclusion concerns geometric
multiplicity, not orthogonal spectral projections for a non-self-adjoint
operator.

**Research context.** The relevant audience includes specialists in
discrete Schrödinger operators, spectral theory of graph operators,
finite-dimensional detection of low-energy states, and rigorous/formal
operator theory. The bound can serve as one input toward a
multiplicity-respecting multi-eigenspace counting theorem. Such a
stronger theorem is an **open goal** in this repository, not a result
verified by the present Comparator.

**Scope and difficulty.** The proof uses the quadratic-form inequality
for vectors vanishing on low-potential coordinates: their Rayleigh
numerator is at least `(R-‖B‖)‖ψ‖²`. An eigenvector with
`λ<R-‖B‖` therefore cannot vanish on those coordinates. Applying
this observation to the kernel of the coordinate restriction on the
whole fixed-λ eigenspace proves injectivity and the dimension bound.
This is a transparent standard-style argument, not a claimed new
analytic technique. Its generality does *not* rely on a named
aperiodic tiling, tile-dependent interactions, or all bounded-degree
graphs being represented by matching colors.

The theorem does **not** estimate the total number of eigenvalues
below a threshold, prove an index-wise min–max comparison or
inverse-square summability, supply a specific Penrose/Ammann–Beenker
model, or imply any statement about the zeros of the Riemann zeta
function.

## Human origin and AI-assisted development

The **initial informal research idea** came from **Alessandro Odasso**.
He does not identify as a mathematician; his interest is in exploring
the use of large language models for scientific research. He initiated
and directed this project and is the responsible human maintainer.

**Development method (maintainer's account):** Alessandro Odasso used
**OpenAI GPT-6 throughout the GitHub development of Jules**, including
the Lean mathematical formalization and associated repository work.
GPT-6 is credited as an AI development assistant, **not** as a human
mathematical coauthor. Naming Odasso under `project.authors` and as
maintainer reflects human project direction and responsibility; it
does not mean that he independently authored all formal proofs.

This description is reported by the maintainer; it does not imply a
complete independently audited log of historical prompts. Lean and the
independent Comparator provide mechanical checking, not a guarantee
of originality, research significance or human peer review.

## Origin, literature and the novelty hypothesis

This exact theorem was first **identified** in the Jules Lean source
development. A **focused, non-exhaustive literature search** conducted
for this preparation on 27 October 2026 considered low-energy spectral
subspaces, onsite potentials, discrete Schrödinger bounds, graph
operators and eigenvalue/multiplicity counting. It did **not identify an
earlier publication of the same precise statement and hypotheses**.
That observation motivates **possible originality**, not verified
priority or a claim that all related mathematics is new. We welcome
correction if an earlier equivalent formulation is found.

The background literature includes:

- Tosio Kato, *Perturbation Theory for Linear Operators*, for general
  principles of bounded perturbations and spectral theory
  (DOI: https://doi.org/10.1007/978-3-642-66282-9).
- Sven Bachmann, Richard Froese and Severin Schraven, *Counting
  eigenvalues of Schrödinger operators using the landscape function*,
  *Journal of Spectral Theory* **13** (2023), 1445–1472,
  DOI: https://doi.org/10.4171/JST/488. Their results compare the
  ranks of spectral projections with sublevel volumes of an effective
  potential, in a different setting and with different hypotheses.
  They demonstrate that spectral-counting estimates are an active,
  developed subject; we do not claim to extend their results.
- Mathlib4, as **background formal-library infrastructure**, not the
  publication or mathematical source of the selected bound.

Accordingly, `formalization.yaml` gives the formalization's
first-identified statement the source classification
`type: original-proof`, `relationship: other`; the mathematical
literature and Mathlib receive `relationship: background`.
An earlier equivalent theorem would require changing that declaration
and citing the real source with the appropriate relationship.
There has been **no expert priority review** and no novelty certificate.

## Verification and exact submission scope

The selected theorem is a **per-eigenspace** dimension estimate, rather
than a global eigenvalue-counting or ordered-spectrum comparison theorem.
Its motivation is finite-coordinate observability for the full
interacting operator. The proof uses standard quadratic-form and
restriction arguments; novelty and research-level significance have
not been independently established. Passing mechanical checks does
not, by itself, imply editorial acceptance.

- `Challenge.lean` imports only Mathlib, independently states the
  theorem and its necessary definitions, and contains deliberate
  Challenge-only `sorry` placeholders.
- `Solution.lean` imports the unchanged, fully proved source theorem
  and its dependency closure.
- The single root `comparator.json` names **one theorem and 16
  supporting definitions/type abbreviations**. It does not certify
  the remaining mathematical modules against independent statements.
- `lean-toolchain` and `lake-manifest.json` fix the environment;
  the full substantive source library is still compiled by Lean.

Reproducible checks from repository root:

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

Both Lean/Mathlib and the independent Palomar Comparator must succeed
on the **exact commit being submitted**. Passing checks on one commit
does not validate subsequent metadata, Challenge or packaging edits.
Consult the repository's [GitHub Actions history](https://github.com/alexodas/jules/actions)
for the status of the chosen commit, rather than relying on a particular
pull-request number or earlier build.
A Palomar submission must refer to a public, immutable **40-character
commit SHA** and is not performed automatically.
