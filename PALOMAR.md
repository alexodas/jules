# Palomar candidate — nine-level response on an octagonal graph

The selected theorem is
`SpectralGeometry.AmmannBeenker.exists_nine_level_response` in
[`AmmannBeenkerOperator.lean`](SpectralGeometry/AmmannBeenkerOperator.lean),
documented in README §4.70.

## Mathematical statement

The vertices are the accepted integer lifts in the explicit open octagonal
cut-and-project construction of README §4.68. The physical projection is
injective, the graph is infinite and has degree at most eight; edges join
lifts differing by a signed standard basis vector. The boundary convention
and physical/internal projections are independently defined in Challenge.

On real ℓ² of the vertices, put V(x)=1+|p(x)|² and use the natural domain
D(V)={ψ∈ℓ²:Vψ∈ℓ²}. The operator and finite intervention are
```math
(Hψ)(x)=V(x)ψ(x)+\frac1{16}\sum_{y\sim x}(ψ(x)-ψ(y)),
\qquad H_τ=H+τP_S,\qquad S=\{x:|p(x)|≤2\}.
```
The theorem constructs complete nondecreasing Hilbert eigenbases for H
and Hτ on that common domain, with ordered levels λ and μτ satisfying
```math
λ_n≥1,\quad λ_n≤3\ (n<9),\quad μ_{τ,n}≥1,
\qquad \fracτ2≤μ_{τ,n}-λ_n≤τ\quad(n<9,\ 0≤τ≤4).
```
Multiplicity is retained; no eigenvalue simplicity or nonempty spectral
window is assumed. The source proves nine distinct central sites with V≤2,
interaction norm at most one, positivity/symmetry, properness and V≥5
outside S. The natural-domain self-adjoint compact-resolvent construction
supplies the complete ordered spectra.

## Research motivation and scope

The result is an explicit infinite geometric example in which a finite
positive intervention moves at least nine ordered levels by a uniform
fraction of its strength. The contribution to assess is the complete
application with derived geometric/operator inputs and quantitative
multiplicity-aware conclusions. Its form and min–max methods are classical;
positive spectral lifting is an established topic.

Polygonal tiling coverage, aperiodicity, global rotational symmetry,
optimality of the sector/constants, finite-patch errors and CUE statistics
are not conclusions. Geometric inverse-square summability and the resulting
entire-product zero-response application remain roadmap obligations.
Choosing an affine line for spectral zeros is not by itself a novelty claim.
No relation to Riemann zeta zeros is asserted.

## Sources and assessment

- F. P. M. Beenker, *Algebraic theory of non-periodic tilings of the plane
  by two simple building blocks: a square and a rhombus* (1982),
  [report](https://pure.tue.nl/ws/files/4269555/253166.pdf): geometric background.
- T. Kato, *Perturbation Theory for Linear Operators*,
  [DOI](https://doi.org/10.1007/978-3-642-66282-9): spectral background.
- I. Nakić, M. Täufer, M. Tautenhahn and I. Veselić, *Unique continuation
  and lifting of spectral band edges of Schrödinger operators on unbounded
  domains* (2020), [DOI](https://doi.org/10.4171/JST/314): spectral-lifting background.
- [Mathlib4](https://github.com/leanprover-community/mathlib4): formal infrastructure.

The precise statement is recorded in the Jules source. The `original-proof`
classification records that presentation, not verified priority or a novel
proof technique. Precise literature comparison and expert assessment of
standalone research interest remain necessary. Mechanical checking is not
editorial acceptance.

## Human origin and AI-assisted development

Alessandro Odasso originated the informal project idea, directs the work
and is the responsible maintainer. He does not identify as a mathematician;
his stated interest is exploring LLMs in scientific research. According to
his account, OpenAI GPT-6 assisted throughout the GitHub/Lean development.
The AI is a development assistant, not a human mathematical coauthor.
Human responsibility does not imply independent authorship of every proof.
No human mathematical peer review or exhaustive provenance audit is claimed.

## Independent statement verification

Challenge imports only Mathlib and independently states the model, natural
domain, eigenbasis structure and theorem. Solution imports the proved source.
The single Comparator selects one theorem and 27 supporting declarations
(26 definitions/abbreviations and the eigenbasis structure). Challenge-only
proposition placeholders are not substantive proofs. Lean, NanoDa and con-ron
must check the comparison; the complete source library is also built.
Toolchain and dependencies are pinned.

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

Use a public immutable 40-character commit SHA with all required checks
passing; see [GitHub Actions](https://github.com/alexodas/jules/actions).
Preparing the package does not automatically submit it to Palomar.
