# Palomar candidate — exact geometric spectral products and nine-level zero response

The selected theorem is
`SpectralGeometry.AmmannBeenker.exists_nine_level_fullProducts` in
[`AmmannBeenkerSpectralProducts.lean`](SpectralGeometry/AmmannBeenkerSpectralProducts.lean),
documented in README §§4.71–4.72.

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

For any fixed center $c\in\mathbb C$ and direction $d\ne0$, the theorem
also derives inverse-square summability of both complete spectra and proves
`HasExactFullSpectralProduct` for each operator. Thus
```math
D_τ(s)=\prod_{n\ge0}\left(1-\frac{(s-c)^2}{d^2μ_{τ,n}^2}\right)
```
is entire, its zeros are exactly the reflected full real bounded-inverse
spectrum, and its analytic zero orders are the geometric eigenspace
multiplicities of that same operator. With $z_n^\pm(τ)=c\pm dμ_{τ,n}$,
```math
z_n^\pm(τ)-z_n^\pm(0)=\pm d(μ_{τ,n}-λ_n),
\qquad |d|\fracτ2≤|z_n^\pm(τ)-z_n^\pm(0)|≤|d|τ
\quad(n<9,\ 0≤τ≤4).
```
All indexed points are zeros of their respective products, and each indexed
branch moves when τ>0. Repeated levels are allowed: nine multiplicity slots
need not be nine distinct locations, and zero sets at different parameters
need not be disjoint. The common natural domain and affine data are fixed;
the compact-resolvent witnessing shift may vary with τ.

The geometric summability is proved, not assumed. An injective code by two
integer coordinates and two residues in {-2,-1,0,1,2} yields
$\#\{|p(x)|≤R\}≤25(2\lceil R+3\rceil+1)^2$ for R≥0, and a product-of-series
majorant proves $\sum_x V(x)^{-2}<\infty$. Positivity and the variational
comparison transfer this to the full spectra throughout the intervention.

## Research motivation and scope

The result connects a concrete finite intervention in an infinite geometric
operator to quantitatively controlled motion of exact full-product zeros
on an arbitrary prescribed affine line. The contribution to assess is the
complete application with derived geometry, summability, operator inputs,
a nonempty window and operator-specific geometric zero multiplicities. Its form and min–max methods are classical;
positive spectral lifting is an established topic.

Polygonal tiling coverage, aperiodicity, global rotational symmetry,
uniform vertex separation, optimality of the sector/constants, numerical
cofactor/radius certificates, relative determinants, finite-patch errors and
CUE statistics are not conclusions.
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
The Comparator selects the main theorem and four supporting witness lemmas:
matching involutivity, finite radius sublevels, onsite properness and
finite-dimensional compact-resolvent eigenspaces. All model definitions
and the eigenbasis structure are compared transitively, with no definition holes. Challenge-only
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
