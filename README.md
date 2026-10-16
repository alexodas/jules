# Theorem C — From infinite tilings to geometry-dependent spectral zeros

**An experimental Lean 4 + Mathlib research program.** The aim is to understand how
geometric tilings and operators built from their interactions can determine the
positions and, ultimately, the *statistics* of zeros of an analytic function.
In parallel, this repository tests how far AI-generated mathematical arguments
can be developed and checked by the Lean kernel.

The research question and experimental direction come from Alessandro Odasso,
who is not a mathematician. The mathematical formalizations were developed with
AI assistance and must be read critically. **This project does not prove the
Riemann hypothesis, identify its constructed product with the Riemann zeta
function, or claim a new result about zeta zeros.**

This README reconstructs the *chronological mathematical progression* by
checking the historical versions of `README.md` and `InfiniteTilings.lean`.
It distinguishes (1) results already merged into `main` and checked by CI,
(2) an additional CI-checked proposal in [PR #11](https://github.com/alexodas/jules/pull/11) that has
**not** been merged, and (3) research goals that have not been proved.

## The central idea, in one minute

We deliberately **keep** an analytic construction that forces all zeros onto
an arbitrarily chosen line, such as the critical line
$\operatorname{Re}(s)=\tfrac12$. We want to **stop choosing their heights
by hand**. Instead, we want the positive zero levels to emerge as eigenvalues
of operators sensitive to tile position, shape, orientation, genuine chirality
(where applicable), and interactions with adjacent tiles.

The existing results establish increasingly rich geometric examples, then
finite interacting operators, and finally a bridge between local operator
eigenvalues and a canonical product. **They do not yet supply a single infinite
tiling operator with the desired global spectrum.** The long-range objective is
to study whether suitable operators on structured, possibly aperiodic,
tessellations—including carefully defined Farey-based constructions—can
produce meaningful level statistics, potentially comparable with those of
the nontrivial zeros of the Riemann zeta function.

## Mathematical conventions

We write $\mathbb N,\mathbb Z,\mathbb R,\mathbb C$ for the natural numbers,
integers, real numbers, and complex numbers. Let $c\in\mathbb C$ be a
*center*, let $d\in\mathbb C\setminus\{0\}$ be a *direction*, and let
$q_n>0$ be positive levels. The prescribed line is

$$
L_{c,d}=\{c+dt:t\in\mathbb R\}.
$$

In particular, $c=\tfrac12$ and $d=i$ give
$L_{1/2,i}=\{s\in\mathbb C:\operatorname{Re}(s)=\tfrac12\}$.
The choice of this line is an **input**, not a discovery of the proof.

Below, **proved** means that the stated result is present in a Lean file at
a commit with a passing Lean/Mathlib CI run, under the exact hypotheses
given. A geometrically suggestive definition is not automatically a
mathematically unique or physically canonical model.

---

## 1. The starting analytic result: Theorem C (**proved on main**)

The first step had no real tiling attached to it. For positive levels
$q_n$, the file defines *paired* factors and their infinite product:

$$
F_n(s)=1-\left(\frac{s-c}{d\,q_n}\right)^2,
\qquad
D_q(s)=\prod_{n=0}^{\infty}F_n(s).
$$

The pairing is crucial: the zeros of each factor are at
$c+dq_n$ and $c-dq_n$, while the factor's deviation from $1$
is quadratic in $q_n^{-1}$, rather than linear.

The `Admissible` structure formalizes positivity plus a summable
majorant on **every compact subset** $K\subset\mathbb C$:
there is a summable real sequence $b_n$ such that

$$
\forall s\in K,\quad |F_n(s)-1|\le b_n.
$$

Lean proves compact-uniform convergence of the partial products.
It also proves the central implication

$$
D_q(s)=0\quad\Longrightarrow\quad s\in L_{c,d}.
$$

This is the **zero-localization theorem**. In a later step, the file
also proves that the full product really vanishes at each prescribed
positive level $c+dq_n$ (under $q_n\neq0$, $d\neq0$).
Thus localization is not merely a vacuous implication.

A reusable sufficient condition proved in the square-grid extension is

$$
q_n>0\quad\text{for all }n,\qquad
\sum_{n=0}^{\infty}\frac1{q_n^2}<\infty
\quad\Longrightarrow\quad
\text{the compact-majorant hypothesis}.
$$

**Lean anchors:** `Admissible`, `product_uniform_on_compact`,
`theoremC_zero_localization`, `admissible_of_inv_sq_summable`,
`canonicalProduct_zero_at_positive_level`.
**Boundary:** these factors have zeros on the chosen line **by
construction**. They are not the Riemann xi or zeta function, and this
product is not the different exponential genus-two product considered
in the exploratory discussion.

## 2. The first *actual* tiling: integer unit squares (**proved on main**)

For $(m,n)\in\mathbb Z^2$, define the closed unit cell

$$
S_{m,n}=[m,m+1]\times[n,n+1].
$$

The Lean source proves that these cells **cover $\mathbb R^2$** and
that two cells cannot have intersecting **open interiors** unless their
integer indices agree. It also constructs an explicit bijective
enumeration $\mathrm{gridPoint}:\mathbb N\to\mathbb Z^2$; hence the
number-indexed family really covers every square.

At first, the energies were associated with the *enumeration*, not
physical distance. If $(a_n,b_n)=\mathrm{Nat.unpair}(n)$, the
**encoded square-shell energy** was

$$
q_n=\bigl(\max(a_n,b_n)+1\bigr)^2.
$$

Lean proves $q_n\ge n+1>0$, giving

$$
\sum_n\frac1{q_n^2}\le
\sum_n\frac1{(n+1)^2}<\infty.
$$

By Theorem C, its associated product converges as required and has
no zeros off the chosen complex line.

**Lean anchors:** `squareCell_covers_plane`,
`squareInterior_unique`, `gridPoint_surjective`,
`gridPoint_injective`, `squareGridEnergy_grows`,
`squareGridEnergy_inv_sq_summable`, `squareGrid_theoremC`.
**Boundary:** this first energy uses encodings of integer coordinates;
it is **not** Euclidean distance between centroids.

## 3. Replacing encoded energies by Euclidean centroids (**proved on main**)

The next result removed that first artificial growth prescription.
The genuine centroid of $S_{m,n}$ is

$$
P_{m,n}=\left(m+\tfrac12,\ n+\tfrac12\right),
$$

and the new positive energy is

$$
q(m,n)=1+\left(m+\tfrac12\right)^2+
          \left(n+\tfrac12\right)^2.
$$

The key mathematical proof is an inverse-square summability estimate
over **all** of $\mathbb Z^2$:

$$
\sum_{(m,n)\in\mathbb Z^2}\frac1{q(m,n)^2}<\infty.
$$

Writing $x=m+\tfrac12$, $y=n+\tfrac12$, the bound is

$$
\frac1{(1+x^2+y^2)^2}
\le\frac1{(1+x^2)(1+y^2)}.
$$

The right side separates into the product of two summable
one-dimensional sequences. Because `gridPoint` is injective, the
estimate transfers to the natural-number enumeration used in the
canonical product.

**Lean anchors:** `squareCentroid`, `centroidEnergy`,
`centroidEnergy_inv_sq_summable`,
`geometricCentroidEnergy_inv_sq_summable`,
`geometricCentroid_theoremC`.
**Significance:** the analytic assumptions now arise from a physical
geometric quantity—not from selecting an arbitrary rapidly growing
sequence. **Boundary:** even this physically motivated choice still
*prescribes* the eventual product-zero levels; they are not operator
eigenvalues.

## 4. Rectangles, shears and invertible affine grids (**proved on main**)

We then tested whether the geometric proof survives changing the
shape of tiles. Let

$$
A=\begin{pmatrix}a&b\\c&d\end{pmatrix},
\qquad \det A=ad-bc\ne0.
$$

Applying $A$ to every unit square gives a full-plane tiling by
parallelograms, including rectangular grids and sheared grids.
Lean proves both the **coverage** of $\mathbb R^2$ and
**nonintersection of distinct open interiors**, using the explicit
inverse of $A$.

If $P=(x,y)$ is the original square centroid, the transformed
energy is

$$
q_A(P)=1+\|AP\|^2
=1+(ax+by)^2+(cx+dy)^2.
$$

Invertibility gives a **uniform coercive comparison**:

$$
1+x^2+y^2\le C_A\,q_A(P),
\qquad
C_A=1+\frac{a^2+b^2+c^2+d^2}{(ad-bc)^2}>0.
$$

Consequently $\sum_{\mathbb Z^2}q_A(P)^{-2}<\infty$, so the same
Theorem C applies for every nondegenerate linear deformation.

**Lean anchors:** `linearGridMap_injective`,
`linearGridMap_surjective`, `linearSquareCell_covers_plane`,
`linearSquareInterior_unique`,
`linearCentroidEnergy_inv_sq_summable`,
`linearGrid_theoremC`, `rectangleGrid_theoremC`,
`parallelogramGrid_theoremC`.
**Boundary:** these remain highly structured affine images of a
periodic lattice, not intrinsically aperiodic prototile systems.

## 5. Arbitrarily shifted horizontal rows (**proved on main**)

To escape globally affine grids, assign an independent horizontal
offset $\delta_n\in\mathbb R$ to each integer row $n$.
The tiles become

$$
S^\delta_{m,n}
=[m+\delta_n,m+\delta_n+1]\times[n,n+1].
$$

For **any offsets**, even unbounded ones, Lean proves plane coverage,
disjointness of different tile interiors, and separation of distinct
centroids by Euclidean distance at least one.

The centroid energy is

$$
q_\delta(m,n)=1+
   (m+\tfrac12+\delta_n)^2+(n+\tfrac12)^2.
$$

If $|\delta_n|\le\tfrac12$ uniformly, Lean additionally proves

$$
q(m,n)\le2\,q_\delta(m,n)
\quad\Longrightarrow\quad
\sum_{m,n}q_\delta(m,n)^{-2}<\infty,
$$

and hence Theorem C applies. **The boundedness restriction is needed
for this energy comparison**, not for coverage or nonoverlap.

**Lean anchors:** `rowShiftCell_covers_plane`,
`rowShiftInterior_unique`, `rowShiftCentroid_separated`,
`rowShiftEnergy_inv_sq_summable`, `rowShiftGrid_theoremC`.
**Boundary:** although offsets need not repeat from row to row, every
such tiling retains the translation period $(1,0)$. It is not
translation-aperiodic in both directions.

## 6. A general coercive criterion for irregular point configurations (**proved on main**)

The common thread of the previous proofs is not periodicity but
**sufficient growth away from the origin**. For any positive family
$q:\mathbb Z^2\to\mathbb R_{>0}$, suppose one constant $C>0$
satisfies, for every lattice index $p=(m,n)$,

$$
1+(m+\tfrac12)^2+(n+\tfrac12)^2\le C\,q(p).
$$

Lean proves the general consequence

$$
\sum_{p\in\mathbb Z^2}\frac1{q(p)^2}<\infty,
$$

as well as admissibility and Theorem C for its enumeration.

A concrete corollary permits a separately chosen point $P_{m,n}$
at *every* lattice index, with bounded coordinate displacements

$$
|P_{m,n}^{(1)}-(m+\tfrac12)|\le\tfrac12,\qquad
|P_{m,n}^{(2)}-(n+\tfrac12)|\le\tfrac12.
$$

For $q_P(m,n)=1+\|P_{m,n}\|^2$, Lean verifies the comparison with
$C=2$ and therefore summability and line-localized product zeros.

**Lean anchors:** `coerciveEnergy_inv_sq_summable`,
`coerciveEnergy_theoremC`, `boundedPointSet_energy_control`,
`boundedPointSet_inv_sq_summable`,
`boundedPointSet_theoremC`.
**Crucial boundary:** these are results about *indexed point
configurations*, not a theorem that arbitrary displaced points are
centroids of actual nonoverlapping tiles. At the endpoint displacement
$\tfrac12$, distinct indices need not even have distinct points.

## 7. A complete tiling with no nonzero translation period (**proved on main**)

The next step restored actual tile geometry while breaking every
nonzero translational symmetry of the *particular tiling*.
Start from the unit-square grid. In one location, replace two adjacent
unit squares by two rectangles of width $\tfrac12$ and $\tfrac32$,
both of height $1$. Elsewhere, leave the unit squares unchanged.

Lean proves that the rectangles still cover the whole plane, their
open interiors are pairwise disjoint, and the width-$\tfrac32$
rectangle is unique. A translation preserving the collection of
rectangles (including shape and position) must fix that unique tile.
Hence

$$
T+\tau=T\quad\Longrightarrow\quad\tau=(0,0)
$$

for the tile-preserving translation notion specified in the source.

The actual rectangular centroids differ by at most $\tfrac12$
in each coordinate from their corresponding square centroids.
The preceding bounded-displacement theorem therefore proves
inverse-square energy summability and Theorem C for this example.

**Lean anchors:** `defectCell_covers_plane`,
`defectInterior_unique`, `defectWidth_unique`,
`defectTiling_translation_aperiodic`,
`defectCentroid_bounded`, `defectTiling_theoremC`.
**Crucial boundary:** this is a *finite defect of a periodic grid*.
It is not a proof of Penrose-style strong aperiodicity of a tile set:
the same prototiles may admit periodic tilings.

## 8. Finite operators detecting tile adjacency (**proved on main**)

So far the product levels depended mostly on centroid energies.
To make neighboring tiles matter, the source defines a weighted
operator on a finite tile patch with $N$ vertices:

$$
(H_Wu)_i=\sum_{j=1}^{N}W_{ij}u_j.
$$

If the weights are real and symmetric, $W_{ij}=W_{ji}$, Lean proves
the real inner-product symmetry

$$
\langle u,H_Wv\rangle=\langle H_Wu,v\rangle.
$$

A separate construction sets non-neighbor weights to zero and
proves that symmetric undirected adjacency plus symmetric edge
weights yields a symmetric finite matrix. No periodicity is assumed
for the finite graph.

**Lean anchors:** `finitePatchOperator`,
`finitePatchOperator_symmetric`,
`geometricEdgeMatrix_symmetric`,
`geometricFinitePatch_symmetric`.
**Boundary:** this is a **finite** self-adjointness identity. It is
not yet the definition, domain analysis or spectral theorem for an
unbounded operator acting on $\ell^2$ of an infinite tiling.

## 9. A concrete two-tile interaction with distinct spectra (**proved on main**)

The two special rectangles really share a vertical boundary.
Their widths have product $\tfrac12\cdot\tfrac32=\tfrac34$.
We assign each tile an *external binary mark* and choose the
interaction law

$$
\eta(\mu,\nu)=
\begin{cases}
1,&\mu=\nu,\\
2,&\mu\ne\nu,
\end{cases}
\qquad
w(\mu,\nu)=\tfrac34\,\eta(\mu,\nu).
$$

The two-tile adjacency operator is

$$
H_w=\begin{pmatrix}0&w\\w&0\end{pmatrix},
\qquad
\operatorname{spec}(H_w)=\{-w,+w\}.
$$

Lean proves both eigenvalues with explicit nonzero eigenvectors
$(1,1)$ and $(1,-1)$, and proves there are **no other real
eigenvalues** in this model. Equal marks give $w=\tfrac34$;
opposite marks give $w=\tfrac32$. In particular, $\tfrac32$
is an eigenvalue in the opposed-mark model and not in the
equal-mark model.

**Lean anchors:** `defectPair_shares_vertical_edge`,
`defectPairWidthWeight_value`,
`markedDefectOperator_symmetric`,
`markedDefect_eigenvalues_exact`,
`aligned_tiles_eigenvalue`, `opposed_tiles_eigenvalue`,
`opposed_eigenvalue_not_aligned`.
**Boundary:** the interaction rule is deliberately *chosen* as a
model; it has not been uniquely derived from geometry. These marks
are **not intrinsic chirality** (rectangles are achiral).
The exact spectrum proved here belongs to a two-dimensional local
operator, not the entire infinite tiling.

## 10. Feeding real local eigenvalues into the product (**proved on main, PR #10**)

The next bridge uses a positive geometric *growth envelope*
$q_0(n)$, together with any real spectral levels $\lambda_n$:

$$
Q_n=q_0(n)(1+\lambda_n^2).
$$

If $q_0(n)>0$ and $\sum_n q_0(n)^{-2}<\infty$, then
$Q_n\ge q_0(n)>0$, so

$$
\sum_n Q_n^{-2}<\infty.
$$

Lean proves admissibility and Theorem C for $D_Q$; it also
proves explicitly, for every index $n$,

$$
D_Q(c+dQ_n)=0.
$$

The concrete version uses the actual Euclidean square-centroid
energy for $q_0$ and a **proved positive eigenvalue** of each
chosen two-tile marked operator for $\lambda_n$.
Matching marks multiply $q_0$ by $25/16$; opposing marks
multiply it by $13/4$. Hence local interaction data can change
the level of a product zero along the same chosen line.

**Lean anchors:** `spectralEnvelopeEnergy_inv_sq_summable`,
`spectralEnvelope_theoremC`,
`canonicalProduct_zero_at_positive_level`,
`localMarkedEigenlevel_is_eigenvalue`,
`markedSpectralGrid_zero_at_level`,
`orientation_changes_energy`.
**Crucial boundary:** $Q_n=q_0(n)(1+\lambda_n^2)$ is a *constructed
combination* of a prescribed centroid baseline and local eigenvalues.
It is **not itself proved to be an eigenvalue** of the local adjacency
operator, much less the spectrum of a single infinite operator.
The choice of zero line remains completely independent of this bridge.

## 11. A level that is an eigenvalue of the *combined* local operator (**CI-checked proposal, PR #11; not on main**)

A subsequent experiment improves the previous distinction by moving
the geometric baseline **inside** a two-site Hamiltonian:

$$
H_n=
\begin{pmatrix}
V_n&w_n\\
w_n&V_n
\end{pmatrix},
\qquad
\lambda_n^\pm=V_n\pm w_n.
$$

Lean proves symmetry and both eigenvalue identities with explicit
nonzero eigenvectors. If $V_n>0$, $w_n\ge0$, and
$\sum_n V_n^{-2}<\infty$, the positive mode

$$
Q_n=\lambda_n^+=V_n+w_n
$$

is an **actual eigenvalue of the full two-site operator $H_n$**,
and it satisfies positivity, inverse-square summability,
admissibility, zero localization and $D_Q(c+dQ_n)=0$.

For the example proposed in PR #11, $V_n$ remains the square-centroid
energy and $w_n$ is the marked coupling of the special rectangles.
This is a step forward from multiplying a separately chosen baseline
by a function of an eigenvalue.

**Lean anchors in PR #11 only:** `interactingPairOperator`,
`interactingPair_positive_mode`, `interactingPair_negative_mode`,
`pairOperatorEigenlevel_inv_sq_summable`,
`markedPairEigenlevel_is_eigenvalue`,
`markedPairEigenlevel_zero_at_level`.
**Verification:** [PR #11](https://github.com/alexodas/jules/pull/11), commit
[`864051f`](https://github.com/alexodas/jules/commit/864051f156eca95c249e6400c1e3d82b9c53b377),
[successful Lean/Mathlib CI](https://github.com/alexodas/jules/actions/runs/38966538546).
**Status:** this branch is **not merged into `main`**.
**Boundary:** each $H_n$ is still a separate two-site operator;
the onsite potential $V_n$ is still chosen from centroid geometry.
This is not a single infinite operator or a proof of zeta statistics.

## 12. A first constraint on level counting (**CI-checked proposal, PR #11; not on main**)

That same pending branch proves a useful limitation of the simple
local model. Suppose $0\le w_n\le C$ and
$Q_n=V_n+w_n$. Then, for every real threshold $T$,

$$
\{n:V_n\le T-C\}
\;\subseteq\;
\{n:Q_n\le T\}
\;\subseteq\;
\{n:V_n\le T\}.
$$

The concrete two-rectangle model proves that $C=\tfrac32$
works for any sequence of binary marks.
These are precise **set inclusions**, formally proved by Lean.
Whenever the sets are finite, their cardinalities obey the
corresponding inequalities.

This matters to the research program: bounded positive local
couplings can shift these selected levels only by a bounded amount.
For the present two-dimensional quadratic centroid baseline, the
elementary lattice-point count is of order $T$, whereas the
positive-ordinate nontrivial Riemann-zeta zero count has leading
order $T\log T$. So simply adding uniformly bounded pair
couplings to that baseline cannot by itself reproduce the
Riemann-zeta level-counting law **when counting the indexed levels
with multiplicity**.

The **set-inclusion theorem** is in Lean; the comparison of these
two asymptotic counting laws is mathematical analysis discussed here,
**not** a Lean-certified theorem in this repository.

**Lean anchors in PR #11 only:**
`pairOperatorEigenlevel_threshold_sandwich`,
`markedDefectCoupling_le_three_halves`,
`markedPairEigenlevel_threshold_sandwich`.
**Boundary:** this is not a general no-go theorem for all
geometry-dependent infinite operators, nor a theorem about
nearest-neighbor spacing statistics.

---

## What is established, and what remains open

**Established on `main`:** the paired canonical product has
compact-uniform convergence under proved sufficient conditions; its
zeros stay on a prescribed complex line; explicit square,
parallelogram, row-shifted and finite-defect tilings satisfy the stated
geometric properties; centroid energies in the stated cases satisfy
inverse-square summability; finite symmetric adjacency operators are
defined; a marked two-tile model has exactly computable
geometry-dependent eigenvalues; and these eigenvalues can influence
the product's chosen zero levels.

**Checked by CI but not merged:** PR #11 directly realizes its
selected positive zero levels as eigenvalues of the *combined* local
two-site Hamiltonians and bounds their threshold sets by those of
the onsite potential. Review status and merge status are separate
from proof compilation status.

**Not established:** an operator on an actual **infinite**
aperiodic tiling with a rigorously specified self-adjoint domain;
its complete discrete spectrum, counting law, multiplicities, or
unfolded spacing statistics; a canonical spectral determinant or
trace formula derived from that infinite operator; or any
identification of these products with Riemann's $\xi$- or
$\zeta$-function. In particular, a guaranteed zero *line*
is not a guaranteed match of *zero heights*.

### The next mathematical questions

1. **Choose the geometry precisely.** For a Farey-based experiment,
   define the ambient space, the tiles, and the dual adjacency graph.
   The classical Farey tessellation is hyperbolic and modular; it
   should not be described without qualification as an intrinsically
   aperiodic Euclidean prototile system.
2. **Build a coherent operator, not unrelated local motifs.**
   Use shape- and adjacency-dependent couplings, and, where intrinsic
   chirality actually exists, study chirality-sensitive terms.
   Prove symmetric weights first, then establish the required
   self-adjoint realization on an infinite Hilbert space.
3. **Prove genuine spectral control.** Separate point, continuous and
   essential spectra; determine whether a discrete sequence suitable
   for a canonical product exists; prove growth and counting
   estimates rather than postulating them.
4. **Test spectral statistics after controlling the counting law.**
   Investigate multiplicities, unfolded nearest-neighbor spacings
   and two-point correlations, and compare them with conjectured
   and known properties of zeta zeros—without fitting parameters
   merely to force an answer.

These are **research directions**, not claims of proof.

## Reproducing the Lean verification

The primary source is [`InfiniteTilings.lean`](InfiniteTilings.lean).
The GitHub Actions workflow
[`lean.yml`](.github/workflows/lean.yml) uses the repository's
Lean toolchain and Mathlib setup. Its essential commands are

```sh
lake update
lake exe cache get
lake build
```

A successful job (including compilation and kernel checking) certifies
the particular file at the particular commit **relative to its stated
definitions and hypotheses**. It does not certify mathematical
novelty, physical modeling choices, or implications that were never
formalized. The source records no proof of the Riemann hypothesis.

For orientation, these commits mark the main historical steps:

- [Initial canonical-product Theorem C](https://github.com/alexodas/jules/commit/8e2e9d3cfac7892633d13b0f3c3fe37f8f64af7d)
- [Explicit square-grid tiling and shell energies](https://github.com/alexodas/jules/commit/a2661ba6ef62ef4f3f208e6be5836d9f6c166770)
- [Euclidean-centroid summability](https://github.com/alexodas/jules/commit/268addee42fda63b349c0b09de934719bdf078a5)
- [All invertible linear grids](https://github.com/alexodas/jules/commit/09f393cb398d4b6efbde923dc85c6fae746c4603)
- [Independent row shifts](https://github.com/alexodas/jules/commit/e481964f62538c2689d20974ba75ef4a9922e278)
- [Coercive and bounded-point-displacement criteria](https://github.com/alexodas/jules/commit/20fd9be7faa5d3a489f1f1c38f3532c251e39728)
- [The translation-aperiodic finite-defect tiling](https://github.com/alexodas/jules/commit/abbc8f9e67ff7896d3fa85dd70850df3a85dd063)
- [Finite geometric adjacency and marked spectra](https://github.com/alexodas/jules/commit/4a4602b001ce646b42fdde8032cb50117a75c83f)
- [Local eigenvalues coupled to canonical-product levels](https://github.com/alexodas/jules/commit/1f9e5832b1a60b85bff21044712ba46583043af1)
- [Direct pair-Hamiltonian eigenlevels and threshold bounds (PR #11)](https://github.com/alexodas/jules/pull/11)

## Attribution and methodological purpose

**Research questions and experimental direction:** Alessandro Odasso,
a non-mathematician exploring what large language models can and
cannot accomplish in formal mathematics.

**Formalizations and explanatory drafts:** AI-generated with OpenAI
ChatGPT and checked, at the noted commits, with Lean 4 and Mathlib.
Mathematical statements should be judged on their explicit
hypotheses and definitions, not on the apparent strength of an
informal description. The project is an experiment in
**human-guided, AI-assisted, kernel-verified mathematics**, not a
claim to have solved the Riemann hypothesis.
