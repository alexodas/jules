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
All twelve stages are now merged into `main`, including the theorems from
[PR #11](https://github.com/alexodas/jules/pull/11). Each step below separates
its motivation, its precisely verified result and its remaining limitations.

## The central idea, in one minute

We deliberately **keep** an analytic construction that forces all zeros onto
an arbitrarily chosen line, such as the critical line
$\Re(s)=\frac{1}{2}$. We want to **stop choosing their heights
by hand**. Instead, we want the positive zero levels to emerge as eigenvalues
of operators sensitive to tile position, shape, orientation, genuine chirality
(where applicable), and interactions with adjacent tiles.

The program deliberately separates two problems: **placing all zeros on
a chosen line**, which the paired product handles by construction, and
**deriving the heights of those zeros from geometry and interactions**,
which motivates the spectral operators. The proposed chain is
**tiling → adjacency graph → weighted operator → real spectral levels →
canonical product → level statistics**. A symmetric operator has real
finite-dimensional eigenvalues, but this alone does not prove their
positivity, growth, discreteness or zeta-like distribution.

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

```math
L_{c,d}=\{c+dt:t\in\mathbb R\}.
```

In particular, $c=\frac{1}{2}$ and $d=i$ give
$L_{1/2,i}=\{s\in\mathbb C:\Re(s)=\frac{1}{2}\}$.
The choice of this line is an **input**, not a discovery of the proof.

Here **proved** means the exact statement and hypotheses occur in Lean
at a commit with a successful Lean/Mathlib build. Each **mathematical
objective** is an explanation of *why* that section is needed, not an
additional theorem certified by Lean. A geometrically suggestive model
is not necessarily unique or physically canonical.

---

## 1. The starting analytic result: Theorem C (**proved on main**)

**Mathematical objective.** Establish a self-contained analytic tool: a normally convergent infinite product whose zero set is confined to an affine complex line, *independently* of any particular geometry. This proves the line-localization mechanism once; later stages only need to construct admissible positive levels.

The first step had no real tiling attached to it. For positive levels
$q_n$, the file defines *paired* factors and their infinite product:

```math
F_n(s) = 1 - \frac{(s-c)^2}{d^2 q_n^2}.
```

The denominator is **the product** of $d^2$ and $q_n^2$; the entire
difference $s-c$ is squared. In plain text, the same formula is
`F_n(s) = 1 - ((s-c)/(d*q_n))^2`.

The infinite canonical product is a separate definition:

```math
D_q(s) = \prod_{n=0}^{\infty} F_n(s).
```

For each index $n$, the two corresponding zeros follow by solving:

```math
F_n(s)=0 \quad\Longleftrightarrow\quad (s-c)^2=d^2q_n^2
\quad\Longleftrightarrow\quad s=c\pm d q_n.
```

The pairing is crucial: the zeros of each factor are at
$c+dq_n$ and $c-dq_n$, while the factor's deviation from $1$
is quadratic in $q_n^{-1}$, rather than linear.

The `Admissible` structure formalizes positivity plus a summable
majorant on **every compact subset** $K\subset\mathbb C$:
there is a summable real sequence $b_n$ such that

```math
\forall s\in K,\quad |F_n(s)-1|\le b_n.
```

Lean proves compact-uniform convergence of the partial products.
It also proves the central implication

```math
D_q(s)=0\quad\Longrightarrow\quad s\in L_{c,d}.
```

This is the **zero-localization theorem**. In a later step, the file
also proves that the full product really vanishes at each prescribed
positive level $c+dq_n$ (under $q_n\neq0$, $d\neq0$).
Thus localization is not merely a vacuous implication.

For positive levels $q_n$, a reusable sufficient condition proved
in the square-grid extension is

```math
\sum_{n=0}^{\infty}\frac{1}{q_n^2}<\infty.
```

Lean proves that this ensures the compact-majorant condition of `Admissible`.

**Why this matters for the next step.** The line is imposed through the paired factors. No geometrical choice, however sophisticated, can turn this line-localization theorem alone into the Riemann hypothesis.

**Lean anchors:** `Admissible`, `product_uniform_on_compact`,
`theoremC_zero_localization`, `admissible_of_inv_sq_summable`,
`canonicalProduct_zero_at_positive_level`.
**Boundary:** these factors have zeros on the chosen line **by
construction**. They are not the Riemann xi or zeta function, and this
product is not the different exponential genus-two product considered
in the exploratory discussion.

## 2. The first *actual* tiling: integer unit squares (**proved on main**)

**Mathematical objective.** Verify that the index set of the infinite product can represent *real tiles of a plane-covering tessellation*, not merely a list of abstract points. Prove coverage, disjoint open interiors and a bijective enumeration, then supply one simple summable test energy.

For $(m,n)\in\mathbb Z^2$, define the closed unit cell

```math
S_{m,n}=[m,m+1]\times[n,n+1].
```

The Lean source proves that these cells **cover $\mathbb R^2$** and
that two cells cannot have intersecting **open interiors** unless their
integer indices agree. It also constructs an explicit bijective enumeration $g:\mathbb N\to\mathbb Z^2$,
called `gridPoint` in Lean, so no square is omitted or counted twice.

At first, the energies were associated with the *enumeration*, not
physical distance. If $(a_n,b_n)$ is the pair returned by `Nat.unpair n`, the
**encoded square-shell energy** was

```math
q_n=\bigl(\max(a_n,b_n)+1\bigr)^2.
```

Lean proves $q_n\ge n+1>0$, giving

```math
\sum_n\frac1{q_n^2}\le
\sum_n\frac1{(n+1)^2}<\infty.
```

By Theorem C, its associated product converges as required and has
no zeros off the chosen complex line.

**Why this matters for the next step.** The initial shell energy depends on how natural numbers encode the grid. It demonstrates mathematical consistency, but it does not yet explain heights in terms of intrinsic tile geometry.

**Lean anchors:** `squareCell_covers_plane`,
`squareInterior_unique`, `gridPoint_surjective`,
`gridPoint_injective`, `squareGridEnergy_grows`,
`squareGridEnergy_inv_sq_summable`, `squareGrid_theoremC`.
**Boundary:** this first energy uses encodings of integer coordinates;
it is **not** Euclidean distance between centroids.

## 3. Replacing encoded energies by Euclidean centroids (**proved on main**)

**Mathematical objective.** Replace the artificial encoding-based energies with the true squared Euclidean distances of tile centroids from the origin. Establish the necessary inverse-square summability across the whole two-dimensional grid without inserting a rapidly growing factor by hand.

The next result removed that first artificial growth prescription.
The genuine centroid of $S_{m,n}$ is

```math
P_{m,n}=\left(m+\frac{1}{2},\ n+\frac{1}{2}\right),
```

and the new positive energy is

```math
q(m,n)=1+\left(m+\frac{1}{2}\right)^2+
          \left(n+\frac{1}{2}\right)^2.
```

The key mathematical proof is an inverse-square summability estimate
over **all** of $\mathbb Z^2$:

```math
\sum_{(m,n)\in\mathbb Z^2}\frac1{q(m,n)^2}<\infty.
```

Writing $x=m+\frac{1}{2}$, $y=n+\frac{1}{2}$, the bound is

```math
\frac1{(1+x^2+y^2)^2}
\le\frac1{(1+x^2)(1+y^2)}.
```

The right side separates into the product of two summable
one-dimensional sequences. Because `gridPoint` is injective, the
estimate transfers to the natural-number enumeration used in the
canonical product.

**Why this matters for the next step.** Once this estimate is proved, every energy value is determined by a tile's position. The enumeration chooses an order only; it no longer determines the numerical heights.

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

**Mathematical objective.** Show that the analytic construction is stable when tiles are stretched, scaled or sheared into rectangles and parallelograms. Prove one theorem for every invertible real two-dimensional linear transformation rather than handling shapes individually.

We then tested whether the geometric proof survives changing the
shape of tiles. Let

```math
A=\begin{pmatrix}a&b\\c&d\end{pmatrix},
\qquad \det A=ad-bc\ne0.
```

Applying $A$ to every unit square gives a full-plane tiling by
parallelograms, including rectangular grids and sheared grids.
Lean proves both the **coverage** of $\mathbb R^2$ and
**nonintersection of distinct open interiors**, using the explicit
inverse of $A$.

If $P=(x,y)$ is the original square centroid, the transformed
energy is

```math
q_A(P)=1+\|AP\|^2
=1+(ax+by)^2+(cx+dy)^2.
```

Invertibility gives a **uniform coercive comparison**:

```math
1+x^2+y^2\le C_A\,q_A(P),
\qquad
C_A=1+\frac{a^2+b^2+c^2+d^2}{(ad-bc)^2}>0.
```

Consequently $\sum_{\mathbb Z^2}q_A(P)^{-2}<\infty$, so the same
Theorem C applies for every nondegenerate linear deformation.

**Why this matters for the next step.** The nonzero determinant supplies a coercive comparison with the square grid. Therefore tile shape can vary without destroying convergence or the selected zero line.

**Lean anchors:** `linearGridMap_injective`,
`linearGridMap_surjective`, `linearSquareCell_covers_plane`,
`linearSquareInterior_unique`,
`linearCentroidEnergy_inv_sq_summable`,
`linearGrid_theoremC`, `rectangleGrid_theoremC`,
`parallelogramGrid_theoremC`.
**Boundary:** these remain highly structured affine images of a
periodic lattice, not intrinsically aperiodic prototile systems.

## 5. Arbitrarily shifted horizontal rows (**proved on main**)

**Mathematical objective.** Relax global affine regularity by giving each horizontal row its own displacement. Distinguish *whether an actual tiling exists* from *whether the associated energy sequence is summable*: the two questions have different hypotheses.

To escape globally affine grids, assign an independent horizontal
offset $\delta_n\in\mathbb R$ to each integer row $n$.
The tiles become

```math
S^\delta_{m,n}
=[m+\delta_n,m+\delta_n+1]\times[n,n+1].
```

For **any offsets**, even unbounded ones, Lean proves plane coverage,
disjointness of different tile interiors, and separation of distinct
centroids by Euclidean distance at least one.

The centroid energy is

```math
q_\delta(m,n)=1+
   (m+\frac{1}{2}+\delta_n)^2+(n+\frac{1}{2})^2.
```

If $|\delta_n|\le\frac{1}{2}$ uniformly, Lean additionally proves

```math
q(m,n)\le2\,q_\delta(m,n)
\quad\Longrightarrow\quad
\sum_{m,n}q_\delta(m,n)^{-2}<\infty,
```

and hence Theorem C applies. **The boundedness restriction is needed
for this energy comparison**, not for coverage or nonoverlap.

**Why this matters for the next step.** Coverage and non-overlap hold for completely arbitrary offsets, but this proof of summability requires a uniform bound. The construction still has a horizontal translation period.

**Lean anchors:** `rowShiftCell_covers_plane`,
`rowShiftInterior_unique`, `rowShiftCentroid_separated`,
`rowShiftEnergy_inv_sq_summable`, `rowShiftGrid_theoremC`.
**Boundary:** although offsets need not repeat from row to row, every
such tiling retains the translation period $(1,0)$. It is not
translation-aperiodic in both directions.

## 6. A general coercive criterion for irregular point configurations (**proved on main**)

**Mathematical objective.** Identify a reusable sufficient growth condition that works for arbitrary lattice-indexed energies and irregular collections of points. The criterion should capture the analytic core of earlier examples without repeatedly proving geometry-specific convergence estimates.

The common thread of the previous proofs is not periodicity but
**sufficient growth away from the origin**. For any positive family
$q:\mathbb Z^2\to\mathbb R_{>0}$, suppose one constant $C>0$
satisfies, for every lattice index $p=(m,n)$,

```math
1+(m+\frac{1}{2})^2+(n+\frac{1}{2})^2\le C\,q(p).
```

Lean proves the general consequence

```math
\sum_{p\in\mathbb Z^2}\frac1{q(p)^2}<\infty,
```

as well as admissibility and Theorem C for its enumeration.

A concrete corollary permits a separately chosen point $P_{m,n}$
at *every* lattice index, with bounded coordinate displacements

```math
|P_{m,n}^{(1)}-(m+\frac{1}{2})|\le\frac{1}{2},\qquad
|P_{m,n}^{(2)}-(n+\frac{1}{2})|\le\frac{1}{2}.
```

For $q_P(m,n)=1+\|P_{m,n}\|^2$, Lean verifies the comparison with
$C=2$ and therefore summability and line-localized product zeros.

**Why this matters for the next step.** A set of points with controlled displacement is not necessarily a tiling. The theorem removes periodicity assumptions from energy summability, not the obligation to prove that geometric tiles cover the plane.

**Lean anchors:** `coerciveEnergy_inv_sq_summable`,
`coerciveEnergy_theoremC`, `boundedPointSet_energy_control`,
`boundedPointSet_inv_sq_summable`,
`boundedPointSet_theoremC`.
**Crucial boundary:** these are results about *indexed point
configurations*, not a theorem that arbitrary displaced points are
centroids of actual nonoverlapping tiles. At the endpoint displacement
$\frac{1}{2}$, distinct indices need not even have distinct points.

## 7. A complete tiling with no nonzero translation period (**proved on main**)

**Mathematical objective.** Find an explicit infinite tiling with *no nonzero translation symmetry* as a particular arrangement, while retaining enough control of true centroids to apply Theorem C. This addresses the persistent period of the row-shift examples.

The next step restored actual tile geometry while breaking every
nonzero translational symmetry of the *particular tiling*.
Start from the unit-square grid. In one location, replace two adjacent
unit squares by two rectangles of width $\frac{1}{2}$ and $\frac{3}{2}$,
both of height $1$. Elsewhere, leave the unit squares unchanged.

Lean proves that the rectangles still cover the whole plane, their
open interiors are pairwise disjoint, and the width-$\frac{3}{2}$
rectangle is unique. A translation preserving the collection of
rectangles (including shape and position) must fix that unique tile.
Hence

```math
T+\tau=T\quad\Longrightarrow\quad\tau=(0,0)
```

for the tile-preserving translation notion specified in the source.

The actual rectangular centroids differ by at most $\frac{1}{2}$
in each coordinate from their corresponding square centroids.
The preceding bounded-displacement theorem therefore proves
inverse-square energy summability and Theorem C for this example.

**Why this matters for the next step.** The local defect supplies a simple fully checked example; it is not a strong aperiodicity theorem for the collection of prototiles, since a finite defect does not prohibit other periodic arrangements.

**Lean anchors:** `defectCell_covers_plane`,
`defectInterior_unique`, `defectWidth_unique`,
`defectTiling_translation_aperiodic`,
`defectCentroid_bounded`, `defectTiling_theoremC`.
**Crucial boundary:** this is a *finite defect of a periodic grid*.
It is not a proof of Penrose-style strong aperiodicity of a tile set:
the same prototiles may admit periodic tilings.

## 8. Finite operators detecting tile adjacency (**proved on main**)

**Mathematical objective.** Pass from independent tile energies to an operator encoding **interactions**. For a finite patch, an amplitude at one tile is coupled to amplitudes at neighboring tiles. Prove the key symmetry identity needed for a real finite-dimensional spectrum.

So far the product levels depended mostly on centroid energies.
To make neighboring tiles matter, the source defines a weighted
operator on a finite tile patch with $N$ vertices:

```math
(H_Wu)_i=\sum_{j=1}^{N}W_{ij}u_j.
```

If the weights are real and symmetric, $W_{ij}=W_{ji}$, Lean proves
the real inner-product symmetry

```math
\langle u,H_Wv\rangle=\langle H_Wu,v\rangle.
```

A separate construction sets non-neighbor weights to zero and
proves that symmetric undirected adjacency plus symmetric edge
weights yields a symmetric finite matrix. No periodicity is assumed
for the finite graph.

**Why this matters for the next step.** This changes the nature of the data determining candidate zero heights: graph connectivity and edge weights matter, not just coordinates. The next obstacle is an operator acting on an infinite tiling.

**Lean anchors:** `finitePatchOperator`,
`finitePatchOperator_symmetric`,
`geometricEdgeMatrix_symmetric`,
`geometricFinitePatch_symmetric`.
**Boundary:** this is a **finite** self-adjointness identity. It is
not yet the definition, domain analysis or spectral theorem for an
unbounded operator acting on $\ell^2$ of an infinite tiling.

## 9. A concrete two-tile interaction with distinct spectra (**proved on main**)

**Mathematical objective.** Verify in a completely explicit two-tile model that changing the coupling induced by widths and binary markings changes the **whole set of eigenvalues**. Prove both eigenmodes and exclude any extra real eigenvalues.

The two special rectangles really share a vertical boundary.
Their widths have product $\frac{1}{2}\cdot\frac{3}{2}=\frac{3}{4}$.
We assign each tile an *external binary mark* and choose the
interaction law

```math
\eta(\mu,\nu)=
\begin{cases}
1,&\mu=\nu,\\
2,&\mu\ne\nu,
\end{cases}
\qquad
w(\mu,\nu)=\frac{3}{4}\,\eta(\mu,\nu).
```

The two-tile adjacency operator is

```math
H_w=\begin{pmatrix}0&w\\w&0\end{pmatrix}.
```

The set of real eigenvalues of this matrix is $\{-w,+w\}$.

Lean proves both eigenvalues with explicit nonzero eigenvectors
$(1,1)$ and $(1,-1)$, and proves there are **no other real
eigenvalues** in this model. Equal marks give $w=\frac{3}{4}$;
opposite marks give $w=\frac{3}{2}$. In particular, $\frac{3}{2}$
is an eigenvalue in the opposed-mark model and not in the
equal-mark model.

**Why this matters for the next step.** The example demonstrates genuine local spectral sensitivity. The interaction rule and markings are deliberate modeling choices; a rectangle has no intrinsic chirality, and no statistical assertion follows from a two-dimensional matrix.

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

**Mathematical objective.** Insert proven real eigenvalues of local operators into a positive, summable sequence usable by the infinite product. The analytic requirements are essential: arbitrary real eigenvalues might be negative, zero or too small to make the product converge.

The next bridge uses a positive geometric *growth envelope*
$q_0(n)$, together with any real spectral levels $\lambda_n$:

```math
Q_n=q_0(n)(1+\lambda_n^2).
```

If $q_0(n)>0$ and $\sum_n q_0(n)^{-2}<\infty$, then
$Q_n\ge q_0(n)>0$, so

```math
\sum_n Q_n^{-2}<\infty.
```

Lean proves admissibility and Theorem C for $D_Q$; it also
proves explicitly, for every index $n$,

```math
D_Q(c+dQ_n)=0.
```

The concrete version uses the actual Euclidean square-centroid
energy for $q_0$ and a **proved positive eigenvalue** of each
chosen two-tile marked operator for $\lambda_n$.
Matching marks multiply $q_0$ by $25/16$; opposing marks
multiply it by $13/4$. Hence local interaction data can change
the level of a product zero along the same chosen line.

**Why this matters for the next step.** This creates the first certified spectral influence on actual zero heights, but each level is a **constructed function** of an eigenvalue and a chosen geometric growth envelope; it is not itself an eigenvalue of the displayed adjacency operator.

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

## 11. A level that is an eigenvalue of the *combined* local operator (**proved on main; PR #11**)

**Mathematical objective.** Eliminate that last algebraic mismatch: construct a combined onsite-plus-interaction Hamiltonian such that the product's selected positive level **is a true eigenvalue of that Hamiltonian**. Reuse the centroid growth estimates to preserve product convergence.

The next merged development improves the previous bridge by moving
the geometric baseline **inside** a two-site Hamiltonian:

```math
H_n=
\begin{pmatrix}
V_n&w_n\\
w_n&V_n
\end{pmatrix},
\qquad
\lambda_n^\pm=V_n\pm w_n.
```

Lean proves symmetry and both eigenvalue identities with explicit
nonzero eigenvectors. If $V_n>0$, $w_n\ge0$, and
$\sum_n V_n^{-2}<\infty$, the positive mode

```math
Q_n=\lambda_n^+=V_n+w_n
```

is an **actual eigenvalue of the full two-site operator $H_n$**,
and it satisfies positivity, inverse-square summability,
admissibility, zero localization and $D_Q(c+dQ_n)=0$.

For the example introduced in PR #11, $V_n$ remains the square-centroid
energy and $w_n$ is the marked coupling of the special rectangles.
This is a step forward from multiplying a separately chosen baseline
by a function of an eigenvalue.

**Why this matters for the next step.** This makes a more direct operator-to-zero link. Nevertheless the separate matrices indexed by $n$ do not constitute a single infinite Hamiltonian, and their diagonal potentials are still prescribed geometric energies.

**Lean anchors on `main` (introduced in PR #11):** `interactingPairOperator`,
`interactingPair_positive_mode`, `interactingPair_negative_mode`,
`pairOperatorEigenlevel_inv_sq_summable`,
`markedPairEigenlevel_is_eigenvalue`,
`markedPairEigenlevel_zero_at_level`.
**Verification:** [PR #11](https://github.com/alexodas/jules/pull/11), commit
[`864051f`](https://github.com/alexodas/jules/commit/864051f156eca95c249e6400c1e3d82b9c53b377),
[successful Lean/Mathlib CI](https://github.com/alexodas/jules/actions/runs/38966538546).
**Status:** merged into `main` in [commit `37eb338`](https://github.com/alexodas/jules/commit/37eb338cfe7f4db4efe0041eec17935dfbd67e94).
**Boundary:** each $H_n$ is still a separate two-site operator;
the onsite potential $V_n$ is still chosen from centroid geometry.
This is not a single infinite operator or a proof of zeta statistics.

## 12. A first constraint on level counting (**proved on main; PR #11**)

**Mathematical objective.** Move beyond the location of individual zeros to a necessary statistical test: **count the selected levels below a large threshold**. Prove that a uniformly bounded nonnegative coupling cannot shift those levels beyond a fixed amount.

That same merged development proves a useful limitation of the simple
local model. Suppose $0\le w_n\le C$ and
$Q_n=V_n+w_n$. Then, for every real threshold $T$,

```math
\{n:V_n\le T-C\}
\;\subseteq\;
\{n:Q_n\le T\}
\;\subseteq\;
\{n:V_n\le T\}.
```

The concrete two-rectangle model proves that $C=\frac{3}{2}$
works for any sequence of binary marks.
These are precise **set inclusions**, formally proved by Lean.
When the threshold sets are finite, define the indexed counting functions

```math
N_V(T)=\#\{n:V_n\le T\},
\qquad
N_Q(T)=\#\{n:Q_n\le T\}.
```

The indices count **with multiplicity**: if two different indices
produce the same eigenvalue, both are counted. The inclusions imply

```math
N_V(T-C)\le N_Q(T)\le N_V(T).
```

For the current two-dimensional quadratic centroid baseline, elementary
lattice-point counting gives $N_V(T)$ of order $T$. By contrast, the
classical Riemann--von Mangoldt formula for the nontrivial zeta zeros
with positive ordinate at most $T$ is

```math
N_{\zeta}(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}
-\frac{T}{2\pi}+O(\log T).
```

Its leading growth is of order $T\log T$. Consequently, bounded local
pair couplings applied to this particular quadratic baseline **cannot
produce the same asymptotic level count**. They might still change
small-scale patterns, but matching the overall density already fails.

**Precisely what Lean proves here** is the threshold-set inclusion.
The counting-function translation, lattice-point estimate, and
Riemann--von Mangoldt comparison are mathematical consequences or
external analytic facts **not independently formalized in this file**.

**Why this matters for the next step.** This constrains spectral density. In particular, bounded corrections to a two-dimensional quadratic baseline cannot change its order-$T$ counting law into the order-$T\log T$ zeta-zero law when counting indexed levels with multiplicity. The asymptotic comparison itself is not a Lean theorem here.

**Lean anchors on `main` (introduced in PR #11):**
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

**Also proved on `main`, via merged PR #11:** selected positive levels
are eigenvalues of combined two-site operators, and the sets of levels
below a threshold satisfy bounds relative to the onsite potential.
These remain **local** operators, not one infinite tiling operator.

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
