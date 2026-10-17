# Jules Spectral Geometry

**An experimental mathematical research program in Lean 4 and Mathlib.**

## 1. Research program and geometric model

We want to investigate how a tiling, including an **aperiodic** one with no natural arrangement into rows and columns, can determine a spectrum through a geometric operator. We distinguish what we **choose when defining the model** from what **emerges as an eigenvalue**.

### A geometric operator with three contributions

Our proposed model is a one-parameter family of operators:

```math
H_{\varepsilon}=V+L_w+\varepsilon P,\qquad \varepsilon\in\mathbb R.
```

Its action on a configuration `ψ`, evaluated at a tile `t`, is:

```math
(H_{\varepsilon}\psi)(t)=
\underbrace{V(t)\psi(t)}_{\text{individual energy}}
+\underbrace{\sum_{u\ne t}w(t,u)\bigl(\psi(t)-\psi(u)\bigr)}_{\text{interactions}}
+\underbrace{\varepsilon(P\psi)(t)}_{\text{controlled perturbation}}.
```

The three contributions play different roles:

- **Individual energy `V(t)`.** We assign an energy to each tile using any number of geometric features: centroid, area, shape, orientation, chirality where applicable, substitution hierarchy, or other properties.
- **Interactions `w(t,u)`.** We prescribe weights between pairs of tiles, including nonadjacent ones. Initially, we consider symmetric nonnegative weights, `w(t,u)=w(u,t)\ge0`, so `L_w` is a weighted graph Laplacian.
- **Perturbation `P`.** We introduce an additional linear operator, scaled by the adjustable parameter `ε`. It may represent a local defect, a change in couplings, or a collective effect involving distant tiles. We study it separately even when it could be absorbed into `V` or `w`. At `ε=0`, we recover the unperturbed operator `H_0=V+L_w`.

Here, **`ψ` assigns an amplitude `ψ(t)` to every tile**. It is a configuration of the entire tiling, not an intrinsic property of one tile. The interaction term compares amplitudes on two tiles; `w(t,u)` describes their geometric relationship. We do not preselect the eigenfunctions using formulas for individual tile features.

For a finite patch of `N` tiles, after ordering the tiles, the same construction has the matrix form:

```math
H_{\varepsilon}=
\mathrm{diag}\left(V_i+\sum_jw_{ij}\right)-W+\varepsilon P,
\qquad W=(w_{ij}).
```

The geometry determines the matrix entries; **we do not choose the eigenvalues**. The perturbation matrix can have both diagonal and off-diagonal entries. If `P` is real symmetric, then `H_{\varepsilon}` is real symmetric for any real `ε` and has `N` real eigenvalues, counted with multiplicity. Symmetry by itself does not guarantee positivity.

An **eigenfunction** `ψ_n^{(\varepsilon)}` is a nonzero configuration satisfying:

```math
H_{\varepsilon}\psi_n^{(\varepsilon)}
=\lambda_n(\varepsilon)\psi_n^{(\varepsilon)}.
```

Both eigenfunctions and eigenvalues may change with `ε`. We are interested primarily in **the eigenvalues `λ_n(ε)`**, not in the coefficients of an arbitrary configuration expanded in eigenfunctions.

### From finite matrices to an infinite tiling

Our first goal is to prove properties that hold for general classes of geometric operators and perturbations. We can then study particular tilings, such as Penrose, Ammann–Beenker, Pinwheel, and Spectre, without imposing a periodic lattice.

For infinitely many tiles, a natural state space is the space of square-summable amplitudes `ℓ²(T)`. We must rigorously define the operator domains, the convergence of interaction and perturbation terms, and conditions for self-adjointness. Unlike a finite symmetric matrix, an infinite operator can have continuous spectrum.

We will investigate hypotheses yielding a positive, discrete spectrum with finite multiplicities, for example through a positive self-adjoint operator with compact resolvent:

```math
0<\lambda_0(\varepsilon)\le\lambda_1(\varepsilon)\le\cdots,
\qquad \lambda_n(\varepsilon)\longrightarrow+\infty.
```

Perturbation theory is part of this program. A bounded self-adjoint perturbation preserves self-adjointness and compact resolvent when the unperturbed operator has those properties, but **positivity requires an additional condition** (for example, a perturbation sufficiently small relative to a positive lower bound). We will investigate how eigenvalues move with `ε` and when the analytic conditions below remain valid. These are mathematical objectives, not yet Lean theorems about an infinite geometric operator.

## 2. Canonical product and analytic foundations

We already have the **definition and Lean formalization** of the canonical product:

```math
D_q(s)=\prod_{n=0}^{\infty}
\left(1-\frac{(s-c)^2}{d^2q_n^2}\right),
\qquad d\ne0.
```

Its definition, convergence criterion, and zero-localization theorems are in **[`SpectralGeometry/CanonicalProduct.lean`](SpectralGeometry/CanonicalProduct.lean)**. In particular, if the levels `q_n` are positive and

```math
\sum_{n=0}^{\infty}\frac1{q_n^2}<\infty,
```

the formalized theorems establish the appropriate convergence of the product, that **all its zeros lie on the prescribed affine line** `s=c+dt` with real `t`, and that each level `q_n` gives rise to zeros at `s=c\pm d q_n`.

Our new challenge is to obtain these levels from **the full infinite geometric operator, including its controlled perturbation**, by setting:

```math
q_n=\lambda_n(\varepsilon),\qquad
H_\varepsilon\psi_n^{(\varepsilon)}
=\lambda_n(\varepsilon)\psi_n^{(\varepsilon)}.
```

We must prove that this operator has the required positive, discrete eigenvalue sequence and that, for the chosen `ε`,

```math
\sum_{n=0}^{\infty}\frac1{\lambda_n(\varepsilon)^2}<\infty.
```

Under these conditions, we can apply the existing canonical-product theory to the **spectrally determined family**:

```math
D_{\varepsilon}(s)=
\prod_{n=0}^{\infty}
\left(1-\frac{(s-c)^2}{d^2\lambda_n(\varepsilon)^2}\right).
```

For `c=1/2` and `d=i`, its zeros lie on the prescribed critical line, at heights given by the eigenvalues:

```math
s=\frac12\pm i\lambda_n(\varepsilon).
```

**The line is imposed by the construction of the product, not derived from any property of the Riemann zeta function.** We have not yet formalized `H_\varepsilon` on an infinite tiling, proved its required spectral properties, or connected its spectrum to the product in Lean. This project does not prove the Riemann hypothesis and does not identify `D_\varepsilon` with the zeta function.

## 3. Finite-dimensional geometric operators

### 3.1. Symmetry under controlled perturbations

The first theorem about our geometric operator is formalized in **[`SpectralGeometry/FinitePerturbation.lean`](SpectralGeometry/FinitePerturbation.lean)** and checked by Lean.

**In simple terms:** imagine a finite collection of tiles. Each tile has its own energy, pairs of tiles interact with symmetric weights, and we add a perturbation matrix `P` whose influence is controlled by `ε`. If both the interaction weights and `P` are symmetric, **the complete matrix remains symmetric whatever real value we choose for `ε`**:

```math
w(t,u)=w(u,t),\quad P_{tu}=P_{ut}
\quad\Longrightarrow\quad
(H_{\varepsilon})_{tu}=(H_{\varepsilon})_{ut}
\quad\text{for every }\varepsilon\in\mathbb R.
```

The file also proves that setting `ε=0` recovers exactly the unperturbed geometric matrix. This is useful because real symmetric finite matrices have real eigenvalues, so changing a symmetric perturbation cannot destroy that structural feature.

**Scope of the proof:** the verified theorem concerns a *finite* matrix. It does not yet establish positive eigenvalues, self-adjointness of the infinite tiling operator, discrete infinite spectrum, or inverse-square summability. Those are separate questions for later files.

### 3.2. Positivity under controlled perturbations

The next theorem is formalized in **[`SpectralGeometry/FinitePositiveEnergy.lean`](SpectralGeometry/FinitePositiveEnergy.lean)**. It concerns the *quadratic energy* of the very same finite matrix defined in the preceding file. For a state `ψ`, define:

```math
Q_M(\psi)=\sum_{t,u}\psi(t)\,M_{tu}\,\psi(u).
```

The formalized identity says that the perturbed energy separates exactly into two parts:

```math
Q_{H_\varepsilon}(\psi)=Q_{H_0}(\psi)+\varepsilon Q_P(\psi).
```

**In simple terms:** if the original geometric operator has nonnegative energy for every configuration, and the chosen perturbation also has nonnegative energy, then turning on that perturbation with `ε\ge0` cannot make the total energy negative:

```math
\bigl(Q_{H_0}(\psi)\ge0,\ Q_P(\psi)\ge0,\ \varepsilon\ge0\bigr)
\quad\Longrightarrow\quad Q_{H_\varepsilon}(\psi)\ge0.
```

The Lean file also proves that **strictly positive** base energy on every nonzero configuration stays strictly positive under the same assumptions. These results concern all tile-amplitude configurations, not a selection of eigenfunctions.

**Scope of the second result:** this theorem proves *stability* of positivity, assuming positivity of the original and perturbation energies. The following section derives a sufficient condition for the original energy from the geometric inputs themselves. The infinite-tiling spectral properties are still unproved.

### 3.3. Nonnegative energy from geometry

The third geometric result is developed in **[`SpectralGeometry/FiniteGeometricEnergy.lean`](SpectralGeometry/FiniteGeometricEnergy.lean)**. It answers the natural question left open by the previous section: *when do the tile energies and interaction weights themselves guarantee nonnegative energy?*

For a finite set of tiles, assume the individual energies are nonnegative, the pair weights are symmetric and nonnegative, and self-interaction weights vanish (`w(t,t)=0`, consistent with summing only over `u\ne t`). The quadratic energy of the unperturbed matrix can then be rewritten as a **sum of squares**:

```math
Q_{H_0}(\psi)=
\sum_t V(t)\psi(t)^2+
\frac12\sum_{t,u}w(t,u)\bigl(\psi(t)-\psi(u)\bigr)^2.
```

Each summand is nonnegative. Thus **the geometry alone forces `Q_{H_0}(\psi)\ge0` for every real tile-amplitude configuration**. The factor `1/2` compensates for counting each pair of distinct tiles in both directions.

Combining this with the preceding perturbation theorem also gives nonnegative energy for `H_\varepsilon=H_0+\varepsilon P` whenever `\varepsilon\ge0` and the quadratic energy of `P` is nonnegative.

**Scope:** this is a statement about finite quadratic forms. Nonnegative energy allows *zero* eigenvalues; it does not itself establish strictly positive eigenvalues, an infinite self-adjoint operator, compact resolvent, or the inverse-square spectral summability needed for the canonical product.

### 3.4. Strictly positive energies and eigenvalues

The next step is formalized in **[`SpectralGeometry/FiniteStrictPositivity.lean`](SpectralGeometry/FiniteStrictPositivity.lean)**. The preceding theorem ruled out *negative* quadratic energy, but still allowed energy equal to zero. Here we prove a sufficient condition that excludes zero for every nonzero configuration.

Assume **every tile has strictly positive individual energy** (`V(t)>0`), while interactions have symmetric nonnegative weights (`w(t,u)=w(u,t)\ge0`, with `w(t,t)=0`). Then the established sum-of-squares identity gives:

```math
\psi\ne0 \quad\Longrightarrow\quad
Q_{H_0}(\psi)=
\sum_t V(t)\psi(t)^2+
\frac12\sum_{t,u}w(t,u)(\psi(t)-\psi(u))^2>0.
```

**Why is it strictly positive?** For a nonzero configuration there is at least one tile where `\psi(t)\ne0`. Since `V(t)>0`, the individual-energy term for that tile is strictly positive, and every other term is nonnegative.

The same conclusion holds for the perturbed operator `H_\varepsilon=H_0+\varepsilon P` if `\varepsilon\ge0` and `Q_P(\psi)\ge0` for every configuration. The Lean file additionally proves the corresponding **real eigenvalue positivity**: for every real eigenpair `H_\varepsilon\psi=\lambda\psi` with `\psi\ne0`, we have `\lambda>0`. Indeed, on an eigenvector:

```math
Q_{H_\varepsilon}(\psi)=
\lambda\sum_t\psi(t)^2>0
\quad\Longrightarrow\quad \lambda>0.
```

Together with the **symmetry theorem** (when `P` is symmetric), this means every eigenvalue of the real symmetric *finite* perturbed matrix is strictly positive under these hypotheses.

**Scope:** the result is finite-dimensional; the hypothesis `V(t)>0` for every tile is sufficient, not necessarily optimal. It does not yet construct the infinite operator, establish a uniform spectral gap across growing patches, or prove inverse-square eigenvalue summability.

## 4. Infinite-dimensional onsite operator

### 4.1. Square-summable states and the natural operator domain

The next Lean module, **[`SpectralGeometry/InfiniteOnsite.lean`](SpectralGeometry/InfiniteOnsite.lean)**, begins the transition from finite matrices to an arbitrary, possibly infinite, set of tiles `T`.

A state now belongs to the real Hilbert space of square-summable tile amplitudes:

```math
\ell^2(T)=\left\{\psi:T\to\mathbb R:
\sum_{t\in T}|\psi(t)|^2<\infty\right\}.
```

There is an essential distinction from the finite case: a potential `V(t)` may grow without bound, so even when `\psi\in\ell^2(T)`, the pointwise product `V(t)\psi(t)` need not lie in `\ell^2(T)`. An operator must therefore have a **specified domain**. For the onsite (diagonal) contribution we choose its natural multiplication domain:

```math
D(V)=\left\{\psi\in\ell^2(T):t\mapsto V(t)\psi(t)\in\ell^2(T)\right\},
\qquad (M_V\psi)(t)=V(t)\psi(t).
```

The new Lean file proves that `D(V)` is a real **linear subspace**, constructs `M_V:D(V)\to\ell^2(T)` as a linear map, checks its value on each tile, and proves that when `V(t)\ge0`, each local energy contribution `\psi(t)(M_V\psi)(t)` is nonnegative. These facts require neither a finite number of tiles nor a bounded potential.

**Scope of this first infinite result:** only the individual-energy contribution is built here. The pair-interaction Laplacian `L_w` and the perturbation `\varepsilon P` have not yet been extended to the infinite setting. The density of `D(V)` is addressed in the next section. Self-adjointness, compact resolvent, discrete eigenvalues, and inverse-square summability are further steps, not consequences of simply defining the domain.

### 4.2. Density of the natural operator domain

The new Lean module **[`SpectralGeometry/InfiniteOnsiteDensity.lean`](SpectralGeometry/InfiniteOnsiteDensity.lean)** establishes that the natural domain `D(V)` introduced in the previous section is **dense in `\ell^2(T)`**, even when the potential `V(t)` is unbounded and the set of tiles is infinite.

**The idea is simple:** switch on amplitudes at only finitely many tiles and leave all other amplitudes equal to zero. Every such finite-support configuration belongs to `D(V)`, because multiplying its finitely many nonzero amplitudes by real numbers `V(t)` still leaves finitely many nonzero amplitudes.

Any square-summable configuration can be approximated arbitrarily closely (in the `\ell^2` norm) by these finite-support configurations. Consequently:

```math
\overline{D(V)}=\ell^2(T).
```

This does **not** say `D(V)=\ell^2(T)`. It says every square-summable state can be approximated as accurately as desired by states on which the onsite operator is well-defined. Mathlib's convergent sum of `lp.single` states supplies the approximation theorem.

**Why it matters:** density is a crucial prerequisite for the Hilbert-space theory of adjoint and self-adjoint unbounded operators. It does *not*, by itself, establish self-adjointness, compact resolvent, a discrete infinite spectrum, or spectral summability. The infinite interaction operator and the perturbation also remain to be constructed.

### 4.3. Point eigenvalues and positivity

The Lean module **[`SpectralGeometry/InfiniteOnsiteEigenvalues.lean`](SpectralGeometry/InfiniteOnsiteEigenvalues.lean)** studies which eigenvalues the densely defined multiplication operator `M_V` can have on an infinite tiling. No bound on `V` and no finiteness of the tile set are assumed.

**In simple terms:** suppose a nonzero state `ψ` is an eigenstate with eigenvalue `λ`. At each tile, the eigenvalue equation says

```math
V(t)\psi(t)=\lambda\psi(t).
```

Therefore, wherever the amplitude `ψ(t)` is nonzero, we must have **`λ=V(t)`**. Conversely, the amplitude must vanish at every tile where `V(t)\ne\lambda`. So a possible eigenstate is supported entirely on tiles with the same onsite energy. This is a property of the *diagonal* infinite operator, not a statement about the full interacting system.

The file formalizes this support restriction and two consequences:

- If every onsite energy satisfies `V(t)>0`, then **every eigenvalue with a nonzero eigenstate is strictly positive**: `λ>0`.
- If all energies satisfy the uniform lower bound `V(t)\ge c`, then every such eigenvalue satisfies `λ\ge c`.

**Scope and important limitation:** these are results about the *point spectrum* of the infinite onsite multiplication operator. They do not prove that the operator is self-adjoint, that every `V(t)` occurs as an eigenvalue, that the entire spectrum is positive or discrete, or that the inverse-square eigenvalue series converges. The infinite interaction Laplacian and controlled perturbation still need to be constructed before we can study the full geometric operator `H_\varepsilon`.

### 4.4. A sufficient growth condition for summable spectral levels

The Lean module **[`SpectralGeometry/InfiniteOnsiteSummability.lean`](SpectralGeometry/InfiniteOnsiteSummability.lean)** provides the next connection between an *infinite* diagonal geometric operator and the already formalized canonical product.

Suppose the tiles have been indexed by natural numbers, and assume their onsite energies grow at least linearly with this index:

```math
V(n)\ge n+1,\qquad n=0,1,2,\ldots.
```

Then each energy is positive, and the new theorem proves the crucial **inverse-square summability**:

```math
\sum_{n=0}^{\infty}\frac{1}{V(n)^2}<\infty.
```

**Why?** The inverse squares are nonnegative and bounded term by term by `1/(n+1)^2`, whose series is convergent. This makes `q_n=V(n)` an admissible sequence for the canonical-product results already checked in `CanonicalProduct.lean`. The new Lean file also proves that **each `V(n)` is a genuine eigenvalue of the diagonal onsite operator**, using a single-tile state as its eigenvector.

**Important limitations:** the linear growth condition is *assumed*, **not** derived from Penrose or any other tiling geometry. It depends on the chosen indexing and is sufficient rather than necessary. The result concerns the diagonal onsite operator alone; it does not establish self-adjointness, compact resolvent, or spectral estimates for the full interacting and perturbed operator `H_\varepsilon`. Nor does canonical-product admissibility identify the resulting zeros with those of the Riemann zeta function.

### 4.5. Power-law growth: the critical exponent one half

The Lean module **[`SpectralGeometry/InfiniteOnsitePowerGrowth.lean`](SpectralGeometry/InfiniteOnsitePowerGrowth.lean)** improves the linear-growth hypothesis in §4.4.

For tiles indexed by the natural numbers, assume the **onsite levels obey**

```math
V(n)\ge (n+1)^\alpha,\qquad \alpha>\frac12.
```

Even though the growth may be *slower than linear*, the formalized comparison with a convergent `p`-series proves

```math
\sum_{n=0}^\infty\frac{1}{V(n)^2}<\infty.
```

The file proves that these levels are positive and form an `Admissible` sequence for the already-verified canonical-product theory. **The threshold is sharp for exact power-law levels**: for `V(n)=(n+1)^α`, the same sum diverges when `α≤1/2`. Thus the theorem separates the *sufficient growth condition* from the critical boundary, rather than imposing linear growth unnecessarily.

**Scope:** indexing the tiles and assuming this lower bound are external modeling choices here; no Penrose, Pinwheel, or other aperiodic tiling has been proved to generate the prescribed growth. The converse divergence applies only to the exact power-law example, not to all sequences satisfying a weak lower bound. These are statements about the diagonal onsite spectrum and its analytic product, **not** self-adjointness or compact resolvent for the full interacting operator and **not** an identification with the Riemann zeta zeros.

### 4.6. Geometric interactions acting on infinite square-summable states

The Lean module **[`SpectralGeometry/InfiniteFiniteEdgeInteraction.lean`](SpectralGeometry/InfiniteFiniteEdgeInteraction.lean)** introduces genuine pairwise interaction operators on the infinite Hilbert space `ℓ²(T)`. For an edge joining tiles `a` and `b` with weight `w≥0`, its action is

```math
L_{a,b}\psi = w(\psi(a)-\psi(b))(\delta_a-\delta_b).
```

This state remains square-summable even when `T` is infinite: only two coordinates can be affected. Its exact quadratic energy is

```math
\langle \psi,L_{a,b}\psi\rangle
 = w(\psi(a)-\psi(b))^2\ge0.
```

The module proves that the edge operator is linear and symmetric, and that **any finite collection of these geometric edges** gives a well-defined symmetric, nonnegative interaction on infinite `ℓ²(T)`.

**Precise scope:** the ambient set of tiles may be infinite, but the number of active interaction edges in this first construction is **finite**. The genuinely infinite-edge Laplacian still needs a convergence or uniform-weight hypothesis. This theorem is not yet a model of every edge in an infinite Penrose or other tiling.

### 4.7. Combining infinite onsite energies, interactions, and perturbations

The Lean module **[`SpectralGeometry/InfiniteBoundedPerturbation.lean`](SpectralGeometry/InfiniteBoundedPerturbation.lean)** combines the existing potentially unbounded onsite operator `M_V` with the finite-edge interaction operator and an **everywhere-defined bounded linear** perturbation `P`:

```math
H_\varepsilon\psi = M_V\psi+L_{E,w}\psi+\varepsilon P\psi,
\qquad \psi\in D(V).
```

All terms map the same state into `ℓ²(T)`; hence their sum is defined on the existing dense onsite domain `D(V)`. Lean formalizes the **exact decomposition of the full quadratic energy**. Assuming `V(t)≥0`, nonnegative active edge weights, `\langle\psi,P\psi\rangle≥0` and `\varepsilon≥0`, the combined energy is nonnegative. The combined operator is also symmetric if the perturbation is symmetric.

**Crucial distinction:** positivity *does* survive an operator sum when the three quadratic forms are well-defined and nonnegative on a shared domain (and the perturbation has the correct sign). However, **self-adjointness, compact resolvent, discrete spectrum, strict positivity and inverse-square spectral summability do not follow automatically from these componentwise hypotheses**. The `V(n)` growth results in §§4.4–4.5 currently refer only to the diagonal operator; they are not yet theorems about eigenvalues of `H_\varepsilon`.

### 4.8. Countably infinite geometric interactions with summable weights

The Lean module **[`SpectralGeometry/InfiniteSummableEdgeInteraction.lean`](SpectralGeometry/InfiniteSummableEdgeInteraction.lean)** removes the *finite number of edges* restriction in §§4.6–4.7 under a rigorous, explicit convergence hypothesis.

Suppose geometric edges are enumerated by natural numbers, with endpoints `(a_n,b_n)` and real weights `w_n`. Assume **absolute summability**:

```math
\sum_{n=0}^\infty |w_n|<\infty.
```

The edge vector is `v_n=δ_{a_n}-δ_{b_n}`. Since `||v_n||≤2`, each rank-one edge operator has norm at most `4|w_n|`. Therefore the **infinite series of operators converges in operator norm**, defining a bounded linear operator on all of `ℓ²(T)`:

```math
L_w=\sum_{n=0}^\infty w_n\lvert v_n\rangle\langle v_n\rvert.
```

If in addition every `w_n≥0`, the module proves the infinite operator is **symmetric and has nonnegative, finite quadratic energy** on every square-summable state. Lean also proves that the combined `M_V+L_w+εP` on the **original dense domain `D(V)`** is symmetric under symmetric `P` and nonnegative when `V≥0`, `w≥0`, `ε≥0`, and the bounded perturbation `P` has nonnegative quadratic energy.

**What is not claimed:** this is a sufficient `ℓ¹` condition on the *entire* edge list, not yet a bounded-degree local graph condition. Infinite tilings with uniformly bounded non-decaying weights typically have infinitely many edges and do not satisfy `∑|w_n|<∞`. No geometry-specific weight bound, self-adjointness of the full unbounded sum, compact resolvent, or full-spectrum inverse-square summability is established.

### 4.9. Bounded-degree local interactions from infinite matching families

The Lean modules **[`SpectralGeometry/InfiniteLocalMatching.lean`](SpectralGeometry/InfiniteLocalMatching.lean)** and **[`SpectralGeometry/InfiniteLocalBoundedDegree.lean`](SpectralGeometry/InfiniteLocalBoundedDegree.lean)** introduce a genuinely infinite set of interacting edges without imposing the global summability of their weights.

In this *matching-colorable* model, each of the `D` colors specifies an involutive bijection `σᵢ:T≃T`; it connects every tile to at most one tile of that color. Thus every tile has at most `D` candidate neighbors. The color has a single nonnegative constant weight `wᵢ≤W`. The corresponding matching operator acts by

```math
(L_i\psi)(t)=\psi(t)-\psi(\sigma_i(t)),
\quad
L_w=\sum_{i=1}^{D} w_iL_i.
```

Even though each color may cover infinitely many edges of fixed nonzero weight, `L_w` acts on all of `ℓ²(T)`. The formalized results show that the norm satisfies

```math
\|L_w\|\le 2DW,
```

that all nonnegative matching weights give **nonnegative, finite quadratic energy**, and that involutive matchings make the operator **symmetric**. The same module combines `L_w` with the possibly unbounded onsite operator and a bounded perturbation on their common dense domain `D(V)`, obtaining conditional positivity and symmetry of the *total* operator.

**Scope:** this is an important subclass of uniformly bounded-degree graphs: those described by finitely many involutive matching permutations with a constant weight per color. We have **not** proved that arbitrary locally finite graphs (including a specific Penrose adjacency graph) have been represented this way; tile-dependent edge weights and general graph decompositions require additional work. Symmetry and positivity still do **not** establish self-adjointness, compact resolvent, or inverse-square summability of the full spectrum.

### 4.10. Lower bounds on point eigenvalues of infinite local operators

The Lean module **[`SpectralGeometry/InfiniteLocalEigenvalueBounds.lean`](SpectralGeometry/InfiniteLocalEigenvalueBounds.lean)** studies point eigenvalues of the **full infinite local matching model** introduced in §4.9, including the unbounded onsite term, infinitely many local interactions (represented by finitely many involutive matching colors), and a bounded perturbation.

Suppose the onsite potential is nonnegative (`V(t)≥0`), the matching weights are nonnegative (`wᵢ≥0`), and the bounded perturbation `P` has nonnegative quadratic energy. For `ε≥0`, every nonzero eigenstate of the combined operator has a **nonnegative eigenvalue**:

```math
H_\varepsilon\psi=\lambda\psi,\quad\psi\ne0
\quad\Longrightarrow\quad \lambda\ge0.
```

The proof uses the nonnegative total quadratic energy established in §4.9 and the eigenvector identity `⟨ψ,Hεψ⟩=λ‖ψ‖²`. It does **not** presuppose an eigenbasis or a discrete spectrum.

A particularly transparent way to obtain a **strict positive lower bound** is a uniform scalar (identity) perturbation `P=I`. With `V≥0` and `wᵢ≥0`, any existing point eigenvalue obeys, for **every real** `ε`,

```math
H_\varepsilon=M_V+L_w+\varepsilon I,\qquad
H_\varepsilon\psi=\lambda\psi,\ \psi\ne0
\quad\Longrightarrow\quad \lambda\ge\varepsilon.
```

Indeed, the onsite and interaction quadratic energies are nonnegative, so `(λ-ε)‖ψ‖²≥0`. If `ε>0`, every point eigenvalue is **strictly positive**. This bound holds without absolute summability of all edge weights and without bounding `V` from above.

**Scope:** these theorems constrain eigenvalues *if nonzero eigenvectors exist*. They neither show that point eigenvalues exist nor rule out continuous spectrum. The full operator's self-adjointness, compact resolvent, discreteness, inverse-square summability, and connection to the canonical product remain open formalization goals.

### 4.11. Stable spectral lower bounds under signed bounded perturbations

The Lean module **[`SpectralGeometry/InfiniteLocalSignedPerturbationGap.lean`](SpectralGeometry/InfiniteLocalSignedPerturbationGap.lean)** extends §4.10 to a **bounded perturbation of arbitrary sign**. We no longer assume that its quadratic energy is nonnegative, nor that the coupling parameter is positive.

For a bounded real-linear perturbation `P` and a square-summable state `ψ`, the operator norm controls its quadratic energy:

```math
\left|\langle\psi,P\psi\rangle\right|
\le \|P\|\,\|\psi\|^2.
```

Assume nonnegative onsite energies `V(t)≥0` and nonnegative matching weights `wᵢ≥0`. Whenever a **nonzero** state in the natural onsite domain is a real eigenvector of the full operator `H_ε=M_V+L_w+εP`, Lean now proves:

```math
H_\varepsilon\psi=\lambda\psi,\quad \psi\ne 0
\quad\Longrightarrow\quad
\lambda\ge -|\varepsilon|\,\|P\|.
```

Thus an arbitrary signed bounded perturbation can lower a **real point eigenvalue** by at most `|ε|‖P‖` relative to the zero lower bound supplied by the nonnegative onsite-plus-matching quadratic energy.

To obtain a positive gap, the file also defines the independently shifted operator

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI.
```

Every real point eigenvalue obeys the **quantitative lower bound**

```math
\lambda\ge m-|\varepsilon|\,\|P\|.
```

In particular, when `m>|ε|‖P‖`, **every existing real point eigenvalue is strictly positive**. This generalizes the identity-only shift of §4.10: `P` may now be a non-positive or nonsymmetric bounded operator, and `ε` may have either sign.

**Precise scope:** these are estimates on **real point eigenvalues**, assuming a nonzero eigenvector exists. Without symmetry of `P`, no claim that the operator has only real spectrum is made. The theorems do **not** establish self-adjointness, the existence of eigenvalues, compact resolvent, absence of continuous spectrum, discreteness, or the inverse-square summability needed for the canonical product.

### 4.12. Coercive energy and residual gap for infinite local operators

The Lean module **[`SpectralGeometry/InfiniteLocalCoerciveGap.lean`](SpectralGeometry/InfiniteLocalCoerciveGap.lean)** strengthens the point-eigenvalue results of §§4.10–4.11. Instead of making a statement only **if an eigenvector exists**, it proves a bound on **every state in the natural domain** `D(V)` of the complete infinite local matching operator.

Continue to assume nonnegative onsite energies `V(t)≥0` and nonnegative constant matching weights `wᵢ≥0`. Let `P` be an arbitrary bounded real-linear perturbation, with no positivity or symmetry assumption, and let `ε,m∈ℝ`. For

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI
```

the formalized **quadratic-form lower bound** is

```math
\langle\psi,H_{\varepsilon,m}\psi\rangle
\ge \left(m-|\varepsilon|\|P\|\right)\|\psi\|^2
\qquad(\psi\in D(V)).
```

Set `g=m-|ε|‖P‖`. For **every real** trial spectral parameter `a`, Lean also proves the quantitative **residual norm bound**

```math
\left\|(H_{\varepsilon,m}-aI)\psi\right\|
\ge (g-a)\|\psi\|
\qquad(\psi\in D(V)).
```

If `a<g`, the right-hand coefficient is strictly positive. Therefore the equation `Hψ=aψ` has **only the zero solution**. Even more strongly, for every unit-norm domain state we have `‖Hψ-aψ‖≥g-a>0`: there cannot be a sequence of normalized domain states whose residual tends to zero at such a real `a`.

**Why this advances the project:** §4.11 controlled only real point eigenvalues. The new estimate controls *all* admissible states and excludes both exact and approximate real eigenvectors below an explicit threshold, without assuming a discrete spectral decomposition.

**Essential limitation:** injectivity and a lower norm bound for `H-aI` do **not** by themselves prove surjectivity or an everywhere-defined inverse. Without appropriate self-adjointness or further range arguments, we do not claim `a` is outside the full spectrum or that there is a compact resolvent. Neither a complete real spectrum, eigenvalue existence, spectral discreteness, inverse-square summability, nor any geometric model of a particular aperiodic tiling has yet been established by this module.

## 5. Building and verification

The established analytic core is in `SpectralGeometry/CanonicalProduct.lean`. The finite-dimensional geometric results are in `SpectralGeometry/FinitePerturbation.lean`, `SpectralGeometry/FinitePositiveEnergy.lean`, `SpectralGeometry/FiniteGeometricEnergy.lean`, and `SpectralGeometry/FiniteStrictPositivity.lean`. These four finite-dimensional modules and the thirteen infinite-dimensional modules `SpectralGeometry/InfiniteOnsite.lean`, `SpectralGeometry/InfiniteOnsiteDensity.lean`, `SpectralGeometry/InfiniteOnsiteEigenvalues.lean`, `SpectralGeometry/InfiniteOnsiteSummability.lean`, `SpectralGeometry/InfiniteOnsitePowerGrowth.lean`, `SpectralGeometry/InfiniteFiniteEdgeInteraction.lean`, `SpectralGeometry/InfiniteBoundedPerturbation.lean`, `SpectralGeometry/InfiniteSummableEdgeInteraction.lean`, `SpectralGeometry/InfiniteLocalMatching.lean`, `SpectralGeometry/InfiniteLocalBoundedDegree.lean`, `SpectralGeometry/InfiniteLocalEigenvalueBounds.lean`, `SpectralGeometry/InfiniteLocalSignedPerturbationGap.lean`, and `SpectralGeometry/InfiniteLocalCoerciveGap.lean` are imported by the `SpectralGeometry.lean` entry point. The toolchain is Lean 4 `v4.35.0` with the corresponding version of Mathlib.

```bash
lake update
lake exe cache get
lake build
```

GitHub Actions automatically checks compilation on every change to `main` and on every pull request.
