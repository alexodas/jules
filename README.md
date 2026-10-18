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

### 4.13. Graph-norm control for infinite local operators

The Lean module **[`SpectralGeometry/InfiniteLocalGraphNorm.lean`](SpectralGeometry/InfiniteLocalGraphNorm.lean)** prepares the next analytic question, **closedness** of the full operator on its natural domain, by quantifying how the unbounded onsite operator and its bounded local corrections compare.

Write, as before,

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI,\qquad
\psi\in D(V).
```

Although the onsite energy `V` may be unbounded, the infinite matching Laplacian `L_w` is a bounded operator on all of `ℓ²(T)`, as is `P`. Let

```math
C=\|L_w\|+|\varepsilon|\|P\|+|m|.
```

Lean proves that the full operator differs from the onsite operator by a **uniformly bounded correction**:

```math
\|(H_{\varepsilon,m}-M_V)\psi\|\le C\|\psi\|.
```

The resulting two-sided **graph estimates** are:

```math
\|H_{\varepsilon,m}\psi\|\le\|M_V\psi\|+C\|\psi\|,
\qquad
\|M_V\psi\|\le\|H_{\varepsilon,m}\psi\|+C\|\psi\|.
```

For `D` matching colors with nonnegative weights `wᵢ≤W` and `W≥0`, the earlier geometric estimate `‖L_w‖≤2DW` gives the explicit bound

```math
\|M_V\psi\|\le\|H_{\varepsilon,m}\psi\|
+(2DW+|\varepsilon|\|P\|+|m|)\|\psi\|.
```

**Interpretation:** the bounded interactions and perturbations cannot change the size of the unbounded part in an uncontrolled way. The natural domain stays `D(V)`, and the graph measurements of `M_V` and `H_{\varepsilon,m}` control one another quantitatively. These statements require no positivity assumption on `V`, and no positivity or symmetry assumption on `P`.

**Scope:** this module establishes explicit norm comparisons, not closedness, self-adjointness, surjectivity, compact resolvent, discreteness of spectrum, or eigenvalue summability. Closedness of the natural onsite operator and of its boundedly perturbed counterpart is established separately in §4.14.

### 4.14. Closed graphs of the onsite and full infinite local operators

The Lean module **[`SpectralGeometry/InfiniteLocalClosedGraph.lean`](SpectralGeometry/InfiniteLocalClosedGraph.lean)** establishes a first genuine **closed-operator** property, building on the graph-norm estimates of §4.13.

The onsite operator `M_V` is multiplication by an arbitrary real onsite potential `V(t)`, possibly unbounded. Its natural domain is

```math
D(V)=\{\psi\in\ell^2(T): V\psi\in\ell^2(T)\}.
```

The module proves that the graph

```math
G(M_V)=\{(\psi,M_V\psi):\psi\in D(V)\}
\subseteq\ell^2(T)\times\ell^2(T)
```

is **closed**. Informally, whenever the inputs `ψₙ` converge in `ℓ²` and their outputs `M_V ψₙ` also converge in `ℓ²`, the limiting input is still in the natural domain, and the limiting output equals the onsite operator applied to it. The proof identifies the graph with the coordinatewise equations `η(t)=V(t)ψ(t)`; each coordinate evaluation on `ℓ²` is continuous, so these simultaneous equations define a closed set.

The interaction Laplacian built from finitely many matching colors is a **bounded** operator, as is any bounded linear perturbation `P` and the identity shift. Therefore, for

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI
\quad\text{on }D(V),
```

the graph `G(H_{\varepsilon,m})` is also **closed**. The proof is explicit: subtracting the bounded correction `B=L_w+εP+mI` from the output of a graph pair reduces it to a pair in `G(M_V)`. This subtraction is continuous.

No nonnegativity of `V`, matching weights or `P` is needed for closedness, and no symmetry of `P` is assumed. The matching-family representation remains the same special class of infinite local interactions as in §4.9.

**Scope:** closedness is **not the same as self-adjointness**. In particular, this result alone does not show that the operator equals its adjoint, has a resolvent at any given point, has compact resolvent, possesses a purely discrete spectrum, or satisfies inverse-square spectral summability. These remain separate formalization goals.

### 4.15. Explicit adjoint characterization and self-adjointness criterion

The Lean module **[`SpectralGeometry/InfiniteLocalAdjointCharacterization.lean`](SpectralGeometry/InfiniteLocalAdjointCharacterization.lean)** begins the self-adjointness stage by characterizing **exactly which input-output pairs satisfy the adjoint pairing identity** for the densely defined operator on its natural domain `D(V)`.

For a real Hilbert-space operator `A`, a pair of square-summable states `(η,χ)` is an *adjoint pair* when

```math
\langle A\varphi,\eta\rangle=\langle\varphi,\chi\rangle
\quad\text{for every }\varphi\in D(V).
```

The module first shows that, for onsite multiplication `M_V` by an arbitrary real potential (even if unbounded), this identity holds **if and only if** `η∈D(V)` and `χ=M_Vη`. The key proof tests the identity on states concentrated on a single tile, forcing the coordinatewise equation `χ(t)=V(t)η(t)`. Because `χ∈ℓ²`, this also forces `η` into the natural onsite domain. The reverse implication uses the previously proved symmetry of onsite multiplication.

For the **complete infinite local matching operator**

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI
```

the analogous characterization is established assuming **involutive matching permutations** and **a symmetric bounded perturbation `P`**. Under these conditions its bounded correction `B=L_w+εP+mI` is symmetric, so an adjoint-pair identity for `H` reduces to one for `M_V` with output `χ-Bη`. The result is

```math
\bigl[\ \langle H\varphi,\eta\rangle
=\langle\varphi,\chi\rangle\ \ \forall\varphi\in D(V)\ \bigr]
\iff
\bigl[\ \eta\in D(V),\ \chi=H\eta\ \bigr].
```

Combined with the independently formalized **density of `D(V)`** (§4.2) and **closedness** (§4.14), this is a mathematically explicit **adjoint-domain equality**, the defining substance of self-adjointness for these real densely defined operators. Unlike symmetry alone, it excludes additional adjoint-domain states.

**Technical scope:** the proof states the full adjoint-pair characterization directly rather than packaging it as a Mathlib `UnboundedLinearOperator`/`IsSelfAdjoint` API instance. This does **not** establish compact resolvent, discrete spectrum, eigenvalue existence, inverse-square summability, or a particular tiling graph. The conclusion for the full operator requires the symmetry hypotheses on the matching permutations and `P`; it is not asserted for arbitrary nonsymmetric perturbations.

### 4.16. Solving a real shifted onsite resolvent equation

The Lean module **[`SpectralGeometry/InfiniteOnsiteResolvent.lean`](SpectralGeometry/InfiniteOnsiteResolvent.lean)** starts the constructive resolvent program. §4.15 established an explicit adjoint-pair characterization for the onsite and symmetric interacting operators; here we obtain **existence and uniqueness** of solutions to a shifted onsite operator equation, rather than only spectral inequalities or adjoint information.

Take an arbitrary real onsite potential `V:T→ℝ`, which may be unbounded above, and a real parameter `a` such that **every onsite energy is at least one unit above** `a`:

```math
V(t)-a\ge 1\qquad\text{for all tiles }t.
```

For **every** input `f∈ℓ²(T)`, Lean proves there exists exactly one `ψ∈D(V)` solving

```math
(M_V-aI)\psi=f,\qquad
\psi(t)=\frac{f(t)}{V(t)-a}.
```

The proof shows that the coordinatewise inverse gives a square-summable state because `|(V(t)-a)^{-1}|≤1`. It then checks that `Vψ=f+aψ` is square-summable, so the solution lies in the **natural unbounded onsite domain**. A separate injectivity argument proves that distinct domain states cannot have the same image, giving bijectivity.

**What this establishes:** the shifted **onsite** operator `M_V-aI : D(V)→ℓ²(T)` is a bijection under the explicit unit-gap assumption, with a concrete coordinate formula for its inverse. This is a genuine solvability statement, stronger than merely excluding real point eigenvalues.

**Relation to subsequent results:** this module establishes bijectivity and the coordinate formula, but does not itself package the inverse as a continuous linear map. That construction and the compactness proof under a finite-sublevel hypothesis are established in §4.18. Bijectivity of the **interacting** operator's shift, compactness of its resolvent, discreteness and inverse-square summability of its full spectrum, and any specialized aperiodic-tiling model remain open formalization goals. The one-unit condition is a convenient sufficient hypothesis, not a necessary one.

### 4.17. Finite low-energy sectors under a proper onsite potential

The Lean module **[`SpectralGeometry/InfiniteOnsiteFiniteLowEnergy.lean`](SpectralGeometry/InfiniteOnsiteFiniteLowEnergy.lean)** makes explicit an important growth hypothesis for the *diagonal onsite operator* `M_V`: for any fixed energy threshold `R`, there are only finitely many tiles with `V(t)≤R`.

Lean proves two consequences on the natural onsite domain: any genuine point eigenvector with real eigenvalue `λ≤R` can be nonzero only on those finitely many low-energy tiles, and only finitely many **distinct onsite point eigenvalues** can lie at or below `R`. These follow from the previously proved coordinate identity `λ=V(t)` whenever an eigenvector is nonzero at tile `t`.

The hypothesis of finite low-energy sublevel sets is a precise form of *onsite potential growth at infinity*. It is additional to previous results and is **not claimed for an arbitrary potential or automatically for a particular geometric tiling**.

**Important scope:** these results concern `M_V`, **not the fully interacting operator** `H=M_V+L_w+εP+mI`. On their own they do not prove compact resolvent, spectral discreteness, inverse-square summability, or eigenvalue existence for an arbitrary potential. The finite-rank approximation and compact onsite resolvent are proved in §4.18 under the additional unit-gap assumption. Establishing a compact resolvent and the required spectral growth for the interacting and perturbed operator remains a separate goal.

### 4.18. Compact resolvent of a proper onsite potential

The Lean module **[`SpectralGeometry/InfiniteOnsiteCompactResolvent.lean`](SpectralGeometry/InfiniteOnsiteCompactResolvent.lean)** packages the inverse of the shifted diagonal onsite operator as a continuous linear map on real `ℓ²(T)`. It then uses the finite-low-energy property of §4.17 to prove compactness.

Fix a real shift `a` and assume both the **uniform gap** `V(t)-a≥1` for every tile and **properness of the onsite potential**: every sublevel set `{t | V(t)≤R}` is finite. The inverse furnished by §4.16 acts coordinatewise as

```math
(R_a f)(t)=\frac{f(t)}{V(t)-a}.
```

For each natural number `n`, truncate to the finite set `S_n={t | V(t)≤a+n+1}`. The corresponding operator `R_{a,n}` has finite rank and is compact, while the discarded coefficients satisfy the explicit operator-norm estimate

```math
\|R_a-R_{a,n}\|\le \frac{1}{n+1}.
```

The finite truncations thus converge to `R_a` in operator norm. Since compact operators are closed under operator-norm limits, **`R_a` is compact**.

**Scope:** this is a compact-resolvent theorem only for diagonal onsite multiplication under an additional, explicitly assumed growth condition. It does not prove compactness of the full interacting and perturbed operator, any property of an actual aperiodic tiling, or inverse-square summability of the resulting eigenvalues. Compact resolvent by itself is insufficient to guarantee the summability required for the canonical product.

### 4.19. The bounded onsite resolvent is the shifted inverse on its natural domain

The Lean module **[`SpectralGeometry/InfiniteOnsiteResolventIdentity.lean`](SpectralGeometry/InfiniteOnsiteResolventIdentity.lean)** connects the bounded continuous resolvent constructed in §4.18 to the unbounded onsite multiplication operator of §4.1 and the bijectivity theorem of §4.16.

Under the unit-gap hypothesis `1≤V(t)-a`, let `R_a` be the coordinatewise bounded operator from §4.18. Lean proves that **for every** `f∈ℓ²(T)` the state `R_a f` belongs to the natural domain `D(V)` and satisfies

```math
R_a f\in D(V),\qquad (M_V-aI)(R_a f)=f.
```

Conversely, **for every** `ψ∈D(V)`, Lean proves the other inverse identity:

```math
R_a\bigl((M_V-aI)\psi\bigr)=\psi.
```

Thus the bounded continuous map is explicitly shown to be the **two-sided inverse of the shifted onsite operator on its actual natural domain**, rather than merely a map with the expected coordinate formula. Combined with §4.18, proper onsite potential growth makes this genuine inverse compact.

**Scope:** this closes the onsite inverse-identification milestone P0 from §6 without introducing any new potential-growth hypothesis. It does **not** prove that the full interacting operator `H=M_V+L_w+εP+mI` is invertible or has compact resolvent; that remains P1.

### 4.20. Compact resolvent under small bounded interactions and perturbations

The Lean module **[`SpectralGeometry/InfiniteLocalCompactResolvent.lean`](SpectralGeometry/InfiniteLocalCompactResolvent.lean)** transfers the compact onsite resolvent of §§4.18–4.19 to an operator with a bounded correction. Let `B:ℓ²(T)→ℓ²(T)` be a continuous linear map and let

```math
H=M_V+B\quad\text{on }D(V),\qquad
R_a=(M_V-aI)^{-1}.
```

Assume the unit gap `V(t)-a≥1`, finite onsite sublevel sets as in §4.18, and the quantitative **smallness condition** `‖B R_a‖<1`. Neumann-series invertibility of `I+B R_a` provides

```math
(H-aI)^{-1}=R_a(I+B R_a)^{-1}.
```

The module constructs this expression as a continuous linear map, shows that its outputs belong to `D(V)`, proves both inverse identities for the **full** shifted operator, and proves its compactness by composition with the compact onsite resolvent.

The result applies to any bounded correction satisfying the stated condition, in particular to the finite-color matching-family interaction with a bounded controlled perturbation encoded by `B=L_w+εP+mI`. It does **not** claim that `‖B R_a‖<1` holds automatically for arbitrary coupling strengths or at an arbitrary spectral shift. No spectral discreteness or inverse-square eigenvalue summability follows merely from this result; those remain separate goals.

### 4.21. Quantitative compact-resolvent bounds and sufficiently negative shifts

The Lean module **[`SpectralGeometry/InfiniteLocalCompactResolventBounds.lean`](SpectralGeometry/InfiniteLocalCompactResolventBounds.lean)** strengthens the conditional compact-inverse theorem of §4.20. If a positive gap `δ` satisfies `V(t)-a≥δ>0` and the earlier unit-gap condition holds, it establishes the **operator norm estimate**

```math
\|R_a\|\le\delta^{-1}.
```

For any bounded correction `B` with `‖B‖<δ`, the product estimate implies `‖B R_a‖<1`; consequently, the inverse of `M_V+B-aI` exists on the natural onsite domain and is compact under the same finite-sublevel hypothesis as §4.18.

**No global smallness assumption is needed to find one resolvent point.** If `V(t)≥v₀` for all tiles, then choosing `δ=‖B‖+1` and `a=v₀-δ` supplies a real shift with compact inverse for *any fixed bounded B*. This proves existence of **some sufficiently negative real resolvent point**, not invertibility at all spectral parameters.

For the finite-color matching-family model from §4.9, with `D` matching colors and weights `0≤wᵢ≤W`, the formalized geometric bound is

```math
\|L_w+\varepsilon P+mI\|
 \le 2DW+|\varepsilon|\,\|P\|+|m|.
```

Thus `V(t)-a≥δ≥1` and `δ>2DW+|ε|‖P‖+|m|` suffice for the compact shifted inverse of the actual local matching operator via its already-proved bounded-correction identity. Neither symmetry of `P` nor a fixed small coupling is required for this existence result. Self-adjoint spectral decomposition, discrete eigenvalues, and inverse-square summability remain separate P1/P2 milestones.

### 4.22. Self-adjoint onsite and infinite local operators in Mathlib's partial-operator API

The Lean module **[`SpectralGeometry/InfiniteLocalSelfAdjointPMap.lean`](SpectralGeometry/InfiniteLocalSelfAdjointPMap.lean)** bridges the explicit natural-domain operators and adjoint-pair characterizations of §§4.14–4.15 to Mathlib's **`LinearPMap`** type for partially defined (potentially unbounded) linear operators.

The module first packages onsite multiplication `M_V` as a `LinearPMap` with domain `D(V)`. It then combines density of `D(V)` with the previously proved adjoint-pair equivalence to establish

```math
M_V^*=M_V
```

in the precise sense of Mathlib's `IsSelfAdjoint` predicate for `LinearPMap`. Thus the conclusion is no longer solely an explicit characterization of possible adjoint pairs.

For the complete infinite local matching operator

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI
\quad\text{on }D(V),
```

the same argument proves `IsSelfAdjoint` for its `LinearPMap` representation when each matching permutation is involutive and the bounded perturbation `P` is symmetric. A reusable graph-and-pairing lemma identifies the adjoint graph with the original graph, using Mathlib's `LinearPMap.adjoint_graph_eq_graph_adjoint`. **The actual domain remains `D(V)`; it is not silently replaced by all of `ℓ²(T)`.**

**Scope:** this establishes the operator-theoretic interface needed before applying later spectral results. It requires the stated symmetry assumptions for the full local operator and makes no claim about compactness without the properness/gap hypotheses of §§4.20–4.21. Discrete eigenvalue enumeration, finite multiplicities, eigenvalue growth, and inverse-square summability remain future P2 goals.

### 4.23. Compact self-adjoint resolvents and their eigenspaces

The Lean module **[`SpectralGeometry/InfiniteLocalResolventSpectrum.lean`](SpectralGeometry/InfiniteLocalResolventSpectrum.lean)** begins the P2 spectral stage by applying Mathlib's compact self-adjoint spectral results to the **bounded resolvent** of the interacting operator. Let `H=M_V+B` on the natural domain `D(V)`; assume the shifted inverse `R_a=(H-aI)⁻¹` is constructed as in §§4.20–4.21, and that the bounded correction `B` is symmetric.

The new module proves that `R_a` is self-adjoint as a continuous linear map, using the two inverse identities from §4.20 and symmetry on `D(V)`. Under the finite-sublevel hypothesis on `V`, `R_a` is also compact. Mathlib's compact-operator results then imply:

- **Finite eigenspace dimension:** for every nonzero real eigenvalue `μ` of `R_a`, its eigenspace is finite-dimensional.
- **Spectral totality:** the orthogonal complement of the supremum of all eigenspaces of `R_a` is zero. Equivalently, their linear span is dense in the real Hilbert space.
- **Local matching specialization:** if each matching permutation is involutive and the bounded perturbation `P` is symmetric, the corrected geometric resolvent is self-adjoint whenever the explicit Neumann condition is satisfied. The gap bounds of §4.21 provide sufficient conditions for its existence.

**Important distinction:** these are formalized properties of the **compact bounded resolvent**. Section 4.24 separately transfers nonzero resolvent eigenpairs to eigenpairs of the unbounded operator `H` via `λ=a+μ⁻¹`. Spectral enumeration, isolation properties, and quantitative growth remain open. No inverse-square eigenvalue summability is established here.

### 4.24. Eigenpair correspondence between the compact resolvent and the full operator

The Lean module **[`SpectralGeometry/InfiniteLocalEigenpairCorrespondence.lean`](SpectralGeometry/InfiniteLocalEigenpairCorrespondence.lean)** connects the spectral statements about the **bounded** resolvent in §4.23 to genuine eigenvectors of the **unbounded** geometric operator on its natural domain. Let `R_a=(M_V+B-aI)⁻¹` denote the two-sided inverse constructed in §4.20, with its original norm-smallness and unit-gap hypotheses. For each **nonzero** real `μ` and state `f∈ℓ²(T)`, Lean proves the equivalence

```math
R_a f=\mu f\quad\Longleftrightarrow\quad
\exists\,\psi\in D(V):\ \psi=f,\quad
(M_V+B-aI)\psi=\mu^{-1}f.
```

In the forward direction, the domain witness is constructed explicitly from the resolvent applied to `μ⁻¹ f`. Consequently, every resolvent eigenvector with nonzero eigenvalue belongs to the natural domain. Conversely, the already formalized left-inverse identity recovers the bounded-resolvent eigenvector equation.

For the complete finite-color matching operator `H=M_V+L_w+εP+mI`, the corresponding Lean theorem gives

```math
R_a f=\mu f\quad\Longleftrightarrow\quad
\exists\,\psi\in D(V):\ \psi=f,\quad
H\psi=(a+\mu^{-1})f.
```

An additional formulation starts with an arbitrary real `λ≠a` and uses `μ=(λ-a)⁻¹`. For nonzero `f`, these are genuine eigenpairs. The correspondence itself is algebraic and does **not** require the bounded correction to be symmetric; the compact self-adjoint spectral conclusions of §4.23 still require their own properness and symmetry hypotheses.

**Scope:** the eigenpair correspondence at a fixed resolvent shift is now formalized. Discreteness and isolation of the **full** spectrum, an eigenvalue enumeration with multiplicities, eigenvalue growth, and inverse-square summability are separate P2 targets not established by this module.

### 4.25. Finite multiplicity and orthogonality of full local eigenvectors

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenspaces.lean`](SpectralGeometry/InfiniteLocalFullEigenspaces.lean)** transfers the finite-dimensional eigenspace result of §4.23 from the compact bounded resolvent to the **unbounded full local operator**, using the eigenpair correspondence of §4.24. For a spectral parameter `a` where the inverse exists, each real eigenvalue `λ≠a` has a well-defined full eigenspace, realized by the resolvent eigenspace at `(λ-a)⁻¹`.

The module identifies membership in this submodule with the actual domain-restricted eigenvalue equation for `H=M_V+L_w+εP+mI` on `D(V)`. Assuming finite sublevel sets for the onsite potential and the existing resolvent smallness condition, it proves that **each such full eigenspace is finite-dimensional**. It also shows that `a` itself cannot be an eigenvalue, because the full shifted operator has a two-sided inverse. Thus the finite-multiplicity statement covers all real eigenvalues of `H`.

Under involutive matching permutations and symmetry of the bounded perturbation `P`, eigenvectors corresponding to **different real eigenvalues are orthogonal**. This orthogonality theorem is an operator-symmetry consequence and does not need the extra compactness hypotheses.

**Still open:** finite-dimensional eigenspaces and orthogonality do not alone imply that every spectral point is an eigenvalue, that each eigenvalue is isolated, or that the eigenvalues admit an enumeration with no finite accumulation. These spectral exhaustion and isolation claims remain P2 goals and are not asserted in §4.25.

## 5. Building and verification

The established analytic core is in `SpectralGeometry/CanonicalProduct.lean`. The finite-dimensional geometric results are in `SpectralGeometry/FinitePerturbation.lean`, `SpectralGeometry/FinitePositiveEnergy.lean`, `SpectralGeometry/FiniteGeometricEnergy.lean`, and `SpectralGeometry/FiniteStrictPositivity.lean`. These four finite-dimensional modules and the twenty-six infinite-dimensional modules `SpectralGeometry/InfiniteOnsite.lean`, `SpectralGeometry/InfiniteOnsiteDensity.lean`, `SpectralGeometry/InfiniteOnsiteEigenvalues.lean`, `SpectralGeometry/InfiniteOnsiteSummability.lean`, `SpectralGeometry/InfiniteOnsitePowerGrowth.lean`, `SpectralGeometry/InfiniteFiniteEdgeInteraction.lean`, `SpectralGeometry/InfiniteBoundedPerturbation.lean`, `SpectralGeometry/InfiniteSummableEdgeInteraction.lean`, `SpectralGeometry/InfiniteLocalMatching.lean`, `SpectralGeometry/InfiniteLocalBoundedDegree.lean`, `SpectralGeometry/InfiniteLocalEigenvalueBounds.lean`, `SpectralGeometry/InfiniteLocalSignedPerturbationGap.lean`, `SpectralGeometry/InfiniteLocalCoerciveGap.lean`, `SpectralGeometry/InfiniteLocalGraphNorm.lean`, `SpectralGeometry/InfiniteLocalClosedGraph.lean`, `SpectralGeometry/InfiniteLocalAdjointCharacterization.lean`, `SpectralGeometry/InfiniteOnsiteResolvent.lean`, `SpectralGeometry/InfiniteOnsiteFiniteLowEnergy.lean` and `SpectralGeometry/InfiniteOnsiteCompactResolvent.lean` and `SpectralGeometry/InfiniteOnsiteResolventIdentity.lean` `SpectralGeometry/InfiniteLocalCompactResolvent.lean` and `SpectralGeometry/InfiniteLocalCompactResolventBounds.lean` and `SpectralGeometry/InfiniteLocalSelfAdjointPMap.lean` and `SpectralGeometry/InfiniteLocalResolventSpectrum.lean` and `SpectralGeometry/InfiniteLocalEigenpairCorrespondence.lean` and `SpectralGeometry/InfiniteLocalFullEigenspaces.lean` are imported by the `SpectralGeometry.lean` entry point. The toolchain is Lean 4 `v4.35.0` with the corresponding version of Mathlib.

```bash
lake update
lake exe cache get
lake build
```

GitHub Actions automatically checks compilation on every change to `main` and on every pull request.

## 6. Roadmap: next formally checked theorems

This section records the **remaining formalization milestones** and marks
completed work explicitly. Priorities follow mathematical dependencies:
first connect the onsite compact map to the genuine inverse (P0, now complete),
then transfer compactness to the interacting operator, and only then build a
spectral sequence for the canonical product. Each milestone counts as
completed only after the corresponding Lean file is imported by
`SpectralGeometry.lean` and the full `lake build` passes.

| Priority | Milestone | Mathematical target | Status |
| --- | --- | --- | --- |
| **P0 — completed** | Onsite inverse identity | The bounded map `infiniteOnsiteResolventCLM` takes values in the natural domain and is a two-sided inverse of the shifted onsite operator (§4.19) | **Formalized and Lean-checked** |
| **P1 — critical (initial case formalized)** | Compact resolvent for the full local operator | Compact inverse of `M_V+B-aI` for bounded `B` under `‖B R_a‖<1`, with both inverse identities (§4.20) | **Small-correction theorem formalized; quantitative/structural extensions pending** |
| **P1 — quantitative (formalized)** | Quantitative compact resolvent bounds | Bounds `‖R_a‖≤1/δ`, obtains compact inverse from `‖B‖<δ`, proves existence of a sufficiently negative real shift for any bounded `B`, and gives geometric bounds for matching families (§4.21) | **Formalized; next P1 milestone is spectral-theory integration** |
| **P1 — infrastructure (formalized)** | Self-adjointness in Mathlib's partial-operator API | Package onsite and local matching operators as `LinearPMap` on the natural domain, and prove `IsSelfAdjoint` from adjoint-pair characterization and density (§4.22) | **Formalized; spectral discreteness remains P2** |
| **P2 — in progress (finite multiplicity)** | Discrete spectrum | Compact resolvent eigenspaces are total (§4.23), eigenpairs transfer to the full unbounded operator (§4.24), and every full real eigenspace is finite-dimensional with orthogonality for distinct symmetric eigenvalues (§4.25) | **Finite multiplicity/orthogonality formalized; spectral isolation, exhaustion and enumeration pending** |
| **P2 — high** | Eigenvalue growth and summability | Transfer quantitative onsite growth to the eigenvalues of the interacting operator, then prove summability of inverse squares under sufficiently strong growth | Planned |
| **P3 — integration** | Spectrally defined canonical product | Instantiate the existing admissibility and zero-localization results with the full operator's positive, summable eigenvalues | Planned |
| **P4 — geometric applications** | Specific aperiodic tiling | Check the operator hypotheses for a concrete tiling model rather than assuming them abstractly | Planned |

### 6.1. P0 — Completed: identify the bounded onsite map with the actual inverse

Use the natural onsite domain `D(V)` and the unit-gap assumption
`1 ≤ V(t)-a` from §§4.16 and 4.18. Let `R_a` be the already constructed
continuous linear map, acting coordinatewise by
`(R_a f)(t)=(V(t)-a)⁻¹ f(t)`. Prove explicitly that

```math
R_a f\in D(V),\qquad (M_V-aI)R_a f=f
\quad\text{for every }f\in\ell^2(T),
```

and, for each `ψ∈D(V)`, that

```math
R_a\bigl((M_V-aI)\psi\bigr)=\psi.
```

The pointwise formula, bijectivity, and compactness were previously available;
**the two inverse identities and domain membership are now formalized** in
`SpectralGeometry/InfiniteOnsiteResolventIdentity.lean`, which imports the
existing compact-resolvent module. No new growth hypothesis is needed.
The next unfinished milestone is **P1**, transferring compactness to the
complete operator with bounded geometric interactions and perturbations.

### 6.2. P1 — Compact resolvent of the interacting operator (small-correction case checked)

Write `H=M_V+B` on `D(V)`, where the interaction and perturbation
correction `B=L_w+εP+mI` is bounded. Establish a sufficiently strong
onsite gap `V(t)-a≥δ>0` and the quantitative estimate
`‖R_a‖≤1/δ`. If `‖B R_a‖<1`, a Neumann-series argument should yield

```math
(H-aI)^{-1}=R_a\,(I+B R_a)^{-1}.
```

**The first small-correction case is now proved** in §4.20: the inverse maps to the natural domain, both inverse identities hold, and the bounded resolvent is compact. The hypothesis is explicitly `‖B R_a‖<1`; the next extension is to derive convenient numeric bounds directly from `‖B‖` and onsite gaps, and to package the substitution `B=L_w+εP+mI` into a dedicated local-matching theorem. No conclusion is asserted for arbitrary unbounded interactions.

**Quantitative milestone (P1, §4.21):** The formalized theorem establishes a general norm estimate
`‖R_a‖≤1/δ` when `V(t)-a≥δ≥1`. Since
`‖B R_a‖≤‖B‖‖R_a‖`, the explicit sufficient condition `‖B‖<δ`
then gives the compact inverse constructed in §4.20. If `V(t)≥v₀`
for all tiles, choose `δ=‖B‖+1` and `a=v₀-δ` to find a real
spectral shift with compact inverse for **every fixed bounded B**,
without assuming B itself is small. This says *some* sufficiently
negative shift works; it makes no claim about resolvents at all
spectral parameters.

**Geometric specialization:** instantiate `B=L_w+εP+mI` with
the already formalized matching-family norm estimate
`‖L_w‖≤2DW` (for nonnegative matching weights bounded by `W`).
The sufficient explicit gap is
`δ>2DW+|ε|‖P‖+|m|`. The new module formalizes the bound, the existence of a sufficiently
negative shift, and the named local-matching corollary. The next
independent P1 milestone is to package the adjoint-domain criterion
for Mathlib's spectral theorem interfaces.

**Self-adjointness integration (P1, §4.22):** The onsite and symmetric local matching operators are now represented by Mathlib's `LinearPMap` with their unchanged natural domain. The earlier adjoint-pair equivalences give genuine `IsSelfAdjoint` theorems in this API. This satisfies the operator-interface milestone; the next priority is the **P2 spectral stage** (discreteness, finite multiplicities, and growth) under appropriate compact-resolvent and symmetry hypotheses.

### 6.3. P2 — Discreteness, multiplicity, and quantitative growth

**First P2 step (§4.23):** The compact bounded resolvent of the symmetric local operator has been shown to be self-adjoint. Its nonzero eigenspaces are finite-dimensional and the supremum of all its eigenspaces is dense, using Mathlib's compact self-adjoint spectral theorem. **Second P2 step (§4.24):** the nonzero resolvent eigenpair equation is now equivalent to the eigenpair equation for the unbounded local operator on its natural domain, with eigenvalue `λ=a+μ⁻¹`. **Third P2 step (§4.25):** the full unbounded operator's eigenspaces are now finite-dimensional, the chosen resolvent shift is not an eigenvalue, and symmetric local eigenvectors at distinct eigenvalues are orthogonal. The next task remains spectral exhaustion, isolation and enumeration with multiplicity. These do not follow from finite multiplicity alone. A lower spectral bound and exclusion of zero are necessary for inverse powers.

Next, prove an eigenvalue comparison under bounded symmetric
perturbations, of the form
`λₙ(M_V+B) ≥ λₙ(M_V)-‖B‖`, using an appropriately ordered
eigenvalue enumeration and suitable multiplicity conventions. The
power-law onsite assumptions of §4.5 are intended inputs; the
inverse-square summability of the **full** operator's eigenvalues is a
separate theorem, not a consequence of compact resolvent alone.

### 6.4. P3–P4 — Analytic integration and concrete geometry

With positive eigenvalues `λₙ` of the full operator and a checked
summability hypothesis `∑ₙ λₙ⁻²<∞`, instantiate the existing
`Admissible` and canonical-product theorems from §2. A smaller,
independent end-to-end onsite example may be formalized earlier as an
integration test, but must not be represented as a theorem about the
interacting system.

Only after the abstract spectral chain is complete should a specific
Penrose, Ammann–Beenker, Pinwheel, Spectre, or other aperiodic geometry
be used to **verify** the required potential growth and interaction
hypotheses. No link to the Riemann zeta function is asserted or implied.
