# Jules Spectral Geometry

**An experimental mathematical research program in Lean 4 and Mathlib.**

## 1. General aim: from tile geometry to the zeros of an analytic function

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

### The established analytic result

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

## 2. First finite-dimensional theorem: symmetry survives perturbation

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

## 3. Second finite-dimensional theorem: positivity under controlled perturbations

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

**What this does *not* yet prove:** positivity of `H_0=V+L_w` directly from hypotheses such as `V(t)\ge0` and symmetric nonnegative `w(t,u)`. The theorem establishes *stability* of positivity **assuming** positivity of the original energy and the perturbation energy. Proving sufficient geometric conditions for that premise is a separate next step. We have not yet established the infinite-tiling spectral properties or formally proved eigenvalue positivity.

## 4. Building and verification

The established analytic core is in `SpectralGeometry/CanonicalProduct.lean`. The geometric finite-dimensional results are in `SpectralGeometry/FinitePerturbation.lean` and `SpectralGeometry/FinitePositiveEnergy.lean`. All three are imported by the `SpectralGeometry.lean` entry point. The toolchain is Lean 4 `v4.35.0` with the corresponding version of Mathlib.

```bash
lake update
lake exe cache get
lake build
```

GitHub Actions automatically checks compilation on every change to `main` and on every pull request.
