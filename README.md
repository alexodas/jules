# Jules Spectral Geometry

**An experimental mathematical research program in Lean 4 and Mathlib.**

## 1. General aim: from tile geometry to the zeros of an analytic function

We want to investigate how a tiling, including an **aperiodic** one with no natural arrangement into rows and columns, can determine a spectrum through a geometric operator. We distinguish what we **choose when defining the model** from what **emerges as an eigenvalue**.

To each tile `t`, we assign an individual energy `V(t)`, which may depend on an arbitrary number of properties: centroid, area, shape, orientation, chirality where applicable, substitution hierarchy, and other geometric features. To each pair of tiles, we assign an interaction weight `w(t,u)`, even when they are not adjacent. For symmetric, nonnegative interactions, our starting model will be:

```math
(H\psi)(t)=\underbrace{V(t)\psi(t)}_{\text{individual energy}}+\underbrace{\sum_{u\ne t}w(t,u)(\psi(t)-\psi(u))}_{\text{interactions}}.
```

Here, **`ψ` is a function that assigns an amplitude `ψ(t)` to each individual tile `t`**. It describes a configuration of the entire tiling, rather than an intrinsic geometric property of a tile. The interaction term compares its values on two tiles, `ψ(t)` and `ψ(u)`; the pair-dependent quantity is the weight `w(t,u)`. We do not prescribe `ψ` as a formula in the tile's geometric features: those features determine `V` and `w`, which in turn determine the operator `H`.

An **eigenfunction** `ψₙ` is a nonzero configuration satisfying `Hψₙ = λₙψₙ`; the corresponding number `λₙ` is its **eigenvalue**. For an infinite tiling, configurations must belong to an appropriate function space (typically square-summable functions), and eigenfunctions must lie in the domain of `H`. These analytic requirements are part of the theory we intend to develop.

Our goal is first to prove very general properties of these operators; we will then study particular tilings, such as Penrose, Ammann–Beenker, Pinwheel, and Spectre. **We will not choose the eigenvalues directly**: we aim to derive them from the full operator. The individual energies and the interaction law are inputs to the model, not preassigned eigenvalues.

On a finite patch of `N` tiles, a real symmetric operator has `N` real eigenvalues, counted with multiplicity. For infinitely many tiles, however, the spectrum may also have continuous parts. We will investigate suitable conditions, such as self-adjointness, positivity, and compact resolvent, that allow us to enumerate the eigenvalues:

```math
0<\lambda_0\le\lambda_1\le\lambda_2\le\cdots,\qquad \lambda_n\longrightarrow+\infty.
```

### The established analytic result

We already have the **definition and Lean formalization** of the canonical function

```math
D_q(s)=\prod_{n=0}^{\infty}\left(1-\frac{(s-c)^2}{d^2q_n^2}\right),\qquad d\ne0.
```

The definition, convergence criterion, and theorems on the localization of zeros are in **[`SpectralGeometry/CanonicalProduct.lean`](SpectralGeometry/CanonicalProduct.lean)**. In particular, if `q_n>0` and

```math
\sum_{n=0}^{\infty}\frac1{q_n^2}<\infty,
```

the formalized theorems establish the appropriate convergence of the product, that **all its zeros lie on the prescribed line** `s=c+dt` with real `t`, and that each level `q_n` gives rise to zeros at `s=c\pm d q_n`.

The new challenge is to obtain these levels as **eigenvalues of the infinite geometric operator**:

```math
H\psi_n=\lambda_n\psi_n,\qquad q_n=\lambda_n.
```

We will need to prove that the chosen operator has an enumerable, positive, discrete spectrum and, in addition, that

```math
\sum_{n=0}^{\infty}\frac1{\lambda_n^2}<\infty.
```

Only then will we be able to rigorously define `D_H(s)=D_{\lambda}(s)`. For `c=1/2` and `d=i`, we will obtain zeros at

```math
s=\frac12\pm i\lambda_n.
```

**The line is imposed by the construction of the product, not derived from any property of the Riemann zeta function.** We have not yet formalized the infinite operator or its spectral connection to the product; these will be the subject of future results. This project does not prove the Riemann hypothesis and does not identify `D_q` with the zeta function.

### Building and verification

The analytic core is defined in `SpectralGeometry/CanonicalProduct.lean`; `SpectralGeometry.lean` is its entry point. The toolchain is Lean 4 `v4.35.0` with the corresponding version of Mathlib.

```bash
lake update
lake exe cache get
lake build
```

GitHub Actions automatically checks compilation on every change to `main` and on every pull request.
