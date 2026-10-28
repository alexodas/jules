# Jules Spectral Geometry

**A mathematical research program in Lean 4 and Mathlib connecting local
geometric operators, finite-coordinate observation, and the response of zeros
on a prescribed complex line.**

## Current status

The first substantive milestone selected for independent statement verification
is a **finite-coordinate observability theorem for a complete low-energy
eigenspace** of an infinite interacting operator. It identifies a finite set of
sites whose coordinates distinguish every vector in that eigenspace and bounds
its geometric multiplicity. The theorem is proved in the source library and is
the single mathematical result selected by the root Comparator configuration.

| Part of the program | Status |
| --- | --- |
| Natural-domain operators, bounded matching interactions, conditional self-adjointness and compact resolvents | Formalized under the explicit hypotheses documented in §4 |
| Real spectral completeness, exact geometric multiplicities, ordered infinite enumeration and qualitative divergence | Formalized under the additional hypotheses of §§4.23–4.38 |
| Finite-coordinate detection and the multiplicity bound for one low-energy eigenspace | Formalized in §4.40; selected for independent statement verification |
| Simultaneous quantitative observation and total low-energy multiplicity counting | Formalized in §§4.41–4.43, with symmetry for simultaneous spectral control |
| Variational characterization, ordered onsite comparison and finite-sector eigenvalue response | Formalized in §§4.44–4.47 with complete eigenbases, exact multiplicities and explicit infinite-indexing conditions |
| Positive full-spectrum inverse-square summability and its preservation under nonnegative finite-sector interventions | Formalized under the sufficient growth, ordering and gap hypotheses of §4.48 |
| Canonical products for admissible positive levels, now including full spectra under §4.48 | Admissibility and the existing convergence/localization results are available; entire holomorphy and exact zero orders remain open in §6.3 |
| A concrete Ammann–Beenker model, relative-product identities and certified finite-patch zero response | Proposed research milestones in §§6.4–6.6 |

The research objective is an end-to-end statement relating an explicitly defined
local geometric modification to a quantitatively controlled change in a
spectral product and its zeros. The current observation theorem supplies a
finite observation sector for this program. The subsequent abstract spectral
response is now proved separately. A concrete geometric application, certified
approximation and statistical results remain open. The Comparator selection
still contains only the original single-eigenspace theorem.

The chosen affine line is part of the definition of the analytic family.
Originality and research significance must come from the geometric and spectral
information established about that family, rather than from choosing the line.
No identification with the Riemann zeta function or proof of the Riemann
hypothesis is claimed.

## 1. Research program and geometric model

### 1.1. The research question

How can a local change in an infinite geometric system be detected in an
analytic function whose zeros record its spectrum? Which finite sets of sites
observe low-energy modes, how do perturbations on those sites move the
corresponding levels, and with what error can finite patches certify that
response?

The program studies these questions for an operator with a confining onsite
potential, bounded local interactions and controlled perturbations. It then
transports the spectral information to a normalized canonical product on a
fixed complex line. A concrete aperiodic model is needed to turn abstract
bounds into an application with independently verified geometric hypotheses.

The intended audience includes discrete Schrödinger and graph-operator
spectral theory, rigorous spectral approximation, entire functions associated
with spectra, and formal methods in infinite-dimensional analysis. A useful
application must identify an actual geometric construction and an informative
estimate, not only a list of possible audiences.

### 1.2. First substantive milestone: finite-coordinate observation

Let
```math
H=M_V+B,\qquad
D(V)=\{\psi\in\ell^2(T):V\psi\in\ell^2(T)\},
\qquad
F_R=\{t\in T:V(t)\le R\}.
```

Here the real Hilbert space of sites may be infinite, the potential may be
unbounded, and the full correction $B$ is bounded. Under the precise
properness and resolvent hypotheses in §4.40, the proved theorem gives
```math
\lambda<R-\|B\|,\qquad \lambda\ne a
\quad\Longrightarrow\quad
\dim E_\lambda(H)\le \#F_R.
```

Its central construction is an injective linear restriction map
```math
E_\lambda(H)\longrightarrow\mathbb R^{F_R},
\qquad \psi\longmapsto\psi|_{F_R}.
```

Thus two vectors in the same fixed-eigenvalue eigenspace that agree on $F_R$
agree everywhere. The result observes the entire eigenspace, not merely one
chosen eigenvector. It concerns geometric multiplicity and does not require
the bounded correction to be symmetric.

The compared Lean declaration is
[SpectralGeometry.infiniteLocalMatching_full_eigenspace_finrank_le_lowEnergyTiles](SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean).
It assumes finite onsite sublevel sets, a real shift $a$ with
$V(t)-a\ge1$, the onsite resolvent $R_a^{\mathrm{on}}=(M_V-aI)^{-1}$,
the bound $\|B R_a^{\mathrm{on}}\|<1$, and the displayed restrictions on
$\lambda$. Its eigenspace is represented through the equivalent eigenspace
of the full compact shifted inverse; the source development connects that
representation to natural-domain eigenvectors.

The proof uses a quadratic-form obstruction: a vector vanishing on all sites
with $V(t)<R$ has energy at least $(R-\|B\|)\|\psi\|^2$. This is
incompatible with a nonzero eigenvector below that threshold. Applied to the
kernel of restriction, the obstruction gives injectivity and the dimension
bound.

**Role in the research program.** The theorem identifies a finite observation
sector for each sufficiently low eigenspace. Under the additional symmetry
and lower-bound assumptions, §§4.41–4.43 now prove quantitative observation of
the whole low-energy spectral subspace and a total count with multiplicities.
The variational bridge of §§4.44–4.46 turns that form inequality into
$\kappa\tau\le\lambda_n(H+\tau P_{F_R})-\lambda_n(H)\le\tau$
for the levels and parameter interval specified in §6.2, including repeated
levels. Section 4.48 transfers onsite summability to the positive full spectrum
and preserves it along this intervention.

These are additional source theorems, not additions to the current
Comparator-selected statement. They do not provide a numerical reconstruction
algorithm or independent control of several zeros. The relative
determinant identity in §6.5 is a separate proof obligation; it does not follow
from this theorem alone.

This is the first selected substantive milestone of the program, supported by
the operator-theoretic results catalogued in §§3–4. Its position in the program
does not assert mathematical priority, a new proof technique or an independent
research-interest assessment. The proof mechanism is a standard
quadratic-form and restriction argument. [PALOMAR.md](PALOMAR.md) records the
precise current submission scope and provenance.

### 1.3. The operator and its geometric inputs

The proposed geometric family is
```math
H_\varepsilon=M_V+L_w+\varepsilon P,
```
with action, whenever the geometric interaction is defined,
```math
(H_\varepsilon\psi)(t)
=V(t)\psi(t)
+\sum_{u\ne t}w(t,u)\bigl(\psi(t)-\psi(u)\bigr)
+\varepsilon(P\psi)(t).
```

The potential $V(t)$ assigns an onsite energy. The weights describe
interactions between sites, and $P$ is a bounded controlled perturbation.
For symmetric nonnegative weights, the interaction is a graph Laplacian.
The amplitude $\psi(t)$ belongs to a state of the entire system; it is not
a prescribed eigenfunction or an intrinsic energy of an individual tile.

The Lean type named Tile is an abstract site type. In a concrete application
its elements may be tiles or vertices of a tiling; that choice must be stated.
The Ammann–Beenker application in §6.4 uses vertices. Geometric rules determine
the potential and the couplings before the spectrum is studied.

For a finite patch the construction has matrix form
```math
H_\varepsilon
=\operatorname{diag}\!\left(V_i+\sum_jw_{ij}\right)-W+\varepsilon P.
```
For infinitely many sites it acts on the natural multiplication domain
$D(V)$, with bounded corrections added on that same domain.

The formalized infinite local interaction uses finitely many matching colors:
each involutive permutation $\sigma_i$ pairs a site with at most one neighbor
of color $i$, with a constant weight for that color. Under
$0\le w_i\le W$,
```math
L_w=\sum_{i=1}^{D}w_i(I-U_{\sigma_i}),
\qquad \|L_w\|\le2DW.
```
A named tiling must be represented by such matchings, or the framework must
first be extended with a proved alternative. The existing modules do not
already establish a representation theorem for every bounded-degree graph.

### 1.4. Confinement, observation and local changes

Finite onsite sublevel sets are a genuine growth assumption. On a
finite-local-complexity tiling, a potential determined only by a finite set of
local tile types takes finitely many values and cannot by itself supply that
assumption on infinitely many sites. The concrete model must specify and
justify confinement. A position-dependent potential such as
$1+|x|^2$ is an explicit modeling choice, not a consequence of aperiodicity.

The first controlled modification will increase onsite energies on a finite
sector:
```math
H_\tau=H+\tau P_{F_R},\qquad \tau\ge0.
```
Later local changes may alter finitely many couplings or site energies.
After any necessary identification of site sets, their operator difference
must be proved to have the finite-support form
$\iota_S K\iota_S^*$. This representation is an obligation for the chosen
geometric change, not an assumption that every tiling modification has it.

The desired analytic response will compare the corresponding canonical
products with a common center, direction and normalization.

## 2. Canonical product and analytic foundations

### 2.1. Verified analytic core

For positive levels $q_n$, a center $c\in\mathbb C$ and a nonzero direction
$d\in\mathbb C$, the analytic core defines
```math
D_q(s)=\prod_{n=0}^{\infty}
\left(1-\frac{(s-c)^2}{d^2q_n^2}\right).
```

[CanonicalProduct.lean](SpectralGeometry/CanonicalProduct.lean) defines
admissibility by positivity and a summable compact-set majorant for the
deviations of these factors from one. It proves compact-uniform convergence,
zero localization on the prescribed affine line, a sufficient admissibility
criterion
```math
\sum_{n=0}^{\infty}q_n^{-2}<\infty,
```
and the existence of a zero at each positive prescribed level. The paired
factors encode symmetric locations. A formal theorem identifying all zero
orders with exact spectral multiplicities remains open.

Section 4.48 now proves positive inverse-square summability for full interacting
levels under explicit properness, onsite ordering, summability and gap
hypotheses. Its power-growth corollary reuses the onsite criterion with exponent
greater than one half. `fullSpectrum_admissible_of_positive_summable` applies the
existing admissibility criterion to these levels, including the nonnegative
finite-sector family. This supplies the analytic core's input; it does not
prove entire holomorphy or exact zero orders.

### 2.2. A common analytic coordinate for geometric operators

The spectral family to construct is
```math
F_H(z)=\prod_{n=0}^{\infty}
\left(1-\frac{z^2}{\lambda_n(H)^2}\right),
\qquad
D_H(s)=F_H\!\left(\frac{s-c}{d}\right).
```

The positive full spectrum with exact multiplicities and inverse-square
summability is now available under §§4.44–4.48. The sufficient signed-correction
criterion requires $v_0>\|B\|$ separately from onsite growth; compact resolvent
alone does not give summability or positivity. The same gap and summability
persist for nonnegative finite-sector perturbations. The target exact zero
divisor is
```math
s=c\pm d\,\lambda_n(H),\qquad D_H(c)=1,
```
with orders equal to the corresponding multiplicities. Holomorphy and these
exact orders must be proved in addition to applying the existing
zero-localization result.

Using the same $c,d$ for every operator makes zero displacement comparable
across the family. For $c=\tfrac12$ and $d=i$, the positive zero heights
are the positive eigenvalues. The affine coordinate fixes the line; it does
not create spectral correlations or encode a preferred distribution.

### 2.3. Target: a relative product for a finite geometric defect

Suppose the self-adjoint operators $H$ and
```math
H'=H+\iota_S K\iota_S^*
```
have a strictly positive spectral gap, compact resolvent and inverse-square-summable
ordered spectra. Here $S$ is finite, $\iota_S$ is coordinate insertion and
$K$ is a finite Hermitian matrix (real symmetric in the real model).

After constructing the necessary complex resolvent interface, define the
finite Green matrix and perturbation determinant
```math
G_S(z)=\iota_S^*(H-zI)^{-1}\iota_S,
\qquad
\Delta_S(z)=\det(I+K G_S(z)).
```

The proposed identity to establish is
```math
\frac{F_{H'}(z)}{F_H(z)}
=\frac{\Delta_S(z)\Delta_S(-z)}{\Delta_S(0)^2}.
```

It must be stated away from the original spectrum, with nonvanishing
normalization at zero and a meromorphic interpretation accounting for common
zeros, poles and multiplicities. **This identity is a research target, not a
theorem currently verified in this repository.**

The determinant has finite size, but its Green-matrix entries still depend on
the infinite operator. Certified finite-patch approximation is therefore part
of the intended result, rather than a consequence of the determinant's size.
The framework of finite-rank perturbation determinants is classical; see,
for example, [Golinskii, Spectra of infinite graphs with tails](https://doi.org/10.1080/03081087.2016.1155529).
Any originality claim must concern a precisely identified geometric or
quantitative contribution beyond that framework.

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

**Scope of this module:** the verified theorem concerns a *finite* matrix; symmetry alone does not imply positive eigenvalues or any infinite-dimensional spectral conclusions. Later §§4.20–4.30 establish conditional self-adjointness, compact resolvent, and isolation and local finiteness of genuine real eigenvalues for the abstract infinite matching-family operator. Conditional real-spectrum enumeration with exact geometric multiplicities is established later in §§4.36–4.37, qualitative divergence in §4.38, and a positive real spectral gap under explicit assumptions in §4.39. Quantitative index-wise comparison and inverse-square summability for the full interacting operator remain open.

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

**Scope of the second result:** this finite-dimensional theorem proves *stability* of positivity, assuming positivity of the original and perturbation energies. The following section derives a sufficient condition for the original energy from the geometric inputs themselves. The distinct infinite-operator results, including conditional self-adjointness, compact resolvent and locally finite real point spectrum, are proved later in §§4.20–4.30. Under additional hypotheses, the full interacting real spectrum is subsequently enumerated with exact geometric multiplicities (§4.37) and its ordered eigenvalues are proved to tend to `+∞` (§4.38). Quantitative growth comparison and inverse-square summability remain open.

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

**Scope:** the result is finite-dimensional; the hypothesis `V(t)>0` for every tile is sufficient, not necessarily optimal. This finite-dimensional theorem does not itself construct the infinite operator or establish a uniform gap across growing patches. The later abstract infinite-operator construction appears in §4; inverse-square summability for the interacting spectrum remains open.

## 4. Infinite-dimensional geometric operators and spectral theory

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

**Scope of this first infinite result:** only the individual-energy contribution is built here. The pair-interaction Laplacian `L_w` and the perturbation `\varepsilon P` are not yet included **in this first module**; §§4.6–4.9 subsequently construct infinite interactions. The density of `D(V)` is addressed in §4.2; §§4.20–4.30 establish conditional self-adjointness, compact resolvent, finite eigenspace dimension, and isolation and local finiteness of the full operator's genuine real eigenvalues. These later theorems require additional hypotheses and do not follow merely from defining the domain; conditional multiplicity-aware ordering and qualitative divergence of the full real spectrum are subsequently proved in §§4.37–4.38; quantitative indexed comparison and inverse-square summability for the interacting spectrum remain open.

### 4.2. Density of the natural operator domain

The new Lean module **[`SpectralGeometry/InfiniteOnsiteDensity.lean`](SpectralGeometry/InfiniteOnsiteDensity.lean)** establishes that the natural domain `D(V)` introduced in the previous section is **dense in `\ell^2(T)`**, even when the potential `V(t)` is unbounded and the set of tiles is infinite.

**The idea is simple:** switch on amplitudes at only finitely many tiles and leave all other amplitudes equal to zero. Every such finite-support configuration belongs to `D(V)`, because multiplying its finitely many nonzero amplitudes by real numbers `V(t)` still leaves finitely many nonzero amplitudes.

Any square-summable configuration can be approximated arbitrarily closely (in the `\ell^2` norm) by these finite-support configurations. Consequently:

```math
\overline{D(V)}=\ell^2(T).
```

This does **not** say `D(V)=\ell^2(T)`. It says every square-summable state can be approximated as accurately as desired by states on which the onsite operator is well-defined. Mathlib's convergent sum of `lp.single` states supplies the approximation theorem.

**Why it matters:** density is a crucial prerequisite for the Hilbert-space theory of adjoint and self-adjoint unbounded operators. It does *not*, by itself, establish self-adjointness, compact resolvent, a discrete infinite spectrum, or spectral summability. The infinite interaction operator and perturbation are constructed in later modules (§§4.6–4.9), not as consequences of density alone.

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

**Scope and important limitation:** these are results about the *point spectrum* of the infinite onsite multiplication operator. They do not prove that the operator is self-adjoint, that every `V(t)` occurs as an eigenvalue, that the entire spectrum is positive or discrete, or that the inverse-square eigenvalue series converges. The subsequent §§4.6–4.9 construct interactions and bounded perturbations, while §§4.20–4.30 prove further conditional results for the full geometric operator `H_\varepsilon`, culminating in isolation and local finiteness of genuine real eigenvalues.

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

**Precise scope:** the ambient set of tiles may be infinite, but the number of active interaction edges in this first construction is **finite**. The genuinely infinite-edge Laplacian requires a convergence or uniform-weight hypothesis, addressed by later constructions in §§4.8–4.9. This finite-edge theorem does not model every edge of a particular Penrose or other aperiodic tiling.

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

**What is not claimed:** this is a sufficient `ℓ¹` condition on the *entire* edge list, not yet a bounded-degree local graph condition. Infinite tilings with uniformly bounded non-decaying weights typically have infinitely many edges and do not satisfy `∑|w_n|<∞`. The matching-family construction in §4.9 addresses a different infinite-edge model; the subsequent §§4.20–4.22 prove compact resolvent and self-adjointness for that model under explicit hypotheses. This summable-edge module alone establishes neither those results nor full-spectrum inverse-square summability.

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

**Scope:** these theorems constrain eigenvalues *if nonzero eigenvectors exist*; they do not by themselves establish spectral completeness or exclude continuous spectrum. Subsequent §§4.20–4.30 prove conditional self-adjointness and compact resolvent, density of genuine eigenvectors, and isolation and bounded-interval finiteness of distinct real eigenvalues. Section 4.32 subsequently establishes the real bounded-inverse spectral-mapping theorem for the unbounded operator; complex-spectrum formalization, inverse-square summability, and a connection to the canonical product remain open.

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

**Scope:** closedness is **not the same as self-adjointness**. This module alone does not establish an adjoint equality, a bounded or compact resolvent, spectral discreteness, or inverse-square summability. Self-adjointness is subsequently proved in §4.22, compact resolvent under explicit hypotheses in §§4.20–4.21, and isolation and local finiteness of genuine real eigenvalues in §§4.29–4.30. Full real bounded-inverse spectral mapping is subsequently established in §4.32; a complex-spectrum extension and inverse-square summability remain open.

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

**Relation to subsequent results:** this module establishes bijectivity and the coordinate formula, but does not itself package the inverse as a continuous linear map. The bounded inverse and its compactness are established in §§4.18–4.19. Sections 4.20–4.21 subsequently prove two-sided invertibility of a shifted **interacting** operator and compactness of its resolvent under explicit hypotheses; §§4.29–4.30 establish isolation and local finiteness of genuine real eigenvalues. Full real bounded-inverse spectral mapping is subsequently established in §4.32; its complex extension, inverse-square summability, and a specialized aperiodic-tiling model remain open. The one-unit condition is a convenient sufficient hypothesis, not a necessary one.

### 4.17. Finite low-energy sectors under a proper onsite potential

The Lean module **[`SpectralGeometry/InfiniteOnsiteFiniteLowEnergy.lean`](SpectralGeometry/InfiniteOnsiteFiniteLowEnergy.lean)** makes explicit an important growth hypothesis for the *diagonal onsite operator* `M_V`: for any fixed energy threshold `R`, there are only finitely many tiles with `V(t)≤R`.

Lean proves two consequences on the natural onsite domain: any genuine point eigenvector with real eigenvalue `λ≤R` can be nonzero only on those finitely many low-energy tiles, and only finitely many **distinct onsite point eigenvalues** can lie at or below `R`. These follow from the previously proved coordinate identity `λ=V(t)` whenever an eigenvector is nonzero at tile `t`.

The hypothesis of finite low-energy sublevel sets is a precise form of *onsite potential growth at infinity*. It is additional to previous results and is **not claimed for an arbitrary potential or automatically for a particular geometric tiling**.

**Important scope:** these results concern `M_V`, **not the fully interacting operator** `H=M_V+L_w+εP+mI`. On their own they do not prove compact resolvent, spectral discreteness, inverse-square summability, or eigenvalue existence for an arbitrary potential. The finite-rank approximation and compact onsite resolvent are proved in §4.18 under the additional unit-gap assumption. A compact resolvent for the **interacting** operator is subsequently proved in §§4.20–4.21, and local finiteness of genuine real eigenvalues in §4.30. Quantitative growth and inverse-square summability for the interacting spectrum remain open.

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

**Scope:** this completes the onsite inverse-identification argument without introducing any new potential-growth hypothesis. By itself it does **not** establish invertibility or compact resolvent of the full interacting operator `H=M_V+L_w+εP+mI`; those conditional results are subsequently proved in §§4.20–4.21.

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

The result applies to any bounded correction satisfying the stated condition, in particular to the finite-color matching-family interaction with a bounded controlled perturbation encoded by `B=L_w+εP+mI`. It does **not** claim that `‖B R_a‖<1` holds automatically for arbitrary coupling strengths or at an arbitrary spectral shift. Compactness alone does not imply the quantitative inverse-square eigenvalue estimate. The subsequent §§4.23–4.30 derive spectral completeness, finite-dimensional eigenspaces, and isolation and local finiteness of genuine real eigenvalues under additional hypotheses; the complete **real** spectral mapping is subsequently proved in §4.32, while a complex-spectrum extension and inverse-square summability remain open.

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

Thus `V(t)-a≥δ≥1` and `δ>2DW+|ε|‖P‖+|m|` suffice for the compact shifted inverse of the actual local matching operator via its already-proved bounded-correction identity. Neither symmetry of `P` nor a fixed small coupling is required for this existence result. With the additional symmetry assumptions, §4.22 proves self-adjointness, §4.27 proves density of genuine eigenvectors, and §§4.29–4.30 establish isolation and local finiteness of distinct real eigenvalues. Full real bounded-inverse spectral mapping is subsequently proved in §4.32. Conditional ordering with exact geometric multiplicities and qualitative divergence are subsequently established in §§4.36–4.38. The complex-spectrum extension, quantitative ordered-level comparison and inverse-square summability remain open P2 objectives.

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

**Scope:** this establishes the operator-theoretic interface needed before applying later spectral results. It requires the stated symmetry assumptions for the full local operator and makes no claim about compactness without the properness/gap hypotheses of §§4.20–4.21. The later §4.25 proves finite-dimensional full-operator eigenspaces under compact-resolvent hypotheses, while §4.29 proves isolation of nonzero real spectral points of the compact bounded resolvent. Section 4.30 subsequently establishes isolation and bounded-interval finiteness for **genuine full-operator real eigenvalues**. Section 4.32 subsequently characterizes the complete **real bounded-inverse spectrum** on the natural domain. Conditional multiplicity-aware ordering and qualitative divergence are proved later (§§4.36–4.38); the complex-spectrum extension, quantitative ordered-level comparison and inverse-square summability remain open.

### 4.23. Compact self-adjoint resolvents and their eigenspaces

The Lean module **[`SpectralGeometry/InfiniteLocalResolventSpectrum.lean`](SpectralGeometry/InfiniteLocalResolventSpectrum.lean)** begins the P2 spectral stage by applying Mathlib's compact self-adjoint spectral results to the **bounded resolvent** of the interacting operator. Let `H=M_V+B` on the natural domain `D(V)`; assume the shifted inverse `R_a=(H-aI)⁻¹` is constructed as in §§4.20–4.21, and that the bounded correction `B` is symmetric.

The new module proves that `R_a` is self-adjoint as a continuous linear map, using the two inverse identities from §4.20 and symmetry on `D(V)`. Under the finite-sublevel hypothesis on `V`, `R_a` is also compact. Mathlib's compact-operator results then imply:

- **Finite eigenspace dimension:** for every nonzero real eigenvalue `μ` of `R_a`, its eigenspace is finite-dimensional.
- **Spectral totality:** the orthogonal complement of the supremum of all eigenspaces of `R_a` is zero. Equivalently, their linear span is dense in the real Hilbert space.
- **Local matching specialization:** if each matching permutation is involutive and the bounded perturbation `P` is symmetric, the corrected geometric resolvent is self-adjoint whenever the explicit Neumann condition is satisfied. The gap bounds of §4.21 provide sufficient conditions for its existence.

**Important distinction:** these are formalized properties of the **compact bounded resolvent**. Section 4.24 separately transfers nonzero resolvent eigenpairs to eigenpairs of the unbounded operator `H` via `λ=a+μ⁻¹`; §4.29 subsequently proves isolation of nonzero real spectral points of the compact resolvent. Section 4.30 also isolates genuine full-operator real eigenvalues and proves that only finitely many distinct eigenvalues occur in each bounded interval. The complete **real bounded-inverse spectrum** is subsequently characterized in §4.32. Later §§4.36–4.38 establish conditional multiplicity-aware ordering and qualitative divergence for the full real spectrum. A full complex-spectrum extension, quantitative ordered-eigenvalue growth and inverse-square summability remain open.

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

**Scope:** the eigenpair correspondence at a fixed resolvent shift is now formalized. Subsequent §4.30 transfers resolvent isolation to the full operator's **real point spectrum**, including finiteness of distinct eigenvalues on bounded intervals. The subsequent §4.32 identifies the full **real bounded-inverse spectrum** of the unbounded operator. Conditional ordering with exact multiplicities and qualitative divergence are established in §§4.36–4.38. The complex-resolvent interface, quantitative comparison and full-spectrum summability remain open (§§6.1–6.2).

### 4.25. Finite multiplicity and orthogonality of full local eigenvectors

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenspaces.lean`](SpectralGeometry/InfiniteLocalFullEigenspaces.lean)** transfers the finite-dimensional eigenspace result of §4.23 from the compact bounded resolvent to the **unbounded full local operator**, using the eigenpair correspondence of §4.24. For a spectral parameter `a` where the inverse exists, each real eigenvalue `λ≠a` has a well-defined full eigenspace, realized by the resolvent eigenspace at `(λ-a)⁻¹`.

The module identifies membership in this submodule with the actual domain-restricted eigenvalue equation for `H=M_V+L_w+εP+mI` on `D(V)`. Assuming finite sublevel sets for the onsite potential and the existing resolvent smallness condition, it proves that **each such full eigenspace is finite-dimensional**. It also shows that `a` itself cannot be an eigenvalue, because the full shifted operator has a two-sided inverse. Thus the finite-multiplicity statement covers all real eigenvalues of `H`.

Under involutive matching permutations and symmetry of the bounded perturbation `P`, eigenvectors corresponding to **different real eigenvalues are orthogonal**. This orthogonality theorem is an operator-symmetry consequence and does not need the extra compactness hypotheses.

**Scope:** finite-dimensional eigenspaces and orthogonality alone do not imply isolation. Section 4.30 uses the additional compact-resolvent spectral isolation from §4.29 to establish isolation and bounded-interval finiteness of **genuine full-operator eigenvalues**. Section 4.32 later identifies the full **real bounded-inverse spectrum** with the point spectrum under explicit hypotheses, and §4.33 introduces unordered multiplicity tags. Conditional ordered enumeration with exact multiplicities is established in §§4.36–4.37 and divergence in §4.38. The complex-resolvent interface, quantitative comparison and full-spectrum summability remain open (§§6.1–6.2).

### 4.26. Fredholm spectral exhaustion for the nonzero local resolvent spectrum

The Lean module **[`SpectralGeometry/InfiniteLocalFredholmSpectralExhaustion.lean`](SpectralGeometry/InfiniteLocalFredholmSpectralExhaustion.lean)** makes a first rigorous spectral-exhaustion statement using Mathlib's **Fredholm alternative for compact operators**. Let `H=M_V+L_w+εP+mI` on its natural domain `D(V)`, and suppose the resolvent `R_a=(H-aI)⁻¹` exists and is compact under the already formalized onsite-gap, finite-sublevel and Neumann-smallness hypotheses.

For every real `μ≠0`, the module proves the following equivalence, where the spectrum on the left is the standard **bounded-operator spectrum in Mathlib**:

```math
\mu\in\sigma(R_a)
\quad\Longleftrightarrow\quad
\exists\,\psi\in D(V)\setminus\{0\}:
H\psi=(a+\mu^{-1})\psi.
```

Equivalently, for a real parameter `λ≠a`, the transformed value `(λ-a)⁻¹` belongs to the resolvent spectrum **if and only if** `λ` admits a nonzero eigenvector of the unbounded full local operator. The forward implication uses Fredholm's alternative; the reverse implication uses the two-sided inverse and the eigenpair correspondence from §4.24. **No symmetry hypothesis is needed** for this compact-operator spectral-point/eigenpair equivalence.

**Precise scope:** the proof exhausts the **nonzero spectrum of the compact bounded resolvent**, not the full spectrum of the unbounded `LinearPMap` by a separate spectral-mapping theorem. The special point `0` of the compact resolvent spectrum is deliberately excluded from this correspondence. Section 4.29 subsequently proves that the nonzero real spectral points of the compact resolvent are isolated and that zero is their only possible accumulation point. Section 4.30 further isolates the actual full-operator real eigenvalues and rules out finite accumulation. Section 4.32 subsequently characterizes the complete **real bounded-inverse spectrum** on the natural domain. Conditional ordered enumeration with exact multiplicities is established in §§4.36–4.37 and divergence in §4.38. The complex-resolvent interface, quantitative comparison and full-spectrum summability remain open (§§6.1–6.2).

### 4.27. Completeness of genuine eigenvectors of the full infinite local operator

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenvectorsComplete.lean`](SpectralGeometry/InfiniteLocalFullEigenvectorsComplete.lean)** proves the strong **eigenvector completeness** consequence of compact self-adjoint resolvent for the *unbounded full matching-family operator* `H=M_V+L_w+εP+mI` on its unchanged natural domain `D(V)`.

First, the resolvent `R_a=(H-aI)⁻¹` has **trivial kernel**, because its constructed natural-domain solution satisfies the explicit right-inverse equation (§4.20). Thus its zero eigenspace is the zero subspace, and the complete compact self-adjoint spectral theorem from §4.23 implies that the eigenspaces of `R_a` with **nonzero** real eigenvalues alone span a dense subspace of `ℓ²(T)`.

Second, by the eigenpair correspondence of §4.24, every nonzero resolvent eigenvalue `μ` gives a real full-operator eigenvalue `λ=a+μ⁻¹` and exactly the same eigenspace, now interpreted as natural-domain eigenvectors. Lean proves that the orthogonal complement of the supremum of these **actual full local eigenspaces**, indexed by real `λ≠a`, is `⊥`. Equivalently, the linear span of all such full-operator eigenvectors is dense in the Hilbert space.

This result requires the existing compactness conditions (onsite finite sublevels, the unit gap and the Neumann smallness condition), involutive matchings and symmetry of the bounded perturbation. It is stronger than merely stating that the resolvent has complete eigenvectors; it directly packages the genuine unbounded operator's natural-domain eigenvectors as a total family.

**Scope:** the complete eigenvector family need not yet be enumerated or ordered. Dense eigenvector span alone does **not** establish that finite full-operator eigenvalues are isolated, that there are no finite spectral accumulation points, or any spectral growth or inverse-square summability estimate. Section 4.30 subsequently establishes isolation and no finite accumulation for genuine real eigenvalues. Conditional ordering with exact multiplicities and qualitative divergence are established in §§4.36–4.38. Quantitative comparison and full-spectrum inverse-square summability remain open (§6.2).

### 4.28. A resolvent-norm exclusion zone for full-operator eigenvalues

The Lean module **[`SpectralGeometry/InfiniteLocalResolventNormGap.lean`](SpectralGeometry/InfiniteLocalResolventNormGap.lean)** adds a quantitative consequence of the Fredholm spectral correspondence from §4.26. Fix a real shift `a` for which the full matching-family operator `H` has a bounded compact resolvent `R_a=(H-aI)⁻¹`, under the same onsite gap, finite-sublevel and Neumann-smallness assumptions as before.

If a nonzero state in the natural domain is a full-operator eigenvector at a real eigenvalue `λ≠a`, the reciprocal `(λ-a)⁻¹` belongs to the spectrum of the bounded resolvent (§4.26). Mathlib's norm bound on the spectrum therefore gives

```math
\left|\frac{1}{\lambda-a}\right|\le\|R_a\|\,\|I\|.
```

The module also formalizes the contrapositive: whenever `λ≠a` and `|(λ-a)⁻¹|>‖R_a‖‖I‖`, every natural-domain solution of `Hψ=λψ` is zero. Here `I` is the identity operator on `ℓ²(T)`. Its norm is one on a nonzero Hilbert space; the Lean statement retains the factor `‖I‖` to avoid requiring a nontrivial-space instance when the tile type can be empty. This excludes genuine eigenvalues from a quantitative neighborhood of the **chosen resolvent shift**. It does not require the symmetry assumptions used for self-adjoint spectral completeness.

**Precise scope:** the result isolates the selected resolvent shift from point eigenvalues with an explicit norm test. It does **not** prove that each full-operator eigenvalue is isolated from other eigenvalues, that the entire unbounded spectrum is exhausted by eigenvalues, that the spectrum can be ordered, or that inverse-square summability holds. Section 4.30 subsequently establishes isolation and bounded-interval finiteness for genuine full-operator real eigenvalues, and §4.32 identifies the complete **real bounded-inverse spectrum**. Conditional ordered enumeration with exact multiplicities and qualitative divergence are established in §§4.36–4.38. The complex-resolvent interface and full-spectrum summability remain open (§§6.1–6.2).

### 4.29. Isolation of nonzero points in the compact resolvent spectrum

The Lean module **[`SpectralGeometry/InfiniteLocalResolventSpectralIsolation.lean`](SpectralGeometry/InfiniteLocalResolventSpectralIsolation.lean)** establishes the P2 isolation result for the **bounded compact resolvent**. Assume the onsite gap, finite onsite sublevel sets, and Neumann-smallness condition already used for `R_a=(H-aI)⁻¹`. Assume also that the bounded correction is symmetric, making `R_a` self-adjoint.

The key intermediate result says that for each `δ>0` there are **only finitely many distinct real spectral values** satisfying `|μ|≥δ`:

```math
\#\{\mu\in\sigma_{\mathbb R}(R_a):|\mu|\ge\delta\}<\infty
\qquad(\delta>0).
```

The proof uses compactness: an infinite family of distinct eigenvalues bounded away from zero would produce infinitely many orthogonal unit eigenvectors, whose images under the compact operator remain uniformly separated, contradicting sequential compactness. Fredholm's alternative turns the eigenvalue statement into one about the full **real bounded-operator spectrum**.

Consequently, **every nonzero real spectral point is isolated**. More precisely, if `μ≠0` and `μ∈σ_ℝ(R_a)`, there exists `r>0` such that

```math
\nu\in\sigma_{\mathbb R}(R_a),\quad |\nu-\mu|<r
\quad\Longrightarrow\quad \nu=\mu.
```

In particular, **zero is the only possible accumulation point** of the real spectrum of the compact resolvent. The module does not require a nonempty tile type or an infinite-dimensional Hilbert space.

**Scope:** this finishes the bounded-resolvent isolation milestone. The following §4.30 transfers it via `λ=a+μ⁻¹` to **genuine real eigenvalues** of the unbounded operator. The subsequent §4.32 establishes real bounded-inverse spectral mapping on the natural domain; conditional ordering with exact multiplicities and qualitative divergence are established in §§4.36–4.38. The complex-resolvent interface and quantitative spectral goals remain open (§§6.1–6.2).

### 4.30. Isolation and local finiteness of genuine full-operator eigenvalues

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenvalueIsolation.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueIsolation.lean)** transfers the compact-resolvent spectral results of §4.29 to the actual **real point spectrum** of the unbounded matching-family operator `H=M_V+L_w+εP+mI` on its unchanged natural domain `D(V)`.

Write `Eig(H)` for the set of real parameters `λ` for which there is a **nonzero** `ψ∈D(V)` with `Hψ=λψ`. Under the earlier unit onsite gap at `a`, finite onsite sublevel sets, Neumann smallness, involutive matchings, and symmetry of `P`, the module proves:

- **Pointwise isolation:** for each `λ∈Eig(H)`, there exists `r>0` such that every `ν∈Eig(H)` with `|ν−λ|<r` satisfies `ν=λ`. Unlike §4.28, this concerns *every* genuine eigenvalue, not just the selected shift.
- **Finiteness in bounded intervals:** for every `M≥0`, the set `{λ∈Eig(H) : |λ|≤M}` is finite. Thus distinct genuine real eigenvalues have **no finite accumulation point**, even at a real parameter that is not itself an eigenvalue.

The transfer uses the existing equivalence `λ∈Eig(H) ↔ (λ−a)⁻¹∈σ_ℝ(R_a)` for `λ≠a` (§4.26). The already-checked two-sided inverse excludes `a` as an eigenvalue (§4.25). Continuity and injectivity of `λ↦(λ−a)⁻¹` yield isolation, while bounded `|λ|` ensures the corresponding resolvent spectral parameters remain uniformly away from zero, so §4.29 gives finiteness.

**Precise scope:** these results by themselves identify properties of the **real point spectrum**; the subsequent §4.32 defines and characterizes the full **real bounded-inverse spectrum** on the same natural domain. Local finiteness counts **distinct eigenvalues**, not multiplicities. The next §4.31 proves countability and constructs a complete, possibly repeating listing of these real eigenvalues when nonempty. Ordered enumeration **with exact geometric multiplicities** and qualitative divergence are proved separately in §§4.36–4.38. Quantitative eigenvalue comparison and inverse-square summability remain open (§6.2).

### 4.31. Countability and a complete (unordered) listing of full-operator eigenvalues

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenvalueEnumeration.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueEnumeration.lean)** builds on the bounded-interval finiteness theorem from §4.30. Under the same explicit compact self-adjoint resolvent hypotheses (onsite gap, finite onsite sublevel sets, Neumann-small correction, involutive matchings, and symmetric perturbation), the set `Eig(H)` of **genuine real eigenvalues of the full operator on `D(V)`** is **countable**:

```math
\operatorname{Eig}(H)=\bigcup_{n\in\mathbb N}
\{\lambda\in\operatorname{Eig}(H):|\lambda|\le n\},
\qquad
\#\{\lambda\in\operatorname{Eig}(H):|\lambda|\le n\}<\infty.
```

If `Eig(H)` is **nonempty**, Lean also constructs a sequence `e : ℕ → ℝ` whose range is **exactly** `Eig(H)`. This works whether the underlying tile type or the point spectrum is finite or infinite: **repetitions are allowed** in the sequence, so a finite nonempty point spectrum is handled correctly. No eigenvalue-existence assertion is made for arbitrary tile types; an empty point spectrum is countable but has no real-valued sequence with exactly that range.

**Scope:** this is a full *set-theoretic listing* of the real **point spectrum**, not a classification of the whole unbounded `LinearPMap` spectrum. The sequence is not asserted increasing or injective and **does not record eigenspace multiplicities**. The project has already proved finite-dimensional eigenspaces (§4.25). The following §4.32 formalizes the **full real bounded-inverse spectral mapping** on the natural domain; conditional ordering **with exact geometric multiplicities** and qualitative divergence are proved later in §§4.36–4.38, while the complex-spectrum extension remains open (§6.1). Quantitative eigenvalue growth and inverse-square summability do not follow from countability alone and remain open (§6.2).

### 4.32. The full real bounded-inverse spectrum on the natural domain

The Lean module **[`SpectralGeometry/InfiniteLocalFullRealResolvent.lean`](SpectralGeometry/InfiniteLocalFullRealResolvent.lean)** goes beyond eigenpair correspondence (§4.26) and constructs actual bounded inverse operators for **arbitrary real spectral shifts** of `H=M_V+B` with the original domain `D(V)`. Here `B` is any bounded real-linear correction; the existing matching-family model is recovered by taking `B=L_w+εP+mI`.

Define a real *regular point* `b` by the existence of a bounded linear `Q_b : ℓ²(T) → ℓ²(T)` satisfying all three conditions: every `Q_b f` lies in `D(V)`, `(H-bI)Q_b f=f` for every input `f`, and `Q_b(H-bI)ψ=ψ` for every `ψ∈D(V)`. The **full real bounded-inverse spectrum** is the complement of this regular-point set. This is a definition based on two-sided bounded invertibility, **not a renaming of the eigenvalue set**.

Suppose a real shift `a` has the previously checked bounded inverse `R_a=(H-aI)⁻¹`, under the unit-gap and Neumann-smallness assumptions, and the onsite potential has finite sublevel sets so `R_a` is compact. On the natural domain Lean proves

```math
(H-bI)=(I-(b-a)R_a)(H-aI).
```

Whenever `I-(b-a)R_a` is invertible in the bounded-operator algebra, a new inverse exists:

```math
Q_b=R_a\,(I-(b-a)R_a)^{-1}.
```

It maps back into `D(V)` and satisfies **both** inverse identities. Compactness and Fredholm's alternative then establish, for `b≠a`, the precise equivalence

```math
b\in\sigma_{\mathrm{real}}(H)
\quad\Longleftrightarrow\quad
(b-a)^{-1}\in\sigma_{\mathbb R}(R_a).
```

The known shift `a` itself lies in the regular set. Unlike §4.26, the left-hand notion concerns **failure of a bounded inverse for the entire shifted unbounded operator**, including surjectivity and the original domain condition; it is not limited to a nonzero eigenpair test.

For the **actual matching-family operator** `H=M_V+L_w+εP+mI`, combining this mapping with the earlier compact-operator Fredholm theorem (§4.26) also proves **real spectral exhaustion**:

```math
b\in\sigma_{\mathrm{real}}(H)
\quad\Longleftrightarrow\quad
\exists\,\psi\in D(V)\setminus\{0\}:H\psi=b\psi.
```

This includes `b=a`, excluded from both sides by the previously checked inverse. The statement requires compactness of the shifted resolvent, but **not self-adjointness**: it rules out additional real bounded-inverse spectral points that are not eigenvalues under these hypotheses.

**Precise scope:** this is a complete **real bounded-inverse spectral mapping** theorem for the natural-domain operator, under the explicit compact-resolvent assumptions. The project has not yet formalized the analogous full **complex** spectrum or a Mathlib-native spectrum API for unbounded `LinearPMap` operators. Conditional ordering **with exact geometric multiplicities** and qualitative divergence are established later in §§4.36–4.38; §4.39 also proves a positive real spectral gap under explicit assumptions. Quantitative ordered-eigenvalue comparison and inverse-square summability remain open (§6.2).

### 4.33. Countable eigenvalue enumeration with eigenspace multiplicity tags

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicity.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicity.lean)** extends the unordered real point-spectrum listing in §4.31. It defines the **geometric multiplicity** `m(λ)` as the finite rank of the full eigenspace from §4.25 when `λ ≠ a`; the known regular resolvent shift `a` is assigned multiplicity zero. Finite dimensionality depends on the stated properness and compact-resolvent hypotheses.

The module then defines the **multiplicity-tagged real point spectrum** as pairs `(λ, k)` such that `λ` is a genuine eigenvalue and `k < m(λ)`. Under the existing symmetry and compactness assumptions it proves that this tagged set is **countable**, and, **if nonempty**, has a sequence with exactly that set as its range.

**Precise limit:** a range-exact sequence may repeat the same tag arbitrarily; it is **not** an injective or ordered enumeration. The next §4.34 proves the missing positive-multiplicity and exact-coverage statements. Multiplicity-aware global ordering is established separately in §4.37 and qualitative divergence in §4.38; quantitative eigenvalue growth and inverse-square summability for the full interacting operator remain open.

### 4.34. Positive geometric multiplicity and exact tagged-spectrum coverage

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicityCoverage.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicityCoverage.lean)** resolves the next P2 milestone following §4.33, using the existing full-operator eigenspaces and compact-resolvent hypotheses (§§4.24–4.25).

For the full natural-domain matching-family operator `H = M_V + L_w + εP + mI` and the §4.33 multiplicity `m(λ)`, it proves the **equivalence**:

```math
\lambda\in\operatorname{Eig}(H)\quad\Longleftrightarrow\quad m(\lambda)>0.
```

The proof separately treats the known resolvent shift `a`, which is excluded from the point spectrum by the existing two-sided inverse and has multiplicity zero. For every `λ ≠ a`, the eigenspace membership theorem (§4.25) equates a genuine nonzero natural-domain eigenvector with a nonzero vector in the corresponding finite-dimensional submodule; the finite-dimensional `finrank` criterion then yields `m(λ)>0`. **No symmetry assumption is needed for this equivalence** beyond the explicit hypotheses needed to construct the compact resolvent and the finite-dimensional eigenspaces.

Writing `Tags(H) = {(λ,k) : λ ∈ Eig(H), k < m(λ)}`, the module additionally proves

```math
\lambda\in\operatorname{Eig}(H)
\quad\Longleftrightarrow\quad
\exists k\in\mathbb N:(\lambda,k)\in\operatorname{Tags}(H),
\qquad
\operatorname{fst}(\operatorname{Tags}(H))=\operatorname{Eig}(H).
```

These are **unconditional in spectrum nonemptiness**: they also hold when both sets are empty. Together with §4.33, the tagged set is countable under the stated symmetry and compactness hypotheses and covers every genuine real eigenvalue.

**Scope:** these theorems concern the real point spectrum and its finite geometric eigenspace dimensions. This module does **not itself** build an injective, increasing, multiplicity-aware eigenvalue sequence; §4.37 subsequently constructs one under explicit lower-bound and infinitude hypotheses, and §4.38 proves qualitative divergence. No result about the full complex unbounded spectrum, quantitative eigenvalue comparison, full-operator inverse-square summability or a concrete aperiodic tiling follows here.

### 4.35. Completeness indexed by the full real bounded-inverse spectrum

The Lean module **[`SpectralGeometry/InfiniteLocalFullRealSpectralCompleteness.lean`](SpectralGeometry/InfiniteLocalFullRealSpectralCompleteness.lean)** closes the **real self-adjoint completeness alternative** in the P2 spectral-notion/completeness milestone, combining the earlier eigenspace totality (§4.27), intrinsic real bounded-inverse spectrum (§4.32), and positive geometric multiplicity (§4.34).

With the previously defined complete real bounded-inverse spectrum `σ_real(H)` and geometric multiplicity `m(λ)`, it proves

```math
\lambda\in\sigma_{\mathrm{real}}(H)\quad\Longleftrightarrow\quad m(\lambda)>0,
\qquad
\sigma_{\mathrm{real}}(H)
=\operatorname{fst}(\operatorname{Tags}(H)).
```

These two exact spectral identities require the same onsite-gap, properness and resolvent-smallness hypotheses as the preceding real spectral-exhaustion and multiplicity results, but **not** self-adjointness.

For the full matching-family operator with an **additional symmetric bounded correction** (involutive matchings and a symmetric `P`), Mathlib's compact self-adjoint resolvent theorem also yields a **spectrally indexed completeness statement**. If `E_\lambda` denotes the genuine full eigenspace at `λ`, then

```math
\left(\bigvee_{\lambda\in\sigma_{\mathrm{real}}(H)}E_\lambda\right)^\perp
=\{0\}.
```

The Lean version explicitly excludes the designated resolvent shift `a` in its index type; the previously proved two-sided inverse shows `a\notin\sigma_{\mathrm{real}}(H)`, so **no real spectral point is discarded**. The proof removes regular parameters from the dense family of §4.27 by showing their full eigenspaces are trivial; it then transfers density to the family indexed solely by actual real spectral points. This is **density of the linear span**, not a claim that the algebraic span is closed.

**Limitations:** these are results for the **real** bounded-inverse spectrum of the actual natural-domain operator, not a formal complex spectral theorem or a naturally indexed eigenbasis. Conditional ordering with exact multiplicities is established in §§4.36–4.37 and qualitative divergence in §4.38. Quantitative comparison and full-spectrum inverse-square summability remain open (§6.2); the complex-resolvent interface needed for the response theorem remains open in §6.1.

### 4.36. Ordered finite spectral windows with exact multiplicity tags

The Lean module **[`SpectralGeometry/InfiniteLocalFullOrderedMultiplicityWindows.lean`](SpectralGeometry/InfiniteLocalFullOrderedMultiplicityWindows.lean)** begins the P2 milestone of ordered enumeration by combining **local finiteness of distinct eigenvalues** (§4.30) with **finite geometric eigenspace dimensions and exact tag coverage** (§§4.33–4.34).

For any radius `M ≥ 0`, it proves that the set

```math
T_M=\{(\lambda,k):\lambda\in\operatorname{Eig}(H),\
|\lambda|\le M,\ 0\le k<m(\lambda)\}
```

is **finite** under the same explicit onsite gap, properness, resolvent-smallness, and symmetry hypotheses as the local-finiteness theorem. The finite-fiber argument itself needs no symmetry: it uses the finite number of distinct eigenvalues in the window and the finite rank of each eigenspace.

More strongly, Lean constructs a **finite list** whose members are **exactly** the tags in `T_M`, **without repetitions**, ordered by lexicographic order: first by increasing `λ`, then by increasing copy index `k` when eigenvalues coincide. This preserves exactly the admissible multiplicity labels of each included eigenvalue; arbitrary duplicate entries are excluded by the proof's `Nodup` condition.

A separate theorem handles an **entire finite real point spectrum**, yielding a globally sorted finite tagged list, including the empty-spectrum case. This is conditional on finiteness of the real point spectrum; it is not a claim that every infinite tiling has only finitely many eigenvalues.

**Precise limit:** the ordered lists are finite on each bounded window or on an already finite spectrum. The module does **not** yet construct a coherent, globally indexed `ℕ → ℝ` eigenvalue sequence for an **infinite** spectrum, prove that the global spectrum is bounded below, or establish `λₙ → +∞`. The global infinite-spectrum enumeration under explicit lower-bound and infinitude hypotheses is subsequently proved in §4.37, and qualitative divergence to `+∞` in §4.38. Quantitative growth/comparison, inverse-square summability and the complex spectrum remain open (§§6.1–6.2).

### 4.37. Globally ordered infinite spectrum with exact geometric multiplicities

The Lean module **[`SpectralGeometry/InfiniteLocalFullGlobalOrderedEnumeration.lean`](SpectralGeometry/InfiniteLocalFullGlobalOrderedEnumeration.lean)** completes the **global-infinite enumeration** subgoal of P2, extending the finite ordered windows of §4.36.

First, it proves a general order-theoretic lemma: **every infinite linear order in which every strict initial segment is finite has a strictly increasing, surjective sequence indexed by ℕ**. The argument assigns to each element its finite number of predecessors; these ranks form an infinite subset of ℕ, whose canonical increasing enumeration can be pulled back injectively and surjectively to the original order.

For the full interacting matching-family operator, assume the previous onsite-gap, finite onsite-sublevel, resolvent-smallness and symmetry hypotheses. In addition, explicitly assume **a real lower bound** `L` for every genuine eigenvalue and **infinitude of the multiplicity-tag set**. Under these hypotheses, each lexicographic initial segment of the tagged spectrum is finite: any preceding tag has eigenvalue in the bounded interval from `L` up to the selected eigenvalue, and §4.36 controls every bounded spectral window *including multiplicities*.

Lean then constructs a **globally strictly increasing sequence of tags**:

```math
t:\mathbb{N}\to\operatorname{Tags}(H),\qquad
t_0<_{\rm lex}t_1<_{\rm lex}\cdots,\qquad
\{t_n:n\in\mathbb N\}=\operatorname{Tags}(H).
```

Writing `λₙ=(t_n)_1` yields a **nondecreasing sequence of real full-operator eigenvalues**. More precisely, the formalized exact-multiplicity assertion ensures

```math
\exists!\,n\in\mathbb{N}:\ t_n=(\lambda,k)
\quad\Longleftrightarrow\quad
\lambda\in\operatorname{Eig}(H)\ \land\ 0\le k<m(\lambda).
```

Consequently each real eigenvalue occurs precisely as often as its **finite geometric eigenspace dimension**, rather than merely being included in an unordered set-theoretic range. This does not follow from countability alone; the key additional ingredients are local finiteness, lower boundedness, and infinitude.

**Precise scope:** the hypotheses of lower boundedness and infinite spectrum are explicit, not inferred for all possible geometric models. Empty and finite spectra are handled separately by §4.36. The theorem concerns the *real* full interacting point/bounded-inverse spectrum, not the unformalized complex spectrum. **Divergence `λₙ→+∞` is proved in §4.38; quantitative comparison with onsite levels, inverse-square summability, and any concrete aperiodic model remain open.** These are recorded in §6.

### 4.38. Divergence to +∞ of the globally ordered full real spectrum

The Lean module **[`SpectralGeometry/InfiniteLocalFullOrderedEigenvalueDivergence.lean`](SpectralGeometry/InfiniteLocalFullOrderedEigenvalueDivergence.lean)** completes the divergence milestone in P2 after the exact multiplicity-aware global enumeration of §4.37.

First, an abstract filter lemma proves that a real sequence `f : ℕ → ℝ` converges to `+∞` whenever, for every real `B`, only finitely many indices satisfy `f(n) < B`. The proof uses the equality of the cofinite filter and `atTop` on the natural numbers; monotonicity is not required by this standalone criterion.

For the **full interacting matching-family operator**, suppose the onsite gap, finite onsite-sublevel, resolvent-smallness, and symmetry assumptions of §§4.30–4.37 hold. Additionally, assume a **uniform real lower bound** on all genuine eigenvalues and take an **injective global enumeration of the exact multiplicity tags** from §4.37. For any threshold `B`, all indexed tags below `B` lie in a bounded window of radius `|L|+|B|`. Section 4.36 proves that this window contains finitely many tags, **counting geometric multiplicities**. Injectivity of the tag enumeration therefore gives a finite set of such indices.

Lean establishes the full limit in the filter formulation:

```math
\operatorname{Tendsto}(\lambda_n,\operatorname{atTop},\operatorname{atTop}),
\qquad \lambda_n=(t_n)_1,
```

equivalently, `λₙ → +∞`. It also proves an existence theorem combining a **strictly increasing, range-exact global enumeration of tags** with divergence of the projected real eigenvalues. With §4.37, each eigenvalue is represented **exactly as many times as its finite geometric eigenspace dimension**.

**Scope:** the assumptions that the tagged spectrum is infinite and the real eigenvalues are bounded below are explicit and are **not** established here for every geometric potential. A limit of `+∞` is a **qualitative** result: it does not imply a polynomial growth rate, a positive spectral gap, or `∑ₙ λₙ⁻² < ∞`. Proving sufficient quantitative comparison and summability conditions for the full operator remains open (§6.2); no claim about the unformalized complex spectrum or a concrete aperiodic model is made.

### 4.39. Variational comparison and uniform real spectral gap for the full operator

The Lean module **[`SpectralGeometry/InfiniteLocalFullVariationalComparison.lean`](SpectralGeometry/InfiniteLocalFullVariationalComparison.lean)** begins the quantitative P2 comparison program using the actual **full interacting operator** `H = M_V + B`, where `B=L_w+\varepsilon P+mI` is bounded and the possibly unbounded multiplication operator `M_V` retains its natural domain `D(V)`.

**Quadratic-form comparison.** For every state `ψ ∈ D(V)`, the full quadratic energy differs from the onsite quadratic energy by at most

```math
\big|\langle\psi,H\psi\rangle-\langle\psi,M_V\psi\rangle\big|
\le \|B\|\,\|\psi\|^2.
```

In particular, `\langle\psi,M_V\psi\rangle-\|B\|\|\psi\|^2
\le\langle\psi,H\psi\rangle
\le\langle\psi,M_V\psi\rangle+\|B\|\|\psi\|^2`. This uses the **norm of the total correction**, not only the norm of `P`. It holds on the common domain **without** symmetry or positivity assumptions on `B`.

**Full real spectrum, not just point eigenvalues.** If `V(t)\ge c` for every tile, the onsite quadratic form is at least `c\|\psi\|^2`. Hence every genuine real eigenvalue of `H` satisfies `\lambda\ge c-\|B\|`. Under the previously verified compact-resolvent/real spectral-exhaustion hypotheses (§4.32), this bound extends to the **entire real bounded-inverse spectrum**, not only eigenvectors selected in advance. In particular, the sufficient condition `c>\|B\|` yields the **uniform positive real spectral gap** `\lambda\ge c-\|B\|>0`.

**What is *not* yet proved:** this is the variational **form inequality** required for min–max; Lean has **not yet derived** the desired index-wise comparison `\lambda_n(H)\ge\lambda_n(M_V)-\|B\|` between the two ordered spectra. Such a theorem still requires a multiplicity-aware min–max principle or counting argument on the unbounded self-adjoint domain, with an explicit bridge to the §4.37 eigenvalue enumeration. Nor does this lemma imply a polynomial growth rate, inverse-square summability, a complex spectrum theorem, or the existence of a concrete geometric tiling. See §6.2 for these remaining tasks.

### 4.40. Low-energy coordinate injection and eigenspace multiplicity counting

The Lean module **[`SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean`](SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean)** advances the P2 min–max/counting program using the **full natural-domain interacting operator** `H=M_V+B` and the sharp variational estimate from §4.39.

For any real threshold `R` and any `ψ∈D(V)` that vanishes on every tile where `V(t)<R`, it proves the high-energy quadratic-form bound

```math
\langle\psi,H\psi\rangle\ge (R-\|B\|)\,\|\psi\|^2.
```

Consequently, every **nonzero** eigenvector of `H` with `\lambda<R-\|B\|` must have a **nonzero coordinate** on some tile of onsite energy `V(t)<R`. Under the properness hypothesis, all such tiles belong to the **finite onsite sector** `F_R=\{t:V(t)\le R\}`.

**Stronger eigenspace result:** for a fixed `\lambda<R-\|B\|` distinct from the regular resolvent shift `a`, restriction of vectors in its full finite-dimensional eigenspace `E_\lambda(H)` to the coordinates in `F_R` is an **injective linear map** into `\mathbb{R}^{F_R}`. Thus the geometric multiplicity satisfies

```math
m_H(\lambda)=\dim E_\lambda(H)\le \#\{t:V(t)\le R\}.
```

This last theorem controls the **dimension of a complete eigenspace** rather than only detecting one eigenvector. It holds without requiring a global indexed onsite-eigenvalue sequence or a new complex-spectrum construction.

**Precise limitation:** the inequality above applies to *one eigenspace at a time*. It cannot simply be summed over distinct eigenvalues: to prove the desired multiplicity-aware counting inequality or `\lambda_n(H)\ge\lambda_n(M_V)-\|B\|`, the next step must control the **direct sum of all low-energy eigenspaces**, using their orthogonality under the self-adjoint hypotheses (§§4.27, 4.35) and a dimension comparison with the finite onsite sector. The final index-wise comparison, interacting inverse-square summability, and concrete tiling instantiation remain open (§6.2).

### 4.41. Simultaneous spectral subspaces on the natural domain

[DomainSpectralSubspace.lean](SpectralGeometry/DomainSpectralSubspace.lean)
defines `domainEigenspace` as the actual kernel of $A-\lambda I$ inside a
specified domain $d$, and `domainLowSpectralSubspace` as the span of **all**
eigenspaces with level at most $E$. For a symmetric domain operator,
`domainLowSpectralSubspace_energy_le` proves
$\langle x,Ax\rangle\le E\|x\|^2$ on this entire span. The proof groups
vectors by distinct levels and uses orthogonality, including arbitrary
combinations of vectors from different eigenspaces. No compactness or
finite-dimensionality is assumed in this abstract lemma.

### 4.42. Quantitative finite-sector observation and closedness

[InfiniteLowEnergyObservation.lean](SpectralGeometry/InfiniteLowEnergyObservation.lean)
constructs the symmetric positive coordinate contraction `finiteSectorProjection`
and the natural-domain operator `onsitePlusBounded`.
For $V\ge v_0$, finite $F$ and $V(t)\ge R$ outside $F$, it proves
```math
\langle x,Hx\rangle\ge(R-\|B\|)\|x\|^2-(R-v_0)\|P_Fx\|^2.
```
`onsitePlusBounded_lowSpectral_observation` combines this with §4.41:
```math
\frac{R-\|B\|-E}{R-v_0}\|x\|^2\le\|P_Fx\|^2,\qquad R>v_0.
```
Symmetry of $B$ is required for the spectral-subspace step. If
$E<R-\|B\|$, restriction is injective and the module **derives** finite
dimensionality, the bound $\dim L_E\le\#F$, and closedness of its image in
the ambient Hilbert space. Thus taking the closed low-energy eigenvector span
adds no vectors and does not lose the natural-domain condition. Properness
supplies $F=F_R$; the reusable form argument only needs the displayed finite
sector hypothesis. It covers finite, empty and infinite site types.

### 4.43. Total low-energy counting with the original multiplicities

[InfiniteLowEnergyCounting.lean](SpectralGeometry/InfiniteLowEnergyCounting.lean)
injects the direct sum of any finite family of distinct low eigenspaces into
the common observed subspace. It bounds the **sum of their dimensions once**,
not by adding separate upper bounds from §4.40.

[InfiniteLocalFullSpectralObservation.lean](SpectralGeometry/InfiniteLocalFullSpectralObservation.lean)
identifies these domain eigenspaces with the existing resolvent eigenspaces.
`infiniteLocalMatching_full_total_lowEnergy_count` constructs a finite set
whose membership is exactly $\lambda\in\sigma_{\rm real}(H)$ and
$\lambda<R-\|B\|$, and proves
```math
\sum_{\lambda<R-\|B\|}m_H(\lambda)\le\#F_R.
```
The multiplicity is the original `infiniteLocalMatchingFullMultiplicity`.
This bridge assumes properness, the unit shifted onsite gap, the small
resolvent-correction bound, involutive matchings and symmetric $P$.
The shift is excluded using its proved resolvent property. The finite set may
be empty; no infinite enumeration is needed for this count.

### 4.44. Complete eigenbases with exact multiplicity tags

[DomainEigenbasis.lean](SpectralGeometry/DomainEigenbasis.lean) records a
complete Hilbert basis of genuine eigenvectors in the specified domain.
`hasSum_energy` derives the energy expansion from symmetry and Parseval
applied to $x$ and $Ax$, without postulating an unbounded-operator expansion.

[InfiniteLocalFullEigenbasis.lean](SpectralGeometry/InfiniteLocalFullEigenbasis.lean)
constructs such a basis from the existing complete finite-dimensional
resolvent eigenspaces. `infiniteLocalMatching_full_exists_tagEigenbasis`
uses exactly the original multiplicity tags, also for finite or empty spaces.
`infiniteLocalMatching_full_exists_domainEigenbasis` reindexes it along any
exact strictly increasing tag enumeration from §4.37. Repeated eigenvalues
therefore have exactly their original number of orthonormal slots.
`infiniteLocalMatching_full_tags_infinite` derives infinitude of the tag set
from an infinite site type and completeness; it does not infer infinitude
from compactness alone. All these matching results retain the explicit
resolvent, properness and symmetry hypotheses.

### 4.45. A variational characterization of the ordered levels

[OrderedVariationalPrinciple.lean](SpectralGeometry/OrderedVariationalPrinciple.lean)
proves `DomainEigenbasis.eigenvalue_le_iff_trial`: for a symmetric domain
operator with a complete eigenbasis and monotone levels,
$\lambda_n\le E$ exactly when there is an injective trial map
$\mathbb R^{n+1}\to d$ whose Rayleigh numerators are at most $E\|x\|^2$.
The first $n+1$ basis vectors give one direction; a dimension argument against
the first $n$ coordinates gives the other.

`ordered_eigenvalues_affine_le` transfers any common-domain form inequality
$\alpha A+\beta I\le K$, $\alpha\ge0$, to
$\alpha\lambda_n(A)+\beta\le\lambda_n(K)$. The zero-coefficient case is
included. `DomainEigenbasis.ordered_levels_unique` proves independence from
basis choices inside repeated eigenspaces. The infinite sequence interface
requires actual complete $\mathbb N$-indexed eigenbases; it makes no infinite
listing claim for finite or empty spaces.

### 4.46. Ordered onsite comparison and finite-sector response

[InfiniteOrderedSpectralControl.lean](SpectralGeometry/InfiniteOrderedSpectralControl.lean)
constructs the onsite eigenbasis from an explicit bijection $e:\mathbb N\simeq T$.
If $v_n=V(e(n))$ is monotone, `onsitePlusBounded_ordered_comparison` proves
```math
v_n-\|B\|\le\lambda_n(H)\le v_n+\|B\|.
```
`infiniteLocalMatching_full_ordered_comparison` applies this directly to the
existing exact matching-spectrum tag enumeration. The site bijection and its
onsite ordering are explicit inputs, not a newly implemented sorting algorithm.
For a nonnegative interaction $L$ and signed correction $Q$, the lower bound
improves to $v_n-\|Q\|$; a wholly nonnegative correction gives $v_n$.

`finiteSector_ordered_response` proves
```math
\frac{R-\|B\|-E}{R-v_0}\,\tau
\le\lambda_n(H+\tau P_F)-\lambda_n(H)\le\tau
```
for $V\ge v_0$, $R>v_0$, finite $F$ with $V\ge R$ outside $F$,
$\lambda_n(H)\le E$ and $0\le\tau\le R-v_0$. It assumes symmetric $B$
and actual monotone complete eigenbases of both operators on the **same**
natural domain. Section 4.47 supplies their existence in the infinite proper
setting. For $E<R-\|B\|$ the lower response coefficient is positive.
The proof uses the affine comparison with $\alpha=1-\tau/(R-v_0)$,
including the endpoint $\alpha=0$. It never assumes simple eigenvalues,
differentiable eigenvalue branches or an absence of crossings.

### 4.47. Existence and operator hypotheses along the perturbation

[InfiniteOrderedSpectralExistence.lean](SpectralGeometry/InfiniteOrderedSpectralExistence.lean)
embeds a generic bounded correction into the existing matching construction
with zero matching colors. `onsitePlusBoundedPMap_isSelfAdjoint` proves genuine
self-adjointness on the unchanged natural domain for symmetric $B$.

For an infinite site type, proper $V$ and a global onsite lower bound,
`onsitePlusBounded_exists_orderedEigenbasis` derives a complete monotone
infinite eigenbasis: it chooses a sufficiently negative compact-resolvent
shift, proves the spectral lower bound and uses §4.44 to establish infinite
tags before invoking §4.37. `finiteSector_exists_orderedEigenbasis` proves
existence for every real perturbation parameter. Boundedness, symmetry,
properness and the natural domain persist; positivity is an additional result
for nonnegative parameters in §4.48. Finite and empty cases are handled by
the tag-basis and observation/counting results, not by this infinite listing.

### 4.48. Full-spectrum summability and a controlled positive family

[InfiniteFullSpectralSummability.lean](SpectralGeometry/InfiniteFullSpectralSummability.lean)
proves that a bounded lower error preserves inverse-square summability for
levels tending to infinity. Properness gives divergence along an injective
site listing. Thus `onsitePlusBounded_ordered_positive_summable` transfers
onsite summability to the complete full spectrum under §4.46's explicit
ordered bijection and eigenbasis assumptions. A separate bound
$V\ge v_0>\|B\|$ gives the uniform positive gap $v_0-\|B\|$.

`onsitePlusBounded_powerGrowth_positive_summable` instantiates this with the
existing sufficient growth $V(k)\ge(k+1)^\alpha$, $\alpha>1/2$, on sites
indexed by $\mathbb N$; these original labels need not already be sorted.
Other onsite criteria, including §4.4, enter through the general transfer.
The gap assumption is not inferred from growth or compactness.

`finiteSector_preserves_gap_summability` preserves any supplied positive
baseline gap and inverse-square summability for every $\tau\ge0$.
`finiteSector_preserves_compact_shift` provides a compact shifted inverse for
every real $\tau$; the chosen shift may depend on $\tau$.
`finiteSector_controlled_summable_family` combines the existence theorem,
the sufficient baseline gap/summability criterion and the response bound on
the entire interval $0\le\tau\le R-v_0$. It does not assume the perturbed
eigenbases or perturbed summability as input.

`fullSpectrum_admissible_of_positive_summable` connects these full levels to
the existing canonical-product predicate. Entire holomorphy, exact zero
orders, relative determinants, the concrete tiling and perturbations of
arbitrary sign remain separate obligations.

## 5. Building and verification

The canonical import list is maintained in [`SpectralGeometry.lean`](SpectralGeometry.lean). It currently imports **56 Lean modules**: one analytic core, four finite-dimensional geometry modules, and fifty-one operator/spectral modules (including domain-generic interfaces).

- **Analytic core (1):** [`CanonicalProduct.lean`](SpectralGeometry/CanonicalProduct.lean)
- **Finite-dimensional geometry (4):**
  - [`FinitePerturbation.lean`](SpectralGeometry/FinitePerturbation.lean)
  - [`FinitePositiveEnergy.lean`](SpectralGeometry/FinitePositiveEnergy.lean)
  - [`FiniteGeometricEnergy.lean`](SpectralGeometry/FiniteGeometricEnergy.lean)
  - [`FiniteStrictPositivity.lean`](SpectralGeometry/FiniteStrictPositivity.lean)
- **Onsite foundations, growth and summability (5):**
  - [`InfiniteOnsite.lean`](SpectralGeometry/InfiniteOnsite.lean)
  - [`InfiniteOnsiteDensity.lean`](SpectralGeometry/InfiniteOnsiteDensity.lean)
  - [`InfiniteOnsiteEigenvalues.lean`](SpectralGeometry/InfiniteOnsiteEigenvalues.lean)
  - [`InfiniteOnsiteSummability.lean`](SpectralGeometry/InfiniteOnsiteSummability.lean)
  - [`InfiniteOnsitePowerGrowth.lean`](SpectralGeometry/InfiniteOnsitePowerGrowth.lean)
- **Infinite interactions and local-operator estimates (11):**
  - [`InfiniteFiniteEdgeInteraction.lean`](SpectralGeometry/InfiniteFiniteEdgeInteraction.lean)
  - [`InfiniteBoundedPerturbation.lean`](SpectralGeometry/InfiniteBoundedPerturbation.lean)
  - [`InfiniteSummableEdgeInteraction.lean`](SpectralGeometry/InfiniteSummableEdgeInteraction.lean)
  - [`InfiniteLocalMatching.lean`](SpectralGeometry/InfiniteLocalMatching.lean)
  - [`InfiniteLocalBoundedDegree.lean`](SpectralGeometry/InfiniteLocalBoundedDegree.lean)
  - [`InfiniteLocalEigenvalueBounds.lean`](SpectralGeometry/InfiniteLocalEigenvalueBounds.lean)
  - [`InfiniteLocalSignedPerturbationGap.lean`](SpectralGeometry/InfiniteLocalSignedPerturbationGap.lean)
  - [`InfiniteLocalCoerciveGap.lean`](SpectralGeometry/InfiniteLocalCoerciveGap.lean)
  - [`InfiniteLocalGraphNorm.lean`](SpectralGeometry/InfiniteLocalGraphNorm.lean)
  - [`InfiniteLocalClosedGraph.lean`](SpectralGeometry/InfiniteLocalClosedGraph.lean)
  - [`InfiniteLocalAdjointCharacterization.lean`](SpectralGeometry/InfiniteLocalAdjointCharacterization.lean)
- **Onsite resolvents and compactness (4):**
  - [`InfiniteOnsiteResolvent.lean`](SpectralGeometry/InfiniteOnsiteResolvent.lean)
  - [`InfiniteOnsiteFiniteLowEnergy.lean`](SpectralGeometry/InfiniteOnsiteFiniteLowEnergy.lean)
  - [`InfiniteOnsiteCompactResolvent.lean`](SpectralGeometry/InfiniteOnsiteCompactResolvent.lean)
  - [`InfiniteOnsiteResolventIdentity.lean`](SpectralGeometry/InfiniteOnsiteResolventIdentity.lean)
- **Interacting resolvents and spectral results (21):**
  - [`InfiniteLocalCompactResolvent.lean`](SpectralGeometry/InfiniteLocalCompactResolvent.lean)
  - [`InfiniteLocalCompactResolventBounds.lean`](SpectralGeometry/InfiniteLocalCompactResolventBounds.lean)
  - [`InfiniteLocalSelfAdjointPMap.lean`](SpectralGeometry/InfiniteLocalSelfAdjointPMap.lean)
  - [`InfiniteLocalResolventSpectrum.lean`](SpectralGeometry/InfiniteLocalResolventSpectrum.lean)
  - [`InfiniteLocalEigenpairCorrespondence.lean`](SpectralGeometry/InfiniteLocalEigenpairCorrespondence.lean)
  - [`InfiniteLocalFullEigenspaces.lean`](SpectralGeometry/InfiniteLocalFullEigenspaces.lean)
  - [`InfiniteLocalFredholmSpectralExhaustion.lean`](SpectralGeometry/InfiniteLocalFredholmSpectralExhaustion.lean)
  - [`InfiniteLocalFullEigenvectorsComplete.lean`](SpectralGeometry/InfiniteLocalFullEigenvectorsComplete.lean)
  - [`InfiniteLocalResolventNormGap.lean`](SpectralGeometry/InfiniteLocalResolventNormGap.lean)
  - [`InfiniteLocalResolventSpectralIsolation.lean`](SpectralGeometry/InfiniteLocalResolventSpectralIsolation.lean)
  - [`InfiniteLocalFullEigenvalueIsolation.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueIsolation.lean)
  - [`InfiniteLocalFullEigenvalueEnumeration.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueEnumeration.lean)
  - [`InfiniteLocalFullRealResolvent.lean`](SpectralGeometry/InfiniteLocalFullRealResolvent.lean)
  - [`InfiniteLocalFullEigenvalueMultiplicity.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicity.lean)
  - [`InfiniteLocalFullEigenvalueMultiplicityCoverage.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicityCoverage.lean)
  - [`InfiniteLocalFullRealSpectralCompleteness.lean`](SpectralGeometry/InfiniteLocalFullRealSpectralCompleteness.lean)
  - [`InfiniteLocalFullOrderedMultiplicityWindows.lean`](SpectralGeometry/InfiniteLocalFullOrderedMultiplicityWindows.lean)
  - [`InfiniteLocalFullGlobalOrderedEnumeration.lean`](SpectralGeometry/InfiniteLocalFullGlobalOrderedEnumeration.lean)
  - [`InfiniteLocalFullOrderedEigenvalueDivergence.lean`](SpectralGeometry/InfiniteLocalFullOrderedEigenvalueDivergence.lean)
  - [`InfiniteLocalFullVariationalComparison.lean`](SpectralGeometry/InfiniteLocalFullVariationalComparison.lean)
  - [`InfiniteLocalFullLowEnergyCounting.lean`](SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean)

- **Simultaneous observation, variational control and full summability (10):**
  - [`DomainSpectralSubspace.lean`](SpectralGeometry/DomainSpectralSubspace.lean)
  - [`InfiniteLowEnergyObservation.lean`](SpectralGeometry/InfiniteLowEnergyObservation.lean)
  - [`InfiniteLowEnergyCounting.lean`](SpectralGeometry/InfiniteLowEnergyCounting.lean)
  - [`InfiniteLocalFullSpectralObservation.lean`](SpectralGeometry/InfiniteLocalFullSpectralObservation.lean)
  - [`DomainEigenbasis.lean`](SpectralGeometry/DomainEigenbasis.lean)
  - [`InfiniteLocalFullEigenbasis.lean`](SpectralGeometry/InfiniteLocalFullEigenbasis.lean)
  - [`OrderedVariationalPrinciple.lean`](SpectralGeometry/OrderedVariationalPrinciple.lean)
  - [`InfiniteOrderedSpectralControl.lean`](SpectralGeometry/InfiniteOrderedSpectralControl.lean)
  - [`InfiniteOrderedSpectralExistence.lean`](SpectralGeometry/InfiniteOrderedSpectralExistence.lean)
  - [`InfiniteFullSpectralSummability.lean`](SpectralGeometry/InfiniteFullSpectralSummability.lean)

The project uses Lean 4 `v4.35.0` with its corresponding Mathlib version. Every module listed above is imported by the root entry point.

```bash
lake exe cache get
lake build SpectralGeometry Challenge Solution
```

The Lean and Mathlib versions are pinned by `lean-toolchain` and
`lake-manifest.json`. Run `lake update` only when intentionally updating
dependencies, not as part of routine verification. `Challenge.lean`
contains deliberate statement placeholders (`sorry`), and is judged
against the original proof modules by Comparator rather than being
treated as an independently proved library.

**Palomar / independent statement verification:** the repository has
one [`comparator.json`](comparator.json), one
[`Challenge.lean`](Challenge.lean) and one [`Solution.lean`](Solution.lean).
Comparator selects **one theorem**, the per-eigenspace low-energy multiplicity
bound of §4.40, together with 16 independently reproduced definitions and type abbreviations needed to state it.
The toolchain's Lean, NanoDa and con-ron kernels verify the selected
comparison. The separate Lean build still covers **all 56 mathematical
source modules**; earlier compact-resolvent, real-spectrum and ordered
enumeration theorems remain compiled prerequisites but are not individually
compared in this submission. The metadata records the first identified
source of the precise formalized statement, while Mathlib and relevant
operator-theory literature are explicitly identified as background.
Mathematical priority and novelty are not asserted.

**Human/AI development provenance:** Alessandro Odasso originated the initial
non-formal research idea and directs the project. He does not identify as a
mathematician; his motivation is exploring LLMs in scientific research. By his
account, he used **OpenAI GPT-6 throughout the GitHub/Lean development**. This
acknowledges the technical AI assistance without assigning mathematical
novelty to it or suggesting that Odasso independently wrote all Lean proofs.
See [`PALOMAR.md`](PALOMAR.md) for the selected statement, contributor roles,
source provenance and limits.

To run the independent statement comparison on a supported Linux runner
with Bubblewrap configured, execute:

```bash
python3 scripts/check-unified-comparator.py
bash scripts/verify-comparator.sh
```

GitHub Actions checks compilation and the unified Comparator on pull
requests and changes to `main`. Both must be green before merging.

## 6. Roadmap: proof status and next steps

The program's central objective is a **quantitative response theorem for the
zeros associated with an explicitly specified local geometric change**.
The finite-coordinate eigenspace theorem of §4.40 is its first selected proved
milestone. The subsequent milestones turn observation into quantitative
spectral response and then into a certified comparison of analytic products.

A checked item refers to a result in the substantive Lean source imported by
[SpectralGeometry.lean](SpectralGeometry.lean), under its documented
hypotheses. The checked items below record the source development's reported
successful full build; any submitted commit must pass its own checks.
Unchecked items are open proof obligations or exploratory questions. P2, P3
and P4 denote research phases, not theorem numbers.

### 6.1. P2 — Spectral foundations and the complex-resolvent interface

**Formalized foundations**

- [x] Define the natural onsite domain, prove its density and establish
  closedness and adjoint characterizations for the relevant operators
  (§§4.1–4.2, 4.13–4.15).
- [x] Construct bounded infinite matching interactions and their energy and
  norm bounds (§§4.6–4.12).
- [x] Prove self-adjointness in Mathlib's partial-operator API and compact
  shifted resolvents under the explicit properness, gap, symmetry and
  bounded-correction hypotheses (§§4.16–4.22).
- [x] Connect full-operator eigenvectors with compact-resolvent eigenspaces;
  prove finite geometric multiplicity, orthogonality and completeness in
  the self-adjoint setting (§§4.23–4.27).
- [x] Identify the real bounded-inverse spectrum with genuine real
  eigenvalues, with isolation, local finiteness and countability
  (§§4.28–4.32).
- [x] Prove positive multiplicity, exact multiplicity-tagged coverage and
  completeness indexed by real spectral levels (§§4.33–4.35).
- [x] Construct sorted finite spectral windows and a globally ordered,
  exact, injective infinite tag enumeration; prove qualitative divergence
  under the stated lower-bound and infinitude hypotheses (§§4.36–4.38).

**Open interface for the analytic response theorem**

- [ ] Construct the required complexification and complex shifted inverse
  on the natural domain, and relate it to the verified real spectral data.
- [ ] Prove the resolvent identities, analyticity and compression facts
  needed to define $G_S(z)$. The real completeness theorem is not by
  itself this complex-resolvent interface.
- [ ] Keep finite, empty and infinite spectral cases distinct. Establish
  lower boundedness and infinitude for the concrete model before using
  the global infinite enumeration.

### 6.2. P2 — Quantitative observation and control of low-energy levels

**Formalized inputs**

- [x] Bound the full quadratic form relative to onsite multiplication by
  $\|B\|\|\psi\|^2$, and obtain a positive real-spectrum gap under the
  explicit hypotheses of §4.39.
- [x] Prove finite-coordinate detection and an injective restriction on
  each complete low-energy eigenspace, yielding its geometric
  multiplicity bound (§4.40).
- [x] Establish inverse-square summability for suitable linearly or
  power-law growing onsite-only levels (§§4.4–4.5).

**Verified simultaneous observation and spectral comparison (§§4.41–4.46)**

Assume the self-adjoint compact-resolvent setting, $V(t)\ge v_0$,
$C=\|B\|$, $R>v_0$, and $E<R-C$. Set
```math
F_R=\{t:V(t)\le R\},
\qquad
\kappa=\frac{R-C-E}{R-v_0}>0.
```

- [x] Strengthen the existing eigenspace restriction theorem to the
  quantitative estimate
  ```math
  \|P_{F_R}\psi\|^2\ge\kappa\|\psi\|^2
  ```
  for the entire spectral subspace below or at $E$, including linear
  combinations from distinct levels. Verify the domain, finite-dimensional
  and spectral-subspace hypotheses explicitly.
- [x] Derive the multiplicity-aware counting bound
  ```math
  \sum_{\substack{\lambda\in\sigma_{\mathrm{real}}(H)\\
                   \lambda<R-\|B\|}}m_H(\lambda)
  \le\#\{t:V(t)\le R\}.
  ```
  The separate bounds on individual eigenspaces in §4.40 cannot simply be
  summed to obtain it.
- [x] Connect the exact ordered enumeration to a variational/counting
  principle and prove
  ```math
  v_n-\|B\|\le\lambda_n(H)\le v_n+\|B\|,
  ```
  for onsite levels $v_n$ and full levels ordered with the same
  multiplicity convention. Exploit a nonnegative Laplacian to sharpen
  the lower bound where applicable.

**Verified finite-sector response and sufficient summability (§§4.46–4.48)**

- [x] For $H_\tau=H+\tau P_{F_R}$, prove
  ```math
  \kappa\tau
  \le\lambda_n(H_\tau)-\lambda_n(H)
  \le\tau,
  \qquad
  \lambda_n(H)\le E,\quad 0\le\tau\le R-v_0.
  ```
  The proof controls ordered levels with multiplicities and does not
  assume simple eigenvalues. The verified form-comparison route establishes
  ```math
  H\ge(R-C)I-(R-v_0)P_{F_R}
  ```
  on the natural domain and applies the proved variational comparison.
- [x] Transfer sufficient quantitative onsite growth to the ordered full
  eigenvalues and prove full-spectrum inverse-square summability.
  Positivity must also be verified; compact resolvent alone is insufficient.
- [x] Preserve the required positive gap and summability for nonnegative
  finite-sector perturbations, and prove existence of the ordered spectra
  throughout the response interval. Self-adjointness and compact shifted
  inverses are supplied by §§4.47–4.48; the resolvent shift may vary with the
  parameter.
- [ ] Extend a suitable gap/summability package to other signed local
  perturbations under independently checked quantitative hypotheses.

**Scope of the verified statements.** The norm comparison and growth transfer
use an explicitly sorted bijection of the onsite sites. Ordered full levels
come from complete domain eigenbases; §4.44 connects the original exact tags,
and §4.47 derives their existence for infinite site types, proper lower-bounded
$V$ and symmetric bounded corrections. The sufficient positive-summability
package uses $v_0>\|B\|$ and summable onsite inverse squares (or the proved
power-growth criterion). Positive interactions admit the sharper lower
comparison in §4.46. Finite/empty cases are covered by observation, counting
and tag bases; the $\mathbb N$-sequence statements explicitly address the
infinite case.

This phase now supplies a proved abstract consequence of finite observation:
a finite onsite intervention has a controlled effect on every selected low
ordered level. An application must still establish a nonempty target window
and its geometric hypotheses. These new source results are **not** part of
the unchanged Comparator-selected theorem of §4.40.

### 6.3. P3 — Full spectral products and their exact zero divisors

**Formalized analytic inputs**

- [x] Define the paired canonical product and prove compact-uniform
  convergence and zero localization for an admissible positive sequence
  (CanonicalProduct.lean, §2).
- [x] Prove admissibility from inverse-square summability, with onsite
  growth examples (§§4.4–4.5) and the full-spectrum transfer (§4.48).
- [x] Package positive ordered full levels as an admissible sequence under
  the explicit lower-gap, properness, onsite-ordering and summability
  hypotheses of §4.48. Sections 4.44 and 4.47 supply exact multiplicity
  indexing and the infinite-site existence conditions.

**Open analytic consequences and geometric instantiation**

- [ ] Prove that $F_H$ and $D_H$ are entire and identify every zero
  and its order. Exact spectral multiplicities must become exact zero
  multiplicities, including repeated eigenvalues.
- [ ] Use fixed $c,d$ with $d\ne0$ and normalization $D_H(c)=1$
  across the family. Prove the paired symmetry and state explicitly that
  the line $c+d\mathbb R$ is prescribed.
- [ ] Instantiate the finite-sector response theorem of §6.2 as a
  displacement estimate for the corresponding indexed zeros along the
  same line. Common zero locations at different parameter values must
  not be confused with stationary indexed levels.
- [ ] Distinguish compact-set convergence of products from quantitative
  approximation of individual zeros or clusters. Additional separation or
  contour hypotheses must be proved when they are used.

### 6.4. P4 — A confined Ammann–Beenker model and a finite intervention

The proposed first concrete application uses **vertices**, rather than tiles,
of an eightfold-symmetric Ammann–Beenker tiling, with edge length one and
the origin at a vertex with eight neighbors. Its algebraic cut-and-project
construction is described in
[Beenker's report](https://pure.tue.nl/ws/files/4269555/253166.pdf).
No named aperiodic tiling is currently formalized in Jules.

The model to construct is
```math
(H\psi)(x)
=(1+|x|^2)\psi(x)
+\frac1{16}\sum_{y\sim x}\bigl(\psi(x)-\psi(y)\bigr).
```

**Open geometric and operator obligations**

- [ ] Define the chosen infinite vertex set, its embedding and edge
  relation, including the window/boundary conventions in the
  cut-and-project construction. Verify the required central patch.
- [ ] Prove uniform discreteness, local finiteness and degree at most
  eight. Use the lifted $\mathbb Z^4$ coordinates to construct eight
  involutive matching colors by direction and coordinate parity, fixing
  sites whose partner is absent. Prove that these matchings represent
  exactly the chosen edge relation.
- [ ] Verify that the interaction is nonnegative and has norm at most
  one, so that the full operator has lower bound one on its natural
  domain. This example need not satisfy the stronger sufficient
  condition $V>\|B\|$ to be positive.
- [ ] Prove properness of $V(x)=1+|x|^2$ and a quantitative two-dimensional
  vertex-counting bound. Transfer the resulting onsite growth to
  full-spectrum summability using the verified comparison/transfer lemmas
  in §§4.46–4.48. This model's positive-Laplacian gap must be established
  separately from the stronger sufficient condition $v_0>\|B\|$.
- [ ] Verify compact-resolvent hypotheses at an appropriate real shift
  and verify the onsite lower bound and infinite vertex type needed to
  invoke the global ordered-spectrum existence result of §4.47.

**Open worked finite-sector application**

Let
```math
S=\{x:|x|\le2\},\qquad H_\tau=H+\tau P_S.
```

- [ ] Prove that $S$ is finite and that the intervention is a bounded,
  finite-rank positive perturbation.
- [ ] Using nonnegativity of the Laplacian, establish
  $H\ge5I-4P_S$ and derive the sharpened estimate
  ```math
  \frac{\tau}{2}
  \le\lambda_n(H_\tau)-\lambda_n(H)
  \le\tau,\qquad
  \lambda_n(H)\le3,\quad 0\le\tau\le4.
  ```
  The general norm-penalty estimate is now proved in §4.46. This concrete
  target still needs a stronger form bound exploiting Laplacian positivity
  and the verified geometric sector.
- [ ] Verify that the central vertex and its eight unit-distance neighbors
  give a nine-dimensional trial space with energy at most three.
  Consequently prove that the application controls at least nine levels
  counted with multiplicity, rather than an unspecified possibly empty
  energy window.
- [ ] Instantiate the entire products and obtain the corresponding
  indexed zero-displacement bounds on the prescribed line.
- [ ] Investigate whether the tiling's geometry permits a smaller
  observation/intervention set with a proved quantitative guarantee.
  This is a separate research question, not a consequence of
  aperiodicity or of the disk estimate.

All displayed model-specific conclusions in this subsection are targets to
verify, not results already checked in Lean. The model and the general
lifting argument do not by themselves establish mathematical novelty.

### 6.5. Local geometric defects and relative spectral products

**Target theorem: an exact finite determinant for the relative product**

For a verified finite-support perturbation
$H'=H+\iota_S K\iota_S^*$, establish the identity of §2.3:
```math
\frac{F_{H'}(z)}{F_H(z)}
=\frac{\det(I+K G_S(z))\det(I+K G_S(-z))}
       {\det(I+K G_S(0))^2}.
```

- [ ] Specify the allowed changes of site energies or couplings and
  prove their finite-support operator representation. If a geometric
  move changes the site set, construct and justify the identification
  used for the two Hilbert spaces.
- [ ] Verify self-adjointness, a strictly positive gap, compact resolvent
  and the summability assumptions for both operators.
- [ ] Construct the complex Green matrix using the interface of §6.1.
  Prove the determinant identity and its normalization, with an explicit
  common domain and meromorphic continuation statement.
- [ ] Track the difference of zero multiplicities through the relative
  identity, including shared zeros and pole cancellations.
- [ ] Relate finite-coordinate observation to the visibility of low
  eigenspaces in the compressed resolvent. Prove any residue-rank or
  nonvanishing statement that is used; do not assume that restriction
  injectivity already supplies the entire determinant theorem.
- [ ] Apply the result to an explicitly verified intervention or geometric
  change in the concrete model. State the resulting information about
  zero response with its actual parameter and energy range.

Finite-rank perturbation determinants are established operator theory, including
in work on infinite graphs; see
[Golinskii](https://doi.org/10.1080/03081087.2016.1155529).
The research contribution must be identified through a precise geometric
application or quantitative result beyond a relabeling of that theory.

### 6.6. Certified finite-patch approximation and zero response

A finite Green matrix still contains information about the infinite system.
This phase provides the missing approximation certificate.

- [ ] Define a finite-patch operator with explicit boundary conditions and
  its embedded resolvent. Preserve the distinction between truncating a
  fixed confined operator and changing the infinite-volume model.
- [ ] Bound the error of the Green matrix on specified compact sets away
  from spectral poles. Derive any exponential buffer estimate from
  verified locality and barrier assumptions, with explicit constants;
  do not assume a universal exponential rate.
- [ ] Propagate the matrix error to the relative determinant and the
  analytic products, controlling their normalizations.
- [ ] Certify zero counts in contours and intervals, with multiplicities.
  Individual displacement estimates require appropriate isolation
  hypotheses or certified clusters; uniform approximation alone must
  not be treated as a simple-root error estimate.
- [ ] Make the resulting error bounds small relative to the spectral
  scale of the proposed application. In statistical comparisons, fix the
  unfolding independently and control its amplification of spectral error.
- [ ] Produce a worked finite certificate for the concrete geometric
  application, separating proved error bounds from numerical evidence.

The intended result is a quantitative statement about the response of an
infinite system that can be assessed using finite data with a proved error.

### 6.7. Exploratory objectives: zero statistics and structural constraints

**Local statistics on the fixed line**

- [ ] Define the energy windows, symmetry sectors, normalization and
  averaging procedure for the zero statistics being compared.
- [ ] Investigate whether a specified model or geometric family has local
  correlations approaching a random-matrix law. A CUE/GUE bulk comparison
  targets the sine-kernel process after unfolding, not merely the
  mean density of zeros or one matching histogram.
- [ ] Analyze the operator's symmetry class. The current real model does
  not automatically provide unitary-class statistics; any magnetic
  extension requires complex couplings, verified self-adjointness and
  analysis of residual symmetries.
- [ ] Treat convergence of pair correlations, convergence of all local
  correlations and evidence from finite spectra as different claims.
  None follows from the prescribed line or from the relative-product
  identity.

**Separate long-term question: a line determined by structure**

- [ ] Define an analytically meaningful object from an independently
  specified geometric construction without encoding a desired zero line
  in its factors or an affine coordinate. Investigate whether a proved
  structural mechanism then forces its zeros onto a line.

This last question is distinct from the program using the prescribed line
$c+d\mathbb R$. It is exploratory, not a prerequisite for the response
theorem, and carries no asserted connection to the Riemann zeta function.

### 6.8. Independent statement verification and research-interest assessment

**Current selected result**

- [x] Select the first substantive observation milestone of §4.40:
  the geometric multiplicity bound for one low-energy real eigenspace.
  The single root Comparator configuration compares that theorem and
  sixteen supporting definitions/type abbreviations.
- [x] Supply the independent Challenge, the source-backed Solution and
  provenance metadata. The selected statement's comparison has been
  reported as passing Lean, NanoDa and con-ron; the complete source
  library remains a separate build obligation.
- [x] Distinguish the first identified source of the precise formal
  statement from the operator-theory and Mathlib background. The
  source classification does not certify mathematical priority.

**Assessment and future selection**

The source results of §§4.41–4.48 now include simultaneous observation,
total counting and an abstract finite-sector response. Their compilation does
not change the selected §4.40 statement, establish a concrete geometric
application or certify originality or independent research interest.

- [ ] Assess the selected result's research interest on its actual
  mathematical content and demonstrated uses. Its role in a larger
  program does not alone establish the significance of a standalone
  submission.
- [ ] Before a new flagship claim is formalized as a submission target,
  compare its precise hypotheses and conclusions with the relevant
  literature and identify the proposed contribution.
- [ ] Select a stronger response theorem only after its substantive
  source proof, geometric application and stated quantitative
  consequences have been verified. A planned consequence must not be
  described as part of the present submission.
- [ ] When the selected theorem actually changes, update PALOMAR.md,
  formalization.yaml, Challenge.lean and comparator.json consistently.
  Until then they continue to describe the existing §4.40 theorem.
- [ ] Use a public immutable 40-character commit SHA whose complete
  required Lean and Comparator checks pass. Mechanical verification,
  research-interest assessment and mathematical novelty are distinct.

**Maintenance rule:** document each new proved result in §4, its roadmap
entry and the canonical §5 module list. Mark a proof obligation complete only
after its source is imported by SpectralGeometry.lean and the full required
build passes.
