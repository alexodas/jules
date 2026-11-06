# Palomar candidate — exact multiplicity of a compact crossing on an infinite octagonal graph

The principal theorem is `SpectralGeometry.AmmannBeenker.crossingEigenspace_finrank`.
The companion `SpectralGeometry.AmmannBeenker.crossing_eigenvector_representation`
identifies every vector in that eigenspace. Both are proved in
[AmmannBeenkerCrossingMultiplicity.lean](SpectralGeometry/AmmannBeenkerCrossingMultiplicity.lean)
and described in [README §4.78](README.md#478-central-support-and-exact-multiplicity-of-the-infinite-crossing).

## Mathematical statement

Vertices are the admitted integer lifts in the centered open octagonal
cut-and-project window of README §4.68. The boundary is excluded; two
vertices are adjacent when their lifts differ by a signed coordinate step.
On real $\ell^2$ of this infinite graph, let $p(v)$ be physical position,
$V(v)=1+|p(v)|^2$, and $D(V)=\{x\in\ell^2:Vx\in\ell^2\}$. Let $A$ be the
eight neighbors of the origin. On $D(V)$ define
```math
(K_t x)(v)=(V(v)+t\,\mathbf{1}_A(v))x(v)
  +\tfrac1{16}\sum_{w\sim v}\bigl(x(v)-x(w)\bigr).
```
The alternating states $a,b$ have amplitudes $+1,-1$ in cyclic order on
their respective eight-site rings and vanish elsewhere. Their first sites
are $A_0=(1,0,0,0)$ and $B_0=(1,1,0,0)$ in lift coordinates. The source
proves that their eigenvalues are $35/16+t$ and $13/4+\sqrt2$, respectively.
Set $t_*=17/16+\sqrt2$ and $E_*=13/4+\sqrt2$. The selected conclusions are
```math
\dim_{\mathbb R}\ker(K_{t_*}-E_* I)=2,\qquad
K_{t_*}x=E_*x\ \Longrightarrow\ x=x(A_0)a+x(B_0)b\quad(x\in D(V)).
```
Thus, identifying domain vectors with their images in $\ell^2$, the kernel
is precisely $\operatorname{span}_{\mathbb R}\{a,b\}$. Support is a
conclusion: no eigenvector at this energy can extend beyond the two rings.

## Why the infinite graph matters

Two independent compact eigenvectors would only give a lower bound of two.
Even a complete calculation on a finite patch would not rule out another
eigenvector with an exterior component. The proof does rule this out.
Let $S=\{v:|p(v)|\le2\}$, consisting of the origin and the two rings, and
write $x=u+q$ with $u=P_Sx$. For $L=K_{t_*}-E_* I$, locality of the first
ring, the central block identity and symmetry give
```math
\langle q,Lq\rangle=\langle u,Lu\rangle=(3/2-E_*)|u(0)|^2\le0.
```
The exterior onsite barrier and the nonnegative interaction also give
$(3/4+\sqrt2)\|q\|^2\le\langle q,Lq\rangle$, hence $q=0$. The central
block retains the full graph degrees, including edges to the exterior;
its kernel gives precisely the two alternating directions. The amplitudes
at the two first sites give a linear equivalence with $\mathbb R^2$.

## Research interest, sources and limits

For researchers studying localization in quasicrystals, the question is
whether two familiar local patterns account for a whole spectral level, or
merely coexist with other states at the same energy. The theorem answers
that question exactly for a specified confined operator on an infinite
octagonal graph. The Comparator-selected result may also interest theoretical
condensed-matter physicists studying compact localized states and
quasicrystal localization: beyond constructing two degenerate compact modes,
it excludes any additional eigenstate at their energy, including one
extending outside the central finite patch. This classification **may be
new for this model**. Priority has not been established.

- M. Ö. Oktel, [*Strictly localized states in the octagonal Ammann–Beenker
  quasicrystal*](https://doi.org/10.1103/PhysRevB.104.014204), §IV (2021):
  source of the type-A and type-B patterns for the vertex tight-binding
  model. The patterns themselves are not claimed as new.
- M. Röntgen, C. V. Morfonios and P. Schmelcher, [*Compact localized states
  and flat bands from local symmetry partitioning*](https://doi.org/10.1103/PhysRevB.97.035161)
  (2018): background on constructing and tuning compact states by local symmetry.
- F. P. M. Beenker, [*Algebraic theory of non-periodic tilings of the plane
  by two simple building blocks: a square and a rhombus*](https://pure.tue.nl/ws/files/4269555/253166.pdf)
  (1982): geometric background.

The Comparator-selected result concerns the centered graph, the quadratic
potential, the specified ring intervention, and one crossing energy. Its
exact-multiplicity statements do not themselves assert a spectral gap.
Separately, the full-project theorem
`crossingGapCandidate_no_other_realSpectrum`
([README §4.79](README.md#479-a-conservative-quantitative-real-spectral-gap-at-the-crossing))
certifies that no other point of the real bounded-inverse spectrum of this
same unperturbed infinite operator lies within the closed radius $1/128$
of $E_*$. That conservative isolation bound is **not** an additional
Comparator-selected statement. A quantitative law for the eigenvalue
that may move under a one-edge change remains open. The exterior energy
estimate above, on its own, is not the quantitative gap proof.

## Human origin and AI-assisted development

Alessandro Odasso originated the informal project idea, directs the work
and is the responsible maintainer. He does not identify as a mathematician;
his stated interest is exploring LLMs in scientific research. According to
his account, OpenAI GPT-6 assisted throughout the GitHub/Lean development.
No human mathematical peer review or exhaustive priority assessment is claimed.
[formalization.yaml](formalization.yaml) records the contributor roles,
sources and correspondence between the statements and the Lean declarations.

## Independent statement verification

[Challenge](Challenge.lean) imports only Mathlib and specifies the graph,
operator, domain, two compact modes, sites and eigenspace. [Solution](Solution.lean)
imports the substantive proof module. [Comparator](comparator.json) selects
the two conclusions above and three proposition witnesses used to define
the model: `admitted_zero`, `mate_involutive` and `centralLift_admitted`.
Only these five statements have placeholders in Challenge; all are proved
in the source. Definitions are compared transitively with no definition
holes. Challenge groups declarations by source module to preserve the names
of Lean's generated proof terms. The independent checks use Lean and the
bundled NanoDa and con-ron kernels; the full library is built separately.

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

Use a public immutable commit SHA with all checks passing. Preparing the
package does not submit or register a result.
