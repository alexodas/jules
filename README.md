# Theorem C — Infinite tilings and zeros on a prescribed line

This is an experimental, AI-generated Lean 4 + Mathlib formalization of a
mathematical construction suggested by **Alessandro Odasso**.

Alessandro Odasso is **not a mathematician**. He is interested in experimenting
with large language models (LLMs) to understand how powerful they are, including
whether they can help develop and formally check mathematical arguments.

## What the theorem means, in simple English

Imagine an infinite tiling. Each tile is assigned a **positive geometric
energy** `qₙ`, perhaps derived from its centroid, orientation or other features.

Choose any point `center` and nonzero complex direction `direction`.
For every tile, put two spectral zeros at

`center + direction × qₙ` and `center − direction × qₙ`.

The key is to combine the two symmetric factors into one *paired canonical
factor*:

```text
1 − [((s − center) / direction)² / qₙ²]
```

The resulting infinite product is well-behaved when its factors approach 1
fast enough. The mathematical admissibility condition used in Lean is precise:
**on every compact set**, the absolute deviations of these factors from 1
are bounded by a summable real sequence.

Under this assumption, Mathlib proves uniform convergence of the finite
products on each compact set. A second theorem proves that the resulting
infinite product has **no zero outside the chosen line**.

For `center = 1/2` and `direction = i`, this line is the critical line
`Re(s) = 1/2`.

**Important:** The function constructed here is **not** the Riemann zeta
function. The theorem therefore **does not prove the Riemann hypothesis**.

## Scope and limitations

- This first formalization concerns a *sequence of positive geometric
  energies*, not a full formal model of tiling adjacency or coverings.
- The proof formalizes the paired regularized product above. It does
  **not** yet formalize the exponential genus-two product
  `(1 − u²/Q) exp(u²/Q)` considered in the original conversation.
- The admissibility condition is a *summable compact majorant*, not
  a restatement of product convergence; deriving it from the more
  elementary condition `∑ 1/qₙ² < ∞` is a future lemma.
- The central zero-localization theorem proves the absence of zeros off
  the line. Showing explicitly that every prescribed factor zero remains a
  zero of the total product is a separate follow-up.
- The mathematical ideas of canonical products and self-adjoint spectra
  are classical. This repository does not claim to have discovered a new
  theorem about the Riemann zeta function.

## Checking the proof

The repository contains a GitHub Actions workflow which installs the
Lean toolchain listed in `lean-toolchain`, downloads Mathlib via Lake,
and checks the file:

```sh
lake update
lake exe cache get
lake build
```

A green CI run is the condition for claiming that this Lean code was
machine-checked. No unverified source text is claimed to be proved.

## Attribution and AI disclosure

**Prompt / research question:** Alessandro Odasso (non-mathematician,
LLM experimentation).

**Mathematical explanation and formalization draft:** AI-generated with
OpenAI ChatGPT, with Mathlib as the proof library.

This is an exploration of what LLMs can and cannot do in formal mathematics.
The AI-generated content should be evaluated critically, and passing
the Lean kernel is not evidence of mathematical novelty or of RH.


## Geometric example: an infinite square tiling

The **same** `InfiniteTilings.lean` file now also defines unit square cells
indexed by `ℤ × ℤ`. It proves:

1. Every point in the real plane belongs to a closed unit square.
2. If a point belongs to the **open interiors** of two squares, the
   squares have the same integer coordinates.
3. An explicit enumeration `gridPoint : ℕ → ℤ × ℤ` visits every
   integer lattice point, so the enumerated cells cover the plane.
4. A positive *squared max-norm shell energy* assigned to each
   enumerated square has summable inverse squares.
5. Therefore this concrete energy family satisfies the earlier
   compact-majorant admissibility hypothesis, and Theorem C applies.

The energy is based on the **nonnegative integer encodings** of the two
signed lattice coordinates: if they are `a,b`, then
`q = (max(a,b) + 1)²`. This is deliberately **not** Euclidean
centroid distance and **not** a proof of a convergence estimate for
that different energy choice.

The point of the new example is an end-to-end implication for one
explicit infinite planar square tiling: geometry, positivity,
summability, uniform convergence and line localization. It does
not establish any identification with Riemann zeros.

A green GitHub Actions build confirms these statements for
the precise Lean declarations shown in the source file.


## New experiment: physical Euclidean centroid energy

This extension, still in the **same** \`InfiniteTilings.lean\` source file,
replaces the encoded shell energy in a separate construction with a
genuinely Euclidean quantity. For a unit square indexed by integers
\`(m,n)\`, its centroid is \`(m + 1/2, n + 1/2)\`. The energy is

\`\`\`text
q(m,n) = 1 + (m + 1/2)^2 + (n + 1/2)^2 .
\`\`\`

The intended theorem proves the convergence of the sum of \`1/q(m,n)^2\`
over the full integer plane, then transfers that summability to the
canonical product and the affine-line localization theorem.

The mathematical estimate is

\`\`\`text
1 / (1 + x^2 + y^2)^2 ≤ 1 / ((1 + x^2)(1 + y^2)).
\`\`\`

The right side separates into two one-dimensional, summable factors.
This is a genuine geometric justification of the analytic hypotheses,
rather than a recurrence adjusted to reproduce particular zeta zeros.

The same approach should subsequently transfer to rectangles and
invertible affine images of square grids, and then—after substantially
more work—to suitably separated aperiodic tilings.

**Verification rule:** a theorem added by an AI is called
"machine-checked" here only after the GitHub Actions Lean/Mathlib
build passes on the corresponding commit. Nothing in these results
identifies the constructed function with the Riemann zeta function.


## Rectangles, shears, and all invertible affine lattices

The same \`InfiniteTilings.lean\` now treats every real matrix
\`[[a,b],[c,d]]\` with nonzero determinant \`a*d - b*c\`, acting on the
centroids of the infinite square grid. The transformed tiles are
parallelograms, with rectangles as the diagonal-matrix special case.

For every lattice point \`p\` with square centroid \`(x,y)\`, we assign

\`\`\`text
q(p) = 1 + (a*x + b*y)^2 + (c*x + d*y)^2.
\`\`\`

The new central proof is a quantitative comparison: invertibility gives
a constant \`C > 0\` (independent of the lattice point) such that

\`\`\`text
1 + x^2 + y^2 ≤ C * q(p).
\`\`\`

This transfers the already certified square-centroid convergence theorem
to every invertible linear deformation. It implies convergence of the
paired infinite product and localization of **all** its zeros to any
prescribed affine complex line.

This covers arbitrary nondegenerate rectangles, sheared rectangular
grids, and general parallelogram lattices *analytically*. It does not
claim that their spectra equal the Riemann zeta spectrum.

The result is AI-generated from Alessandro Odasso's experimental
question, and is called certified only when Lean/Mathlib GitHub Actions
passes on the precise commit.

The affine-grid extension also proves that transformed parallelogram cells **cover the entire plane** and that distinct cells have **disjoint open interiors**, using an explicit inverse for the nonsingular matrix. Thus both the tiling geometry and the associated spectral-product summability are checked in one Lean source file.


## Beyond globally affine grids: independently shifted rows

The same \`InfiniteTilings.lean\` file now formalizes a larger family
of planar square tilings. Each row indexed by integer \`n\` is shifted
horizontally by an independently chosen real number \`offset(n)\`. The
function need **not** repeat, and the positions are **not** required
to be a common linear image of the original grid.

The geometric claims are formal:

- The shifted square cells still cover all of the real plane.
- Different cells have disjoint open interiors.
- The centroids of distinct cells are separated by Euclidean
  distance at least one, for **arbitrary** row offsets.
- When all offsets satisfy \`|offset(n)| ≤ 1/2\`, their Euclidean
  squared-distance energy is comparable with the original square
  centroid energy. This proves summability without assuming it.
- Consequently the canonical product converges compact-uniformly
  and its zeros stay on an arbitrarily prescribed affine complex line.

**Precise limitation:** Such stripwise-shifted tilings always retain
horizontal translation symmetry by one unit. They may have *no
periodicity across rows*, but they are **not fully aperiodic tilings**
in the strict sense of having no nonzero translational period.
A general theorem for all uniformly separated, density-controlled
point sets, and genuinely aperiodic tilings, remains future work.

This is a classical type of geometric/spectral argument formalized
by AI in response to a research question from Alessandro Odasso,
who is not a mathematician and is exploring LLM capabilities.
It does **not** prove the Riemann hypothesis.


## General criterion: irregular centroid configurations

The extension in the **same** \`InfiniteTilings.lean\` file treats
an arbitrary family of positive energies \`q(m,n)\`, indexed by all
integer pairs. The theorem applies whenever there is one constant
\`C > 0\` such that, for every \`(m,n)\`,

\`\`\`text
1 + (m + 1/2)² + (n + 1/2)² <= C * q(m,n).
\`\`\`

This *coercive growth* inequality forces convergence of
\`sum 1/q(m,n)^2\` and hence the canonical-product hypotheses of
Theorem C.

A concrete corollary allows every point \`P(m,n)\` to move independently
from its original lattice-square centroid by at most \`1/2\` along
**each** coordinate. Its Euclidean energy is
\`q(m,n) = 1 + P(m,n).x² + P(m,n).y²\`.
A proved estimate shows that the coercive criterion holds with
\`C = 2\`. No periodicity, fixed pattern or common affine transformation
is required for the convergence and zero-localization conclusion.

**Important scope distinction:** These are *point configurations*
(or possible centroid arrangements). Arbitrary displacements alone
do not prove that actual polygonal tiles with those centroids cover
the plane or have nonoverlapping interiors. Nor is this a theorem
for every uniformly separated point set: such a generalization would
require a separate counting/packing argument. Also the current
bounded-displacement criterion itself does not guarantee distinct
points at the endpoint \`1/2\`; a strict smaller displacement could
be used for separation.

As in earlier steps, the AI-generated mathematics is exploratory
work prompted by Alessandro Odasso, a non-mathematician exploring the
capabilities and limitations of large language models. None of these
constructions identifies the product's zeros with those of Riemann's
zeta function or proves the Riemann hypothesis.


## First geometrically translation-aperiodic infinite tiling

The latest single-file Lean experiment defines an **actual infinite tiling**
by axis-aligned rectangles. Start with all unit squares of the standard
integer grid. Replace the two adjacent squares at indices \`(0,0)\`
and \`(1,0)\` by two rectangles filling precisely their old union:
one with width \`1/2\` and one with width \`3/2\`. Every other unit
square remains unchanged.

The source file formalizes and proves:

- The new rectangular cells **cover the whole real plane**.
- Distinct rectangles have **disjoint open interiors**.
- Exactly one rectangle has width \`3/2\`.
- A translation that maps every rectangle to a member of the same
  tiling (preserving its size and lower-left corner geometry) must
  be the **zero** translation.
- Every rectangle's centroid is within \`1/2\` in each coordinate
  of its original square centroid. Therefore the inverse-squared
  Euclidean centroid energy is summable, and Theorem C applies:
  the associated canonical product has all its zeros on a
  prescribed affine complex line.

**Important distinction:** This is a specific **nonperiodic
configuration of tiles**, but it is a *finite defect of a periodic
tiling*. It is NOT a Penrose-type, repetitive, intrinsically
aperiodic tile set: the same shapes can be arranged in other ways,
and the single defect is not a proof of nonperiodicity under other
mathematical conventions (such as strong aperiodicity of tile sets).
It is a genuine example with no nonzero translational symmetry
of the given infinite geometric tiling.

The source is **AI-generated** following Alessandro Odasso's
question; he is not a mathematician, and his purpose is to
experiment with the capabilities and limitations of LLMs.
This classical geometric-spectral construction has **no proved
identification with Riemann's zeta function** and does not
establish the Riemann hypothesis.


## New direction: operators that sense geometry and orientation

Earlier canonical products put their zeros on a chosen complex line by
construction. They use chiefly centroid-derived positive energies, not
fine tile structure. The new single-file Lean section **does not** use
those products to derive its eigenvalues.

For an arbitrary **finite** set of tile vertices, it defines a
weighted adjacency operator and proves a finite self-adjointness
identity whenever neighbor relations and real edge weights are
symmetric. This is a mathematical framework for geometry-dependent
spectral analysis; no periodicity of the underlying tile patch is
needed.

A **concrete two-tile example** is taken from the previously verified
infinite rectangle tiling. The adjacent special rectangles have widths
\`1/2\` and \`3/2\` and share a vertical edge. A binary *orientation mark*
is added to each tile. With the explicitly chosen interaction law
\`1\` for matching marks and \`2\` for opposing marks, multiplied by the
two widths' product \`3/4\`, the symmetric adjacency operator is

\`\`\`text
H(u,v) = (w v, w u).
\`\`\`

Its **entire real eigenvalue set** is exactly \`{w, -w}\`.
Matching marks yield eigenvalues \`±3/4\`, opposite marks \`±3/2\`.
Lean proves in particular that \`3/2\` is an eigenvalue in the
opposed-mark case but **not** in the aligned-mark case.

This demonstrates an explicit dependency of eigenvalues on the
local geometry and orientation **marking**, not merely on centroids.
However the interaction law itself is chosen as a model, not deduced
uniquely from geometry. Rectangles are intrinsically achiral, so
the binary marks must not be confused with actual tile chirality.
This is still a finite example, not yet an infinite Penrose/Farey
spectral operator. Self-adjointness and real eigenvalues are expected
linear-algebra facts, not evidence for the Riemann hypothesis.
No identification with Riemann zeta zeros is claimed.

As before, source and proofs are **AI-generated** in response to
Alessandro Odasso (not a mathematician) experimenting with LLM
capabilities and limitations. Claims of Lean verification apply only
to commits that pass the CI build.


## Bridging operator eigenvalues to the canonical energies Q

This section formalizes the **precise bridge** requested between the
earlier line-zero products and the later geometry-sensitive operators.
Let \`q₀(n) > 0\` be a geometrically justified growth envelope with

\`\`\`text
sum_n 1/q₀(n)^2 < infinity.
\`\`\`

For any real spectral levels \`eig(n)\`, define

\`\`\`text
Q(n) = q₀(n) * (1 + eig(n)^2).
\`\`\`

Then \`Q(n) >= q₀(n)\` and the inverse-square summability condition
continues to hold. Thus the paired canonical product

\`\`\`text
D(s) = product_n [1 - ((s-center)/(direction*Q(n)))^2]
\`\`\`

is locally uniformly convergent and has **no zeros outside** the
chosen complex affine line \`center + direction*real\`. The new Lean
theorems also prove that \`center + direction*Q(n)\` is actually a zero
of the entire infinite product for **each** index \`n\`. This is a
stronger bridge than a mere zero-localization implication.

For a concrete application, \`q₀(n)\` is the previously formalized
physical square-centroid energy, and \`eig(n)\` is a verified positive
eigenvalue of the two-rectangle local adjacency operator, with an
independently chosen pair of binary orientation marks at each index.
Aligned markings give \`eig = 3/4\` and multiplicative correction
\`25/16\`; opposite markings give \`eig = 3/2\` and correction \`13/4\`.
Thus geometric and orientation choices change the levels Q and their
corresponding zeros **along the line**.

**Precise limitations:** The multiplication by \`q₀\` is deliberate and
essential to the proven convergence; spectral eigenvalues alone do
not establish the required growth. The operators in the concrete
application are independent local two-tile motifs, **not** one
self-adjoint operator on the infinite tiling. The paired factors still
force their zero line **by construction**; the spectral input changes
zero positions, not the selection of that line. Coincident eigenlevels,
multiplicities and their statistical laws have not been identified with
Riemann zeta zeros, nor has the Riemann hypothesis been proved.

This is AI-generated formal exploration prompted by Alessandro Odasso,
who is not a mathematician and is studying what LLMs can and cannot do.
Verification claims apply only after successful Lean/Mathlib CI.
