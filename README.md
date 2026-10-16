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
