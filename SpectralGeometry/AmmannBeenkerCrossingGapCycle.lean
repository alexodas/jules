module

public import SpectralGeometry.AmmannBeenkerCrossingMultiplicity

public section

/-!
# A certified eight-cycle estimate for the proposed crossing gap

The central crossing block consists of an origin and two eight-site rings.
The ring-to-ring part acts through the sum of neighboring amplitudes:
  x_i ↦ x_i + x_(i+1), indices modulo eight.

The alternating ring mode lies in the kernel. The following polynomial
certificate shows that on vectors orthogonal to that mode, the cyclic
neighbor-sum map has squared norm at least 1/2 times the squared norm.

This is a finite algebraic ingredient, NOT YET a proof of the full
17-vertex central block bound or the infinite-operator gap.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Four-periodic amplitudes: removing the alternating direction gives
a particularly strong positive bound for the cyclic neighbor sums. -/
private theorem crossingPeriodicFourCycle_bound (a b c d : ℝ)
    (h : a - b + c - d = 0) :
    (1 / 2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤
      (a + b) ^ 2 + (b + c) ^ 2 + (c + d) ^ 2 + (d + a) ^ 2 := by
  have hs : b + d = a + c := by linarith
  have heq :
      (a + b) ^ 2 + (b + c) ^ 2 + (c + d) ^ 2 + (d + a) ^ 2 =
        2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) +
          2 * (a + c) * (b + d) := by ring
  rw [heq, hs]
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c,
    sq_nonneg d, sq_nonneg (a + c)]

/-- Four-antiperiodic amplitudes: a rational sum-of-squares certificate
implies a factor 1/2 lower bound (the sharp factor is 2 - sqrt 2). -/
private theorem crossingAntiperiodicFourCycle_bound (a b c d : ℝ) :
    (1 / 2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤
      (a + b) ^ 2 + (b + c) ^ 2 + (c + d) ^ 2 + (d - a) ^ 2 := by
  have heq :
      (a + b) ^ 2 + (b + c) ^ 2 + (c + d) ^ 2 + (d - a) ^ 2 =
        (1 / 2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) +
          (3 / 2 : ℝ) * (b + (2 / 3 : ℝ) * (a + c)) ^ 2 +
          (3 / 2 : ℝ) * (d + (2 / 3 : ℝ) * (c - a)) ^ 2 +
          (1 / 6 : ℝ) * (a ^ 2 + c ^ 2) := by ring
  rw [heq]
  nlinarith [sq_nonneg (b + (2 / 3 : ℝ) * (a + c)),
    sq_nonneg (d + (2 / 3 : ℝ) * (c - a)),
    sq_nonneg a, sq_nonneg c]

/-- Exact eight-cycle lower bound outside the alternating direction.
The alternating-sum hypothesis is crucial: without it the cyclic
neighbor-sum map has a nonzero kernel. -/
theorem crossingEightCycle_neighbor_sum_lower
    (a b c d e f g h : ℝ)
    (halt : a - b + c - d + e - f + g - h = 0) :
    (1 / 2 : ℝ) *
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 +
          e ^ 2 + f ^ 2 + g ^ 2 + h ^ 2) ≤
      (a + b) ^ 2 + (b + c) ^ 2 + (c + d) ^ 2 +
        (d + e) ^ 2 + (e + f) ^ 2 + (f + g) ^ 2 +
        (g + h) ^ 2 + (h + a) ^ 2 := by
  let p0 : ℝ := (a + e) / 2
  let p1 : ℝ := (b + f) / 2
  let p2 : ℝ := (c + g) / 2
  let p3 : ℝ := (d + h) / 2
  let m0 : ℝ := (a - e) / 2
  let m1 : ℝ := (b - f) / 2
  let m2 : ℝ := (c - g) / 2
  let m3 : ℝ := (d - h) / 2
  have hpalt : p0 - p1 + p2 - p3 = 0 := by
    dsimp [p0, p1, p2, p3]
    linarith [halt]
  have hp := crossingPeriodicFourCycle_bound p0 p1 p2 p3 hpalt
  have hm := crossingAntiperiodicFourCycle_bound m0 m1 m2 m3
  have hn :
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 +
          e ^ 2 + f ^ 2 + g ^ 2 + h ^ 2 =
        2 * (p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2 +
          m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2) := by
    dsimp [p0, p1, p2, p3, m0, m1, m2, m3]
    ring
  have he :
      (a + b) ^ 2 + (b + c) ^ 2 + (c + d) ^ 2 +
          (d + e) ^ 2 + (e + f) ^ 2 + (f + g) ^ 2 +
          (g + h) ^ 2 + (h + a) ^ 2 =
        2 * ((p0 + p1) ^ 2 + (p1 + p2) ^ 2 +
          (p2 + p3) ^ 2 + (p3 + p0) ^ 2 +
          (m0 + m1) ^ 2 + (m1 + m2) ^ 2 +
          (m2 + m3) ^ 2 + (m3 - m0) ^ 2) := by
    dsimp [p0, p1, p2, p3, m0, m1, m2, m3]
    ring
  rw [hn, he]
  linarith [hp, hm]

/-- The rational 1/24 target for the central-block spectral gap is
strictly below the lower bound delivered by the eight-cycle estimate
after scaling the neighbor sum by 1/16. -/
theorem crossingEightCycle_threshold :
    (1 / 24 : ℝ) ^ 2 < (1 / 16 : ℝ) ^ 2 * (1 / 2 : ℝ) := by
  norm_num


/-!
The rotationally invariant component of the 17-vertex central block has
three coordinates: the origin amplitude z, and the mean amplitudes u, v
on the first and second rings. Its squared norm and residual squared norm
are respectively
  z^2 + 8*u^2 + 8*v^2
and
  (d*z+u/2)^2 + (z+2*v)^2/32 + u^2/8,
where d = crossingEnergy-3/2 > 3.

The following estimate proves a squared lower bound 1/144 for that
three-coordinate sector. Combined with the eight-cycle estimate on the
zero-mean parts, this is sufficient for the targeted central-block
constant 1/24; the actual 17-coordinate orthogonal-decomposition
identity has not yet been formalized.
-/

/-- A rational, fully algebraic singular-value certificate for the
three-coordinate constant Fourier sector of the central crossing block. -/
theorem crossingCentralConstantMode_gap
    (d z u v : ℝ) (hd : 3 ≤ d) :
    (1 / 144 : ℝ) * (z ^ 2 + 8 * u ^ 2 + 8 * v ^ 2) ≤
      (d * z + u / 2) ^ 2 + (z + 2 * v) ^ 2 / 32 + u ^ 2 / 8 := by
  have hdplus : 0 ≤ d + 3 := by linarith
  have hdminus : 0 ≤ d - 3 := by linarith
  have hcoeff : 0 ≤ (d - 3) * (d + 3) := mul_nonneg hdminus hdplus
  have hnonneg : 0 ≤ (d - 3) * (d + 3) * z ^ 2 :=
    mul_nonneg hcoeff (sq_nonneg z)
  have hdz : 9 * z ^ 2 ≤ (d * z) ^ 2 := by
    nlinarith only [hnonneg]
  have hsum : (d * z) ^ 2 ≤ 2 * (d * z + u / 2) ^ 2 + u ^ 2 / 2 := by
    nlinarith only [sq_nonneg (d * z + u)]
  have hz : z ^ 2 ≤ (2 / 9 : ℝ) * (d * z + u / 2) ^ 2 +
      (1 / 18 : ℝ) * u ^ 2 := by
    nlinarith only [hdz, hsum]
  have hv : 8 * v ^ 2 ≤ 4 * (z + 2 * v) ^ 2 + 4 * z ^ 2 := by
    nlinarith only [sq_nonneg (2 * z + 2 * v)]
  nlinarith [sq_nonneg (d * z + u / 2), sq_nonneg (z + 2 * v),
    sq_nonneg u]

/-- The known exterior bound also certifies d > 3 for the actual model. -/
theorem crossingCentralConstantDiagonal_gt_three :
    (3 : ℝ) < crossingEnergy - 3 / 2 := by
  have h := crossingExteriorCoefficient_gt_two
  dsimp only [crossingEnergy] at *
  linarith

/-- Instantiate the algebraic three-coordinate gap at the exact crossing. -/
theorem crossingCentralConstantMode_concrete (z u v : ℝ) :
    (1 / 144 : ℝ) * (z ^ 2 + 8 * u ^ 2 + 8 * v ^ 2) ≤
      ((crossingEnergy - 3 / 2) * z + u / 2) ^ 2 +
        (z + 2 * v) ^ 2 / 32 + u ^ 2 / 8 :=
  crossingCentralConstantMode_gap _ _ _ _
    (le_of_lt crossingCentralConstantDiagonal_gt_three)

end
end SpectralGeometry.AmmannBeenker
