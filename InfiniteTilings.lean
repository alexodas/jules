import Mathlib

/-!
# Theorem C: line-localized zeros of an infinite canonical product

A family of positive geometric energies `q n` is called admissible
when the paired factors have a summable majorant on each compact set.
The paired factor `1 - ((s - center) / direction)^2 / (q n)^2`
is a regularized product: the potentially divergent first-order terms
cancel between the two roots.

This module does NOT identify its zeros with the zeros of Riemann's zeta.
-/

open Filter
open scoped BigOperators

namespace InfiniteTilings

noncomputable section

/-- The perturbation of 1 in the paired canonical factor. -/
def perturb (q : ℕ → ℝ) (center direction : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  -(((s - center) / direction) ^ 2 / ((q n : ℂ) ^ 2))

/-- A factor corresponding to the symmetric geometric levels `±q n`. -/
def factor (q : ℕ → ℝ) (center direction : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  1 + perturb q center direction n s

/-- The infinite paired (regularized) product. -/
def canonicalProduct (q : ℕ → ℝ) (center direction : ℂ) (s : ℂ) : ℂ :=
  ∏' n : ℕ, factor q center direction n s

/--
An *admissible* energy family has positive energies and a summable
majorant for the deviations of the canonical factors from 1 on
every compact set. This is a checkable normal-convergence condition,
rather than an assumption that the product already converges.

For 2D tiling examples, the natural sufficient analytic bound is
`∑ n, (q n)⁻² < ∞`; establishing that implication is separate.
-/
structure Admissible (q : ℕ → ℝ) (center direction : ℂ) : Prop where
  positive : ∀ n, 0 < q n
  compactMajorant :
    ∀ K : Set ℂ, IsCompact K →
      ∃ b : ℕ → ℝ, Summable b ∧
        ∀ n s, s ∈ K → ‖perturb q center direction n s‖ ≤ b n

/-- A compact-uniform convergence theorem for the infinite product. -/
theorem product_uniform_on_compact
    {q : ℕ → ℝ} {center direction : ℂ}
    (h : Admissible q center direction)
    (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun n s => factor q center direction n s)
      (canonicalProduct q center direction) K := by
  obtain ⟨b, hb, hbound⟩ := h.compactMajorant K hK
  unfold factor canonicalProduct
  exact hb.hasProdUniformlyOn_one_add hK
    (Filter.Eventually.of_forall (fun n s hs => hbound n s hs))
    (fun n => by
      apply Continuous.continuousOn
      unfold perturb
      fun_prop)

/-- Each factor can vanish only on the given affine complex line. -/
theorem factor_zero_on_line
    {q : ℕ → ℝ} {center direction s : ℂ}
    (h : Admissible q center direction)
    (hd : direction ≠ 0)
    (n : ℕ)
    (hz : factor q center direction n s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) := by
  have hqn : (q n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (h.positive n))
  have hfrac :
      ((s - center) / direction) ^ 2 / ((q n : ℂ) ^ 2) = 1 := by
    have heq : 1 - ((s - center) / direction) ^ 2 / ((q n : ℂ) ^ 2) = 0 := by
      simpa [factor, perturb, sub_eq_add_neg] using hz
    exact (sub_eq_zero.mp heq).symm
  have hsq : ((s - center) / direction) ^ 2 = ((q n : ℂ) ^ 2) := by
    simpa using (div_eq_iff (pow_ne_zero 2 hqn)).mp hfrac
  have hroots :
      (((s - center) / direction) - (q n : ℂ)) *
        (((s - center) / direction) + (q n : ℂ)) = 0 := by
    calc
      _ = ((s - center) / direction) ^ 2 - ((q n : ℂ) ^ 2) := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hroots with hplus | hminus
  · have heq : (s - center) / direction = (q n : ℂ) :=
      sub_eq_zero.mp hplus
    have hm := (div_eq_iff hd).mp heq
    refine ⟨q n, ?_⟩
    calc
      s = center + (s - center) := by ring
      _ = center + (q n : ℂ) * direction := by rw [hm]
      _ = center + direction * (q n : ℂ) := by ring
  · have heq : (s - center) / direction = -(q n : ℂ) :=
      add_eq_zero_iff_eq_neg.mp hminus
    have hm := (div_eq_iff hd).mp heq
    refine ⟨-(q n), ?_⟩
    calc
      s = center + (s - center) := by ring
      _ = center + (-(q n : ℂ)) * direction := by rw [hm]
      _ = center + direction * ((-(q n) : ℝ) : ℂ) := by push_cast; ring

/--
**Theorem C (zero localization).** The infinite regularized product
cannot have any zero outside the line selected by the center and direction.
This is not an assertion about Riemann's zeta.
-/
theorem theoremC_zero_localization
    {q : ℕ → ℝ} {center direction s : ℂ}
    (h : Admissible q center direction)
    (hd : direction ≠ 0)
    (hz : canonicalProduct q center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) := by
  by_contra hn
  have hnonzero : ∀ n : ℕ, 1 + perturb q center direction n s ≠ 0 := by
    intro n hzero
    apply hn
    exact factor_zero_on_line h hd n (by simpa [factor] using hzero)
  obtain ⟨b, hb, hbound⟩ :=
    h.compactMajorant ({s} : Set ℂ) isCompact_singleton
  have hsum : Summable (fun n : ℕ => ‖perturb q center direction n s‖) :=
    Summable.of_norm_bounded hb (fun n => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        hbound n s (by simp))
  exact (tprod_one_add_ne_zero_of_summable hnonzero hsum)
    (by simpa [canonicalProduct, factor] using hz)


/-! ## A concrete infinite square grid -/

/-- A unit square with lower-left corner at the integer lattice point `p`. -/
def squareCell (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | (p.1 : ℝ) ≤ z.1 ∧ z.1 ≤ (p.1 : ℝ) + 1 ∧
       (p.2 : ℝ) ≤ z.2 ∧ z.2 ≤ (p.2 : ℝ) + 1}

/-- The open interior of a unit grid square. -/
def squareInterior (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | (p.1 : ℝ) < z.1 ∧ z.1 < (p.1 : ℝ) + 1 ∧
       (p.2 : ℝ) < z.2 ∧ z.2 < (p.2 : ℝ) + 1}

/-- Every point of the real plane belongs to some unit square. -/
theorem squareCell_covers_plane (z : ℝ × ℝ) :
    ∃ p : ℤ × ℤ, z ∈ squareCell p := by
  refine ⟨(⌊z.1⌋, ⌊z.2⌋), ?_⟩
  exact ⟨Int.floor_le z.1, le_of_lt (Int.lt_floor_add_one z.1),
    Int.floor_le z.2, le_of_lt (Int.lt_floor_add_one z.2)⟩

/-- Different grid squares have disjoint open interiors. -/
theorem squareInterior_unique
    {p q : ℤ × ℤ} {z : ℝ × ℝ}
    (hp : z ∈ squareInterior p) (hq : z ∈ squareInterior q) : p = q := by
  change (p.1 : ℝ) < z.1 ∧ z.1 < (p.1 : ℝ) + 1 ∧
    (p.2 : ℝ) < z.2 ∧ z.2 < (p.2 : ℝ) + 1 at hp
  change (q.1 : ℝ) < z.1 ∧ z.1 < (q.1 : ℝ) + 1 ∧
    (q.2 : ℝ) < z.2 ∧ z.2 < (q.2 : ℝ) + 1 at hq
  have h1 : p.1 < q.1 + 1 := by
    exact_mod_cast (lt_trans hp.1 hq.2.1)
  have h2 : q.1 < p.1 + 1 := by
    exact_mod_cast (lt_trans hq.1 hp.2.1)
  have h3 : p.2 < q.2 + 1 := by
    exact_mod_cast (lt_trans hp.2.2.1 hq.2.2.2)
  have h4 : q.2 < p.2 + 1 := by
    exact_mod_cast (lt_trans hq.2.2.1 hp.2.2.2)
  have heq1 : p.1 = q.1 := by omega
  have heq2 : p.2 = q.2 := by omega
  exact Prod.ext heq1 heq2

/--
A concrete enumeration of *all* integer lattice points. It is built
from Mathlib's natural-number pairing and integer encoding.
-/
def gridPoint (n : ℕ) : ℤ × ℤ :=
  (Equiv.intEquivNat.symm (Nat.unpair n).1,
   Equiv.intEquivNat.symm (Nat.unpair n).2)

theorem gridPoint_surjective (p : ℤ × ℤ) :
    ∃ n : ℕ, gridPoint n = p := by
  refine ⟨Nat.pair (Equiv.intEquivNat p.1) (Equiv.intEquivNat p.2), ?_⟩
  simp [gridPoint]

/-- The enumerated square grid really covers the entire plane. -/
theorem enumerated_squares_cover (z : ℝ × ℝ) :
    ∃ n : ℕ, z ∈ squareCell (gridPoint n) := by
  obtain ⟨p, hp⟩ := squareCell_covers_plane z
  obtain ⟨n, hn⟩ := gridPoint_surjective p
  exact ⟨n, hn.symm ▸ hp⟩

/-!
## A geometric energy with a provably summable inverse square

The integer grid is enumerated by `Nat.unpair`. For the two nonnegative
encoded coordinates `a,b`, choose the squared max-norm shell
`(max a b + 1)^2`. The pairing map satisfies
`n < (max a b + 1)^2`, which allows direct comparison with a
classical convergent p-series. This is a shell energy associated with
the grid indexing; it is **not** the Euclidean squared centroid norm.
-/

/-- Squared max-norm shell energy of a square in the enumerated grid. -/
def squareGridEnergy (n : ℕ) : ℝ :=
  (((max (Nat.unpair n).1 (Nat.unpair n).2 + 1) ^ 2 : ℕ) : ℝ)

theorem squareGridEnergy_pos (n : ℕ) : 0 < squareGridEnergy n := by
  unfold squareGridEnergy
  exact_mod_cast (pow_pos (Nat.succ_pos _) 2)

theorem squareGridEnergy_grows (n : ℕ) :
    (n : ℝ) + 1 ≤ squareGridEnergy n := by
  have hn : n < (max (Nat.unpair n).1 (Nat.unpair n).2 + 1) ^ 2 := by
    simpa only [Nat.pair_unpair] using
      (Nat.pair_lt_max_add_one_sq (Nat.unpair n).1 (Nat.unpair n).2)
  have hn' : n + 1 ≤ (max (Nat.unpair n).1 (Nat.unpair n).2 + 1) ^ 2 :=
    Nat.succ_le_iff.mpr hn
  have hnreal : (((n + 1 : ℕ) : ℝ) ≤ squareGridEnergy n) := by
    change ((n + 1 : ℕ) : ℝ) ≤
      (((max (Nat.unpair n).1 (Nat.unpair n).2 + 1) ^ 2 : ℕ) : ℝ)
    exact_mod_cast hn'
  simpa only [Nat.cast_add, Nat.cast_one] using hnreal

/-- Geometry implies the summability needed by the canonical product. -/
theorem squareGridEnergy_inv_sq_summable :
    Summable (fun n : ℕ => 1 / (squareGridEnergy n) ^ 2) := by
  have hseries : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa [Nat.cast_add] using
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 hseries
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hshift
  show 1 / (squareGridEnergy n) ^ 2 ≤ 1 / ((n : ℝ) + 1) ^ 2
  gcongr
  exact squareGridEnergy_grows n

/--
Convert a summable sequence of inverse squared energies into the
compact-majorant hypothesis of Theorem C.
-/
theorem admissible_of_inv_sq_summable
    {q : ℕ → ℝ} (hq : ∀ n, 0 < q n)
    (hsum : Summable (fun n => 1 / (q n) ^ 2))
    (center direction : ℂ) : Admissible q center direction := by
  refine ⟨hq, ?_⟩
  intro K hK
  have hcont : Continuous (fun s : ℂ => ((s - center) / direction) ^ 2) := by
    fun_prop
  obtain ⟨C, hC⟩ :=
    (hK.image hcont).isBounded.exists_norm_le
  refine ⟨fun n => C * (1 / (q n) ^ 2), hsum.mul_left C, ?_⟩
  intro n s hs
  have hden : ‖((q n : ℂ) ^ 2)‖ = (q n) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq n)]
  have hnorm :
      ‖perturb q center direction n s‖ =
        ‖((s - center) / direction) ^ 2‖ * (1 / (q n) ^ 2) := by
    rw [perturb, norm_neg, norm_div, hden]
    ring
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right (hC _ ⟨s, hs, rfl⟩) (by positivity)

/-- A genuine infinite square-grid energy is admissible without assuming it. -/
theorem squareGridEnergy_admissible (center direction : ℂ) :
    Admissible squareGridEnergy center direction :=
  admissible_of_inv_sq_summable squareGridEnergy_pos
    squareGridEnergy_inv_sq_summable center direction

/--
**Geometric Theorem C for the square grid**:
all zeros of the infinite canonical product computed from the square
grid's max-norm shell energy lie on the prescribed affine line.
-/
theorem squareGrid_theoremC
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct squareGridEnergy center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) :=
  theoremC_zero_localization (squareGridEnergy_admissible center direction) hd hz


/-! ## Physical centroid energy of the square tiling -/

/-- The centre (centroid) of the unit cell indexed by an integer pair. -/
def squareCentroid (p : ℤ × ℤ) : ℝ × ℝ :=
  ((p.1 : ℝ) + 1 / 2, (p.2 : ℝ) + 1 / 2)

/-- Squared Euclidean distance of a square's centroid from the origin,
plus 1 to keep every energy strictly positive. -/
def centroidEnergy (p : ℤ × ℤ) : ℝ :=
  1 + (squareCentroid p).1 ^ 2 + (squareCentroid p).2 ^ 2

theorem centroidEnergy_pos (p : ℤ × ℤ) : 0 < centroidEnergy p := by
  unfold centroidEnergy
  positivity

/-- The one-dimensional summability estimate for half-integer centroids. -/
private theorem summable_centroid_axis :
    Summable (fun m : ℤ => 1 / (1 + ((m : ℝ) + 1 / 2) ^ 2)) := by
  have hbase : Summable
      (fun m : ℤ => 1 / |(m : ℝ) + (1 / 2 : ℝ)| ^ (2 : ℝ)) :=
    (Real.summable_one_div_int_add_rpow (1 / 2) 2).2 (by norm_num)
  have hpowers : Summable
      (fun m : ℤ => 1 / (((m : ℝ) + 1 / 2) ^ 2)) := by
    simpa only [Real.rpow_two, sq_abs] using hbase
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) hpowers
  have hnonzero : (m : ℝ) + 1 / 2 ≠ 0 := by
    intro hz
    have hh : (2 : ℝ) * (m : ℝ) = -1 := by linarith
    have hhi : (2 : ℤ) * m = -1 := by exact_mod_cast hh
    omega
  have hpos : 0 < ((m : ℝ) + 1 / 2) ^ 2 := sq_pos_of_ne_zero hnonzero
  apply one_div_le_one_div_of_le hpos
  linarith

/-- The inverse square of the Euclidean centroid energy is summable
over all of the two-dimensional integer lattice. -/
theorem centroidEnergy_inv_sq_summable :
    Summable (fun p : ℤ × ℤ => 1 / (centroidEnergy p) ^ 2) := by
  have haxis := summable_centroid_axis
  have hprod : Summable (fun p : ℤ × ℤ =>
      (1 / (1 + ((p.1 : ℝ) + 1 / 2) ^ 2)) *
      (1 / (1 + ((p.2 : ℝ) + 1 / 2) ^ 2))) := by
    have hnorm : Summable (fun m : ℤ =>
        ‖((1 : ℝ) / (1 + ((m : ℝ) + 1 / 2) ^ 2))‖) := by
      have heq : (fun m : ℤ =>
          ‖((1 : ℝ) / (1 + ((m : ℝ) + 1 / 2) ^ 2))‖) =
          (fun m : ℤ =>
          (1 : ℝ) / (1 + ((m : ℝ) + 1 / 2) ^ 2)) := by
        funext m
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [heq]
      exact haxis
    exact summable_mul_of_summable_norm
      (f := fun m : ℤ => (1 : ℝ) / (1 + ((m : ℝ) + 1 / 2) ^ 2))
      (g := fun m : ℤ => (1 : ℝ) / (1 + ((m : ℝ) + 1 / 2) ^ 2))
      hnorm hnorm
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) hprod
  let x : ℝ := (p.1 : ℝ) + 1 / 2
  let y : ℝ := (p.2 : ℝ) + 1 / 2
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have hxy : (1 + x ^ 2) * (1 + y ^ 2) ≤ (1 + x ^ 2 + y ^ 2) ^ 2 := by
    nlinarith [mul_nonneg hx hy, sq_nonneg (x ^ 2 + y ^ 2)]
  change 1 / (1 + x ^ 2 + y ^ 2) ^ 2 ≤
    (1 / (1 + x ^ 2)) * (1 / (1 + y ^ 2))
  calc
    1 / (1 + x ^ 2 + y ^ 2) ^ 2 ≤
        1 / ((1 + x ^ 2) * (1 + y ^ 2)) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact hxy
    _ = (1 / (1 + x ^ 2)) * (1 / (1 + y ^ 2)) := by
      simp only [one_div, mul_inv_rev]
      ac_rfl

/-- The enumeration used for the square tiling has no repeated lattice points. -/
theorem gridPoint_injective : Function.Injective gridPoint := by
  intro i j hij
  have ha : (Nat.unpair i).1 = (Nat.unpair j).1 := by
    apply (Equiv.intEquivNat.symm).injective
    exact congrArg Prod.fst hij
  have hb : (Nat.unpair i).2 = (Nat.unpair j).2 := by
    apply (Equiv.intEquivNat.symm).injective
    exact congrArg Prod.snd hij
  have hp : Nat.unpair i = Nat.unpair j := Prod.ext ha hb
  calc
    i = Nat.pair (Nat.unpair i).1 (Nat.unpair i).2 := (Nat.pair_unpair i).symm
    _ = Nat.pair (Nat.unpair j).1 (Nat.unpair j).2 := by rw [hp]
    _ = j := Nat.pair_unpair j

/-- The genuine Euclidean centroid energy, indexed by the natural enumeration. -/
def geometricCentroidEnergy (n : ℕ) : ℝ :=
  centroidEnergy (gridPoint n)

/-- A pure geometric convergence theorem, with no artificial shell factor. -/
theorem geometricCentroidEnergy_inv_sq_summable :
    Summable (fun n : ℕ => 1 / (geometricCentroidEnergy n) ^ 2) := by
  simpa only [geometricCentroidEnergy, Function.comp_def] using
    centroidEnergy_inv_sq_summable.comp_injective gridPoint_injective

/-- The physical centroid energy satisfies Theorem C's analytic hypotheses. -/
theorem geometricCentroidEnergy_admissible (center direction : ℂ) :
    Admissible geometricCentroidEnergy center direction := by
  apply admissible_of_inv_sq_summable
  · intro n
    exact centroidEnergy_pos (gridPoint n)
  · exact geometricCentroidEnergy_inv_sq_summable

/-- **Theorem C for squared Euclidean centroid energies of all plane squares.** -/
theorem geometricCentroid_theoremC
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct geometricCentroidEnergy center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) :=
  theoremC_zero_localization (geometricCentroidEnergy_admissible center direction) hd hz


/-! ## All invertible linear images: rectangles and parallelograms -/

/-- The physical squared-centroid energy after applying a real 2×2
linear transformation. Its determinant must be nonzero to preserve
the two-dimensional nature of the tiling. -/
def linearCentroidEnergy (a b c d : ℝ) (p : ℤ × ℤ) : ℝ :=
  1 + (a * (squareCentroid p).1 + b * (squareCentroid p).2) ^ 2 +
      (c * (squareCentroid p).1 + d * (squareCentroid p).2) ^ 2

theorem linearCentroidEnergy_pos (a b c d : ℝ) (p : ℤ × ℤ) :
    0 < linearCentroidEnergy a b c d p := by
  unfold linearCentroidEnergy
  positivity

/-- The adjugate identity supplies a coercive quadratic lower bound for
every invertible real 2×2 matrix. The two extra terms on the left are
squares, so the inequality follows without analytic assumptions. -/
private theorem linear_sq_control (a b c d x y : ℝ) :
    (a * d - b * c) ^ 2 * (x ^ 2 + y ^ 2) ≤
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) *
        ((a * x + b * y) ^ 2 + (c * x + d * y) ^ 2) := by
  let u : ℝ := a * x + b * y
  let v : ℝ := c * x + d * y
  have hidentity :
      (a * d - b * c) ^ 2 * (x ^ 2 + y ^ 2) +
        (b * u + d * v) ^ 2 + (a * u + c * v) ^ 2 =
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (u ^ 2 + v ^ 2) := by
    dsimp [u, v]
    ring
  calc
    _ ≤ (a * d - b * c) ^ 2 * (x ^ 2 + y ^ 2) +
          (b * u + d * v) ^ 2 + (a * u + c * v) ^ 2 := by
            positivity
    _ = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (u ^ 2 + v ^ 2) := hidentity
    _ = _ := rfl

/-- Quantitative Euclidean-energy comparison for any invertible
2×2 real matrix; the constant is independent of lattice points. -/
private theorem linear_energy_control (a b c d x y : ℝ)
    (hdet : a * d - b * c ≠ 0) :
    1 + x ^ 2 + y ^ 2 ≤
      (((a * d - b * c) ^ 2 +
            (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) /
        (a * d - b * c) ^ 2) *
      (1 + (a * x + b * y) ^ 2 + (c * x + d * y) ^ 2) := by
  let δ : ℝ := a * d - b * c
  let S : ℝ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2
  let u : ℝ := a * x + b * y
  let v : ℝ := c * x + d * y
  have hδ : 0 < δ ^ 2 := sq_pos_of_ne_zero hdet
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hUV : 0 ≤ u ^ 2 + v ^ 2 := by positivity
  have hc : δ ^ 2 * (x ^ 2 + y ^ 2) ≤ S * (u ^ 2 + v ^ 2) := by
    simpa [δ, S, u, v] using linear_sq_control a b c d x y
  have hmain : δ ^ 2 * (1 + x ^ 2 + y ^ 2) ≤
      (δ ^ 2 + S) * (1 + u ^ 2 + v ^ 2) := by
    nlinarith only [hc, hδ.le, hS, hUV,
      mul_nonneg hδ.le hUV, mul_nonneg hS hUV]
  have hdiv : 1 + x ^ 2 + y ^ 2 ≤
      ((δ ^ 2 + S) * (1 + u ^ 2 + v ^ 2)) / δ ^ 2 := by
    apply (le_div_iff₀ hδ).2
    nlinarith only [hmain]
  calc
    1 + x ^ 2 + y ^ 2 ≤
        ((δ ^ 2 + S) * (1 + u ^ 2 + v ^ 2)) / δ ^ 2 := hdiv
    _ = ((δ ^ 2 + S) / δ ^ 2) * (1 + u ^ 2 + v ^ 2) := by ring
    _ = _ := rfl

/-- Squared inverse Euclidean centroid energies remain summable under
*every* nonsingular real linear deformation of the square grid. -/
theorem linearCentroidEnergy_inv_sq_summable
    (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) :
    Summable (fun p : ℤ × ℤ => 1 / (linearCentroidEnergy a b c d p) ^ 2) := by
  let δ : ℝ := a * d - b * c
  let S : ℝ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2
  let C : ℝ := (δ ^ 2 + S) / δ ^ 2
  have hδ : 0 < δ ^ 2 := sq_pos_of_ne_zero hdet
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC : 0 < C := div_pos (add_pos_of_pos_of_nonneg hδ hS) hδ
  have hcomp (p : ℤ × ℤ) :
      centroidEnergy p ≤ C * linearCentroidEnergy a b c d p := by
    simpa only [centroidEnergy, linearCentroidEnergy, C, δ, S] using
      linear_energy_control a b c d
        (squareCentroid p).1 (squareCentroid p).2 hdet
  have hsum : Summable (fun p : ℤ × ℤ =>
      C ^ 2 * (1 / (centroidEnergy p) ^ 2)) :=
    centroidEnergy_inv_sq_summable.mul_left (C ^ 2)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) hsum
  have hp : 0 < centroidEnergy p := centroidEnergy_pos p
  have hlin : 0 < linearCentroidEnergy a b c d p :=
    linearCentroidEnergy_pos a b c d p
  have hsquare :
      (centroidEnergy p) ^ 2 ≤ C ^ 2 * (linearCentroidEnergy a b c d p) ^ 2 := by
    calc
      _ ≤ (C * linearCentroidEnergy a b c d p) ^ 2 := by
        gcongr
        exact hcomp p
      _ = _ := by ring
  calc
    1 / (linearCentroidEnergy a b c d p) ^ 2 ≤
        C ^ 2 / (centroidEnergy p) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hlin) (sq_pos_of_pos hp)).2
      simpa only [one_mul] using hsquare
    _ = C ^ 2 * (1 / (centroidEnergy p) ^ 2) := by ring

/-- Energies of the transformed lattice indexed by the original
bijection with the natural numbers. -/
def linearGridEnergy (a b c d : ℝ) (n : ℕ) : ℝ :=
  linearCentroidEnergy a b c d (gridPoint n)

/-- Every nonsingular real affine lattice is analytically admissible
for the same infinite canonical-product theorem C. -/
theorem linearGridEnergy_admissible (a b c d : ℝ)
    (hdet : a * d - b * c ≠ 0) (center direction : ℂ) :
    Admissible (linearGridEnergy a b c d) center direction := by
  apply admissible_of_inv_sq_summable
  · intro n
    exact linearCentroidEnergy_pos a b c d (gridPoint n)
  · simpa only [linearGridEnergy, Function.comp_def] using
      (linearCentroidEnergy_inv_sq_summable a b c d hdet).comp_injective
        gridPoint_injective

/-- Theorem C for all nonsingular linear images of the infinite square
grid, including rectangles, oblique lattices and parallelogram tilings. -/
theorem linearGrid_theoremC
    (a b c d : ℝ) (hdet : a * d - b * c ≠ 0)
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct (linearGridEnergy a b c d) center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) :=
  theoremC_zero_localization
    (linearGridEnergy_admissible a b c d hdet center direction) hd hz

/-- Every rectangle with nonzero side lengths is covered. -/
theorem rectangleGrid_theoremC (width height : ℝ)
    (hw : width ≠ 0) (hh : height ≠ 0)
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct (linearGridEnergy width 0 0 height)
      center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) := by
  apply linearGrid_theoremC width 0 0 height
  · simpa using mul_ne_zero hw hh
  · exact hd
  · exact hz

/-- Every nonsingular sheared rectangular grid (parallelograms) is covered. -/
theorem parallelogramGrid_theoremC (width height shear : ℝ)
    (hw : width ≠ 0) (hh : height ≠ 0)
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct (linearGridEnergy width shear 0 height)
      center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) := by
  apply linearGrid_theoremC width shear 0 height
  · simpa using mul_ne_zero hw hh
  · exact hd
  · exact hz

end
end InfiniteTilings
