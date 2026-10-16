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

/-- Apply the real 2×2 matrix to a point in the plane. -/
def linearGridMap (a b c d : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (a * z.1 + b * z.2, c * z.1 + d * z.2)

/-- Every real 2×2 matrix with nonzero determinant acts injectively
on the plane; this is independent of the analytic-product arguments. -/
theorem linearGridMap_injective (a b c d : ℝ)
    (hdet : a * d - b * c ≠ 0) :
    Function.Injective (linearGridMap a b c d) := by
  intro x y h
  have h₁ : a * (x.1 - y.1) + b * (x.2 - y.2) = 0 := by
    have hf := congrArg Prod.fst h
    dsimp [linearGridMap] at hf
    linarith
  have h₂ : c * (x.1 - y.1) + d * (x.2 - y.2) = 0 := by
    have hs := congrArg Prod.snd h
    dsimp [linearGridMap] at hs
    linarith
  have hxmul : (a * d - b * c) * (x.1 - y.1) = 0 := by
    calc
      _ = d * (a * (x.1 - y.1) + b * (x.2 - y.2)) -
          b * (c * (x.1 - y.1) + d * (x.2 - y.2)) := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  have hymul : (a * d - b * c) * (x.2 - y.2) = 0 := by
    calc
      _ = a * (c * (x.1 - y.1) + d * (x.2 - y.2)) -
          c * (a * (x.1 - y.1) + b * (x.2 - y.2)) := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  apply Prod.ext
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hxmul).resolve_left hdet)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hymul).resolve_left hdet)

/-- The explicit inverse formula makes the linear transformation
surjective whenever its determinant is nonzero. -/
theorem linearGridMap_surjective (a b c d : ℝ)
    (hdet : a * d - b * c ≠ 0) :
    Function.Surjective (linearGridMap a b c d) := by
  intro z
  refine ⟨((d * z.1 - b * z.2) / (a * d - b * c),
           (a * z.2 - c * z.1) / (a * d - b * c)), ?_⟩
  apply Prod.ext
  · change a * ((d * z.1 - b * z.2) / (a * d - b * c)) +
        b * ((a * z.2 - c * z.1) / (a * d - b * c)) = z.1
    calc
      _ = (a * (d * z.1 - b * z.2) +
            b * (a * z.2 - c * z.1)) / (a * d - b * c) := by ring
      _ = z.1 := by
        apply (div_eq_iff hdet).2
        ring
  · change c * ((d * z.1 - b * z.2) / (a * d - b * c)) +
        d * ((a * z.2 - c * z.1) / (a * d - b * c)) = z.2
    calc
      _ = (c * (d * z.1 - b * z.2) +
            d * (a * z.2 - c * z.1)) / (a * d - b * c) := by ring
      _ = z.2 := by
        apply (div_eq_iff hdet).2
        ring

/-- A deformed unit square is a parallelogram cell. -/
def linearSquareCell (a b c d : ℝ) (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  linearGridMap a b c d '' squareCell p

/-- The image of the open interior of a unit square. -/
def linearSquareInterior (a b c d : ℝ) (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  linearGridMap a b c d '' squareInterior p

/-- Images of all integer unit squares under an invertible matrix
still cover the whole plane. -/
theorem linearSquareCell_covers_plane (a b c d : ℝ)
    (hdet : a * d - b * c ≠ 0) (z : ℝ × ℝ) :
    ∃ p : ℤ × ℤ, z ∈ linearSquareCell a b c d p := by
  obtain ⟨w, hw⟩ := linearGridMap_surjective a b c d hdet z
  obtain ⟨p, hp⟩ := squareCell_covers_plane w
  exact ⟨p, ⟨w, hp, hw⟩⟩

/-- The interiors of distinct transformed cells do not overlap. -/
theorem linearSquareInterior_unique (a b c d : ℝ)
    (hdet : a * d - b * c ≠ 0)
    {p q : ℤ × ℤ} {z : ℝ × ℝ}
    (hp : z ∈ linearSquareInterior a b c d p)
    (hq : z ∈ linearSquareInterior a b c d q) : p = q := by
  obtain ⟨x, hx, hxz⟩ := hp
  obtain ⟨y, hy, hyz⟩ := hq
  have hxy : x = y :=
    (linearGridMap_injective a b c d hdet) (hxz.trans hyz.symm)
  subst y
  exact squareInterior_unique hx hy


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
            have h₁ : 0 ≤ (b * u + d * v) ^ 2 := sq_nonneg _
            have h₂ : 0 ≤ (a * u + c * v) ^ 2 := sq_nonneg _
            linarith
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


/-! ## Infinite row-shifted tilings beyond affine grids

Each horizontal strip is tiled by unit squares, with an independent
horizontal offset chosen for that row. These tilings need not be globally
linear images of the square lattice. They always have horizontal period
one, so we do **not** claim they are fully aperiodic tilings.
-/

/-- The closed square cell in row \`p.2\`, horizontally offset by
\`offset p.2\`. Adjacent rows may have different offsets. -/
def rowShiftCell (offset : ℤ → ℝ) (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | (p.1 : ℝ) + offset p.2 ≤ z.1 ∧
       z.1 ≤ (p.1 : ℝ) + offset p.2 + 1 ∧
       (p.2 : ℝ) ≤ z.2 ∧ z.2 ≤ (p.2 : ℝ) + 1}

/-- The open interior of a row-shifted square. -/
def rowShiftInterior (offset : ℤ → ℝ) (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | (p.1 : ℝ) + offset p.2 < z.1 ∧
       z.1 < (p.1 : ℝ) + offset p.2 + 1 ∧
       (p.2 : ℝ) < z.2 ∧ z.2 < (p.2 : ℝ) + 1}

/-- For *any* row offsets, even unbounded ones, row-shifted cells cover
all of \`ℝ × ℝ\` without gaps. -/
theorem rowShiftCell_covers_plane (offset : ℤ → ℝ) (z : ℝ × ℝ) :
    ∃ p : ℤ × ℤ, z ∈ rowShiftCell offset p := by
  let n : ℤ := ⌊z.2⌋
  let m : ℤ := ⌊z.1 - offset n⌋
  refine ⟨(m,n), ?_⟩
  change (m : ℝ) + offset n ≤ z.1 ∧
    z.1 ≤ (m : ℝ) + offset n + 1 ∧
    (n : ℝ) ≤ z.2 ∧ z.2 ≤ (n : ℝ) + 1
  have hmx : (m : ℝ) ≤ z.1 - offset n := Int.floor_le _
  have hmx' : z.1 - offset n < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have hny : (n : ℝ) ≤ z.2 := Int.floor_le _
  have hny' : z.2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · exact hny
  · exact hny'.le

/-- Different shifted unit squares cannot share an interior point,
regardless of how the rows are offset. -/
theorem rowShiftInterior_unique (offset : ℤ → ℝ)
    {p q : ℤ × ℤ} {z : ℝ × ℝ}
    (hp : z ∈ rowShiftInterior offset p)
    (hq : z ∈ rowShiftInterior offset q) : p = q := by
  change (p.1 : ℝ) + offset p.2 < z.1 ∧
    z.1 < (p.1 : ℝ) + offset p.2 + 1 ∧
    (p.2 : ℝ) < z.2 ∧ z.2 < (p.2 : ℝ) + 1 at hp
  change (q.1 : ℝ) + offset q.2 < z.1 ∧
    z.1 < (q.1 : ℝ) + offset q.2 + 1 ∧
    (q.2 : ℝ) < z.2 ∧ z.2 < (q.2 : ℝ) + 1 at hq
  have hy₁ : p.2 < q.2 + 1 := by
    exact_mod_cast (lt_trans hp.2.2.1 hq.2.2.2)
  have hy₂ : q.2 < p.2 + 1 := by
    exact_mod_cast (lt_trans hq.2.2.1 hp.2.2.2)
  have hy : p.2 = q.2 := by omega
  have hx₁ : (p.1 : ℝ) < (q.1 : ℝ) + 1 := by
    have hlow := hp.1
    have hhigh := hq.2.1
    rw [hy] at hlow
    linarith
  have hx₂ : (q.1 : ℝ) < (p.1 : ℝ) + 1 := by
    have hlow := hq.1
    have hhigh := hp.2.1
    rw [hy] at hhigh
    linarith
  have hxi₁ : p.1 < q.1 + 1 := by exact_mod_cast hx₁
  have hxi₂ : q.1 < p.1 + 1 := by exact_mod_cast hx₂
  have hx : p.1 = q.1 := by omega
  exact Prod.ext hx hy

/-- Euclidean centroid of the row-shifted square. -/
def rowShiftCentroid (offset : ℤ → ℝ) (p : ℤ × ℤ) : ℝ × ℝ :=
  ((squareCentroid p).1 + offset p.2, (squareCentroid p).2)

/-- Natural positive squared-distance energy for the shifted centroid. -/
def rowShiftEnergy (offset : ℤ → ℝ) (p : ℤ × ℤ) : ℝ :=
  1 + (rowShiftCentroid offset p).1 ^ 2 +
      (rowShiftCentroid offset p).2 ^ 2

theorem rowShiftEnergy_pos (offset : ℤ → ℝ) (p : ℤ × ℤ) :
    0 < rowShiftEnergy offset p := by
  unfold rowShiftEnergy
  positivity

/-- A uniform bound of one half per row controls the original centroid
energy by twice the row-shifted one. No periodicity is assumed. -/
private theorem rowShift_energy_control (offset : ℤ → ℝ)
    (hbound : ∀ n, |offset n| ≤ 1 / 2) (p : ℤ × ℤ) :
    centroidEnergy p ≤ 2 * rowShiftEnergy offset p := by
  let x : ℝ := (squareCentroid p).1
  let y : ℝ := (squareCentroid p).2
  let δ : ℝ := offset p.2
  have hδ := hbound p.2
  have hlo : -(1 / 2 : ℝ) ≤ δ := (abs_le.mp hδ).1
  have hhi : δ ≤ (1 / 2 : ℝ) := (abs_le.mp hδ).2
  have hδsq : δ ^ 2 ≤ 1 / 4 := by
    have hmul : 0 ≤ (1 / 2 - δ) * (1 / 2 + δ) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hsquare : 0 ≤ (x + 2 * δ) ^ 2 := sq_nonneg _
  have hy : 0 ≤ y ^ 2 := sq_nonneg _
  change 1 + x ^ 2 + y ^ 2 ≤ 2 * (1 + (x + δ) ^ 2 + y ^ 2)
  nlinarith

/-- Squared inverse energies are summable for every bounded row offset,
including irregular and nonconstant arrangements of the rows. -/
theorem rowShiftEnergy_inv_sq_summable (offset : ℤ → ℝ)
    (hbound : ∀ n, |offset n| ≤ 1 / 2) :
    Summable (fun p : ℤ × ℤ => 1 / (rowShiftEnergy offset p) ^ 2) := by
  have hsum : Summable (fun p : ℤ × ℤ =>
      (4 : ℝ) * (1 / (centroidEnergy p) ^ 2)) :=
    centroidEnergy_inv_sq_summable.mul_left 4
  apply Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hsum
  have hp : 0 < centroidEnergy p := centroidEnergy_pos p
  have hq : 0 < rowShiftEnergy offset p := rowShiftEnergy_pos offset p
  have hsquare : (centroidEnergy p) ^ 2 ≤
      4 * (rowShiftEnergy offset p) ^ 2 := by
    calc
      _ ≤ (2 * rowShiftEnergy offset p) ^ 2 := by
        gcongr
        exact rowShift_energy_control offset hbound p
      _ = _ := by ring
  calc
    1 / (rowShiftEnergy offset p) ^ 2 ≤
        4 / (centroidEnergy p) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hq) (sq_pos_of_pos hp)).2
      simpa only [one_mul] using hsquare
    _ = 4 * (1 / (centroidEnergy p) ^ 2) := by ring

/-- A basic integer separation bound. -/
private theorem integer_centroid_gap {m n : ℤ} (h : m ≠ n) :
    1 ≤ ((m : ℝ) - (n : ℝ)) ^ 2 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hint : m + 1 ≤ n := by omega
    have hr : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hint
    nlinarith
  · have hint : n + 1 ≤ m := by omega
    have hr : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hint
    nlinarith

/-- The row-shifted centroids are *uniformly separated*, even if the
offsets are unbounded. Their mutual Euclidean distance is at least 1. -/
theorem rowShiftCentroid_separated (offset : ℤ → ℝ)
    {p q : ℤ × ℤ} (hpq : p ≠ q) :
    1 ≤ ((rowShiftCentroid offset p).1 -
        (rowShiftCentroid offset q).1) ^ 2 +
        ((rowShiftCentroid offset p).2 -
        (rowShiftCentroid offset q).2) ^ 2 := by
  by_cases hy : p.2 = q.2
  · have hx : p.1 ≠ q.1 := by
      intro h
      exact hpq (Prod.ext h hy)
    have hgap := integer_centroid_gap hx
    have hdiff : (rowShiftCentroid offset p).1 -
        (rowShiftCentroid offset q).1 =
        (p.1 : ℝ) - (q.1 : ℝ) := by
      simp [rowShiftCentroid, squareCentroid, hy]
    rw [hdiff]
    nlinarith [sq_nonneg
      ((rowShiftCentroid offset p).2 - (rowShiftCentroid offset q).2)]
  · have hgap := integer_centroid_gap hy
    have hdiff : (rowShiftCentroid offset p).2 -
        (rowShiftCentroid offset q).2 =
        (p.2 : ℝ) - (q.2 : ℝ) := by
      simp [rowShiftCentroid, squareCentroid]
    rw [hdiff]
    nlinarith [sq_nonneg
      ((rowShiftCentroid offset p).1 - (rowShiftCentroid offset q).1)]

/-- Enumerate all shifted-centroid energies without duplicates. -/
def rowShiftGridEnergy (offset : ℤ → ℝ) (n : ℕ) : ℝ :=
  rowShiftEnergy offset (gridPoint n)

/-- Bounded row-shift tilings satisfy the compact-normal convergence
hypothesis of the infinite canonical product theorem. -/
theorem rowShiftGridEnergy_admissible (offset : ℤ → ℝ)
    (hbound : ∀ n, |offset n| ≤ 1 / 2)
    (center direction : ℂ) :
    Admissible (rowShiftGridEnergy offset) center direction := by
  apply admissible_of_inv_sq_summable
  · intro n
    exact rowShiftEnergy_pos offset (gridPoint n)
  · simpa only [rowShiftGridEnergy, Function.comp_def] using
      (rowShiftEnergy_inv_sq_summable offset hbound).comp_injective
        gridPoint_injective

/-- **Geometric Theorem C for arbitrarily row-shifted infinite square
tilings**. All zeros are on the prescribed complex line. -/
theorem rowShiftGrid_theoremC (offset : ℤ → ℝ)
    (hbound : ∀ n, |offset n| ≤ 1 / 2)
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct (rowShiftGridEnergy offset) center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) :=
  theoremC_zero_localization
    (rowShiftGridEnergy_admissible offset hbound center direction) hd hz



/-! ## General centroid sets with controlled geometric displacement

This is a theorem about the distribution of centroid-like points, not about
the existence of a tiling with those centroids. In particular, arbitrary
displacements do not automatically preserve cell covering or disjointness.

The geometric input is deliberately much broader than affine grids or
row-wise shifts: a *different* bounded displacement may be assigned to
every pair of integer coordinates. No translation symmetry is required.
-/

/-- A positive geometric energy is **coercive relative to the square
lattice** if it dominates the lattice squared-distance energy up to
one uniform constant. This hypothesis is sufficient for summability;
it does not itself assert uniform point separation. -/
theorem coerciveEnergy_inv_sq_summable
    (q : ℤ × ℤ → ℝ) (C : ℝ) (hC : 0 < C)
    (hq : ∀ p, 0 < q p)
    (hcontrol : ∀ p, centroidEnergy p ≤ C * q p) :
    Summable (fun p : ℤ × ℤ => 1 / (q p) ^ 2) := by
  have hsum : Summable (fun p : ℤ × ℤ =>
      C ^ 2 * (1 / (centroidEnergy p) ^ 2)) :=
    centroidEnergy_inv_sq_summable.mul_left (C ^ 2)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) hsum
  have hp : 0 < centroidEnergy p := centroidEnergy_pos p
  have hsquare : (centroidEnergy p) ^ 2 ≤ C ^ 2 * (q p) ^ 2 := by
    calc
      _ ≤ (C * q p) ^ 2 := by
        gcongr
        exact hcontrol p
      _ = _ := by ring
  calc
    1 / (q p) ^ 2 ≤ C ^ 2 / (centroidEnergy p) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos (hq p)) (sq_pos_of_pos hp)).2
      simpa only [one_mul] using hsquare
    _ = C ^ 2 * (1 / (centroidEnergy p) ^ 2) := by ring

/-- An arbitrary countable collection of positive geometric energies,
indexed bijectively by the integer lattice, can be fed into Theorem C
provided it satisfies the same coercive comparison. -/
def enumeratedEnergy (q : ℤ × ℤ → ℝ) (n : ℕ) : ℝ :=
  q (gridPoint n)

/-- This is an *analytic* criterion for arbitrary lattice-indexed
centroid energies; actual geometric tilings are separate. -/
theorem coerciveEnergy_admissible
    (q : ℤ × ℤ → ℝ) (C : ℝ) (hC : 0 < C)
    (hq : ∀ p, 0 < q p)
    (hcontrol : ∀ p, centroidEnergy p ≤ C * q p)
    (center direction : ℂ) :
    Admissible (enumeratedEnergy q) center direction := by
  apply admissible_of_inv_sq_summable
  · intro n
    exact hq (gridPoint n)
  · simpa only [enumeratedEnergy, Function.comp_def] using
      (coerciveEnergy_inv_sq_summable q C hC hq hcontrol).comp_injective
        gridPoint_injective

/-- General geometric localization theorem for any such coercive
lattice-indexed sequence: no regularized-product zero can lie away
from the chosen complex affine line. -/
theorem coerciveEnergy_theoremC
    (q : ℤ × ℤ → ℝ) (C : ℝ) (hC : 0 < C)
    (hq : ∀ p, 0 < q p)
    (hcontrol : ∀ p, centroidEnergy p ≤ C * q p)
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct (enumeratedEnergy q) center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) :=
  theoremC_zero_localization
    (coerciveEnergy_admissible q C hC hq hcontrol center direction) hd hz

/-- Squared Euclidean centroid energy of an **arbitrary** point
configuration indexed by the integer lattice. -/
def pointSetEnergy (point : ℤ × ℤ → ℝ × ℝ) (p : ℤ × ℤ) : ℝ :=
  1 + (point p).1 ^ 2 + (point p).2 ^ 2

theorem pointSetEnergy_pos (point : ℤ × ℤ → ℝ × ℝ) (p : ℤ × ℤ) :
    0 < pointSetEnergy point p := by
  unfold pointSetEnergy
  positivity

/-- A real inequality: moving both coordinates by at most 1/2
preserves the original squared-distance energy up to a factor two. -/
private theorem bounded_displacement_energy_control
    (x y u v : ℝ)
    (hx : |u - x| ≤ 1 / 2)
    (hy : |v - y| ≤ 1 / 2) :
    1 + x ^ 2 + y ^ 2 ≤ 2 * (1 + u ^ 2 + v ^ 2) := by
  have hxlo : -(1 / 2 : ℝ) ≤ u - x := (abs_le.mp hx).1
  have hxhi : u - x ≤ (1 / 2 : ℝ) := (abs_le.mp hx).2
  have hylo : -(1 / 2 : ℝ) ≤ v - y := (abs_le.mp hy).1
  have hyhi : v - y ≤ (1 / 2 : ℝ) := (abs_le.mp hy).2
  have hxsq : (u - x) ^ 2 ≤ (1 / 4 : ℝ) := by
    have h : 0 ≤ (1 / 2 - (u - x)) * (1 / 2 + (u - x)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hysq : (v - y) ^ 2 ≤ (1 / 4 : ℝ) := by
    have h : 0 ≤ (1 / 2 - (v - y)) * (1 / 2 + (v - y)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  nlinarith [sq_nonneg (x - 2 * u), sq_nonneg (y - 2 * v)]

/-- Any bounded displacement field, with no spatial periodicity
assumption, gives a geometric coercive energy inequality. -/
theorem boundedPointSet_energy_control
    (point : ℤ × ℤ → ℝ × ℝ)
    (hbound : ∀ p,
      |(point p).1 - (squareCentroid p).1| ≤ 1 / 2 ∧
      |(point p).2 - (squareCentroid p).2| ≤ 1 / 2)
    (p : ℤ × ℤ) :
    centroidEnergy p ≤ 2 * pointSetEnergy point p := by
  simpa only [centroidEnergy, pointSetEnergy] using
    bounded_displacement_energy_control
      (squareCentroid p).1 (squareCentroid p).2
      (point p).1 (point p).2 (hbound p).1 (hbound p).2

/-- Bounded, potentially fully nonperiodic perturbations of all
integer-grid centroids always have a summable inverse-square energy.
The point function need not be periodic or induced by a tile map. -/
theorem boundedPointSet_inv_sq_summable
    (point : ℤ × ℤ → ℝ × ℝ)
    (hbound : ∀ p,
      |(point p).1 - (squareCentroid p).1| ≤ 1 / 2 ∧
      |(point p).2 - (squareCentroid p).2| ≤ 1 / 2) :
    Summable (fun p : ℤ × ℤ => 1 / (pointSetEnergy point p) ^ 2) :=
  coerciveEnergy_inv_sq_summable (pointSetEnergy point) 2 (by norm_num)
    (pointSetEnergy_pos point) (boundedPointSet_energy_control point hbound)

/-- All such irregular centroid sets meet the compact-uniform
product-convergence hypothesis, regardless of point-set periodicity. -/
theorem boundedPointSet_admissible
    (point : ℤ × ℤ → ℝ × ℝ)
    (hbound : ∀ p,
      |(point p).1 - (squareCentroid p).1| ≤ 1 / 2 ∧
      |(point p).2 - (squareCentroid p).2| ≤ 1 / 2)
    (center direction : ℂ) :
    Admissible (enumeratedEnergy (pointSetEnergy point)) center direction :=
  coerciveEnergy_admissible (pointSetEnergy point) 2 (by norm_num)
    (pointSetEnergy_pos point) (boundedPointSet_energy_control point hbound)
    center direction

/-- **Theorem C for arbitrarily perturbed centroid sets.**
There is no symmetry or periodicity premise. All zeros of the
associated infinite canonical product lie on the prescribed line. -/
theorem boundedPointSet_theoremC
    (point : ℤ × ℤ → ℝ × ℝ)
    (hbound : ∀ p,
      |(point p).1 - (squareCentroid p).1| ≤ 1 / 2 ∧
      |(point p).2 - (squareCentroid p).2| ≤ 1 / 2)
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct (enumeratedEnergy (pointSetEnergy point))
      center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) :=
  theoremC_zero_localization
    (boundedPointSet_admissible point hbound center direction) hd hz


/-! ## A genuinely translation-aperiodic planar rectangle tiling

This is a finite, geometrically explicit defect of the square grid:
replace the unit squares at (0,0) and (1,0) with rectangles of widths
1/2 and 3/2. Everywhere else the tiling consists of unit squares.
The unique 3/2-wide rectangle rules out every nonzero translation
period preserving the family of tiles. This is aperiodic in the
translation-symmetry sense, not an aperiodic *tile set*: unit squares
and two other rectangles can also tile periodically.
-/

/-- Left horizontal edge of each rectangle. -/
def defectLeft (p : ℤ × ℤ) : ℝ :=
  if p = (1, 0) then 1 / 2 else (p.1 : ℝ)

/-- Right horizontal edge of each rectangle. -/
def defectRight (p : ℤ × ℤ) : ℝ :=
  if p = (0, 0) then 1 / 2 else (p.1 : ℝ) + 1

/-- Full closed rectangle with vertical boundaries at integer heights. -/
def defectCell (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | defectLeft p ≤ z.1 ∧ z.1 ≤ defectRight p ∧
       (p.2 : ℝ) ≤ z.2 ∧ z.2 ≤ (p.2 : ℝ) + 1}

/-- Open geometric interior of the rectangle. -/
def defectInterior (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | defectLeft p < z.1 ∧ z.1 < defectRight p ∧
       (p.2 : ℝ) < z.2 ∧ z.2 < (p.2 : ℝ) + 1}

/-- The rectangle cells cover every point of the plane. -/
theorem defectCell_covers_plane (z : ℝ × ℝ) :
    ∃ p : ℤ × ℤ, z ∈ defectCell p := by
  obtain ⟨p, hp⟩ := squareCell_covers_plane z
  change (p.1 : ℝ) ≤ z.1 ∧ z.1 ≤ (p.1 : ℝ) + 1 ∧
    (p.2 : ℝ) ≤ z.2 ∧ z.2 ≤ (p.2 : ℝ) + 1 at hp
  by_cases h0 : p = (0, 0)
  · subst p
    rcases hp with ⟨hxlo, hxhi, hylo, hyhi⟩
    rcases le_total z.1 (1 / 2 : ℝ) with hx | hx
    · refine ⟨(0, 0), ?_⟩
      simp only [defectCell, Set.mem_setOf_eq]
      norm_num [defectLeft, defectRight] at *
      exact ⟨hxlo, hx, hylo, hyhi⟩
    · refine ⟨(1, 0), ?_⟩
      simp only [defectCell, Set.mem_setOf_eq]
      norm_num [defectLeft, defectRight] at *
      exact ⟨hx, by linarith, hylo, hyhi⟩
  · by_cases h1 : p = (1, 0)
    · subst p
      refine ⟨(1, 0), ?_⟩
      simp only [defectCell, Set.mem_setOf_eq]
      norm_num [defectLeft, defectRight] at *
      rcases hp with ⟨hxlo, hxhi, hylo, hyhi⟩
      exact ⟨by linarith, hxhi, hylo, hyhi⟩
    · refine ⟨p, ?_⟩
      change defectLeft p ≤ z.1 ∧ z.1 ≤ defectRight p ∧
        (p.2 : ℝ) ≤ z.2 ∧ z.2 ≤ (p.2 : ℝ) + 1
      simpa only [defectLeft, defectRight, if_neg h0, if_neg h1] using hp

/-- Two different intervals in one horizontal row cannot have
overlapping interiors: the earlier tile ends before the later begins. -/
private theorem defectRight_le_left_of_lt (p q : ℤ × ℤ)
    (h : p.1 < q.1) (hy : p.2 = q.2) :
    defectRight p ≤ defectLeft q := by
  by_cases hq : q = (1, 0)
  · have hpne : p ≠ (1, 0) := by
      intro h1
      rw [h1, hq] at h
      omega
    by_cases hp0 : p = (0, 0)
    · subst p
      simp [defectRight, defectLeft, hq]
    · have hi : p.1 + 1 ≤ 0 := by
        have hq1 : q.1 = 1 := congrArg Prod.fst hq
        have hq2 : q.2 = 0 := congrArg Prod.snd hq
        have hp2 : p.2 = 0 := by omega
        have hp1 : p.1 ≠ 0 := by
          intro h
          apply hp0
          exact Prod.ext h hp2
        omega
      have hr : (p.1 : ℝ) + 1 ≤ 0 := by
        exact_mod_cast hi
      simp only [defectRight, if_neg hp0, defectLeft, if_pos hq]
      linarith
  · by_cases hp0 : p = (0, 0)
    · have hi : 1 ≤ q.1 := by
        have hp1 : p.1 = 0 := congrArg Prod.fst hp0
        omega
      have hr : (1 : ℝ) ≤ (q.1 : ℝ) := by
        exact_mod_cast hi
      simp only [defectRight, if_pos hp0, defectLeft, if_neg hq]
      linarith
    · have hi : p.1 + 1 ≤ q.1 := by omega
      have hr : (p.1 : ℝ) + 1 ≤ (q.1 : ℝ) := by
        exact_mod_cast hi
      simpa only [defectRight, if_neg hp0, defectLeft, if_neg hq] using hr

/-- The open interiors of distinct rectangles are disjoint. -/
theorem defectInterior_unique
    {p q : ℤ × ℤ} {z : ℝ × ℝ}
    (hp : z ∈ defectInterior p)
    (hq : z ∈ defectInterior q) : p = q := by
  change defectLeft p < z.1 ∧ z.1 < defectRight p ∧
    (p.2 : ℝ) < z.2 ∧ z.2 < (p.2 : ℝ) + 1 at hp
  change defectLeft q < z.1 ∧ z.1 < defectRight q ∧
    (q.2 : ℝ) < z.2 ∧ z.2 < (q.2 : ℝ) + 1 at hq
  have hy₁ : p.2 < q.2 + 1 := by
    exact_mod_cast (lt_trans hp.2.2.1 hq.2.2.2)
  have hy₂ : q.2 < p.2 + 1 := by
    exact_mod_cast (lt_trans hq.2.2.1 hp.2.2.2)
  have hy : p.2 = q.2 := by omega
  by_cases hx : p.1 < q.1
  · have hinterval := defectRight_le_left_of_lt p q hx hy
    exfalso
    linarith [hp.2.1, hq.1]
  · by_cases hx' : q.1 < p.1
    · have hinterval := defectRight_le_left_of_lt q p hx' hy.symm
      exfalso
      linarith [hq.2.1, hp.1]
    · have hxeq : p.1 = q.1 := by omega
      exact Prod.ext hxeq hy

/-- Horizontal width of each actual rectangle. -/
def defectWidth (p : ℤ × ℤ) : ℝ :=
  defectRight p - defectLeft p

/-- The 3/2-wide rectangle is geometrically unique. -/
theorem defectWidth_unique (p : ℤ × ℤ)
    (hw : defectWidth p = 3 / 2) : p = (1, 0) := by
  by_cases h1 : p = (1, 0)
  · exact h1
  · by_cases h0 : p = (0, 0)
    · subst p
      norm_num [defectWidth, defectRight, defectLeft] at hw
    · have heq : defectWidth p = 1 := by
        simp only [defectWidth, defectRight, defectLeft,
          if_neg h0, if_neg h1]
        ring
      rw [heq] at hw
      norm_num at hw

/-- A translation period in the geometric, tile-preserving sense:
translation of each rectangle must produce another rectangle of the
same width with the correspondingly translated lower-left corner.
This is exactly the coordinate formulation for axis-aligned rectangles
of common height one. -/
def HasDefectTilePeriod (t : ℝ × ℝ) : Prop :=
  ∀ p : ℤ × ℤ, ∃ q : ℤ × ℤ,
    defectWidth p = defectWidth q ∧
    defectLeft p + t.1 = defectLeft q ∧
    (p.2 : ℝ) + t.2 = (q.2 : ℝ)

/-- The infinite rectangle tessellation has NO nontrivial
translation period. The unique wide rectangle is forced to stay fixed. -/
theorem defectTiling_translation_aperiodic
    (t : ℝ × ℝ) (ht : HasDefectTilePeriod t) :
    t = (0, 0) := by
  obtain ⟨q, hw, hx, hy⟩ := ht (1, 0)
  have hwidth : defectWidth (1, 0) = (3 / 2 : ℝ) := by
    norm_num [defectWidth, defectLeft, defectRight]
  have hq : q = (1, 0) :=
    defectWidth_unique q (by rw [← hw, hwidth])
  subst q
  have htx : t.1 = 0 := by
    simpa using hx
  have hty : t.2 = 0 := by
    simpa using hy
  exact Prod.ext htx hty

/-- The true centroid of a special or ordinary rectangular tile. -/
def defectCentroid (p : ℤ × ℤ) : ℝ × ℝ :=
  ((defectLeft p + defectRight p) / 2, (p.2 : ℝ) + 1 / 2)

/-- All actual rectangle centroids are within one half unit (in each
coordinate) of the corresponding ordinary square centroid. -/
theorem defectCentroid_bounded (p : ℤ × ℤ) :
    |(defectCentroid p).1 - (squareCentroid p).1| ≤ 1 / 2 ∧
    |(defectCentroid p).2 - (squareCentroid p).2| ≤ 1 / 2 := by
  constructor
  · by_cases h0 : p = (0, 0)
    · subst p
      norm_num [defectCentroid, defectLeft, defectRight, squareCentroid]
    · by_cases h1 : p = (1, 0)
      · subst p
        norm_num [defectCentroid, defectLeft, defectRight, squareCentroid]
      · have heq :
            (defectCentroid p).1 - (squareCentroid p).1 = 0 := by
          simp only [defectCentroid, defectLeft, defectRight,
            squareCentroid, if_neg h0, if_neg h1]
          ring
        rw [heq]
        norm_num
  · simp [defectCentroid, squareCentroid]

/-- The actual rectangle centroids' inverse-square Euclidean energy is
summable, directly by the earlier bounded-displacement theorem. -/
theorem defectTiling_inv_sq_summable :
    Summable (fun p : ℤ × ℤ => 1 / (pointSetEnergy defectCentroid p) ^ 2) :=
  boundedPointSet_inv_sq_summable defectCentroid defectCentroid_bounded

/-- Final geometric theorem C for this genuinely aperiodic infinite
planar rectangle tiling. Its canonical product has zeros only
on the prescribed complex affine line. -/
theorem defectTiling_theoremC
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct (enumeratedEnergy (pointSetEnergy defectCentroid))
      center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) :=
  boundedPointSet_theoremC defectCentroid defectCentroid_bounded
    center direction s hd hz


/-! ## A geometry-dependent finite-patch operator

Previous canonical products place roots on an affine line *by definition*.
This section deliberately changes approach: a finite graph of adjacent,
marked tiles determines a real symmetric adjacency operator. The exact
two-tile eigenvalues are derived from that operator rather than prescribed
as roots of the earlier canonical product.

This is not yet a Penrose/Farey operator and has no established relation
to the Riemann zeta function. The mark is a binary orientation label on
the tile; it is not an intrinsic chirality of a square or rectangle.
-/

/-- A weighted finite-patch adjacency operator. Vertex indices are
tiles; geometric edges and their weights are supplied independently. -/
def finitePatchOperator {n : ℕ}
    (W : Fin n → Fin n → ℝ) (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, W i j * u j

/-- Symmetry of the weights implies self-adjointness with respect to
the ordinary real dot product on functions on a finite tile patch. -/
theorem finitePatchOperator_symmetric {n : ℕ}
    (W : Fin n → Fin n → ℝ)
    (hW : ∀ i j, W i j = W j i)
    (u v : Fin n → ℝ) :
    (∑ i : Fin n, u i * finitePatchOperator W v i) =
      ∑ j : Fin n, finitePatchOperator W u j * v j := by
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, u i * (W i j * v j) := by
      simp [finitePatchOperator, Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ i : Fin n, u i * (W i j * v j) := Finset.sum_comm
    _ = ∑ j : Fin n, ∑ i : Fin n, (W j i * u i) * v j := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hW i j]
      ring
    _ = ∑ j : Fin n, finitePatchOperator W u j * v j := by
      simp [finitePatchOperator, Finset.sum_mul]

/-- Retain only geometric neighbor edges. The construction uses no
periodicity, and is applicable to arbitrary finite adjacency graphs. -/
noncomputable def geometricEdgeMatrix {n : ℕ}
    (neighbor : Fin n → Fin n → Prop)
    (weight : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ := by
  classical
  exact if neighbor i j then weight i j else 0

/-- Undirected geometric adjacency with symmetric edge weights gives
a symmetric matrix. -/
theorem geometricEdgeMatrix_symmetric {n : ℕ}
    (neighbor : Fin n → Fin n → Prop)
    (weight : Fin n → Fin n → ℝ)
    (hn : ∀ i j, neighbor i j ↔ neighbor j i)
    (hw : ∀ i j, weight i j = weight j i)
    (i j : Fin n) :
    geometricEdgeMatrix neighbor weight i j =
      geometricEdgeMatrix neighbor weight j i := by
  classical
  by_cases h : neighbor i j
  · have h' : neighbor j i := (hn i j).mp h
    simp [geometricEdgeMatrix, h, h', hw i j]
  · have h' : ¬ neighbor j i := by
      intro h'
      exact h ((hn i j).mpr h')
    simp [geometricEdgeMatrix, h, h']

/-- Consequently, every undirected weighted finite tile patch defines
an operator symmetric in the real dot product. -/
theorem geometricFinitePatch_symmetric {n : ℕ}
    (neighbor : Fin n → Fin n → Prop)
    (weight : Fin n → Fin n → ℝ)
    (hn : ∀ i j, neighbor i j ↔ neighbor j i)
    (hw : ∀ i j, weight i j = weight j i)
    (u v : Fin n → ℝ) :
    (∑ i : Fin n,
       u i * finitePatchOperator (geometricEdgeMatrix neighbor weight) v i) =
    ∑ j : Fin n,
       finitePatchOperator (geometricEdgeMatrix neighbor weight) u j * v j :=
  finitePatchOperator_symmetric _ (geometricEdgeMatrix_symmetric neighbor weight hn hw) u v

/-- The two adjacent unequal rectangles in our certified finite-defect
tiling really share their vertical boundary. -/
theorem defectPair_shares_vertical_edge :
    defectRight (0, 0) = defectLeft (1, 0) := by
  norm_num [defectRight, defectLeft]

/-- The geometric, positive width-product of the adjacent rectangles. -/
def defectPairWidthWeight : ℝ :=
  defectWidth (0, 0) * defectWidth (1, 0)

theorem defectPairWidthWeight_value :
    defectPairWidthWeight = 3 / 4 := by
  norm_num [defectPairWidthWeight, defectWidth, defectLeft, defectRight]

/-- An orientation mark is an external binary label (e.g. arrow up/down).
Equal marks yield one interaction strength; opposite marks yield twice
that strength. This is a modeling choice, not a canonical law of tilings. -/
def orientationInteraction (leftMark rightMark : Bool) : ℝ :=
  if leftMark = rightMark then 1 else 2

/-- Geometry- and marking-dependent weight of the shared tile edge. -/
def markedDefectCoupling (leftMark rightMark : Bool) : ℝ :=
  defectPairWidthWeight * orientationInteraction leftMark rightMark

theorem aligned_marked_coupling :
    markedDefectCoupling true true = 3 / 4 := by
  norm_num [markedDefectCoupling, orientationInteraction,
    defectPairWidthWeight_value]

theorem opposed_marked_coupling :
    markedDefectCoupling true false = 3 / 2 := by
  norm_num [markedDefectCoupling, orientationInteraction,
    defectPairWidthWeight_value]

/-- The two-tile adjacency operator interchanges the two amplitudes,
weighted by actual tile widths and their orientation marks. -/
def markedDefectOperator (leftMark rightMark : Bool)
    (u : ℝ × ℝ) : ℝ × ℝ :=
  (markedDefectCoupling leftMark rightMark * u.2,
   markedDefectCoupling leftMark rightMark * u.1)

/-- The concrete two-tile operator is symmetric: its spectral reality
comes from self-adjointness, not from prescribing an affine zero-line. -/
theorem markedDefectOperator_symmetric (leftMark rightMark : Bool)
    (u v : ℝ × ℝ) :
    u.1 * (markedDefectOperator leftMark rightMark v).1 +
      u.2 * (markedDefectOperator leftMark rightMark v).2 =
    (markedDefectOperator leftMark rightMark u).1 * v.1 +
      (markedDefectOperator leftMark rightMark u).2 * v.2 := by
  dsimp [markedDefectOperator]
  ring

/-- A real eigenvalue is characterized by a **nonzero** eigenvector.
This elementary finite-dimensional definition avoids making unproved
claims about infinite-dimensional operator spectra. -/
def PairHasEigenvalue (H : (ℝ × ℝ) → (ℝ × ℝ)) (eig : ℝ) : Prop :=
  ∃ u : ℝ × ℝ, u ≠ (0, 0) ∧ H u = (eig * u.1, eig * u.2)

/-- The symmetric mode, with both tile amplitudes equal. -/
theorem markedDefect_positive_mode (leftMark rightMark : Bool) :
    PairHasEigenvalue (markedDefectOperator leftMark rightMark)
      (markedDefectCoupling leftMark rightMark) := by
  refine ⟨(1, 1), by norm_num, ?_⟩
  simp [markedDefectOperator]

/-- The antisymmetric mode, with opposite tile amplitudes. -/
theorem markedDefect_negative_mode (leftMark rightMark : Bool) :
    PairHasEigenvalue (markedDefectOperator leftMark rightMark)
      (-markedDefectCoupling leftMark rightMark) := by
  refine ⟨(1, -1), by norm_num, ?_⟩
  dsimp [markedDefectOperator]
  congr 1 <;> ring

/-- There are **no other** eigenvalues of the actual two-tile operator.
Thus both eigenvalues are derived from the geometric interaction. -/
theorem markedDefect_eigenvalues_exact (leftMark rightMark : Bool)
    (eig : ℝ)
    (heig : PairHasEigenvalue (markedDefectOperator leftMark rightMark) eig) :
    eig = markedDefectCoupling leftMark rightMark ∨
      eig = -markedDefectCoupling leftMark rightMark := by
  obtain ⟨⟨x, y⟩, hnonzero, heq⟩ := heig
  let w : ℝ := markedDefectCoupling leftMark rightMark
  have hx : w * y = eig * x := by
    have hh := congrArg Prod.fst heq
    exact hh
  have hy : w * x = eig * y := by
    have hh := congrArg Prod.snd heq
    exact hh
  by_cases hplus : eig = w
  · exact Or.inl hplus
  · right
    by_contra hminus
    have hsum : (w - eig) * (x + y) = 0 := by
      nlinarith [hx, hy]
    have hdiff : (w + eig) * (x - y) = 0 := by
      nlinarith [hx, hy]
    have hne₁ : w - eig ≠ 0 := by
      intro h
      apply hplus
      linarith
    have hne₂ : w + eig ≠ 0 := by
      intro h
      apply hminus
      linarith
    have hxy₁ : x + y = 0 :=
      (mul_eq_zero.mp hsum).resolve_left hne₁
    have hxy₂ : x - y = 0 :=
      (mul_eq_zero.mp hdiff).resolve_left hne₂
    have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    apply hnonzero
    exact Prod.ext hx0 hy0

/-- Marking a pair with equal orientations produces the real
eigenvalue 3/4, computed from the actual two-tile geometry. -/
theorem aligned_tiles_eigenvalue :
    PairHasEigenvalue (markedDefectOperator true true) (3 / 4) := by
  rw [← aligned_marked_coupling]
  exact markedDefect_positive_mode true true

/-- Opposite orientation markings produce a *different* eigenvalue:
3/2 instead of 3/4. -/
theorem opposed_tiles_eigenvalue :
    PairHasEigenvalue (markedDefectOperator true false) (3 / 2) := by
  rw [← opposed_marked_coupling]
  exact markedDefect_positive_mode true false

/-- This shows concretely that the local spectrum can detect
orientation mismatch: 3/2 is absent for aligned marks. -/
theorem opposed_eigenvalue_not_aligned :
    ¬ PairHasEigenvalue (markedDefectOperator true true) (3 / 2) := by
  intro h
  rcases markedDefect_eigenvalues_exact true true (3 / 2) h with h1 | h2
  · rw [aligned_marked_coupling] at h1
    norm_num at h1
  · rw [aligned_marked_coupling] at h2
    norm_num at h2


/-! ## Spectral eigenvalues as the new geometric energies Q

We combine the two established constructions without falsely identifying
the infinite product with a determinant of an infinite tile operator.

The number eig(n) is a real eigenvalue of a chosen local or finite-patch
operator. The positive level Q(n)=q₀(n)*(1+eig(n)^2) retains a geometric
growth envelope q₀(n), which makes the inverse-square sum convergent
even if the operator eigenvalues remain bounded. The spectral factor
genuinely moves zeros *along* the chosen affine complex line; it does
not determine that line. The paired canonical factors still put their
zeros on it by construction.

An eigenvalue sequence alone, especially from uniformly bounded local
operators, need not make any infinite product convergent. The growth
factor is essential unless independent spectral growth has been proved.
-/

/-- A strictly positive geometric growth envelope, enhanced by
arbitrary real spectral levels. -/
def spectralEnvelopeEnergy (baseline eigenlevel : ℕ → ℝ) (n : ℕ) : ℝ :=
  baseline n * (1 + (eigenlevel n) ^ 2)

/-- The squared spectral contribution cannot decrease the baseline
energy, so the original summability proof still applies. -/
theorem spectralEnvelopeEnergy_ge (baseline eigenlevel : ℕ → ℝ)
    (hpos : ∀ n, 0 < baseline n) (n : ℕ) :
    baseline n ≤ spectralEnvelopeEnergy baseline eigenlevel n := by
  unfold spectralEnvelopeEnergy
  calc
    baseline n = baseline n * 1 := by ring
    _ ≤ baseline n * (1 + (eigenlevel n) ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (eigenlevel n)])
        (hpos n).le

theorem spectralEnvelopeEnergy_pos (baseline eigenlevel : ℕ → ℝ)
    (hpos : ∀ n, 0 < baseline n) (n : ℕ) :
    0 < spectralEnvelopeEnergy baseline eigenlevel n :=
  lt_of_lt_of_le (hpos n) (spectralEnvelopeEnergy_ge baseline eigenlevel hpos n)

/-- Convergence is inherited from the baseline, without assuming
boundedness or a particular distribution for the real eigenvalues. -/
theorem spectralEnvelopeEnergy_inv_sq_summable
    (baseline eigenlevel : ℕ → ℝ)
    (hpos : ∀ n, 0 < baseline n)
    (hsum : Summable (fun n : ℕ => 1 / (baseline n) ^ 2)) :
    Summable (fun n : ℕ =>
      1 / (spectralEnvelopeEnergy baseline eigenlevel n) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hsum
  show 1 / (spectralEnvelopeEnergy baseline eigenlevel n) ^ 2 ≤
    1 / (baseline n) ^ 2
  apply one_div_le_one_div_of_le (pow_pos (hpos n) 2)
  gcongr
  exact spectralEnvelopeEnergy_ge baseline eigenlevel hpos n

/-- Theorem C's compact majorant follows for any real spectral
eigenvalue sequence added to an already-summable growth envelope. -/
theorem spectralEnvelopeEnergy_admissible
    (baseline eigenlevel : ℕ → ℝ)
    (hpos : ∀ n, 0 < baseline n)
    (hsum : Summable (fun n : ℕ => 1 / (baseline n) ^ 2))
    (center direction : ℂ) :
    Admissible (spectralEnvelopeEnergy baseline eigenlevel)
      center direction :=
  admissible_of_inv_sq_summable
    (spectralEnvelopeEnergy_pos baseline eigenlevel hpos)
    (spectralEnvelopeEnergy_inv_sq_summable baseline eigenlevel hpos hsum)
    center direction

/-- All zeros of a paired product enhanced with *real spectral
eigenvalues* stay on the selected affine complex line. -/
theorem spectralEnvelope_theoremC
    (baseline eigenlevel : ℕ → ℝ)
    (hpos : ∀ n, 0 < baseline n)
    (hsum : Summable (fun n : ℕ => 1 / (baseline n) ^ 2))
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct (spectralEnvelopeEnergy baseline eigenlevel)
      center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) :=
  theoremC_zero_localization
    (spectralEnvelopeEnergy_admissible baseline eigenlevel hpos hsum
      center direction) hd hz

/-- Crucially, every positive Q(n) is also an *actual* zero of the
n-th paired factor, not just a number used in a convergence bound. -/
theorem factor_zero_at_positive_level
    (q : ℕ → ℝ) (n : ℕ)
    (hq : q n ≠ 0)
    (center direction : ℂ) (hd : direction ≠ 0) :
    factor q center direction n
      (center + direction * (q n : ℂ)) = 0 := by
  have hqc : (q n : ℂ) ≠ 0 := by exact_mod_cast hq
  simp only [factor, perturb, add_sub_cancel_left]
  field_simp [hd, hqc] <;> ring

/-- If one factor is zero, its infinite canonical product is zero,
regardless of the order of all other factors. -/
theorem canonicalProduct_zero_at_positive_level
    (q : ℕ → ℝ) (n : ℕ) (hq : q n ≠ 0)
    (center direction : ℂ) (hd : direction ≠ 0) :
    canonicalProduct q center direction
      (center + direction * (q n : ℂ)) = 0 := by
  unfold canonicalProduct
  exact tprod_of_exists_eq_zero
    ⟨n, factor_zero_at_positive_level q n hq center direction hd⟩

/-- Spectral levels therefore give explicit zeros at their corresponding
Q(n), as well as the global no-off-line-zero localization theorem. -/
theorem spectralEnvelope_has_zero_at_each_level
    (baseline eigenlevel : ℕ → ℝ)
    (hpos : ∀ n, 0 < baseline n)
    (center direction : ℂ) (hd : direction ≠ 0) (n : ℕ) :
    canonicalProduct (spectralEnvelopeEnergy baseline eigenlevel)
      center direction
      (center + direction *
        (spectralEnvelopeEnergy baseline eigenlevel n : ℂ)) = 0 :=
  canonicalProduct_zero_at_positive_level
    (spectralEnvelopeEnergy baseline eigenlevel) n
    (ne_of_gt (spectralEnvelopeEnergy_pos baseline eigenlevel hpos n))
    center direction hd

/-- For every n, the two-tile geometric operator with the specified
marks has the following real eigenvalue, certified by a nonzero
eigenvector. These are *local* operator eigenvalues, not the spectrum
of an infinite adjacency operator. -/
def localMarkedEigenlevel (marks : ℕ → Bool × Bool) (n : ℕ) : ℝ :=
  markedDefectCoupling (marks n).1 (marks n).2

theorem localMarkedEigenlevel_is_eigenvalue
    (marks : ℕ → Bool × Bool) (n : ℕ) :
    PairHasEigenvalue
      (markedDefectOperator (marks n).1 (marks n).2)
      (localMarkedEigenlevel marks n) :=
  markedDefect_positive_mode (marks n).1 (marks n).2

/-- Q(n) built from physical square-centroid growth *and* actual
two-tile geometric operator eigenvalues. -/
def markedSpectralGridEnergy (marks : ℕ → Bool × Bool) (n : ℕ) : ℝ :=
  spectralEnvelopeEnergy geometricCentroidEnergy (localMarkedEigenlevel marks) n

/-- This combined geometric-spectral Q meets the original analytic
hypotheses, with no restriction on the sequence of local marks. -/
theorem markedSpectralGrid_admissible
    (marks : ℕ → Bool × Bool) (center direction : ℂ) :
    Admissible (markedSpectralGridEnergy marks) center direction :=
  spectralEnvelopeEnergy_admissible geometricCentroidEnergy
    (localMarkedEigenlevel marks)
    (fun n => centroidEnergy_pos (gridPoint n))
    geometricCentroidEnergy_inv_sq_summable center direction

/-- Original Theorem C applied to the *spectrally enriched* energies. -/
theorem markedSpectralGrid_theoremC
    (marks : ℕ → Bool × Bool)
    (center direction s : ℂ) (hd : direction ≠ 0)
    (hz : canonicalProduct (markedSpectralGridEnergy marks)
      center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) :=
  theoremC_zero_localization
    (markedSpectralGrid_admissible marks center direction) hd hz

/-- Each Q(n), depending on a verified local operator eigenvalue,
provides a zero of the infinite canonical product *at that level*. -/
theorem markedSpectralGrid_zero_at_level
    (marks : ℕ → Bool × Bool) (center direction : ℂ)
    (hd : direction ≠ 0) (n : ℕ) :
    canonicalProduct (markedSpectralGridEnergy marks) center direction
      (center + direction * (markedSpectralGridEnergy marks n : ℂ)) = 0 := by
  exact spectralEnvelope_has_zero_at_each_level geometricCentroidEnergy
    (localMarkedEigenlevel marks)
    (fun k => centroidEnergy_pos (gridPoint k))
    center direction hd n

/-- For aligned marks the spectral correction to any baseline Q
is exactly 25/16, by the computed eigenvalue 3/4. -/
theorem aligned_spectral_multiplier (base : ℝ) :
    base * (1 + (markedDefectCoupling true true) ^ 2) =
      base * (25 / 16) := by
  rw [aligned_marked_coupling]
  ring

/-- For opposed marks it becomes 13/4, by the eigenvalue 3/2.
Hence the same geometric envelope can give different zero levels. -/
theorem opposed_spectral_multiplier (base : ℝ) :
    base * (1 + (markedDefectCoupling true false) ^ 2) =
      base * (13 / 4) := by
  rw [opposed_marked_coupling]
  ring

/-- The local eigenvalue information makes the Q-levels genuinely
different for aligned and opposed marks whenever the baseline is
strictly positive. -/
theorem orientation_changes_energy (base : ℝ) (hb : 0 < base) :
    base * (1 + (markedDefectCoupling true true) ^ 2) ≠
      base * (1 + (markedDefectCoupling true false) ^ 2) := by
  rw [aligned_spectral_multiplier, opposed_spectral_multiplier]
  intro h
  nlinarith

end
end InfiniteTilings
