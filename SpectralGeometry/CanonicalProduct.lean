import Mathlib

/-!
# Canonical product: zeros on a prescribed line

A family of positive levels `q n` is called admissible
when the paired factors have a summable majorant on each compact set.
The paired factor `1 - ((s - center) / direction)^2 / (q n)^2`
is a regularized product: the potentially divergent first-order terms
cancel between the two roots.

This module does NOT identify its zeros with the zeros of Riemann's zeta.
-/

open Filter
open scoped BigOperators

namespace SpectralGeometry

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

The sufficient bound `∑ n, (q n)⁻² < ∞` is proved below.
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



/-- Summable inverse squares imply the compact-majorant condition. -/
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


/-- The n-th factor has a zero at its positive level. -/
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


end
end SpectralGeometry
