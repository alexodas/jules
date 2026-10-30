module

public import SpectralGeometry.CanonicalProductAnalytic

public section

/-!
# Explicit scalar error for finite canonical products

The error is controlled by the inverse-square tail, with no division by a
finite product and hence no zero-free assumption. These are truncations of
a fixed spectral sequence, not finite-patch operators.
-/

namespace SpectralGeometry

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Initial factors of the same canonical product, including the empty
product at `N = 0`. -/
@[expose] def canonicalPartialProduct (q : ℕ → ℝ) (c d : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∏ n ∈ Finset.range N, factor q c d n z

/-- A quantitative truncation bound on any set where the squared affine
coordinate is at most `A`. Its tail is an explicit analytic input. -/
@[expose] def canonicalProductApproximationError (q : ℕ → ℝ) (A : ℝ) (N : ℕ) : ℝ :=
  Real.exp (A * ∑' n, 1 / (q n) ^ 2) *
    (Real.exp (A * ∑' k, 1 / (q (k + N)) ^ 2) - 1)

/-- Pass the finite-product exponential bound to the infinite product. -/
theorem norm_tprod_one_add_sub_one_le_exp_tsum (u : ℕ → ℂ)
    (hu : Summable (fun n => ‖u n‖)) :
    ‖(∏' n, (1 + u n)) - 1‖ ≤ Real.exp (∑' n, ‖u n‖) - 1 := by
  have hp := (multipliable_one_add_of_summable hu).hasProd.tendsto_prod_nat
  have hs := hu.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto ((hp.sub tendsto_const_nhds).norm)
    ((Real.continuous_exp.tendsto _ |>.comp hs).sub tendsto_const_nhds)
    (Eventually.of_forall (fun N => (Finset.range N).norm_prod_one_add_sub_one_le u))

/-- A summable majorant yields an absolute truncation error, including at
zeros of the partial product. No logarithmic branch is chosen. -/
theorem tprod_one_add_truncation_error (u : ℕ → ℂ) (b : ℕ → ℝ)
    (hb : Summable b) (hbound : ∀ n, ‖u n‖ ≤ b n) (N : ℕ) :
    ‖(∏' n, (1 + u n)) - ∏ n ∈ Finset.range N, (1 + u n)‖ ≤
      Real.exp (∑' n, b n) * (Real.exp (∑' k, b (k + N)) - 1) := by
  have hb0 : ∀ n, 0 ≤ b n := fun n => (norm_nonneg _).trans (hbound n)
  have hu := Summable.of_nonneg_of_le (fun n => norm_nonneg (u n)) hbound hb
  have hut : Summable (fun k => ‖u (k + N)‖) := (summable_nat_add_iff N).mpr hu
  have hbt : Summable (fun k => b (k + N)) := (summable_nat_add_iff N).mpr hb
  have hprod : ‖∏ n ∈ Finset.range N, (1 + u n)‖ ≤ Real.exp (∑' n, b n) := by
    have hfinite := (Finset.range N).norm_prod_one_add_sub_one_le u
    have hnorm := norm_le_norm_sub_add (∏ n ∈ Finset.range N, (1 + u n)) 1
    have hsum : (∑ n ∈ Finset.range N, ‖u n‖) ≤ ∑' n, b n :=
      (Finset.sum_le_sum (fun n _ => hbound n)).trans
        (hb.sum_le_tsum _ (fun n _ => hb0 n))
    have hexp := Real.exp_le_exp.mpr hsum
    simp only [norm_one] at hnorm
    linarith
  have htail : ‖(∏' k, (1 + u (k + N))) - 1‖ ≤ Real.exp (∑' k, b (k + N)) - 1 :=
    (norm_tprod_one_add_sub_one_le_exp_tsum (fun k => u (k + N)) hut).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr
        (hut.tsum_le_tsum (fun k => hbound (k + N)) hbt)) 1)
  have hsplit := Multipliable.prod_mul_tprod_nat_mul'
    (f := fun n => 1 + u n) (k := N) (multipliable_one_add_of_summable hut)
  rw [← hsplit, ← mul_sub_one, norm_mul]
  exact mul_le_mul hprod htail (norm_nonneg _) (Real.exp_pos _).le

theorem canonicalProductApproximationError_nonneg (q : ℕ → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (N : ℕ) : 0 ≤ canonicalProductApproximationError q A N := by
  unfold canonicalProductApproximationError
  apply mul_nonneg (Real.exp_pos _).le
  exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hA (tsum_nonneg (fun _ => by positivity))))

/-- Independently verified upper bounds for the total inverse-square sum
and its tail give a scalar error budget containing no infinite sums. -/
theorem canonicalProductApproximationError_le_of_bounds (q : ℕ → ℝ)
    {A S T : ℝ} (hA : 0 ≤ A) (N : ℕ)
    (hS : (∑' n, 1 / (q n) ^ 2) ≤ S)
    (hT : (∑' k, 1 / (q (k + N)) ^ 2) ≤ T) :
    canonicalProductApproximationError q A N ≤
      Real.exp (A * S) * (Real.exp (A * T) - 1) := by
  unfold canonicalProductApproximationError
  apply mul_le_mul
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hS hA))
    (sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT hA)) 1)
  · exact sub_nonneg.mpr (Real.one_le_exp
      (mul_nonneg hA (tsum_nonneg (fun _ => by positivity))))
  · exact (Real.exp_pos _).le

/-- Explicit pointwise error, uniform whenever the affine-coordinate bound
`A` is uniform. Positivity and inverse-square summability are the same
inputs used to construct admissibility of the full product. -/
theorem canonicalProduct_partial_error_le {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hs : Summable (fun n => 1 / (q n) ^ 2))
    (c d : ℂ) (N : ℕ) {A : ℝ} {z : ℂ}
    (hz : ‖(z - c) / d‖ ^ 2 ≤ A) :
    ‖canonicalProduct q c d z - canonicalPartialProduct q c d N z‖ ≤
      canonicalProductApproximationError q A N := by
  have hb := hs.mul_left A
  have hbound : ∀ n, ‖perturb q c d n z‖ ≤ A * (1 / (q n) ^ 2) := by
    intro n
    have hden : ‖(q n : ℂ) ^ 2‖ = (q n) ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq n)]
    rw [perturb, norm_neg, norm_div, norm_pow, hden, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hz (by positivity)
  have he := tprod_one_add_truncation_error (fun n => perturb q c d n z)
    (fun n => A * (1 / (q n) ^ 2)) hb hbound N
  simpa only [canonicalProduct, canonicalPartialProduct, factor,
    canonicalProductApproximationError, tsum_mul_left] using he

/-- The explicit error tends to zero for every fixed affine-coordinate
bound. A numerical rate still requires a numerical bound for the tail. -/
theorem canonicalProductApproximationError_tendsto_zero {q : ℕ → ℝ}
    (_hs : Summable (fun n => 1 / (q n) ^ 2)) (A : ℝ) :
    Tendsto (canonicalProductApproximationError q A) atTop (𝓝 0) := by
  unfold canonicalProductApproximationError
  have ht := tendsto_sum_nat_add (fun n => 1 / (q n) ^ 2)
  have he := (Real.continuous_exp.tendsto _).comp (ht.const_mul A)
  simpa only [mul_zero, Real.exp_zero, sub_self, Function.comp_apply] using
    (he.sub (tendsto_const_nhds (x := (1 : ℝ)))).const_mul
      (Real.exp (A * ∑' n, 1 / (q n) ^ 2))

/-- Any additional certified error in the finite approximation adds to the
tail bound. This permits approximate coefficients or another analytic
approximant without identifying it with a finite-patch operator. -/
theorem canonicalProduct_approximation_error_add {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hs : Summable (fun n => 1 / (q n) ^ 2))
    (c d : ℂ) (N : ℕ) {A η : ℝ} {g : ℂ → ℂ} {z : ℂ}
    (hz : ‖(z - c) / d‖ ^ 2 ≤ A)
    (hg : ‖g z - canonicalPartialProduct q c d N z‖ ≤ η) :
    ‖g z - canonicalProduct q c d z‖ ≤ canonicalProductApproximationError q A N + η := by
  have he := canonicalProduct_partial_error_le hq hs c d N hz
  calc
    ‖g z - canonicalProduct q c d z‖ ≤
        ‖g z - canonicalPartialProduct q c d N z‖ +
          ‖canonicalPartialProduct q c d N z - canonicalProduct q c d z‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ η + canonicalProductApproximationError q A N :=
      add_le_add hg (by simpa [norm_sub_rev] using he)
    _ = _ := add_comm _ _

end
end SpectralGeometry
