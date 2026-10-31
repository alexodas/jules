module

public import SpectralGeometry.CanonicalProductApproximation
public import SpectralGeometry.InfiniteOnsiteSummability

public section

/-!
# Numerical tails and lower bounds for canonical products

Linear spectral growth gives a certified inverse-square tail `1 / N`.
On bounded affine-coordinate disks this gives an explicit truncation rate.
A summable norm budget also gives a lower bound for a nonvanishing tail,
which can be combined with finitely many explicitly bounded factors.
-/

namespace SpectralGeometry

open Filter
open scoped Topology

noncomputable section

private theorem inv_sq_succ_le_difference {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  calc
    1 / (x + 1) ^ 2 ≤ 1 / (x * (x + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    _ = 1 / x - 1 / (x + 1) := by field_simp; ring

private theorem linear_inv_sq_partial_tail (N : ℕ) (hN : 0 < N) (K : ℕ) :
    (∑ k ∈ Finset.range K, 1 / ((k + N : ℕ) + 1 : ℝ) ^ 2) ≤
      1 / (N : ℝ) - 1 / ((K + N : ℕ) : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hp : (0 : ℝ) < ((K + N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K + N)
    have he := inv_sq_succ_le_difference hp
    push_cast at *
    rw [show (K : ℝ) + 1 + N = (K : ℝ) + N + 1 by ring]
    linarith

/-- A linear lower growth bound yields a numerical inverse-square tail.
The cutoff must be positive; the total series is bounded separately. -/
theorem invSq_tail_le_of_linear_growth {q : ℕ → ℝ}
    (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ q n) (N : ℕ) (hN : 0 < N) :
    (∑' k, 1 / (q (k + N)) ^ 2) ≤ 1 / (N : ℝ) := by
  have hs := infiniteOnsiteLinearGrowth_invSq_summable q (by simpa using hq)
  have ht := (summable_nat_add_iff N).mpr hs
  apply le_of_tendsto ht.hasSum.tendsto_sum_nat
  apply Eventually.of_forall
  intro K
  calc
    (∑ k ∈ Finset.range K, 1 / (q (k + N)) ^ 2) ≤
        ∑ k ∈ Finset.range K, 1 / ((k + N : ℕ) + 1 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by positivity) (hq (k + N)) 2
    _ ≤ 1 / (N : ℝ) - 1 / ((K + N : ℕ) : ℝ) := linear_inv_sq_partial_tail N hN K
    _ ≤ 1 / (N : ℝ) := sub_le_self _ (by positivity)

/-- The total inverse-square series is at most two under unit linear growth. -/
theorem invSq_sum_le_two_of_linear_growth {q : ℕ → ℝ}
    (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ q n) : (∑' n, 1 / (q n) ^ 2) ≤ 2 := by
  have hs := infiniteOnsiteLinearGrowth_invSq_summable q (by simpa using hq)
  have htail := invSq_tail_le_of_linear_growth hq 1 (by norm_num)
  have hfirst : 1 / (q 0) ^ 2 ≤ 1 := by
    have hq0 := hq 0
    norm_num at hq0
    exact (div_le_one (by positivity)).mpr (by nlinarith)
  have hsplit := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_one, div_one] at hsplit htail
  linarith

/-- A deliberately conservative rational rate, uniform for squared affine
coordinates at most two. No numerical evaluation of `exp` is assumed. -/
theorem canonicalProductApproximationError_le_linear_rate {q : ℕ → ℝ}
    (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ q n) {A : ℝ} (hA : 0 ≤ A) (hA2 : A ≤ 2)
    (N : ℕ) (hN : 2 ≤ N) :
    canonicalProductApproximationError q A N ≤ 324 / (N : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 ≤ A * (1 / (N : ℝ)) := by positivity
  have hx1 : A * (1 / (N : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_one hNp]
    exact hA2.trans hNr
  have htail : Real.exp (A * (1 / (N : ℝ))) - 1 ≤ 4 / (N : ℝ) := by
    have he := Real.abs_exp_sub_one_le (x := A * (1 / (N : ℝ)))
      (by rw [abs_of_nonneg hx0]; exact hx1)
    have he' := (le_abs_self (Real.exp (A * (1 / (N : ℝ))) - 1)).trans he
    rw [abs_of_nonneg hx0] at he'
    calc
      _ ≤ 2 * (A * (1 / (N : ℝ))) := he'
      _ ≤ 2 * (2 * (1 / (N : ℝ))) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hA2 (le_of_lt (one_div_pos.mpr hNp))) (by norm_num)
      _ = 4 / (N : ℝ) := by ring
  have hexp : Real.exp (A * 2) ≤ 81 := by
    calc
      Real.exp (A * 2) ≤ Real.exp 4 := Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp 1) ^ 4 := by simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 4
      _ ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 4
      _ = 81 := by norm_num
  calc
    canonicalProductApproximationError q A N ≤
        Real.exp (A * 2) * (Real.exp (A * (1 / (N : ℝ))) - 1) :=
      canonicalProductApproximationError_le_of_bounds q hA N
        (invSq_sum_le_two_of_linear_growth hq) (invSq_tail_le_of_linear_growth hq N (by omega))
    _ ≤ 81 * (4 / (N : ℝ)) :=
      mul_le_mul hexp htail (sub_nonneg.mpr (Real.one_le_exp hx0)) (by norm_num)
    _ = 324 / (N : ℝ) := by ring

private theorem norm_prod_one_add_ge_one_sub_sum (u : ℕ → ℂ) (s : Finset ℕ)
    (hu : ∀ n ∈ s, ‖u n‖ ≤ 1) :
    1 - ∑ n ∈ s, ‖u n‖ ≤ ‖∏ n ∈ s, (1 + u n)‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    have hun := hu n (by simp)
    have hus := fun k hk => hu k (Finset.mem_insert_of_mem hk)
    have hi := ih hus
    have hl : 1 - ‖u n‖ ≤ ‖1 + u n‖ := by
      have ht := norm_sub_le (1 + u n) (u n)
      simpa only [add_sub_cancel_right, norm_one, sub_le_iff_le_add] using ht
    have hs : 0 ≤ ∑ k ∈ s, ‖u k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    rw [Finset.sum_insert hn, Finset.prod_insert hn, norm_mul]
    calc
      1 - (‖u n‖ + ∑ k ∈ s, ‖u k‖) ≤
          (1 - ‖u n‖) * (1 - ∑ k ∈ s, ‖u k‖) := by
            nlinarith [norm_nonneg (u n)]
      _ ≤ (1 - ‖u n‖) * ‖∏ k ∈ s, (1 + u k)‖ :=
        mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hun)
      _ ≤ ‖1 + u n‖ * ‖∏ k ∈ s, (1 + u k)‖ :=
        mul_le_mul_of_nonneg_right hl (norm_nonneg _)

/-- A small summable norm budget gives a lower bound for the entire tail
product, by passing finite product bounds to the limit. -/
theorem norm_tprod_one_add_ge_one_sub_tsum (u : ℕ → ℂ)
    (hu : Summable (fun n => ‖u n‖)) (hbudget : (∑' n, ‖u n‖) ≤ 1) :
    1 - ∑' n, ‖u n‖ ≤ ‖∏' n, (1 + u n)‖ := by
  have hpoint : ∀ n, ‖u n‖ ≤ 1 := fun n =>
    (hu.le_tsum n (fun _ _ => norm_nonneg _)).trans hbudget
  have hp := (multipliable_one_add_of_summable hu).hasProd.tendsto_prod_nat.norm
  have hs := (tendsto_const_nhds (x := (1 : ℝ))).sub hu.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto hs hp (Eventually.of_forall (fun N =>
    norm_prod_one_add_ge_one_sub_sum u (Finset.range N) (fun n _ => hpoint n)))

/-- A numerical inverse-square tail bound controls the modulus of the
corresponding complex tail product from below. -/
theorem canonicalProduct_tail_norm_lower {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hs : Summable (fun n => 1 / (q n) ^ 2))
    (c d : ℂ) (N : ℕ) {z : ℂ} {A T : ℝ} (hA : 0 ≤ A)
    (hz : ‖(z - c) / d‖ ^ 2 ≤ A)
    (hT : (∑' k, 1 / (q (k + N)) ^ 2) ≤ T) (hbudget : A * T ≤ 1) :
    1 - A * T ≤ ‖∏' k, factor q c d (k + N) z‖ := by
  have hbound : ∀ k, ‖perturb q c d (k + N) z‖ ≤ A * (1 / (q (k + N)) ^ 2) := by
    intro k
    have hden : ‖(q (k + N) : ℂ) ^ 2‖ = (q (k + N)) ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq (k + N))]
    rw [perturb, norm_neg, norm_div, norm_pow, hden, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hz (by positivity)
  have hmajor := ((summable_nat_add_iff N).mpr hs).mul_left A
  have hu := Summable.of_nonneg_of_le (fun k => norm_nonneg (perturb q c d (k + N) z))
    hbound hmajor
  have hsum : (∑' k, ‖perturb q c d (k + N) z‖) ≤ A * T := by
    calc
      _ ≤ ∑' k, A * (1 / (q (k + N)) ^ 2) := hu.tsum_le_tsum hbound hmajor
      _ = A * ∑' k, 1 / (q (k + N)) ^ 2 := tsum_mul_left
      _ ≤ A * T := mul_le_mul_of_nonneg_left hT hA
  have hl := norm_tprod_one_add_ge_one_sub_tsum
    (fun k => perturb q c d (k + N) z) hu (hsum.trans hbudget)
  exact (sub_le_sub_left hsum 1).trans (by simpa only [factor] using hl)

/-- Exact prefix/tail factorization, including at zeros of the prefix. -/
theorem canonicalProduct_eq_partial_mul_tail {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hs : Summable (fun n => 1 / (q n) ^ 2))
    (c d : ℂ) (N : ℕ) (z : ℂ) :
    canonicalProduct q c d z = canonicalPartialProduct q c d N z *
      ∏' k, factor q c d (k + N) z := by
  have hu := (summable_nat_add_iff N).mpr
    (canonical_perturb_norm_summable (admissible_of_inv_sq_summable hq hs c d) z)
  have hp : Multipliable (fun k => factor q c d (k + N) z) :=
    multipliable_one_add_of_summable hu
  exact (Multipliable.prod_mul_tprod_nat_mul'
    (f := fun n => factor q c d n z) (k := N) hp).symm

/-- A finite-prefix modulus certificate and a tail budget give a lower
bound for the full product. This can bound a local analytic cofactor
without evaluating the infinite product or assuming the desired bound. -/
theorem canonicalProduct_lower_of_prefix_tail {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hs : Summable (fun n => 1 / (q n) ^ 2))
    (c d : ℂ) (N : ℕ) {z : ℂ} {A T L : ℝ} (hA : 0 ≤ A)
    (hz : ‖(z - c) / d‖ ^ 2 ≤ A)
    (hT : (∑' k, 1 / (q (k + N)) ^ 2) ≤ T) (hbudget : A * T ≤ 1)
    (hprefix : L ≤ ‖canonicalPartialProduct q c d N z‖) :
    L * (1 - A * T) ≤ ‖canonicalProduct q c d z‖ := by
  rw [canonicalProduct_eq_partial_mul_tail hq hs c d N z, norm_mul]
  exact mul_le_mul hprefix (canonicalProduct_tail_norm_lower hq hs c d N hA hz hT hbudget)
    (sub_nonneg.mpr hbudget) (norm_nonneg _)

end
end SpectralGeometry
