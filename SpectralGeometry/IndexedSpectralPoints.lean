module

public import SpectralGeometry.CanonicalProductZeroOrder

public section

/-!
# Algebraic displacement of indexed spectral points

Both signs use a fixed center and direction. The exact norm identities
keep the absolute value of the real difference until monotonicity is known.
-/

namespace SpectralGeometry

noncomputable section

/-- The positive point associated with the n-th real level. -/
@[expose] def positiveSpectralPoint (ev : ℕ → ℝ) (c d : ℂ) (n : ℕ) : ℂ :=
  c + d * (ev n : ℂ)

/-- The negative point associated with the n-th real level. -/
@[expose] def negativeSpectralPoint (ev : ℕ → ℝ) (c d : ℂ) (n : ℕ) : ℂ :=
  c - d * (ev n : ℂ)

theorem positiveSpectralPoint_sub (ev μ : ℕ → ℝ) (c d : ℂ) (n : ℕ) :
    positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n =
      d * ((μ n - ev n : ℝ) : ℂ) := by
  simp only [positiveSpectralPoint, Complex.ofReal_sub]
  ring

theorem negativeSpectralPoint_sub (ev μ : ℕ → ℝ) (c d : ℂ) (n : ℕ) :
    negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n =
      -d * ((μ n - ev n : ℝ) : ℂ) := by
  simp only [negativeSpectralPoint, Complex.ofReal_sub]
  ring

theorem positiveSpectralPoint_sub_norm (ev μ : ℕ → ℝ) (c d : ℂ) (n : ℕ) :
    ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ =
      ‖d‖ * |μ n - ev n| := by
  rw [positiveSpectralPoint_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem negativeSpectralPoint_sub_norm (ev μ : ℕ → ℝ) (c d : ℂ) (n : ℕ) :
    ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ =
      ‖d‖ * |μ n - ev n| := by
  rw [negativeSpectralPoint_sub, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]

/-- Ordered real response removes the absolute value, simultaneously for
both points. The lower coefficient is required nonnegative here. -/
theorem indexedSpectralPoints_norm_bounds (ev μ : ℕ → ℝ) (c d : ℂ)
    (κ τ : ℝ) (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    (n : ℕ) (hlo : κ * τ ≤ μ n - ev n) (hhi : μ n - ev n ≤ τ) :
    (‖d‖ * (κ * τ) ≤
        ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ ∧
      ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ ≤
        ‖d‖ * τ) ∧
    (‖d‖ * (κ * τ) ≤
        ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ ∧
      ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ ≤
        ‖d‖ * τ) := by
  have hnonneg : 0 ≤ μ n - ev n := (mul_nonneg hκ hτ).trans hlo
  rw [positiveSpectralPoint_sub_norm, negativeSpectralPoint_sub_norm,
    abs_of_nonneg hnonneg]
  exact ⟨⟨mul_le_mul_of_nonneg_left hlo (norm_nonneg d),
    mul_le_mul_of_nonneg_left hhi (norm_nonneg d)⟩,
    ⟨mul_le_mul_of_nonneg_left hlo (norm_nonneg d),
    mul_le_mul_of_nonneg_left hhi (norm_nonneg d)⟩⟩

/-- Strict positive response moves each indexed point, even if a different
index at the other parameter can occupy the same complex location. -/
theorem indexedSpectralPoints_ne (ev μ : ℕ → ℝ) (c d : ℂ)
    (hd : d ≠ 0) (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ)
    (n : ℕ) (hlo : κ * τ ≤ μ n - ev n) :
    positiveSpectralPoint μ c d n ≠ positiveSpectralPoint ev c d n ∧
    negativeSpectralPoint μ c d n ≠ negativeSpectralPoint ev c d n := by
  have hdiff : μ n - ev n ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (mul_pos hκ hτ) hlo)
  constructor
  · intro heq
    have heq' := positiveSpectralPoint_sub ev μ c d n
    rw [heq, sub_self] at heq'
    exact (mul_ne_zero hd (by exact_mod_cast hdiff)) heq'.symm
  · intro heq
    have heq' := negativeSpectralPoint_sub ev μ c d n
    rw [heq, sub_self] at heq'
    exact (mul_ne_zero (neg_ne_zero.mpr hd) (by exact_mod_cast hdiff)) heq'.symm

end
end SpectralGeometry
