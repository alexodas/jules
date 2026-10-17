import SpectralGeometry.InfiniteOnsiteSummability

/-!
# Power-law onsite energies: the inverse-square threshold

The earlier linear-growth assumption can be relaxed. For an onsite
operator on ℓ²(ℕ), if V(n) is at least (n+1)^alpha and alpha > 1/2,
then its inverse-square eigenvalue series converges.

For the exact model V(n) = (n+1)^alpha, the exponent threshold is sharp:
at alpha ≤ 1/2 the reciprocal-square series diverges.

This is conditional on a chosen enumeration and an explicit growth
bound. No specific tiling has been proved to satisfy that bound, and
we do not claim results for the full interacting geometric operator.
-/

namespace SpectralGeometry

private theorem onsite_power_square_eq
    (alpha : ℝ) (n : ℕ) :
    ((((n + 1 : ℕ) : ℝ) ^ alpha) ^ 2) =
      (((n + 1 : ℕ) : ℝ) ^ (2 * alpha)) := by
  have hn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  simpa only [mul_comm alpha (2 : ℝ)] using
    (Real.rpow_mul_natCast hn alpha 2).symm

/-- A power-law lower bound with exponent greater than one half is
sufficient for square-reciprocal summability. The potential need not
be linear in the tile index. -/
theorem infiniteOnsitePowerGrowth_invSq_summable
    (V : ℕ → ℝ) (alpha : ℝ) (halpha : (1 / 2 : ℝ) < alpha)
    (hGrowth : ∀ n, (((n + 1 : ℕ) : ℝ) ^ alpha) ≤ V n) :
    Summable (fun n : ℕ => 1 / (V n) ^ 2) := by
  have hExponent : (1 : ℝ) < 2 * alpha := by linarith
  have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * alpha)) :=
    (Real.summable_one_div_nat_rpow (p := 2 * alpha)).mpr hExponent
  have hshift :
      Summable (fun n : ℕ =>
        (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ (2 * alpha))) := by
    simpa using
      ((summable_nat_add_iff
        (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * alpha)) 1).mpr hp)
  apply Summable.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hpositive : 0 < (((n + 1 : ℕ) : ℝ) ^ alpha) :=
      Real.rpow_pos_of_pos hn alpha
    have hsq :
        ((((n + 1 : ℕ) : ℝ) ^ alpha) ^ 2) ≤ (V n) ^ 2 := by
      gcongr
      exact hGrowth n
    calc
      1 / (V n) ^ 2 ≤
          1 / ((((n + 1 : ℕ) : ℝ) ^ alpha) ^ 2) :=
        one_div_le_one_div_of_le (pow_pos hpositive 2) hsq
      _ = 1 / (((n + 1 : ℕ) : ℝ) ^ (2 * alpha)) := by
        rw [onsite_power_square_eq]
  · exact hshift

/-- The power-law lower bound automatically keeps onsite levels
strictly positive. -/
theorem infiniteOnsitePowerGrowth_positive
    (V : ℕ → ℝ) (alpha : ℝ)
    (hGrowth : ∀ n, (((n + 1 : ℕ) : ℝ) ^ alpha) ≤ V n)
    (n : ℕ) : 0 < V n := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hn alpha) (hGrowth n)

/-- Power-law growth above the threshold supplies exactly the
admissibility assumption of the existing canonical-product theory. -/
theorem infiniteOnsitePowerGrowth_admissible
    (V : ℕ → ℝ) (alpha : ℝ) (halpha : (1 / 2 : ℝ) < alpha)
    (hGrowth : ∀ n, (((n + 1 : ℕ) : ℝ) ^ alpha) ≤ V n)
    (center direction : ℂ) :
    Admissible V center direction :=
  admissible_of_inv_sq_summable
    (infiniteOnsitePowerGrowth_positive V alpha hGrowth)
    (infiniteOnsitePowerGrowth_invSq_summable V alpha halpha hGrowth)
    center direction

/-- Sharpness for the exact power-law example: at exponent at most
one half, its inverse-square series is not summable. This does NOT
assert divergence for arbitrary potentials with only a lower bound. -/
theorem infiniteOnsiteExactPower_not_invSq_summable
    (alpha : ℝ) (halpha : alpha ≤ (1 / 2 : ℝ)) :
    ¬ Summable (fun n : ℕ =>
      1 / (((((n + 1 : ℕ) : ℝ) ^ alpha) ^ 2))) := by
  intro hsum
  have hshift :
      Summable (fun n : ℕ =>
        (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ (2 * alpha))) := by
    apply hsum.congr
    intro n
    simp only [onsite_power_square_eq]
  have hp : Summable (fun n : ℕ =>
      (1 : ℝ) / (n : ℝ) ^ (2 * alpha)) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * alpha)) 1).mp
      (by simpa using hshift)
  have hExponent : (1 : ℝ) < 2 * alpha :=
    (Real.summable_one_div_nat_rpow (p := 2 * alpha)).mp hp
  linarith

end SpectralGeometry
