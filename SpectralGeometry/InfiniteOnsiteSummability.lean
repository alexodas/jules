import SpectralGeometry.CanonicalProduct
import SpectralGeometry.InfiniteOnsiteEigenvalues

/-!
# Linear growth of infinite onsite energies and inverse-square summability

For tiles indexed by natural numbers, a concrete sufficient condition for
the square-reciprocal summability required by the canonical product is

  (n + 1 : ℝ) ≤ V n.

This bound is an explicit hypothesis, **not** a property proved from any
particular tiling. We also show that each V n is an actual eigenvalue
of the diagonal onsite operator, with a single-tile eigenvector.

No interaction Laplacian, perturbation, compact-resolvent theorem, or
connection with the Riemann zeta zeros is established here.
-/

namespace SpectralGeometry

/-- A linear lower bound forces every onsite energy to be positive. -/
theorem infiniteOnsiteLinearGrowth_positive
    (V : ℕ → ℝ) (hGrowth : ∀ n, ((n + 1 : ℕ) : ℝ) ≤ V n)
    (n : ℕ) : 0 < V n := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  exact lt_of_lt_of_le hn (hGrowth n)

/-- Linear growth forces summability of the inverse squares of the
onsite energy levels, including for an infinite set of tiles. -/
theorem infiniteOnsiteLinearGrowth_invSq_summable
    (V : ℕ → ℝ) (hGrowth : ∀ n, ((n + 1 : ℕ) : ℝ) ≤ V n) :
    Summable (fun n : ℕ => 1 / (V n) ^ 2) := by
  have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift :
      Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa using
      ((summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hp)
  apply Summable.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hv : 0 < V n := infiniteOnsiteLinearGrowth_positive V hGrowth n
    have hsq : (((n + 1 : ℕ) : ℝ) ^ 2) ≤ (V n) ^ 2 := by
      gcongr
      exact hGrowth n
    exact one_div_le_one_div_of_le (pow_pos hn 2) hsq
  · exact hshift

/-- The summability estimate gives the exact admissibility hypothesis
needed by the already-checked paired canonical-product theory. -/
theorem infiniteOnsiteLinearGrowth_admissible
    (V : ℕ → ℝ) (hGrowth : ∀ n, ((n + 1 : ℕ) : ℝ) ≤ V n)
    (center direction : ℂ) :
    Admissible V center direction :=
  admissible_of_inv_sq_summable
    (infiniteOnsiteLinearGrowth_positive V hGrowth)
    (infiniteOnsiteLinearGrowth_invSq_summable V hGrowth)
    center direction

/-- Every tile energy really is a point eigenvalue of the diagonal
operator, witnessed by the state supported on that tile. -/
theorem infiniteOnsiteNat_single_eigenvector
    (V : ℕ → ℝ) (n : ℕ) :
    ∃ ψ : infiniteOnsiteDomain V,
      ψ.1 n = 1 ∧
        infiniteOnsiteOperator V ψ = V n • (ψ.1 : TileHilbert ℕ) := by
  classical
  let e : TileHilbert ℕ := lp.single (2 : ENNReal) n (1 : ℝ)
  have he : e ∈ infiniteOnsiteDomain V := infiniteOnsiteDomain_single V n 1
  let ψ : infiniteOnsiteDomain V := ⟨e, he⟩
  refine ⟨ψ, ?_, ?_⟩
  · change e n = 1
    simp [e]
  · apply lp.ext
    funext t
    change V t * e t = V n * e t
    by_cases ht : t = n
    · subst t
      rfl
    · have hz : e t = 0 := by
        simp [e, lp.single_apply, Pi.single_eq_of_ne ht]
      simp [hz]

end SpectralGeometry
