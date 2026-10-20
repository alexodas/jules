module

public import Mathlib

public section

/-!
# Paired canonical products: convergence and prescribed-line zeros

The independent statement surface of SpectralGeometry/CanonicalProduct.lean.
Positive levels q(n) determine paired quadratic factors. Admissibility means
a summable majorant for deviations from one on every compact set.

Theorem C proves that zeros of this *constructed* infinite product lie on
the chosen affine real line; it does not concern zeros of the zeta function
or identify the levels with any spectral operator. Inverse-square summability
is a sufficient condition for admissibility. The sorry lines here are
Comparator's intentional challenge holes; proved declarations are in Solution.
-/

open Filter
open scoped BigOperators

namespace SpectralGeometry

noncomputable section

/-- The perturbation of 1 in the paired canonical factor. -/
@[expose] def perturb (q : ℕ → ℝ) (center direction : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  -(((s - center) / direction) ^ 2 / ((q n : ℂ) ^ 2))

/-- A factor corresponding to the symmetric geometric levels `±q n`. -/
@[expose] def factor (q : ℕ → ℝ) (center direction : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  1 + perturb q center direction n s

/-- The infinite paired (regularized) product. -/
@[expose] def canonicalProduct (q : ℕ → ℝ) (center direction : ℂ) (s : ℂ) : ℂ :=
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


theorem product_uniform_on_compact
    {q : ℕ → ℝ} {center direction : ℂ}
    (h : Admissible q center direction)
    (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun n s => factor q center direction n s)
      (canonicalProduct q center direction) K := by
  sorry

theorem factor_zero_on_line
    {q : ℕ → ℝ} {center direction s : ℂ}
    (h : Admissible q center direction)
    (hd : direction ≠ 0)
    (n : ℕ)
    (hz : factor q center direction n s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) := by
  sorry

theorem theoremC_zero_localization
    {q : ℕ → ℝ} {center direction s : ℂ}
    (h : Admissible q center direction)
    (hd : direction ≠ 0)
    (hz : canonicalProduct q center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) := by
  sorry

theorem admissible_of_inv_sq_summable
    {q : ℕ → ℝ} (hq : ∀ n, 0 < q n)
    (hsum : Summable (fun n => 1 / (q n) ^ 2))
    (center direction : ℂ) : Admissible q center direction := by
  sorry

theorem factor_zero_at_positive_level
    (q : ℕ → ℝ) (n : ℕ)
    (hq : q n ≠ 0)
    (center direction : ℂ) (hd : direction ≠ 0) :
    factor q center direction n
      (center + direction * (q n : ℂ)) = 0 := by
  sorry

theorem canonicalProduct_zero_at_positive_level
    (q : ℕ → ℝ) (n : ℕ) (hq : q n ≠ 0)
    (center direction : ℂ) (hd : direction ≠ 0) :
    canonicalProduct q center direction
      (center + direction * (q n : ℂ)) = 0 := by
  sorry

end
end SpectralGeometry
