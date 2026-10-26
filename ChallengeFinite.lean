module

public import Mathlib

public section

/-!
# Independent statement surface: finite geometry

This module does not import the proof modules. The intentional sorry terms
are holes for Comparator; the actual proofs live in the SolutionFinite module.
-/

namespace SpectralGeometry

variable {Tile : Type*} [Fintype Tile] [DecidableEq Tile]

@[expose] noncomputable def finiteUnperturbedMatrix
    (V : Tile → ℝ) (w : Tile → Tile → ℝ) : Matrix Tile Tile ℝ :=
  fun t u =>
    if t = u then
      V t + ∑ v : Tile, if v = t then (0 : ℝ) else w t v
    else
      -w t u

@[expose] noncomputable def finitePerturbedMatrix
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ) : Matrix Tile Tile ℝ :=
  fun t u => finiteUnperturbedMatrix V w t u + ε * P t u

@[expose] noncomputable def finiteQuadraticEnergy
    (M : Matrix Tile Tile ℝ) (ψ : Tile → ℝ) : ℝ :=
  ∑ t : Tile, ∑ u : Tile, ψ t * (M t u * ψ u)

-- Independently reproduced statement signatures from SpectralGeometry/FinitePerturbation.lean
theorem finiteUnperturbedMatrix_symmetric
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hw : ∀ t u, w t u = w u t) :
    ∀ t u, finiteUnperturbedMatrix V w t u =
      finiteUnperturbedMatrix V w u t := by
  sorry

theorem finitePerturbedMatrix_symmetric
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hw : ∀ t u, w t u = w u t)
    (hP : ∀ t u, P t u = P u t) :
    ∀ t u, finitePerturbedMatrix V w P ε t u =
      finitePerturbedMatrix V w P ε u t := by
  sorry

theorem finitePerturbedMatrix_zero
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) :
    finitePerturbedMatrix V w P 0 = finiteUnperturbedMatrix V w := by
  sorry

-- Independently reproduced statement signatures from SpectralGeometry/FinitePositiveEnergy.lean
theorem finitePerturbedMatrix_energy_eq
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ) (ψ : Tile → ℝ) :
    finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ =
      finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ +
        ε * finiteQuadraticEnergy P ψ := by
  sorry

theorem finitePerturbedMatrix_energy_nonneg
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hBase : ∀ ψ : Tile → ℝ,
      0 ≤ finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ)
    (hP : ∀ ψ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P ψ)
    (hε : 0 ≤ ε) (ψ : Tile → ℝ) :
    0 ≤ finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ := by
  sorry

theorem finitePerturbedMatrix_energy_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hBase : ∀ ψ : Tile → ℝ, (∃ t, ψ t ≠ 0) →
      0 < finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ)
    (hP : ∀ ψ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P ψ)
    (hε : 0 ≤ ε) (ψ : Tile → ℝ)
    (hψ : ∃ t, ψ t ≠ 0) :
    0 < finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ := by
  sorry

-- Independently reproduced statement signatures from SpectralGeometry/FiniteGeometricEnergy.lean
theorem finiteGeometricEnergy_sum_squares
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hw : ∀ t u, w t u = w u t)
    (hdiag : ∀ t, w t t = 0) (ψ : Tile → ℝ) :
    finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ =
      (∑ t : Tile, V t * ψ t ^ 2) +
        (1 / 2 : ℝ) * (∑ t : Tile, ∑ u : Tile,
          w t u * (ψ t - ψ u) ^ 2) := by
  sorry

theorem finiteGeometricEnergy_nonneg
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hV : ∀ t, 0 ≤ V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (ψ : Tile → ℝ) :
    0 ≤ finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ := by
  sorry

theorem finiteGeometricPerturbedEnergy_nonneg
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hV : ∀ t, 0 ≤ V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (hP : ∀ ψ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P ψ)
    (hε : 0 ≤ ε) (ψ : Tile → ℝ) :
    0 ≤ finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ := by
  sorry

-- Independently reproduced statement signatures from SpectralGeometry/FiniteStrictPositivity.lean
theorem finiteGeometricEnergy_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hV : ∀ t, 0 < V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (ψ : Tile → ℝ) (hψ : ∃ t, ψ t ≠ 0) :
    0 < finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ := by
  sorry

theorem finiteGeometricPerturbedEnergy_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hV : ∀ t, 0 < V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (hP : ∀ ψ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P ψ)
    (hε : 0 ≤ ε)
    (ψ : Tile → ℝ) (hψ : ∃ t, ψ t ≠ 0) :
    0 < finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ := by
  sorry

theorem finiteGeometricEigenvalue_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hV : ∀ t, 0 < V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (ψ : Tile → ℝ) (eigenvalue : ℝ)
    (hψ : ∃ t, ψ t ≠ 0)
    (heigen : ∀ t,
      (∑ u : Tile, finiteUnperturbedMatrix V w t u * ψ u) =
        eigenvalue * ψ t) :
    0 < eigenvalue := by
  sorry

theorem finiteGeometricPerturbedEigenvalue_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hV : ∀ t, 0 < V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (hP : ∀ χ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P χ)
    (hε : 0 ≤ ε)
    (ψ : Tile → ℝ) (eigenvalue : ℝ)
    (hψ : ∃ t, ψ t ≠ 0)
    (heigen : ∀ t,
      (∑ u : Tile, finitePerturbedMatrix V w P ε t u * ψ u) =
        eigenvalue * ψ t) :
    0 < eigenvalue := by
  sorry

end SpectralGeometry
