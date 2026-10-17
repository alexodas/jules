import SpectralGeometry.FinitePerturbation

/-!
# Nonnegative quadratic energy under controlled perturbations

We define quadratic energy for finite real matrices and prove that the
energy of the perturbed geometric operator splits into the original
geometric energy and the epsilon-scaled perturbation energy.

If both contributions are nonnegative, the total energy is nonnegative
for nonnegative epsilon. A strictly positive base energy remains strictly
positive. These are finite-dimensional and conditional statements.
-/

namespace SpectralGeometry

variable {Tile : Type*} [Fintype Tile] [DecidableEq Tile]

/-- The quadratic energy of a finite real matrix on a tile configuration. -/
noncomputable def finiteQuadraticEnergy
    (M : Matrix Tile Tile ℝ) (ψ : Tile → ℝ) : ℝ :=
  ∑ t : Tile, ∑ u : Tile, ψ t * (M t u * ψ u)

/-- The quadratic energy decomposes into geometric and perturbation parts. -/
theorem finitePerturbedMatrix_energy_eq
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ) (ψ : Tile → ℝ) :
    finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ =
      finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ +
        ε * finiteQuadraticEnergy P ψ := by
  classical
  unfold finiteQuadraticEnergy finitePerturbedMatrix
  calc
    (∑ t : Tile, ∑ u : Tile,
      ψ t * ((finiteUnperturbedMatrix V w t u + ε * P t u) * ψ u)) =
      (∑ t : Tile, ∑ u : Tile,
        (ψ t * (finiteUnperturbedMatrix V w t u * ψ u) +
          ε * (ψ t * (P t u * ψ u)))) := by
            apply Finset.sum_congr rfl
            intro t ht
            apply Finset.sum_congr rfl
            intro u hu
            ring
    _ = (∑ t : Tile, ∑ u : Tile,
          ψ t * (finiteUnperturbedMatrix V w t u * ψ u)) +
        ε * (∑ t : Tile, ∑ u : Tile, ψ t * (P t u * ψ u)) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- A nonnegative perturbation cannot destroy nonnegative quadratic energy
when its coupling parameter is nonnegative. -/
theorem finitePerturbedMatrix_energy_nonneg
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hBase : ∀ ψ : Tile → ℝ,
      0 ≤ finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ)
    (hP : ∀ ψ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P ψ)
    (hε : 0 ≤ ε) (ψ : Tile → ℝ) :
    0 ≤ finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ := by
  rw [finitePerturbedMatrix_energy_eq]
  exact add_nonneg (hBase ψ) (mul_nonneg hε (hP ψ))

/-- Strictly positive base energy stays strictly positive under a
nonnegative perturbation. -/
theorem finitePerturbedMatrix_energy_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hBase : ∀ ψ : Tile → ℝ, (∃ t, ψ t ≠ 0) →
      0 < finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ)
    (hP : ∀ ψ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P ψ)
    (hε : 0 ≤ ε) (ψ : Tile → ℝ)
    (hψ : ∃ t, ψ t ≠ 0) :
    0 < finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ := by
  rw [finitePerturbedMatrix_energy_eq]
  exact add_pos_of_pos_of_nonneg (hBase ψ hψ) (mul_nonneg hε (hP ψ))

end SpectralGeometry
