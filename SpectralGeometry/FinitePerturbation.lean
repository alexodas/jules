import Mathlib

/-!
# Finite geometric operators with a controlled perturbation

This file is a first finite-dimensional step toward the infinite tiling operator.

For a finite type of tiles, we construct a real matrix with three contributions:
* a potential depending on the individual tile;
* a weighted Laplacian built from pairwise interactions;
* an independent perturbation scaled by a real parameter `ε`.

The diagonal interaction coefficient sums only over *other* tiles.
The main theorem proves that symmetric weights and a symmetric perturbation
give a symmetric matrix for every real `ε`.

This does not yet construct an infinite operator or establish positivity,
compact resolvent, or eigenvalue summability.
-/

namespace SpectralGeometry

variable {Tile : Type*} [Fintype Tile] [DecidableEq Tile]

/-- Finite geometric matrix: individual energy plus pairwise interactions.
The off-diagonal entries are `-w t u`; the diagonal sums `w t u`
over the other tiles `u`. -/
noncomputable def finiteUnperturbedMatrix
    (V : Tile → ℝ) (w : Tile → Tile → ℝ) : Matrix Tile Tile ℝ :=
  fun t u =>
    if t = u then
      V t + ∑ v : Tile, if v = t then (0 : ℝ) else w t v
    else
      -w t u

/-- The finite geometric matrix with an independently chosen perturbation `P`,
scaled by the real control parameter `ε`. -/
noncomputable def finitePerturbedMatrix
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ) : Matrix Tile Tile ℝ :=
  fun t u => finiteUnperturbedMatrix V w t u + ε * P t u

/-- Symmetric pairwise interaction weights yield a symmetric unperturbed matrix. -/
theorem finiteUnperturbedMatrix_symmetric
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hw : ∀ t u, w t u = w u t) :
    ∀ t u, finiteUnperturbedMatrix V w t u =
      finiteUnperturbedMatrix V w u t := by
  intro t u
  by_cases htu : t = u
  · subst u
    rfl
  · simp only [finiteUnperturbedMatrix, if_neg htu, if_neg (Ne.symm htu)]
    rw [hw t u]

/-- **First perturbed-operator theorem.** If the geometric weights and the
perturbation matrix are symmetric, the complete matrix remains symmetric
for *every* real value of the perturbation parameter. -/
theorem finitePerturbedMatrix_symmetric
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hw : ∀ t u, w t u = w u t)
    (hP : ∀ t u, P t u = P u t) :
    ∀ t u, finitePerturbedMatrix V w P ε t u =
      finitePerturbedMatrix V w P ε u t := by
  intro t u
  change finiteUnperturbedMatrix V w t u + ε * P t u =
    finiteUnperturbedMatrix V w u t + ε * P u t
  rw [finiteUnperturbedMatrix_symmetric V w hw t u, hP t u]

/-- Switching the perturbation off recovers exactly the geometric matrix. -/
theorem finitePerturbedMatrix_zero
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) :
    finitePerturbedMatrix V w P 0 = finiteUnperturbedMatrix V w := by
  ext t u
  simp [finitePerturbedMatrix]

end SpectralGeometry
