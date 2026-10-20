module

public import SpectralGeometry.FiniteGeometricEnergy

public section

/-!
# Strictly positive finite geometric energy and eigenvalues

This file upgrades nonnegative quadratic energy to *strict* positivity on
every nonzero configuration, assuming every tile has strictly positive
individual energy. Interactions remain symmetric and nonnegative.

We also prove directly that a nonzero real eigenvector of the finite
geometric matrix cannot have a nonpositive real eigenvalue. The same
conclusion holds for the controlled perturbation if its quadratic energy
and its coupling parameter are nonnegative.

The results concern finite matrices, not an infinite spectral operator.
-/

namespace SpectralGeometry

variable {Tile : Type*} [Fintype Tile] [DecidableEq Tile]

/-- Strictly positive onsite energy, together with nonnegative symmetric
pair interactions, forces strictly positive energy on nonzero states. -/
theorem finiteGeometricEnergy_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hV : ∀ t, 0 < V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (ψ : Tile → ℝ) (hψ : ∃ t, ψ t ≠ 0) :
    0 < finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ := by
  classical
  rw [finiteGeometricEnergy_sum_squares V w hw hdiag]
  have hOnsite : 0 < ∑ t : Tile, V t * ψ t ^ 2 := by
    apply Finset.sum_pos'
    · intro t ht
      exact mul_nonneg (le_of_lt (hV t)) (sq_nonneg _)
    · obtain ⟨t, hne⟩ := hψ
      exact ⟨t, Finset.mem_univ t,
        mul_pos (hV t) (sq_pos_of_ne_zero hne)⟩
  have hInteraction :
      0 ≤ (1 / 2 : ℝ) * (∑ t : Tile, ∑ u : Tile,
          w t u * (ψ t - ψ u) ^ 2) := by
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply Finset.sum_nonneg
    intro t ht
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (hwpos t u) (sq_nonneg _)
  exact add_pos_of_pos_of_nonneg hOnsite hInteraction

/-- The same strict positivity persists under an epsilon-scaled
perturbation with nonnegative quadratic energy, when epsilon is nonnegative. -/
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
  exact finitePerturbedMatrix_energy_pos V w P ε
    (fun χ hχ => finiteGeometricEnergy_pos V w hV hw hwpos hdiag χ hχ)
    hP hε ψ hψ

/-- On an eigenvector, quadratic energy equals the eigenvalue times
the sum of the squared amplitudes. -/
private theorem finiteEnergy_on_eigenvector
    (M : Matrix Tile Tile ℝ) (ψ : Tile → ℝ) (eigenvalue : ℝ)
    (heigen : ∀ t, (∑ u : Tile, M t u * ψ u) = eigenvalue * ψ t) :
    finiteQuadraticEnergy M ψ = eigenvalue * ∑ t : Tile, ψ t ^ 2 := by
  classical
  unfold finiteQuadraticEnergy
  calc
    (∑ t : Tile, ∑ u : Tile, ψ t * (M t u * ψ u)) =
        ∑ t : Tile, ψ t * (∑ u : Tile, M t u * ψ u) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
    _ = ∑ t : Tile, eigenvalue * ψ t ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [heigen t]
          ring
    _ = eigenvalue * ∑ t : Tile, ψ t ^ 2 := by rw [Finset.mul_sum]

/-- A finite matrix with strictly positive quadratic energy can have
no nonpositive eigenvalue with a nonzero real eigenvector. -/
private theorem eigenvalue_pos_of_energy_pos
    (M : Matrix Tile Tile ℝ) (ψ : Tile → ℝ) (eigenvalue : ℝ)
    (hQ : 0 < finiteQuadraticEnergy M ψ)
    (heigen : ∀ t, (∑ u : Tile, M t u * ψ u) = eigenvalue * ψ t) :
    0 < eigenvalue := by
  have hnorm : 0 ≤ ∑ t : Tile, ψ t ^ 2 := by
    apply Finset.sum_nonneg
    intro t ht
    exact sq_nonneg _
  rw [finiteEnergy_on_eigenvector M ψ eigenvalue heigen] at hQ
  by_contra hn
  have heigenvalue : eigenvalue ≤ 0 := le_of_not_gt hn
  have hnonpos : eigenvalue * (∑ t : Tile, ψ t ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg heigenvalue hnorm
  exact (not_le_of_gt hQ) hnonpos

/-- Positive onsite energies exclude zero and negative eigenvalues for
the unperturbed finite geometric operator. -/
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
  exact eigenvalue_pos_of_energy_pos
    (finiteUnperturbedMatrix V w) ψ eigenvalue
    (finiteGeometricEnergy_pos V w hV hw hwpos hdiag ψ hψ)
    heigen

/-- Strict positivity of eigenvalues persists for nonnegative
perturbation energy and epsilon, as long as the chosen vector is a
nonzero real eigenvector of the finite perturbed matrix. -/
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
  exact eigenvalue_pos_of_energy_pos
    (finitePerturbedMatrix V w P ε) ψ eigenvalue
    (finiteGeometricPerturbedEnergy_pos V w P ε
      hV hw hwpos hdiag hP hε ψ hψ)
    heigen

end SpectralGeometry
