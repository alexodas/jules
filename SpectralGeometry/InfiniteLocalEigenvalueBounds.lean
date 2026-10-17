import SpectralGeometry.InfiniteLocalBoundedDegree

/-!
# Point-eigenvalue lower bounds for infinite local geometric operators

The matching-colored local Laplacian may contain infinitely many edges
with weights that are not summable over all edges. Nevertheless its
quadratic energy is nonnegative for nonnegative matching weights.

We show two rigorous consequences for the point spectrum of the full
operator on its natural dense onsite domain:

* Nonnegative onsite energies and a nonnegative bounded perturbation
  at nonnegative coupling rule out negative point eigenvalues.
* When the perturbation is the identity, its coefficient ε produces a
  uniform lower bound λ ≥ ε on every point eigenvalue, even when the
  onsite potential is unbounded and the edge weights are not globally
  summable. In particular ε > 0 excludes zero eigenvalues.

These conclusions concern existing eigenvectors. They do NOT establish
existence of eigenvalues, self-adjointness, compact resolvent, or an
inverse-square-summable discrete spectrum.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- An infinite local matching operator with a nonnegative onsite
potential, nonnegative matching weights and a nonnegative bounded
perturbation (with ε ≥ 0) has no negative point eigenvalues. -/
theorem infiniteLocalMatchingPerturbedEigenvalue_nonneg
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (hP : ∀ ψ : TileHilbert Tile, 0 ≤ inner ℝ ψ (P ψ))
    (hε : 0 ≤ ε)
    (ψ : infiniteOnsiteDomain V) (λ : ℝ)
    (heigen : infiniteLocalMatchingPerturbedOperator D V σ w P ε ψ =
      λ • (ψ.1 : TileHilbert Tile))
    (hψ : (ψ.1 : TileHilbert Tile) ≠ 0) :
    0 ≤ λ := by
  have henergy :=
    infiniteLocalMatchingPerturbedOperator_energy_nonneg
      D V σ w P ε hV hw hP hε ψ
  have hnorm : 0 < ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hψ)
  rw [heigen, real_inner_smul_right, real_inner_self_eq_norm_sq] at henergy
  by_contra hn
  have hneg : λ < 0 := lt_of_not_ge hn
  have hprod : λ * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hneg hnorm
  linarith

/-- Adding ε times the identity to a nonnegative onsite-plus-matching
operator shifts every point eigenvalue above ε. No sign condition on
the real parameter ε is necessary. -/
theorem infiniteLocalMatchingIdentityShift_eigenvalue_ge
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (ε : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (ψ : infiniteOnsiteDomain V) (λ : ℝ)
    (heigen :
      infiniteLocalMatchingPerturbedOperator D V σ w
        (ContinuousLinearMap.id ℝ (TileHilbert Tile)) ε ψ =
        λ • (ψ.1 : TileHilbert Tile))
    (hψ : (ψ.1 : TileHilbert Tile) ≠ 0) :
    ε ≤ λ := by
  have honsite := infiniteOnsiteOperator_energy_nonneg V hV ψ
  have hedge :=
    infiniteLocalMatchingLaplacian_energy_nonneg D σ w hw ψ.1
  have hnorm : 0 < ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hψ)
  have hdecompose :
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalMatchingPerturbedOperator D V σ w
          (ContinuousLinearMap.id ℝ (TileHilbert Tile)) ε ψ) =
      inner ℝ (ψ.1 : TileHilbert Tile) (infiniteOnsiteOperator V ψ) +
        inner ℝ (ψ.1 : TileHilbert Tile)
          (infiniteLocalMatchingLaplacian D σ w ψ.1) +
        ε * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
    rw [infiniteLocalMatchingPerturbedOperator_apply]
    simp only [inner_add_right, real_inner_smul_right,
      ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  have hvalue :
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalMatchingPerturbedOperator D V σ w
          (ContinuousLinearMap.id ℝ (TileHilbert Tile)) ε ψ) =
      λ * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
    rw [heigen, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hbound :
      ε * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
      λ * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
    rw [← hvalue, hdecompose]
    linarith
  exact (mul_le_mul_iff_of_pos_right hnorm).mp hbound

/-- A strictly positive identity shift creates a positive lower bound
for each existing eigenvalue of the infinite local matching model. -/
theorem infiniteLocalMatchingIdentityShift_eigenvalue_pos
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (ε : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (hε : 0 < ε)
    (ψ : infiniteOnsiteDomain V) (λ : ℝ)
    (heigen :
      infiniteLocalMatchingPerturbedOperator D V σ w
        (ContinuousLinearMap.id ℝ (TileHilbert Tile)) ε ψ =
        λ • (ψ.1 : TileHilbert Tile))
    (hψ : (ψ.1 : TileHilbert Tile) ≠ 0) :
    0 < λ :=
  lt_of_lt_of_le hε
    (infiniteLocalMatchingIdentityShift_eigenvalue_ge
      D V σ w ε hV hw ψ λ heigen hψ)

end SpectralGeometry
