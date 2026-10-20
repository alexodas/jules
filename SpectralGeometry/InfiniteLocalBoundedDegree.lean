module

public import SpectralGeometry.InfiniteLocalMatching

public section

/-!
# Uniformly bounded local degree via finitely many infinite matchings

A graph can be presented by D matching colors, each encoded by an
involutive permutation σᵢ of its (possibly infinite) tile set. Thus
each tile has at most D candidate neighbors. Constant nonnegative
weight wᵢ≤W may be assigned to every edge of color i.

Unlike the earlier ℓ¹ edge condition, the sum of weights across all
edges need not converge: each color may contain infinitely many edges
of fixed nonzero weight.

The resulting bounded Laplacian is symmetric and nonnegative, with
operator norm ≤2 D W. It can be added to unbounded onsite multiplication
and a bounded perturbation on the original dense domain D(V).

This proves the finite-matching-color case, NOT the general theorem
for arbitrary bounded-degree graphs with tile-dependent edge weights.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- Candidate neighbors of a tile in a D-color matching graph. -/
noncomputable def infiniteMatchingNeighbors (D : ℕ)
    (σ : Fin D → Tile ≃ Tile) (t : Tile) : Finset Tile :=
  Finset.univ.image (fun i : Fin D => σ i t)

/-- Every tile has at most D candidate neighbors, independent of
whether there are finitely or infinitely many tiles. -/
theorem infiniteMatchingNeighbors_card_le (D : ℕ)
    (σ : Fin D → Tile ≃ Tile) (t : Tile) :
    (infiniteMatchingNeighbors D σ t).card ≤ D := by
  unfold infiniteMatchingNeighbors
  exact (Finset.card_image_le).trans (by simp)

/-- Infinite local Laplacian made of D matchings with a constant
weight for each matching color. -/
noncomputable def infiniteLocalMatchingLaplacian (D : ℕ)
    (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ∑ i : Fin D, w i • infiniteMatchingLaplacian (σ i)

/-- The infinite local interaction energy is nonnegative if its
matching weights are nonnegative. No summability across edges needed. -/
theorem infiniteLocalMatchingLaplacian_energy_nonneg (D : ℕ)
    (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ψ : TileHilbert Tile) :
    0 ≤ inner ℝ ψ (infiniteLocalMatchingLaplacian D σ w ψ) := by
  simp only [infiniteLocalMatchingLaplacian, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inner_sum, real_inner_smul_right]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i) (infiniteMatchingLaplacian_energy_nonneg (σ i) ψ)

/-- The operator norm of a D-color graph Laplacian is at most 2DW
when 0≤wᵢ≤W. In particular, it acts on every state in ℓ²(Tile). -/
theorem infiniteLocalMatchingLaplacian_norm_le (D : ℕ)
    (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (W : ℝ) (hW : 0 ≤ W)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ W) :
    ‖infiniteLocalMatchingLaplacian D σ w‖ ≤ 2 * (D : ℝ) * W := by
  have hpiece (i : Fin D) :
      ‖w i • infiniteMatchingLaplacian (σ i)‖ ≤ 2 * W := by
    calc
      ‖w i • infiniteMatchingLaplacian (σ i)‖ =
          w i * ‖infiniteMatchingLaplacian (σ i)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 i)]
      _ ≤ w i * 2 := mul_le_mul_of_nonneg_left
        (infiniteMatchingLaplacian_norm_le_two (σ i)) (hw0 i)
      _ ≤ W * 2 := mul_le_mul_of_nonneg_right (hw i) (by norm_num)
      _ = 2 * W := by ring
  calc
    ‖infiniteLocalMatchingLaplacian D σ w‖ ≤
        ∑ i : Fin D, ‖w i • infiniteMatchingLaplacian (σ i)‖ := by
          unfold infiniteLocalMatchingLaplacian
          exact norm_sum_le _ _
    _ ≤ ∑ i : Fin D, (2 * W) :=
      Finset.sum_le_sum (fun i _ => hpiece i)
    _ = 2 * (D : ℝ) * W := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- Symmetry for involutive tile matchings. -/
theorem infiniteLocalMatchingLaplacian_symmetric (D : ℕ)
    (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (ψ φ : TileHilbert Tile) :
    inner ℝ ψ (infiniteLocalMatchingLaplacian D σ w φ) =
      inner ℝ (infiniteLocalMatchingLaplacian D σ w ψ) φ := by
  simp only [infiniteLocalMatchingLaplacian, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inner_sum, sum_inner,
    real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [infiniteMatchingLaplacian_symmetric (σ i) (hσ i) ψ φ]

/-- Complete operator with infinite local matching interactions,
possibly unbounded onsite energies, and bounded perturbations. -/
noncomputable def infiniteLocalMatchingPerturbedOperator (D : ℕ)
    (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ) :
    infiniteOnsiteDomain V →ₗ[ℝ] TileHilbert Tile :=
  infiniteOnsiteOperator V +
    (infiniteLocalMatchingLaplacian D σ w).toLinearMap.comp
      (infiniteOnsiteDomain V).subtype +
    ε • (P.toLinearMap.comp (infiniteOnsiteDomain V).subtype)

/-- The full operator acts termwise on a common dense domain. -/
theorem infiniteLocalMatchingPerturbedOperator_apply (D : ℕ)
    (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (ψ : infiniteOnsiteDomain V) :
    infiniteLocalMatchingPerturbedOperator D V σ w P ε ψ =
      infiniteOnsiteOperator V ψ +
        infiniteLocalMatchingLaplacian D σ w ψ.1 + ε • P ψ.1 := by
  simp [infiniteLocalMatchingPerturbedOperator, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply]

/-- The total quadratic energy is nonnegative under nonnegative onsite
levels, nonnegative matching weights and a positive bounded perturbation. -/
theorem infiniteLocalMatchingPerturbedOperator_energy_nonneg (D : ℕ)
    (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (hP : ∀ ψ : TileHilbert Tile, 0 ≤ inner ℝ ψ (P ψ))
    (hε : 0 ≤ ε) (ψ : infiniteOnsiteDomain V) :
    0 ≤ inner ℝ ψ.1
      (infiniteLocalMatchingPerturbedOperator D V σ w P ε ψ) := by
  rw [infiniteLocalMatchingPerturbedOperator_apply]
  simp only [inner_add_right, real_inner_smul_right]
  exact add_nonneg
    (add_nonneg (infiniteOnsiteOperator_energy_nonneg V hV ψ)
      (infiniteLocalMatchingLaplacian_energy_nonneg D σ w hw ψ.1))
    (mul_nonneg hε (hP ψ.1))

/-- Symmetry survives the full sum if the matching permutations are
involutions and the bounded perturbation is symmetric. -/
theorem infiniteLocalMatchingPerturbedOperator_symmetric (D : ℕ)
    (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (ψ φ : infiniteOnsiteDomain V) :
    inner ℝ ψ.1 (infiniteLocalMatchingPerturbedOperator D V σ w P ε φ) =
      inner ℝ (infiniteLocalMatchingPerturbedOperator D V σ w P ε ψ) φ.1 := by
  rw [infiniteLocalMatchingPerturbedOperator_apply,
    infiniteLocalMatchingPerturbedOperator_apply]
  simp only [inner_add_right, inner_add_left,
    real_inner_smul_left, real_inner_smul_right]
  rw [infiniteOnsiteOperator_symmetric V ψ φ,
    infiniteLocalMatchingLaplacian_symmetric D σ w hσ ψ.1 φ.1,
    hP ψ.1 φ.1]

end SpectralGeometry
