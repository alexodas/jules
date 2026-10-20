module

public import SpectralGeometry.InfiniteLocalAdjointCharacterization
public import SpectralGeometry.InfiniteOnsiteEigenvalues

public section

/-!
# Finite low-energy sectors of the infinite onsite operator

Proper growth of the onsite energies is encoded as: for every energy
threshold R, only finitely many tiles have V(t) ≤ R.

At a fixed threshold, every point eigenstate of onsite multiplication
with eigenvalue ≤ R is supported entirely on that finite tile set.
Consequently there are only finitely many DISTINCT onsite point
eigenvalues below any fixed threshold.

These claims concern the unperturbed diagonal onsite operator. They do
not yet show compactness of a resolvent for the full interacting
operator, nor the summability needed for the canonical product.
-/

namespace SpectralGeometry

variable {Tile : Type*}

/-- Tiles whose individual onsite energies are at most R. -/
def infiniteOnsiteLowEnergyTiles (V : Tile → ℝ) (R : ℝ) :
    Set Tile := {t | V t ≤ R}

/-- An onsite eigenstate with eigenvalue at most R can only be
nonzero on tiles whose onsite energy is at most R. -/
theorem infiniteOnsiteEigenvector_support_subset_lowEnergy
    (V : Tile → ℝ) (R eigenvalue : ℝ)
    (hbound : eigenvalue ≤ R)
    (ψ : infiniteOnsiteDomain V)
    (heigen : infiniteOnsiteOperator V ψ =
      eigenvalue • (ψ.1 : TileHilbert Tile)) :
    {t : Tile | ψ.1 t ≠ 0} ⊆ infiniteOnsiteLowEnergyTiles V R := by
  intro t ht
  change V t ≤ R
  have heq :=
    infiniteOnsiteEigenvalue_eq_at_nonzero
      V ψ eigenvalue heigen t ht
  rw [← heq]
  exact hbound

/-- If there are only finitely many low-energy tiles, every onsite
eigenstate below the given threshold has finite coordinate support. -/
theorem infiniteOnsiteEigenvector_support_finite
    (V : Tile → ℝ) (R eigenvalue : ℝ)
    (hfinite : (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hbound : eigenvalue ≤ R)
    (ψ : infiniteOnsiteDomain V)
    (heigen : infiniteOnsiteOperator V ψ =
      eigenvalue • (ψ.1 : TileHilbert Tile)) :
    {t : Tile | ψ.1 t ≠ 0}.Finite := by
  exact hfinite.subset
    (infiniteOnsiteEigenvector_support_subset_lowEnergy
      V R eigenvalue hbound ψ heigen)

/-- Every genuine onsite point eigenvalue ≤ R belongs to the image
of the finite low-energy tile set under the potential V. -/
theorem infiniteOnsitePointEigenvalues_below_subset_image
    (V : Tile → ℝ) (R : ℝ) :
    {a | a ≤ R ∧
      ∃ ψ : infiniteOnsiteDomain V,
        (∃ t : Tile, ψ.1 t ≠ 0) ∧
        infiniteOnsiteOperator V ψ =
          a • (ψ.1 : TileHilbert Tile)} ⊆
      V '' infiniteOnsiteLowEnergyTiles V R := by
  intro a ha
  rcases ha with ⟨hbound, ψ, ⟨t, ht⟩, heigen⟩
  have heq := infiniteOnsiteEigenvalue_eq_at_nonzero
    V ψ a heigen t ht
  refine ⟨t, ?_, ?_⟩
  · change V t ≤ R
    rw [← heq]
    exact hbound
  · exact heq.symm

/-- A proper onsite potential has only finitely many distinct
point eigenvalues below each fixed real threshold. -/
theorem infiniteOnsitePointEigenvalues_below_finite
    (V : Tile → ℝ) (R : ℝ)
    (hfinite : (infiniteOnsiteLowEnergyTiles V R).Finite) :
    {a | a ≤ R ∧
      ∃ ψ : infiniteOnsiteDomain V,
        (∃ t : Tile, ψ.1 t ≠ 0) ∧
        infiniteOnsiteOperator V ψ =
          a • (ψ.1 : TileHilbert Tile)}.Finite := by
  exact (hfinite.image V).subset
    (infiniteOnsitePointEigenvalues_below_subset_image V R)

end SpectralGeometry
