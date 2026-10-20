module

public import SpectralGeometry.InfiniteLocalFullEigenvectorsComplete
public import Mathlib.Analysis.Normed.Algebra.Spectrum

public section

/-!
# A quantitative spectral exclusion zone around the resolvent shift

For the full matching-family operator H on its natural domain, the
compact resolvent Rₐ is a bounded inverse of H - aI under the earlier
unit-gap, finite-sublevel and Neumann smallness assumptions.

The Fredholm/eigenpair correspondence shows that a genuine full
eigenvalue λ ≠ a gives a spectral value (λ-a)⁻¹ of Rₐ. The standard
norm bound on the spectrum of a bounded operator yields

  ‖(λ-a)⁻¹‖ ≤ ‖Rₐ‖ · ‖I‖.

Consequently, no full-operator eigenvector can exist at a parameter
for which ‖(λ-a)⁻¹‖ > ‖Rₐ‖ · ‖I‖. This is an explicit exclusion zone
around the chosen *resolvent shift*, not isolation of every
full-operator eigenvalue or spectral enumeration.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev GapEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- A genuine full-operator eigenvalue at λ ≠ a has inverse
distance to the resolvent shift bounded by the resolvent norm
multiplied by the norm of the identity endomorphism. The norm-one
factor cannot be simplified uniformly when the Hilbert space may
be zero-dimensional.
This uses neither involutive matching colors nor symmetry of P. -/
theorem infiniteLocalMatching_full_eigenvalue_inverse_shift_bound
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : GapEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (hne : eigenvalue ≠ a)
    (ψ : infiniteOnsiteDomain V)
    (hψ : (ψ.1 : TileHilbert Tile) ≠ 0)
    (heigen : infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
      eigenvalue • (ψ.1 : TileHilbert Tile)) :
    ‖(eigenvalue - a)⁻¹‖ ≤
      ‖infiniteBoundedOnsiteResolvent V a hgap
        (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall‖ *
      ‖(1 : GapEnd Tile)‖ := by
  have hspec :
      (eigenvalue - a)⁻¹ ∈ spectrum ℝ
        (infiniteBoundedOnsiteResolvent V a hgap
          (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall) :=
    (infiniteLocalMatching_full_eigenpair_iff_resolvent_spectrum
      D V σ w P ε shift a hgap hproper hsmall eigenvalue hne).mpr
        ⟨ψ, hψ, heigen⟩
  exact spectrum.norm_le_norm_mul_of_mem hspec

/-- If the reciprocal distance from λ to the chosen resolvent
shift exceeds the resolvent-norm times the identity norm,
every natural-domain solution
of Hψ = λψ is zero. This does not claim that other eigenvalues
are isolated. -/
theorem infiniteLocalMatching_no_eigenvector_in_resolvent_norm_zone
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : GapEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (hne : eigenvalue ≠ a)
    (hclose :
      ‖infiniteBoundedOnsiteResolvent V a hgap
        (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall‖ *
      ‖(1 : GapEnd Tile)‖ < ‖(eigenvalue - a)⁻¹‖)
    (ψ : infiniteOnsiteDomain V)
    (heigen : infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
      eigenvalue • (ψ.1 : TileHilbert Tile)) :
    (ψ.1 : TileHilbert Tile) = 0 := by
  by_contra hψ
  have hbound :=
    infiniteLocalMatching_full_eigenvalue_inverse_shift_bound
      D V σ w P ε shift a hgap hproper hsmall
      eigenvalue hne ψ hψ heigen
  exact (not_le_of_gt hclose) hbound

end SpectralGeometry
