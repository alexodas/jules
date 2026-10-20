module

public import SpectralGeometry.InfiniteLocalFullEigenspaces
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

public section

/-!
# Fredholm spectral exhaustion for the full infinite local matching operator

The first P2 spectral statements studied the compact resolvent Rₐ of the
unbounded local operator H = M_V + L_w + εP + mI. We now apply the
Fredholm alternative from Mathlib: every NONZERO spectral point of a
compact bounded operator is an eigenvalue.

Combined with the two-sided resolvent inverse and the checked natural
domain eigenpair correspondence, this shows that the nonzero spectrum
of Rₐ corresponds EXACTLY to eigenpairs of the full unbounded H.

This is a spectral exhaustion result for the NONZERO COMPACT RESOLVENT
SPECTRUM, not a definition or classification of the full unbounded
operator's entire spectrum. It neither asserts isolation of these
spectral points nor enumerates the full eigenvalues.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev FredholmEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- A nonzero point μ of the compact full local resolvent's spectrum
is equivalent to a nonzero actual eigenvector of the unbounded full
local operator on its natural domain with eigenvalue a+μ⁻¹.
The reverse direction does not need symmetry: the Fredholm alternative
is valid for arbitrary compact operators. -/
theorem infiniteLocalMatching_resolvent_spectrum_iff_full_eigenpair
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FredholmEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (μ : ℝ) (hμ : μ ≠ 0) :
    μ ∈ spectrum ℝ (infiniteBoundedOnsiteResolvent V a hgap
        (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall) ↔
      ∃ ψ : infiniteOnsiteDomain V,
        (ψ.1 : TileHilbert Tile) ≠ 0 ∧
        infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
          (a + μ⁻¹) • (ψ.1 : TileHilbert Tile) := by
  let R : FredholmEnd Tile :=
    infiniteBoundedOnsiteResolvent V a hgap
      (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall
  have hcompact : IsCompactOperator R :=
    infiniteBoundedOnsiteResolvent_compact V a hgap hproper
      (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall
  have hfred : Module.End.HasEigenvalue R.toLinearMap μ ↔ μ ∈ spectrum ℝ R :=
    IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcompact hμ
  change μ ∈ spectrum ℝ R ↔
    ∃ ψ : infiniteOnsiteDomain V,
      (ψ.1 : TileHilbert Tile) ≠ 0 ∧
      infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
        (a + μ⁻¹) • (ψ.1 : TileHilbert Tile)
  rw [← hfred]
  constructor
  · intro hspec
    obtain ⟨f, hf⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hspec
    have hRf : R f = μ • f :=
      Module.End.mem_eigenspace_iff.mp hf.1
    obtain ⟨ψ, hψ, hH⟩ :=
      (infiniteLocalMatching_resolvent_eigenpair_iff
        D V σ w P ε shift a hgap hsmall μ hμ f).mp hRf
    refine ⟨ψ, ?_, ?_⟩
    · simpa only [hψ] using hf.2
    · simpa only [hψ] using hH
  · rintro ⟨ψ, hψ, hH⟩
    have hRψ : R (ψ.1 : TileHilbert Tile) = μ • (ψ.1 : TileHilbert Tile) :=
      (infiniteLocalMatching_resolvent_eigenpair_iff
        D V σ w P ε shift a hgap hsmall μ hμ
          (ψ.1 : TileHilbert Tile)).mpr ⟨ψ, rfl, hH⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector
    exact ⟨(Module.End.mem_eigenspace_iff).mpr hRψ, hψ⟩

/-- An equivalent spectral characterization in terms of a real
full-operator eigenvalue λ different from the real resolvent shift a.
No full unbounded-operator spectrum API or isolation assertion is used. -/
theorem infiniteLocalMatching_full_eigenpair_iff_resolvent_spectrum
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FredholmEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (hne : eigenvalue ≠ a) :
    (eigenvalue - a)⁻¹ ∈ spectrum ℝ
        (infiniteBoundedOnsiteResolvent V a hgap
          (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall) ↔
      ∃ ψ : infiniteOnsiteDomain V,
        (ψ.1 : TileHilbert Tile) ≠ 0 ∧
        infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
          eigenvalue • (ψ.1 : TileHilbert Tile) := by
  have hμ : (eigenvalue - a)⁻¹ ≠ 0 :=
    inv_ne_zero (sub_ne_zero.mpr hne)
  have hh :=
    infiniteLocalMatching_resolvent_spectrum_iff_full_eigenpair
      D V σ w P ε shift a hgap hproper hsmall
        (eigenvalue - a)⁻¹ hμ
  have hvalue : a + ((eigenvalue - a)⁻¹)⁻¹ = eigenvalue := by
    rw [inv_inv]
    ring
  simpa only [hvalue] using hh

end SpectralGeometry
