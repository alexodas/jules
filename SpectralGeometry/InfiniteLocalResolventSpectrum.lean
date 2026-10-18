import SpectralGeometry.InfiniteLocalSelfAdjointPMap
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# First spectral consequences of compact self-adjoint local resolvents

The unbounded onsite-plus-bounded operator H = M_V+B is symmetric on
its natural domain when B is symmetric. If the quantitative onsite gap
makes the bounded inverse Rₐ=(H-aI)⁻¹ exist, then Rₐ is itself
self-adjoint. Its compactness, already proved in P1, gives the first
direct applications of Mathlib's compact self-adjoint spectral theorem:

* every nonzero eigenspace of Rₐ is finite-dimensional;
* the closed linear span of all its eigenspaces is the full Hilbert space.

These statements concern the compact bounded resolvent. A subsequent
step must transfer its eigenvalues and eigenvectors to H and provide
an eigenvalue enumeration and growth estimates. They are NOT asserted
in this module.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev SpectralEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- Adding any bounded symmetric correction to the shifted
onsite multiplication preserves symmetry on the natural domain. -/
private theorem infiniteBoundedOnsiteShift_symmetric
    (V : Tile → ℝ) (a : ℝ) (B : SpectralEnd Tile)
    (hB : ∀ ψ φ : TileHilbert Tile,
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ))
    (ψ φ : infiniteOnsiteDomain V) :
    inner ℝ (infiniteBoundedOnsiteShift V a B ψ) (φ.1 : TileHilbert Tile) =
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteBoundedOnsiteShift V a B φ) := by
  change inner ℝ
      (infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile) + B ψ.1) φ.1 =
    inner ℝ (ψ.1 : TileHilbert Tile)
      (infiniteOnsiteOperator V φ - a • (φ.1 : TileHilbert Tile) + B φ.1)
  simp only [inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [infiniteOnsiteOperator_symmetric V ψ φ,
    hB (ψ.1 : TileHilbert Tile) (φ.1 : TileHilbert Tile)]

/-- The bounded inverse of the shifted symmetric unbounded operator
is genuinely self-adjoint as a continuous linear map. -/
theorem infiniteBoundedOnsiteResolvent_isSelfAdjoint
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : SpectralEnd Tile)
    (hB : ∀ ψ φ : TileHilbert Tile,
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ))
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    IsSelfAdjoint
      (infiniteBoundedOnsiteResolvent V a hgap B hsmall) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  let ψ := infiniteBoundedOnsiteResolventSolution V a hgap B hsmall f
  let φ := infiniteBoundedOnsiteResolventSolution V a hgap B hsmall g
  have hf : infiniteBoundedOnsiteShift V a B ψ = f :=
    infiniteBoundedOnsiteResolvent_right_inverse V a hgap B hsmall f
  have hg : infiniteBoundedOnsiteShift V a B φ = g :=
    infiniteBoundedOnsiteResolvent_right_inverse V a hgap B hsmall g
  change inner ℝ (ψ.1 : TileHilbert Tile) g =
    inner ℝ f (φ.1 : TileHilbert Tile)
  calc
    inner ℝ (ψ.1 : TileHilbert Tile) g =
        inner ℝ (ψ.1 : TileHilbert Tile)
          (infiniteBoundedOnsiteShift V a B φ) := by rw [hg]
    _ = inner ℝ (infiniteBoundedOnsiteShift V a B ψ)
          (φ.1 : TileHilbert Tile) :=
      (infiniteBoundedOnsiteShift_symmetric V a B hB ψ φ).symm
    _ = inner ℝ f (φ.1 : TileHilbert Tile) := by rw [hf]

/-- Nonzero eigenvalues of the full compact resolvent have finite
multiplicity (their eigenspaces are finite-dimensional). -/
theorem infiniteBoundedOnsiteResolvent_finite_dimensional_eigenspace
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : SpectralEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (μ : ℝ) (hμ : μ ≠ 0) :
    FiniteDimensional ℝ
      (Module.End.eigenspace
        (infiniteBoundedOnsiteResolvent V a hgap B hsmall).toLinearMap μ) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace
    (infiniteBoundedOnsiteResolvent_compact V a hgap hproper B hsmall) μ hμ

/-- Compactness and symmetry imply that the resolvent eigenspaces
have dense linear span; this is the compact self-adjoint spectral
theorem of Mathlib, now applied to our full local resolvent. -/
theorem infiniteBoundedOnsiteResolvent_eigenspaces_dense
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : SpectralEnd Tile)
    (hB : ∀ ψ φ : TileHilbert Tile,
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ))
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    (⨆ μ : ℝ,
      Module.End.eigenspace
        (infiniteBoundedOnsiteResolvent V a hgap B hsmall).toLinearMap μ)ᗮ =
        ⊥ := by
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  have hcompact : IsCompactOperator R :=
    infiniteBoundedOnsiteResolvent_compact V a hgap hproper B hsmall
  have hself : IsSelfAdjoint R :=
    infiniteBoundedOnsiteResolvent_isSelfAdjoint V a hgap B hB hsmall
  have hsym : (R : TileHilbert Tile →ₗ[ℝ] TileHilbert Tile).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    hcompact hsym

/-- The correction for involutive finite-color matchings is symmetric,
so the full geometric compact resolvent satisfies the hypotheses of
the spectral theorem. -/
theorem infiniteLocalMatchingResolvent_isSelfAdjoint
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : SpectralEnd Tile) (ε shift a : ℝ)
    (hgap : ∀ t, 1 ≤ V t - a)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    IsSelfAdjoint (infiniteBoundedOnsiteResolvent V a hgap
      (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall) := by
  apply infiniteBoundedOnsiteResolvent_isSelfAdjoint
  · intro ψ φ
    exact infiniteLocalBoundedCorrection_symmetric
      D σ w P ε shift hσ hP ψ φ

end SpectralGeometry
