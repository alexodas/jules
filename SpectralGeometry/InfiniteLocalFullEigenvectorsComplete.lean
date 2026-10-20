module

public import SpectralGeometry.InfiniteLocalFredholmSpectralExhaustion

public section

/-!
# Completeness of eigenvectors of the full unbounded local operator

The compact self-adjoint resolvent was previously shown to have a total
family of eigenspaces. Here we remove the zero eigenspace by proving
that the resolvent is injective, using its genuine right inverse on the
natural onsite domain.

For a symmetric finite-color matching-family perturbation, the
previous eigenpair correspondence then identifies every nonzero
resolvent eigenspace with a full-operator eigenspace at
λ = a + μ⁻¹. This gives totality (dense linear span) of genuine
natural-domain eigenvectors of the unbounded full operator.

No isolation, eigenvalue enumeration, or growth rate is inferred from
eigenvector completeness alone.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev CompleteEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- The compact interacting resolvent has trivial kernel because its
right inverse on the natural onsite domain recovers any input. -/
theorem infiniteBoundedOnsiteResolvent_zero_eigenspace_eq_bot
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : CompleteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    Module.End.eigenspace
      (infiniteBoundedOnsiteResolvent V a hgap B hsmall).toLinearMap 0 = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  rw [Module.End.mem_eigenspace_iff] at hf
  simp only [zero_smul] at hf
  let ψ := infiniteBoundedOnsiteResolventSolution V a hgap B hsmall f
  have hψ : (ψ.1 : TileHilbert Tile) =
      infiniteBoundedOnsiteResolvent V a hgap B hsmall f := rfl
  have hψ0 : ψ = 0 := by
    apply Subtype.ext
    exact hψ.trans hf
  have hr := infiniteBoundedOnsiteResolvent_right_inverse
    V a hgap B hsmall f
  change infiniteBoundedOnsiteShift V a B ψ = f at hr
  rw [hψ0] at hr
  have hz : infiniteBoundedOnsiteShift V a B
      (0 : infiniteOnsiteDomain V) = 0 := by
    simp [infiniteBoundedOnsiteShift]
  rw [hz] at hr
  exact hr.symm

/-- All the nonzero eigenspaces of a compact self-adjoint interacting
resolvent already have dense linear span. Its zero eigenspace is
trivial by the explicit inverse identities, not an extra hypothesis. -/
theorem infiniteBoundedOnsiteResolvent_nonzero_eigenspaces_dense
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : CompleteEnd Tile)
    (hB : ∀ ψ φ : TileHilbert Tile,
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ))
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    (⨆ μ : {μ : ℝ // μ ≠ 0},
      Module.End.eigenspace
        (infiniteBoundedOnsiteResolvent V a hgap B hsmall).toLinearMap
        (μ : ℝ))ᗮ = ⊥ := by
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  have hzero : Module.End.eigenspace R.toLinearMap 0 = ⊥ :=
    infiniteBoundedOnsiteResolvent_zero_eigenspace_eq_bot V a hgap B hsmall
  have hsup :
      (⨆ μ : {μ : ℝ // μ ≠ 0},
        Module.End.eigenspace R.toLinearMap (μ : ℝ)) =
      (⨆ μ : ℝ, Module.End.eigenspace R.toLinearMap μ) := by
    apply le_antisymm
    · apply iSup_le
      intro μ
      exact le_iSup_of_le (μ : ℝ) (le_refl _)
    · apply iSup_le
      intro μ
      by_cases hμ : μ = 0
      · subst μ
        rw [hzero]
        exact bot_le
      · exact le_iSup_of_le (⟨μ, hμ⟩ : {μ : ℝ // μ ≠ 0}) (le_refl _)
  rw [hsup]
  exact infiniteBoundedOnsiteResolvent_eigenspaces_dense
    V a hgap hproper B hB hsmall

/-- The genuine eigenvectors of the full unbounded finite-color
matching-family operator have dense linear span in the Hilbert
space, under the usual compact-resolvent and symmetry assumptions.

The family ranges over real eigenvalue parameters different from a;
the resolvent shift itself has no nonzero eigenvectors by §4.25.
Every member is a genuine natural-domain eigenvector by the earlier
full-eigenspace membership theorem. -/
theorem infiniteLocalMatchingFullEigenspaces_dense
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : CompleteEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ) :
    (⨆ eigenvalue : {eigenvalue : ℝ // eigenvalue ≠ a},
      infiniteLocalMatchingFullEigenspace
        D V σ w P ε shift a hgap hsmall
        (eigenvalue : ℝ) eigenvalue.property)ᗮ = ⊥ := by
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  have hB : ∀ ψ φ : TileHilbert Tile,
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ) := by
    intro ψ φ
    exact infiniteLocalBoundedCorrection_symmetric
      D σ w P ε shift hσ hP ψ φ
  have htotal :
      (⨆ μ : {μ : ℝ // μ ≠ 0},
        Module.End.eigenspace R.toLinearMap (μ : ℝ))ᗮ = ⊥ :=
    infiniteBoundedOnsiteResolvent_nonzero_eigenspaces_dense
      V a hgap hproper B hB hsmall
  have hle :
      (⨆ μ : {μ : ℝ // μ ≠ 0},
        Module.End.eigenspace R.toLinearMap (μ : ℝ)) ≤
      (⨆ eigenvalue : {eigenvalue : ℝ // eigenvalue ≠ a},
        infiniteLocalMatchingFullEigenspace
          D V σ w P ε shift a hgap hsmall
          (eigenvalue : ℝ) eigenvalue.property) := by
    apply iSup_le
    rintro ⟨μ, hμ⟩
    let eigenvalue : ℝ := a + μ⁻¹
    have hμinv : μ⁻¹ ≠ 0 := inv_ne_zero hμ
    have hne : eigenvalue ≠ a := by
      dsimp [eigenvalue]
      intro hh
      have heq : μ⁻¹ = 0 := by linarith
      exact hμinv heq
    have htrans : (eigenvalue - a)⁻¹ = μ := by
      dsimp [eigenvalue]
      have hh : a + μ⁻¹ - a = μ⁻¹ := by ring
      rw [hh, inv_inv]
    have heq :
        Module.End.eigenspace R.toLinearMap μ =
          infiniteLocalMatchingFullEigenspace
            D V σ w P ε shift a hgap hsmall eigenvalue hne := by
      change Module.End.eigenspace R.toLinearMap μ =
        Module.End.eigenspace R.toLinearMap (eigenvalue - a)⁻¹
      rw [htrans]
    rw [heq]
    exact le_iSup_of_le
      (⟨eigenvalue, hne⟩ :
        {eigenvalue : ℝ // eigenvalue ≠ a}) (le_refl _)
  apply le_antisymm
  · calc
      (⨆ eigenvalue : {eigenvalue : ℝ // eigenvalue ≠ a},
        infiniteLocalMatchingFullEigenspace
          D V σ w P ε shift a hgap hsmall
          (eigenvalue : ℝ) eigenvalue.property)ᗮ ≤
        (⨆ μ : {μ : ℝ // μ ≠ 0},
          Module.End.eigenspace R.toLinearMap (μ : ℝ))ᗮ :=
        Submodule.orthogonal_le hle
      _ = ⊥ := htotal
  · exact bot_le

end SpectralGeometry
