import SpectralGeometry.InfiniteOnsiteResolventIdentity

/-!
# Compact resolvent for bounded perturbations of proper onsite multiplication

Let Rₐ be the continuous inverse of M_V - aI from the onsite
resolvent identity theorem, and let B be any bounded real-linear
correction. If ‖B ∘ Rₐ‖ < 1, the Neumann-series unit of
I + B ∘ Rₐ yields the bounded inverse

    (M_V + B - aI)⁻¹ = Rₐ ∘ (I + B ∘ Rₐ)⁻¹.

The right-hand side maps into the natural onsite domain. If the
onsite potential has finite sublevel sets, then Rₐ is compact,
and hence the full shifted inverse is also compact.

This applies to bounded infinite matching-family interactions and
bounded perturbations via the existing bounded correction map.
Self-adjointness is not required for invertibility at this shift;
spectral discreteness is not asserted here.
-/

namespace SpectralGeometry

variable {Tile : Type*}

private abbrev OnsiteEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- The bounded shift of onsite multiplication by a continuous correction,
defined on the unchanged natural onsite domain. -/
noncomputable def infiniteBoundedOnsiteShift
    (V : Tile → ℝ) (a : ℝ) (B : OnsiteEnd Tile)
    (ψ : infiniteOnsiteDomain V) : TileHilbert Tile :=
  infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile) + B ψ.1

/-- A Neumann-series unit for the bounded correction to the onsite
resolvent under the quantitative smallness hypothesis. -/
noncomputable def infiniteBoundedOnsiteCorrectionUnit
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    (OnsiteEnd Tile)ˣ :=
  Units.oneSub (-(B.comp (infiniteOnsiteResolventCLM V a hgap)))
    (by simpa only [norm_neg] using hsmall)

private theorem infiniteBoundedOnsiteCorrectionUnit_val
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    ((infiniteBoundedOnsiteCorrectionUnit V a hgap B hsmall :
      (OnsiteEnd Tile)ˣ) : OnsiteEnd Tile) =
      1 + B.comp (infiniteOnsiteResolventCLM V a hgap) := by
  simp [infiniteBoundedOnsiteCorrectionUnit]

private theorem inverse_one_plus_apply_right
    (R B : OnsiteEnd Tile) (U : (OnsiteEnd Tile)ˣ)
    (hU : (U : OnsiteEnd Tile) = 1 + B.comp R)
    (f : TileHilbert Tile) :
    (U⁻¹ : OnsiteEnd Tile) f +
      B (R ((U⁻¹ : OnsiteEnd Tile) f)) = f := by
  have h := congrArg (fun T : OnsiteEnd Tile => T f) (Units.mul_inv U)
  rw [hU] at h
  simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using h

private theorem inverse_one_plus_apply_left
    (R B : OnsiteEnd Tile) (U : (OnsiteEnd Tile)ˣ)
    (hU : (U : OnsiteEnd Tile) = 1 + B.comp R)
    (f : TileHilbert Tile) :
    (U⁻¹ : OnsiteEnd Tile) (f + B (R f)) = f := by
  have h := congrArg (fun T : OnsiteEnd Tile => T f) (Units.inv_mul U)
  rw [hU] at h
  simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using h

/-- The full bounded resolvent obtained by composing the compact onsite
resolvent with the inverse of the Neumann-series correction. -/
noncomputable def infiniteBoundedOnsiteResolvent
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    OnsiteEnd Tile :=
  (infiniteOnsiteResolventCLM V a hgap).comp
    ((infiniteBoundedOnsiteCorrectionUnit V a hgap B hsmall)⁻¹ :
      OnsiteEnd Tile)

/-- The corrected resolvent takes values in the unbounded onsite
domain, so the full shifted equation makes sense. -/
noncomputable def infiniteBoundedOnsiteResolventSolution
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (f : TileHilbert Tile) : infiniteOnsiteDomain V :=
  infiniteOnsiteResolventSolution V a hgap
    (((infiniteBoundedOnsiteCorrectionUnit V a hgap B hsmall)⁻¹ :
      OnsiteEnd Tile) f)

/-- The full shifted onsite-plus-bounded operator maps its constructed
resolvent solution back to the input. -/
theorem infiniteBoundedOnsiteResolvent_right_inverse
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (f : TileHilbert Tile) :
    infiniteBoundedOnsiteShift V a B
      (infiniteBoundedOnsiteResolventSolution V a hgap B hsmall f) = f := by
  let R := infiniteOnsiteResolventCLM V a hgap
  let U := infiniteBoundedOnsiteCorrectionUnit V a hgap B hsmall
  let g : TileHilbert Tile := (U⁻¹ : OnsiteEnd Tile) f
  have h0 :=
    infiniteOnsiteResolventCLM_shift_right_inverse V a hgap g
  have h1 := inverse_one_plus_apply_right R B U
    (infiniteBoundedOnsiteCorrectionUnit_val V a hgap B hsmall) f
  change
    (infiniteOnsiteOperator V (infiniteOnsiteResolventSolution V a hgap g) -
      a • ((infiniteOnsiteResolventSolution V a hgap g).1 : TileHilbert Tile)) +
      B (R g) = f
  rw [h0]
  exact h1

/-- The full bounded resolvent is also a left inverse on the natural
onsite domain, hence the full shifted operator is bijective. -/
theorem infiniteBoundedOnsiteResolvent_left_inverse
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (ψ : infiniteOnsiteDomain V) :
    infiniteBoundedOnsiteResolvent V a hgap B hsmall
      (infiniteBoundedOnsiteShift V a B ψ) = (ψ.1 : TileHilbert Tile) := by
  let R := infiniteOnsiteResolventCLM V a hgap
  let U := infiniteBoundedOnsiteCorrectionUnit V a hgap B hsmall
  let g : TileHilbert Tile :=
    infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile)
  have hR : R g = (ψ.1 : TileHilbert Tile) :=
    infiniteOnsiteResolventCLM_shift_left_inverse V a hgap ψ
  have hU := inverse_one_plus_apply_left R B U
    (infiniteBoundedOnsiteCorrectionUnit_val V a hgap B hsmall) g
  change R ((U⁻¹ : OnsiteEnd Tile) (g + B ψ.1)) = ψ.1
  calc
    R ((U⁻¹ : OnsiteEnd Tile) (g + B ψ.1)) =
        R ((U⁻¹ : OnsiteEnd Tile) (g + B (R g))) := by rw [hR]
    _ = R g := by rw [hU]
    _ = ψ.1 := hR

/-- Under finite onsite sublevel sets, the **full** shifted
onsite-plus-bounded inverse is compact, not merely the diagonal one. -/
theorem infiniteBoundedOnsiteResolvent_compact
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    IsCompactOperator
      (infiniteBoundedOnsiteResolvent V a hgap B hsmall) := by
  let R := infiniteOnsiteResolventCLM V a hgap
  let U := infiniteBoundedOnsiteCorrectionUnit V a hgap B hsmall
  have hc : IsCompactOperator R :=
    infiniteOnsiteResolventCLM_compact V a hgap hproper
  have hh := hc.comp_clm (U⁻¹ : OnsiteEnd Tile)
  convert hh using 1
  funext f
  rfl

end SpectralGeometry
