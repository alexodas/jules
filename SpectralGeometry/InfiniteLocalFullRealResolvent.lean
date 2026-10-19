import SpectralGeometry.InfiniteLocalFullEigenvalueEnumeration

/-!
# Bounded inverses for new real shifts of the full unbounded local operator

Starting from the constructed two-sided inverse Rₐ of M_V + B - aI on
the natural domain D(V), the algebraic factor
  I - (b-a) Rₐ
controls the shift at an arbitrary real b.

If that bounded factor is a unit, we construct a new continuous inverse
Q_b = Rₐ ∘ (I - (b-a) Rₐ)⁻¹. The proof explicitly checks its domain-valued
range and both inverse equations; it is not merely an eigenvalue test.

No additional compactness or self-adjointness is necessary for this
bounded-inverse construction. This is an intermediate step toward the
full real spectral mapping statement.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev ShiftEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- A real parameter belongs to the bounded-resolvent set of the full
unbounded onsite-plus-bounded operator on D(V) if a continuous linear
inverse exists, takes values in the natural domain, and obeys both
inverse equations. The existence is nontrivial: the inverse is bounded
even when M_V is not. -/
def infiniteBoundedOnsiteRealRegular
    (V : Tile → ℝ) (B : ShiftEnd Tile) (b : ℝ) : Prop :=
  ∃ Q : ShiftEnd Tile,
    (∀ f : TileHilbert Tile,
      ∃ ψ : infiniteOnsiteDomain V,
        (ψ.1 : TileHilbert Tile) = Q f ∧
          infiniteBoundedOnsiteShift V b B ψ = f) ∧
    (∀ ψ : infiniteOnsiteDomain V,
      Q (infiniteBoundedOnsiteShift V b B ψ) =
        (ψ.1 : TileHilbert Tile))

/-- The shifted full operator factors through the known inverse Rₐ:
(H-bI) = (I-(b-a)Rₐ)(H-aI) on the unchanged domain D(V). -/
theorem infiniteBoundedOnsiteShift_factor
    (V : Tile → ℝ) (a b : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : ShiftEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (ψ : infiniteOnsiteDomain V) :
    (1 - (b - a) • infiniteBoundedOnsiteResolvent V a hgap B hsmall)
      (infiniteBoundedOnsiteShift V a B ψ) =
    infiniteBoundedOnsiteShift V b B ψ := by
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  have hleft : R (infiniteBoundedOnsiteShift V a B ψ) =
      (ψ.1 : TileHilbert Tile) :=
    infiniteBoundedOnsiteResolvent_left_inverse V a hgap B hsmall ψ
  have hformula (x : TileHilbert Tile) :
      (1 - (b - a) • R) x = x - (b - a) • R x := by
    simp
  rw [hformula, hleft]
  unfold infiniteBoundedOnsiteShift
  rw [show b = a + (b - a) by ring, add_smul]
  abel

/-- A unit factor I-(b-a)Rₐ gives a bounded two-sided inverse for
the unbounded operator H-bI, with solutions still in D(V). -/
theorem infiniteBoundedOnsite_realRegular_of_unit
    (V : Tile → ℝ) (a b : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : ShiftEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hunit : IsUnit
      (1 - (b - a) • infiniteBoundedOnsiteResolvent V a hgap B hsmall)) :
    infiniteBoundedOnsiteRealRegular V B b := by
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  let U : (ShiftEnd Tile)ˣ := hunit.unit
  have hU : (U : ShiftEnd Tile) = 1 - (b - a) • R := hunit.unit_spec
  let Q : ShiftEnd Tile := R.comp (↑(U⁻¹) : ShiftEnd Tile)
  have hmul (f : TileHilbert Tile) :
      (U : ShiftEnd Tile) ((↑(U⁻¹) : ShiftEnd Tile) f) = f := by
    have hh := congrArg (fun T : ShiftEnd Tile => T f) (Units.mul_inv U)
    simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using hh
  have hinvmul (f : TileHilbert Tile) :
      (↑(U⁻¹) : ShiftEnd Tile) ((U : ShiftEnd Tile) f) = f := by
    have hh := congrArg (fun T : ShiftEnd Tile => T f) (Units.inv_mul U)
    simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using hh
  refine ⟨Q, ?_, ?_⟩
  · intro f
    let g : TileHilbert Tile := (↑(U⁻¹) : ShiftEnd Tile) f
    let ψ := infiniteBoundedOnsiteResolventSolution V a hgap B hsmall g
    refine ⟨ψ, ?_, ?_⟩
    · change R g = R g
      rfl
    · have ha : infiniteBoundedOnsiteShift V a B ψ = g :=
        infiniteBoundedOnsiteResolvent_right_inverse V a hgap B hsmall g
      rw [← infiniteBoundedOnsiteShift_factor V a b hgap B hsmall ψ]
      rw [← hU, ha]
      exact hmul f
  · intro ψ
    have hfactor := infiniteBoundedOnsiteShift_factor V a b hgap B hsmall ψ
    rw [← hU] at hfactor
    change R ((↑(U⁻¹) : ShiftEnd Tile)
      (infiniteBoundedOnsiteShift V b B ψ)) = (ψ.1 : TileHilbert Tile)
    rw [← hfactor, hinvmul]
    exact infiniteBoundedOnsiteResolvent_left_inverse V a hgap B hsmall ψ


/-- A real parameter b different from the known resolvent shift a
has a bounded two-sided inverse for H-bI whenever its reciprocal
spectral parameter (b-a)⁻¹ lies outside the bounded spectrum of Rₐ.
Unlike the eigenpair correspondence, this constructs the inverse
on every forcing term, with values in D(V). -/
theorem infiniteBoundedOnsite_realRegular_of_notMem_resolventSpectrum
    (V : Tile → ℝ) (a b : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : ShiftEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hb : b ≠ a)
    (hnot : (b - a)⁻¹ ∉ spectrum ℝ
      (infiniteBoundedOnsiteResolvent V a hgap B hsmall)) :
    infiniteBoundedOnsiteRealRegular V B b := by
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  let t : ℝˣ := Units.mk0 (b - a) (sub_ne_zero.mpr hb)
  have ht : (t : ℝ) = b - a := rfl
  have htinv : (↑(t⁻¹) : ℝ) = (b - a)⁻¹ := by
    simp [t]
  have hunitR : IsUnit ((b - a)⁻¹ • (1 : ShiftEnd Tile) - R) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (spectrum.notMem_iff.mp hnot)
  have htunit : IsUnit ((t⁻¹) • (1 : ShiftEnd Tile) - R) := by
    simpa only [Units.smul_def, htinv] using hunitR
  have hfactor : IsUnit (1 - (t : ℝ) • R) := by
    have hu := (IsUnit.smul_sub_iff_sub_inv_smul (t⁻¹) R).mp htunit
    simpa only [inv_inv, Units.smul_def] using hu
  exact infiniteBoundedOnsite_realRegular_of_unit V a b hgap B hsmall
    (by simpa only [ht] using hfactor)

end SpectralGeometry
