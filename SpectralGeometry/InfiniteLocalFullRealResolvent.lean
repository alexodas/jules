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
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using hh
  have hinvmul (f : TileHilbert Tile) :
      (↑(U⁻¹) : ShiftEnd Tile) ((U : ShiftEnd Tile) f) = f := by
    have hh := congrArg (fun T : ShiftEnd Tile => T f) (Units.inv_mul U)
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using hh
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
  letI : IsScalarTower ℝˣ (ShiftEnd Tile) (ShiftEnd Tile) :=
    ⟨fun r x y => by
      change ((r : ℝ) • x) * y = (r : ℝ) • (x * y)
      exact smul_mul_assoc _ _ _⟩
  have hfactor : IsUnit (1 - (t : ℝ) • R) := by
    have hu := (IsUnit.smul_sub_iff_sub_inv_smul (t⁻¹) R).mp htunit
    simpa only [inv_inv, Units.smul_def] using hu
  exact infiniteBoundedOnsite_realRegular_of_unit V a b hgap B hsmall
    (by simpa only [ht] using hfactor)


/-- With compact resolvent Rₐ, the actual bounded-inverse condition
for the full unbounded shift H-bI is equivalent to exclusion of the
reciprocal spectral parameter from the bounded spectrum of Rₐ.
No self-adjointness is needed for this real spectral mapping theorem. -/
theorem infiniteBoundedOnsite_realRegular_iff_resolventSpectrum_compl
    (V : Tile → ℝ) (a b : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : ShiftEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hb : b ≠ a) :
    infiniteBoundedOnsiteRealRegular V B b ↔
      (b - a)⁻¹ ∉ spectrum ℝ
        (infiniteBoundedOnsiteResolvent V a hgap B hsmall) := by
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  constructor
  · rintro ⟨Q, _, hleft⟩ hspec
    have hcompact : IsCompactOperator R :=
      infiniteBoundedOnsiteResolvent_compact V a hgap hproper B hsmall
    have hμ : (b - a)⁻¹ ≠ 0 :=
      inv_ne_zero (sub_ne_zero.mpr hb)
    have heig : Module.End.HasEigenvalue R.toLinearMap (b - a)⁻¹ :=
      (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcompact hμ).mpr hspec
    obtain ⟨f, hf⟩ := Module.End.HasEigenvalue.exists_hasEigenvector heig
    have hRf : R f = (b - a)⁻¹ • f :=
      Module.End.mem_eigenspace_iff.mp hf.1
    obtain ⟨ψ, hψ, hshift⟩ :=
      (infiniteBoundedOnsiteResolvent_eigenpair_iff
        V a hgap B hsmall (b - a)⁻¹ hμ f).mp hRf
    have hshiftb : infiniteBoundedOnsiteShift V b B ψ = 0 := by
      have hshift' : infiniteBoundedOnsiteShift V a B ψ =
          (b - a) • f := by
        simpa only [inv_inv] using hshift
      change infiniteOnsiteOperator V ψ -
          b • (ψ.1 : TileHilbert Tile) + B ψ.1 = 0
      change infiniteOnsiteOperator V ψ -
          a • (ψ.1 : TileHilbert Tile) + B ψ.1 = (b - a) • f at hshift'
      rw [hψ] at hshift' ⊢
      rw [show b = a + (b - a) by ring, add_smul]
      calc
        infiniteOnsiteOperator V ψ - (a • f + (b - a) • f) + B f =
          (infiniteOnsiteOperator V ψ - a • f + B f) -
            (b - a) • f := by abel
        _ = 0 := by rw [hshift']; exact sub_self _
    have hzero := hleft ψ
    rw [hshiftb, map_zero] at hzero
    apply hf.2
    rw [← hψ]
    exact hzero.symm
  · exact infiniteBoundedOnsite_realRegular_of_notMem_resolventSpectrum
      V a b hgap B hsmall hb

/-- The real spectrum of the unbounded operator, defined intrinsically
as the complement of the set of shifts possessing a bounded two-sided
inverse on its natural domain. This is *not* the point spectrum. -/
def infiniteBoundedOnsiteRealSpectrum (V : Tile → ℝ)
    (B : ShiftEnd Tile) : Set ℝ :=
  {b | ¬ infiniteBoundedOnsiteRealRegular V B b}

/-- Spectral mapping for the entire **real bounded-inverse spectrum**
of the unbounded natural-domain operator, away from the known shift a:
b belongs to this spectrum exactly when (b-a)⁻¹ belongs to the
bounded-operator spectrum of Rₐ. -/
theorem infiniteBoundedOnsite_realSpectrum_iff_resolventSpectrum
    (V : Tile → ℝ) (a b : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : ShiftEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hb : b ≠ a) :
    b ∈ infiniteBoundedOnsiteRealSpectrum V B ↔
      (b - a)⁻¹ ∈ spectrum ℝ
        (infiniteBoundedOnsiteResolvent V a hgap B hsmall) := by
  change ¬ infiniteBoundedOnsiteRealRegular V B b ↔
    (b - a)⁻¹ ∈ spectrum ℝ
      (infiniteBoundedOnsiteResolvent V a hgap B hsmall)
  rw [infiniteBoundedOnsite_realRegular_iff_resolventSpectrum_compl
    V a b hgap hproper B hsmall hb]
  simp

/-- The shift a with the already constructed resolvent belongs to the
regular set, hence is excluded from the full real spectrum. -/
theorem infiniteBoundedOnsite_shift_not_mem_realSpectrum
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : ShiftEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    a ∉ infiniteBoundedOnsiteRealSpectrum V B := by
  intro ha
  apply ha
  apply infiniteBoundedOnsite_realRegular_of_unit V a a hgap B hsmall
  have h1 : IsUnit (1 : ShiftEnd Tile) := isUnit_one
  simpa only [sub_self, zero_smul, sub_zero] using h1


/-- Under compact-resolvent hypotheses, the *entire real bounded-inverse
spectrum* of the full natural-domain matching-family operator consists
precisely of its genuine real point eigenvalues. The spectral definition
involves surjectivity, injectivity, and a bounded inverse; it is not
defined in terms of eigenvectors. The proof needs no symmetry assumptions:
compactness and the Fredholm alternative suffice over the reals. -/
theorem infiniteLocalMatching_fullRealSpectrum_iff_hasFullEigenvalue
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : ShiftEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (b : ℝ) :
    b ∈ infiniteBoundedOnsiteRealSpectrum V
      (infiniteLocalBoundedCorrection D σ w P ε shift) ↔
    infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift b := by
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  change b ∈ infiniteBoundedOnsiteRealSpectrum V B ↔
    infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift b
  by_cases hb : b = a
  · subst b
    have hreg : a ∉ infiniteBoundedOnsiteRealSpectrum V B :=
      infiniteBoundedOnsite_shift_not_mem_realSpectrum V a hgap B hsmall
    have hnone :
        ¬ infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift a := by
      rintro ⟨ψ, hψne, hψ⟩
      exact hψne (infiniteLocalMatching_no_eigenvector_at_shift
        D V σ w P ε shift a hgap hsmall ψ hψ)
    exact ⟨fun h => False.elim (hreg h), fun h => False.elim (hnone h)⟩
  · rw [infiniteBoundedOnsite_realSpectrum_iff_resolventSpectrum
      V a b hgap hproper B hsmall hb]
    exact infiniteLocalMatching_full_eigenpair_iff_resolvent_spectrum
      D V σ w P ε shift a hgap hproper hsmall b hb

end SpectralGeometry
