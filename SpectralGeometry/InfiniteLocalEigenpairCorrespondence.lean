module

public import SpectralGeometry.InfiniteLocalResolventSpectrum

public section

/-!
# Eigenpair correspondence between the compact resolvent and the full local operator

For the already constructed two-sided inverse Rₐ of M_V+B-aI on the
natural onsite domain D(V), every nonzero resolvent eigenvalue μ
corresponds to an eigenvalue a+μ⁻¹ of the unbounded full operator.

The forward direction constructs an actual natural-domain state from
the resolvent eigenvector; the reverse direction uses the established
left inverse. A geometric specialization identifies eigenvectors of
the concrete finite-color local matching operator.

This result does NOT yet enumerate all eigenvalues, assert their
isolation, or prove eigenvalue growth and inverse-square summability.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

abbrev CorrespondenceEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- A nonzero eigenvalue μ of the bounded resolvent corresponds to
a natural-domain eigenpair of the shifted unbounded onsite-plus-bounded
operator with eigenvalue μ⁻¹, and conversely. -/
theorem infiniteBoundedOnsiteResolvent_eigenpair_iff
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : CorrespondenceEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (μ : ℝ) (hμ : μ ≠ 0) (f : TileHilbert Tile) :
    infiniteBoundedOnsiteResolvent V a hgap B hsmall f = μ • f ↔
      ∃ ψ : infiniteOnsiteDomain V,
        (ψ.1 : TileHilbert Tile) = f ∧
        infiniteBoundedOnsiteShift V a B ψ = μ⁻¹ • f := by
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  constructor
  · intro heig
    let ψ := infiniteBoundedOnsiteResolventSolution V a hgap B hsmall (μ⁻¹ • f)
    have hR : R (μ⁻¹ • f) = f := by
      calc
        R (μ⁻¹ • f) = μ⁻¹ • R f := R.map_smul _ _
        _ = μ⁻¹ • (μ • f) := by rw [heig]
        _ = f := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
    refine ⟨ψ, ?_, ?_⟩
    · change R (μ⁻¹ • f) = f
      exact hR
    · exact infiniteBoundedOnsiteResolvent_right_inverse
        V a hgap B hsmall (μ⁻¹ • f)
  · rintro ⟨ψ, hψ, hshift⟩
    have hleft :
        R (infiniteBoundedOnsiteShift V a B ψ) =
          (ψ.1 : TileHilbert Tile) :=
      infiniteBoundedOnsiteResolvent_left_inverse V a hgap B hsmall ψ
    rw [hshift, hψ] at hleft
    have hscaled := congrArg (fun x : TileHilbert Tile => μ • x) hleft
    simpa only [map_smul, smul_smul, mul_inv_cancel₀ hμ, one_smul] using hscaled

/-- Every nonzero-resolvent eigenvector lies in the natural onsite
domain of the full unbounded operator. -/
theorem infiniteBoundedOnsiteResolvent_eigenvector_mem_domain
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : CorrespondenceEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (μ : ℝ) (hμ : μ ≠ 0) (f : TileHilbert Tile)
    (heig : infiniteBoundedOnsiteResolvent V a hgap B hsmall f = μ • f) :
    f ∈ infiniteOnsiteDomain V := by
  obtain ⟨ψ, hψ, _⟩ :=
    (infiniteBoundedOnsiteResolvent_eigenpair_iff
      V a hgap B hsmall μ hμ f).mp heig
  rw [← hψ]
  exact ψ.2

/-- Eigenvectors of the bounded full matching resolvent correspond
exactly to natural-domain eigenvectors of the actual unbounded
matching-family operator, with eigenvalue a+μ⁻¹. -/
theorem infiniteLocalMatching_resolvent_eigenpair_iff
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : CorrespondenceEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (μ : ℝ) (hμ : μ ≠ 0) (f : TileHilbert Tile) :
    infiniteBoundedOnsiteResolvent V a hgap
      (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall f = μ • f ↔
      ∃ ψ : infiniteOnsiteDomain V,
        (ψ.1 : TileHilbert Tile) = f ∧
        infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
          (a + μ⁻¹) • f := by
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  have hpair :=
    infiniteBoundedOnsiteResolvent_eigenpair_iff
      V a hgap B hsmall μ hμ f
  constructor
  · intro heig
    obtain ⟨ψ, hψ, hA⟩ := hpair.mp heig
    refine ⟨ψ, hψ, ?_⟩
    have hH := infiniteLocalShiftedPerturbed_eq_onsite_add_correction
      D V σ w P ε shift ψ
    change infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile) +
      B ψ.1 = μ⁻¹ • f at hA
    rw [hψ] at hA
    rw [hH, hψ, add_smul]
    calc
      infiniteOnsiteOperator V ψ + B f =
        (infiniteOnsiteOperator V ψ - a • f + B f) + a • f := by abel
      _ = μ⁻¹ • f + a • f := by rw [hA]
      _ = a • f + μ⁻¹ • f := add_comm _ _
  · rintro ⟨ψ, hψ, hH⟩
    apply hpair.mpr
    refine ⟨ψ, hψ, ?_⟩
    rw [infiniteLocalShiftedPerturbed_eq_onsite_add_correction,
      hψ, add_smul] at hH
    change infiniteOnsiteOperator V ψ -
      a • (ψ.1 : TileHilbert Tile) + B ψ.1 = μ⁻¹ • f
    rw [hψ]
    calc
      infiniteOnsiteOperator V ψ - a • f + B f =
        (infiniteOnsiteOperator V ψ + B f) - a • f := by abel
      _ = (a • f + μ⁻¹ • f) - a • f := by rw [hH]
      _ = μ⁻¹ • f := by abel

/-- An equivalent, directly usable statement with an unbounded
eigenvalue eigenvalue ≠ a: the corresponding resolvent eigenvalue is
(eigenvalue-a)⁻¹. -/
theorem infiniteLocalMatching_resolvent_eigenpair_iff_of_ne
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : CorrespondenceEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (heigenvalue : eigenvalue ≠ a) (f : TileHilbert Tile) :
    infiniteBoundedOnsiteResolvent V a hgap
      (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall f =
        (eigenvalue - a)⁻¹ • f ↔
      ∃ ψ : infiniteOnsiteDomain V,
        (ψ.1 : TileHilbert Tile) = f ∧
        infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
          eigenvalue • f := by
  have hμ : (eigenvalue - a)⁻¹ ≠ 0 :=
    inv_ne_zero (sub_ne_zero.mpr heigenvalue)
  have hh :=
    infiniteLocalMatching_resolvent_eigenpair_iff
      D V σ w P ε shift a hgap hsmall
      (eigenvalue - a)⁻¹ hμ f
  have hvalue : a + ((eigenvalue - a)⁻¹)⁻¹ = eigenvalue := by
    rw [inv_inv]
    ring
  simpa only [hvalue] using hh

end SpectralGeometry
