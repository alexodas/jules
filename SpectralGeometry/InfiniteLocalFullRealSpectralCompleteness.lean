import SpectralGeometry.InfiniteLocalFullEigenvalueMultiplicityCoverage

/-!
# Real spectral completeness for the interacting matching-family operator

The previous modules separately established three features of the full
unbounded geometric operator on its natural domain:

* the genuine full-operator eigenspaces have dense linear span when the
  compact resolvent is self-adjoint (§4.27);
* the full real bounded-inverse spectrum equals the genuine real point
  spectrum under the compact-resolvent hypotheses (§4.32);
* the latter set is exactly the set of parameters of positive finite
  eigenspace multiplicity (§4.34).

This module makes their joint consequence explicit: the only real spectral
points are precisely the positive-multiplicity parameters, and the
eigenspaces indexed *only by these real spectral points* already have
dense linear span. In particular, there is no missing real continuous
bounded-inverse spectrum. This does not formalize the complex spectrum,
an eigenbasis indexed by natural numbers, or quantitative spectral growth.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev RealCompleteEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- Full real bounded-inverse spectral membership is equivalent to
strict positivity of the finite geometric eigenspace dimension.
The claim does not require self-adjointness: compactness and the
existing real Fredholm spectral-exhaustion theorem suffice. -/
theorem infiniteLocalMatching_fullRealSpectrum_iff_multiplicity_pos
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : RealCompleteEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (b : ℝ) :
    b ∈ infiniteBoundedOnsiteRealSpectrum V
      (infiniteLocalBoundedCorrection D σ w P ε shift) ↔
    0 < infiniteLocalMatchingFullMultiplicity
      D V σ w P ε shift a hgap hproper hsmall b := by
  exact
    (infiniteLocalMatching_fullRealSpectrum_iff_hasFullEigenvalue
      D V σ w P ε shift a hgap hproper hsmall b).trans
    (infiniteLocalMatching_full_eigenvalue_iff_multiplicity_pos
      D V σ w P ε shift a hgap hproper hsmall b)

/-- The entire real bounded-inverse spectrum is the projection of the
finite-multiplicity tag set: the two independently defined notions of
real spectrum are now shown to agree exactly. -/
theorem infiniteLocalMatching_fullRealSpectrum_eq_multiplicity_tags_image
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : RealCompleteEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    infiniteBoundedOnsiteRealSpectrum V
      (infiniteLocalBoundedCorrection D σ w P ε shift) =
    (fun p : ℝ × ℕ => p.1) ''
      infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall := by
  rw [infiniteLocalMatching_full_multiplicity_tags_image_fst
    D V σ w P ε shift a hgap hproper hsmall]
  ext b
  exact infiniteLocalMatching_fullRealSpectrum_iff_hasFullEigenvalue
    D V σ w P ε shift a hgap hproper hsmall b

/-- Under compact self-adjoint resolvent hypotheses, the eigenspaces
indexed by the real bounded-inverse spectrum alone have dense linear
span. The additional inequality excludes the designated regular shift,
which is automatically outside the real spectrum. The indexed sum
may be nonclosed, so density is expressed by the orthogonal complement
being bottom rather than by asserting that the sum itself is top.

No complex-spectrum or ordered-enumeration result is claimed. -/
theorem infiniteLocalMatching_fullRealSpectralEigenspaces_dense
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : RealCompleteEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ) :
    (⨆ b : {b : ℝ //
      b ≠ a ∧ b ∈ infiniteBoundedOnsiteRealSpectrum V
        (infiniteLocalBoundedCorrection D σ w P ε shift)},
      infiniteLocalMatchingFullEigenspace
        D V σ w P ε shift a hgap hsmall (b : ℝ) b.property.1)ᗮ = ⊥ := by
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  let S := infiniteBoundedOnsiteRealSpectrum V B
  have hdense :
      (⨆ b : {b : ℝ // b ≠ a},
        infiniteLocalMatchingFullEigenspace
          D V σ w P ε shift a hgap hsmall (b : ℝ) b.property)ᗮ = ⊥ :=
    infiniteLocalMatchingFullEigenspaces_dense
      D V σ w P ε shift a hgap hproper hsmall hσ hP
  have hle :
      (⨆ b : {b : ℝ // b ≠ a},
        infiniteLocalMatchingFullEigenspace
          D V σ w P ε shift a hgap hsmall (b : ℝ) b.property) ≤
      (⨆ b : {b : ℝ // b ≠ a ∧ b ∈ S},
        infiniteLocalMatchingFullEigenspace
          D V σ w P ε shift a hgap hsmall (b : ℝ) b.property.1) := by
    apply iSup_le
    intro b
    by_cases hbS : (b : ℝ) ∈ S
    · exact le_iSup_of_le
        (⟨(b : ℝ), b.property, hbS⟩ :
          {b : ℝ // b ≠ a ∧ b ∈ S}) (le_refl _)
    · have hbot :
          infiniteLocalMatchingFullEigenspace
            D V σ w P ε shift a hgap hsmall
            (b : ℝ) b.property = ⊥ := by
        apply eq_bot_iff.mpr
        intro f hf
        obtain ⟨ψ, hψf, heq⟩ :=
          (infiniteLocalMatchingFullEigenspace_mem_iff
            D V σ w P ε shift a hgap hsmall
            (b : ℝ) b.property f).mp hf
        by_contra hfne
        have heig : infiniteLocalMatchingHasFullEigenvalue
            D V σ w P ε shift (b : ℝ) := by
          refine ⟨ψ, ?_, ?_⟩
          · rw [hψf]
            exact hfne
          · rw [hψf]
            exact heq
        have hspec :
            (b : ℝ) ∈ S :=
          (infiniteLocalMatching_fullRealSpectrum_iff_hasFullEigenvalue
            D V σ w P ε shift a hgap hproper hsmall (b : ℝ)).mpr heig
        exact hbS hspec
      rw [hbot]
      exact bot_le
  change
    (⨆ b : {b : ℝ // b ≠ a ∧ b ∈ S},
      infiniteLocalMatchingFullEigenspace
        D V σ w P ε shift a hgap hsmall (b : ℝ) b.property.1)ᗮ = ⊥
  apply le_antisymm
  · calc
      (⨆ b : {b : ℝ // b ≠ a ∧ b ∈ S},
        infiniteLocalMatchingFullEigenspace
          D V σ w P ε shift a hgap hsmall (b : ℝ) b.property.1)ᗮ ≤
        (⨆ b : {b : ℝ // b ≠ a},
          infiniteLocalMatchingFullEigenspace
            D V σ w P ε shift a hgap hsmall (b : ℝ) b.property)ᗮ :=
          Submodule.orthogonal_le hle
      _ = ⊥ := hdense
  · exact bot_le

end SpectralGeometry
