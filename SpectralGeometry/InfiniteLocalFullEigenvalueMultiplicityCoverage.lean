module

public import SpectralGeometry.InfiniteLocalFullEigenvalueMultiplicity

public section

/-!
# Positive geometric multiplicity and exact coverage by multiplicity tags

The finite-dimensional eigenspace from §4.25 represents the actual
natural-domain eigenvalue equation whenever λ differs from the known
resolvent shift a. Thus the full matching operator has a genuine real
eigenvalue λ exactly when this space has positive finrank. The regular
shift a is excluded by its existing two-sided inverse and has
multiplicity zero.

Consequently each genuine real eigenvalue has at least one multiplicity
tag (λ, k), and projection of the tagged real point spectrum onto
its eigenvalue coordinate equals the entire real point spectrum.
These statements do not order eigenvalues or address the complex spectrum.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev CoverageEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- Under the compact-resolvent hypotheses, being a genuine eigenvalue
of the unbounded full matching operator is equivalent to having positive
geometric eigenspace dimension. No assumption of symmetry is needed. -/
theorem infiniteLocalMatching_full_eigenvalue_iff_multiplicity_pos
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : CoverageEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) :
    infiniteLocalMatchingHasFullEigenvalue
      D V σ w P ε shift eigenvalue ↔
    0 < infiniteLocalMatchingFullMultiplicity
      D V σ w P ε shift a hgap hproper hsmall eigenvalue := by
  classical
  by_cases hne : eigenvalue = a
  · subst eigenvalue
    have hnot : ¬ infiniteLocalMatchingHasFullEigenvalue
        D V σ w P ε shift a := by
      rintro ⟨ψ, hψne, hψ⟩
      exact hψne (infiniteLocalMatching_no_eigenvector_at_shift
        D V σ w P ε shift a hgap hsmall ψ hψ)
    have hzero : infiniteLocalMatchingFullMultiplicity
        D V σ w P ε shift a hgap hproper hsmall a = 0 :=
      infiniteLocalMatchingFullMultiplicity_at_shift
        D V σ w P ε shift a hgap hproper hsmall
    constructor
    · intro heigen
      exact False.elim (hnot heigen)
    · intro hpos
      rw [hzero] at hpos
      omega
  · let E : Submodule ℝ (TileHilbert Tile) :=
      infiniteLocalMatchingFullEigenspace
        D V σ w P ε shift a hgap hsmall eigenvalue hne
    letI : FiniteDimensional ℝ E :=
      infiniteLocalMatchingFullEigenspace_finiteDimensional
        D V σ w P ε shift a hgap hproper hsmall eigenvalue hne
    have hm : infiniteLocalMatchingFullMultiplicity
        D V σ w P ε shift a hgap hproper hsmall eigenvalue =
        Module.finrank ℝ E := by
      simp [infiniteLocalMatchingFullMultiplicity, hne, E]
    rw [hm, Module.finrank_pos_iff_exists_ne_zero]
    constructor
    · rintro ⟨ψ, hψne, hψ⟩
      have hmem : (ψ.1 : TileHilbert Tile) ∈ E :=
        (infiniteLocalMatchingFullEigenspace_mem_iff
          D V σ w P ε shift a hgap hsmall eigenvalue hne
          (ψ.1 : TileHilbert Tile)).2 ⟨ψ, rfl, hψ⟩
      refine ⟨⟨ψ.1, hmem⟩, ?_⟩
      intro hz
      apply hψne
      have hval := congrArg (fun x : E => (x.1 : TileHilbert Tile)) hz
      simpa using hval
    · rintro ⟨f, hf⟩
      obtain ⟨ψ, hval, heigen⟩ :=
        (infiniteLocalMatchingFullEigenspace_mem_iff
          D V σ w P ε shift a hgap hsmall eigenvalue hne
          (f.1 : TileHilbert Tile)).1 f.2
      have hfval : (f.1 : TileHilbert Tile) ≠ 0 := by
        intro hz
        apply hf
        apply Subtype.ext
        simpa using hz
      refine ⟨ψ, ?_, ?_⟩
      · rw [hval]
        exact hfval
      · rw [hval]
        exact heigen

/-- Every genuine real eigenvalue occurs as the first coordinate of at
least one multiplicity tag; conversely no tag has a non-eigenvalue
as its first coordinate. This holds without assuming the spectrum
or the tagged set is nonempty. -/
theorem infiniteLocalMatching_full_eigenvalue_iff_exists_tag
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : CoverageEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) :
    infiniteLocalMatchingHasFullEigenvalue
      D V σ w P ε shift eigenvalue ↔
    ∃ k : ℕ, (eigenvalue, k) ∈
      infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall := by
  constructor
  · intro heigen
    have hpos :=
      (infiniteLocalMatching_full_eigenvalue_iff_multiplicity_pos
        D V σ w P ε shift a hgap hproper hsmall eigenvalue).mp heigen
    exact ⟨0, heigen, hpos⟩
  · rintro ⟨k, hk⟩
    exact hk.1

/-- The first-coordinate projection of the multiplicity-tagged real
point spectrum equals the entire genuine real point spectrum, not just
a subset. -/
theorem infiniteLocalMatching_full_multiplicity_tags_image_fst
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : CoverageEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    (fun p : ℝ × ℕ => p.1) ''
      infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall =
      {eigenvalue : ℝ |
        infiniteLocalMatchingHasFullEigenvalue
          D V σ w P ε shift eigenvalue} := by
  ext eigenvalue
  constructor
  · rintro ⟨⟨μ, k⟩, hk, hμ⟩
    change μ = eigenvalue at hμ
    subst μ
    exact hk.1
  · intro heigen
    obtain ⟨k, hk⟩ :=
      (infiniteLocalMatching_full_eigenvalue_iff_exists_tag
        D V σ w P ε shift a hgap hproper hsmall eigenvalue).mp heigen
    exact ⟨(eigenvalue, k), hk, rfl⟩

end SpectralGeometry
