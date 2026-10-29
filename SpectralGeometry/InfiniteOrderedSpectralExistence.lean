module

public import SpectralGeometry.InfiniteOrderedSpectralControl

public section

/-!
# Existence of ordered full eigenbases under preserved operator hypotheses

A generic bounded correction is a matching correction with zero matching
colors. This reuses the established self-adjoint compact-resolvent theory.
Infinitude of the site type supplies infinitely many multiplicity tags.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

/-- The generic bounded correction is an instance of the existing local
operator construction, with an empty matching family. -/
theorem zeroMatching_correction (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) :
    infiniteLocalBoundedCorrection 0 (fun i => Fin.elim0 i) (fun _ => 0) B 1 0 = B := by
  simp [infiniteLocalBoundedCorrection, infiniteLocalMatchingLaplacian]
  exact zero_smul ℝ (ContinuousLinearMap.id ℝ (TileHilbert Tile))

/-- Generic onsite-plus-bounded multiplication in the established partial
operator API, using exactly the original natural onsite domain. -/
@[expose] def onsitePlusBoundedPMap (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) :
    TileHilbert Tile →ₗ.[ℝ] TileHilbert Tile :=
  infiniteLocalShiftedPerturbedPMap 0 V (fun i => Fin.elim0 i) (fun _ => 0) B 1 0

theorem onsitePlusBoundedPMap_domain (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) :
    (onsitePlusBoundedPMap V B).domain = infiniteOnsiteDomain V := rfl

theorem onsitePlusBoundedPMap_apply (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) (x : infiniteOnsiteDomain V) :
    onsitePlusBoundedPMap V B x = onsitePlusBounded V B x := by
  have hh := onsitePlusBounded_eq_local 0 V (fun i => Fin.elim0 i) (fun _ => 0) B 1 0
  rw [zeroMatching_correction] at hh
  exact (congrArg (fun A => A x) hh).symm

theorem onsitePlusBoundedPMap_isSelfAdjoint (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) :
    IsSelfAdjoint (onsitePlusBoundedPMap V B) :=
  infiniteLocalShiftedPerturbedPMap_isSelfAdjoint
    0 V (fun i => Fin.elim0 i) (fun _ => 0) B 1 0
    (fun i => Fin.elim0 i) (fun x y => (hB x y).symm)

/-- Lower-bounded proper onsite energies and a symmetric bounded correction
on infinitely many sites supply a complete monotonically ordered eigenbasis.
No simple-spectrum or infinite-tag assumption is added. -/
theorem onsitePlusBounded_exists_orderedEigenbasis [Infinite Tile]
    (V : Tile → ℝ) (v₀ : ℝ) (hV : ∀ t, v₀ ≤ V t)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) :
    ∃ ev : ℕ → ℝ, Monotone ev ∧
      Nonempty (DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev) := by
  classical
  obtain ⟨a, hgap, hsmall, _⟩ := infiniteBoundedOnsite_exists_compact_shift V v₀ hV hproper B
  let σ : Fin 0 → Tile ≃ Tile := fun i => Fin.elim0 i
  let w : Fin 0 → ℝ := fun _ => 0
  have hc : infiniteLocalBoundedCorrection 0 σ w B 1 0 = B := zeroMatching_correction B
  have hs : ‖(infiniteLocalBoundedCorrection 0 σ w B 1 0).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1 := by simpa only [hc] using hsmall
  have hσ : ∀ i t, σ i (σ i t) = t := fun i => Fin.elim0 i
  have hP : ∀ x y, inner ℝ x (B y) = inner ℝ (B x) y := fun x y => (hB x y).symm
  have hi := infiniteLocalMatching_full_tags_infinite 0 V σ w B 1 0 a hgap hproper hs hσ hP
  have hlo (ev : ℝ) (he : infiniteLocalMatchingHasFullEigenvalue 0 V σ w B 1 0 ev) :
      v₀ - ‖infiniteLocalBoundedCorrection 0 σ w B 1 0‖ ≤ ev := by
    obtain ⟨x, hx, he⟩ := he
    exact infiniteLocalShiftedPerturbed_eigenvalue_ge_onsite_lower_sub_norm
      0 V σ w B 1 0 v₀ hV x ev he hx
  obtain ⟨seq, hseq, hrange⟩ :=
    infiniteLocalMatching_full_infinite_tags_exists_strictMono_enumeration
      0 V σ w B 1 0 a hgap hproper hs hσ hP _ hlo hi
  have hb := infiniteLocalMatching_full_exists_domainEigenbasis
    0 V σ w B 1 0 a hgap hproper hs hσ hP seq hseq hrange
  refine ⟨fun n => (ofLex (seq n)).1, ?_, ?_⟩
  · exact fun i j hij => Prod.Lex.monotone_fst _ _ (hseq.monotone hij)
  · simpa only [hc] using hb

/-- Positive finite-sector perturbations keep all hypotheses needed for an
ordered infinite eigenbasis. In fact existence holds for every real parameter;
nonnegativity is only needed for monotonicity and gap preservation. -/
theorem finiteSector_exists_orderedEigenbasis [Infinite Tile]
    (V : Tile → ℝ) (v₀ : ℝ) (hV : ∀ t, v₀ ≤ V t)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (F : Finset Tile) (τ : ℝ) :
    ∃ ev : ℕ → ℝ, Monotone ev ∧
      Nonempty (DomainEigenbasis (infiniteOnsiteDomain V)
        (onsitePlusBounded V (B + τ • finiteSectorProjection F)) ev) :=
  onsitePlusBounded_exists_orderedEigenbasis V v₀ hV hproper _
    (finiteSectorCorrection_symmetric B hB F τ)

end
end SpectralGeometry
