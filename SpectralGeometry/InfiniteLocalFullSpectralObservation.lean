module

public import SpectralGeometry.InfiniteLowEnergyCounting

public section

/-!
# Observation and total counting for the existing matching operator

This module connects the natural-domain spectral subspace to the existing
resolvent eigenspaces and their multiplicities. The counting theorem sums
the original geometric multiplicities over the entire real spectrum below
the threshold, including the empty case.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

/-- The generic operator equals the existing matching operator. -/
theorem onsitePlusBounded_eq_local (D : ℕ) (V : Tile → ℝ)
    (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε shift : ℝ) :
    onsitePlusBounded V (infiniteLocalBoundedCorrection D σ w P ε shift) =
      infiniteLocalShiftedPerturbedOperator D V σ w P ε shift := by
  apply LinearMap.ext
  intro x
  exact (infiniteLocalShiftedPerturbed_eq_onsite_add_correction D V σ w P ε shift x).symm

variable (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
variable (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε shift a : ℝ)
variable (hgap : ∀ t, 1 ≤ V t - a)
variable (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
variable (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
  (infiniteOnsiteResolventCLM V a hgap)‖ < 1)

/-- Natural-domain and compact-resolvent eigenspaces are equivalent. -/
@[expose] def domainEigenspaceEquivFull (ev : ℝ) (hne : ev ≠ a) :
    domainEigenspace (infiniteOnsiteDomain V)
      (onsitePlusBounded V (infiniteLocalBoundedCorrection D σ w P ε shift)) ev ≃ₗ[ℝ]
    infiniteLocalMatchingFullEigenspace D V σ w P ε shift a hgap hsmall ev hne := by
  let f : domainEigenspace (infiniteOnsiteDomain V)
      (onsitePlusBounded V (infiniteLocalBoundedCorrection D σ w P ε shift)) ev →ₗ[ℝ]
      infiniteLocalMatchingFullEigenspace D V σ w P ε shift a hgap hsmall ev hne := {
    toFun := fun x => ⟨(x : infiniteOnsiteDomain V),
      (infiniteLocalMatchingFullEigenspace_mem_iff D V σ w P ε shift a hgap hsmall ev hne _).mpr
        ⟨x, rfl, by
          have hx := (mem_domainEigenspace _ _ ev (x : infiniteOnsiteDomain V)).mp x.property
          simpa only [onsitePlusBounded_eq_local] using hx⟩⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : infiniteLocalMatchingFullEigenspace
      D V σ w P ε shift a hgap hsmall ev hne => (z : TileHilbert Tile)) hxy
  · intro y
    obtain ⟨x, hxy, hx⟩ :=
      (infiniteLocalMatchingFullEigenspace_mem_iff D V σ w P ε shift a hgap hsmall ev hne y).mp y.property
    have hm : x ∈ domainEigenspace (infiniteOnsiteDomain V)
        (onsitePlusBounded V (infiniteLocalBoundedCorrection D σ w P ε shift)) ev := by
      rw [mem_domainEigenspace, onsitePlusBounded_eq_local, hxy]
      exact hx
    exact ⟨⟨x, hm⟩, Subtype.ext hxy⟩

/-- Counting uses precisely the previously defined geometric multiplicity. -/
theorem domainEigenspace_finrank_eq_fullMultiplicity (ev : ℝ) (hne : ev ≠ a) :
    Module.finrank ℝ (domainEigenspace (infiniteOnsiteDomain V)
      (onsitePlusBounded V (infiniteLocalBoundedCorrection D σ w P ε shift)) ev) =
    infiniteLocalMatchingFullMultiplicity D V σ w P ε shift a hgap hproper hsmall ev := by
  simp only [infiniteLocalMatchingFullMultiplicity, dif_pos hne]
  exact (domainEigenspaceEquivFull D V σ w P ε shift a hgap hsmall ev hne).finrank_eq

variable (hσ : ∀ i t, σ i (σ i t) = t)
variable (hP : ∀ x y : TileHilbert Tile, inner ℝ x (P y) = inner ℝ (P x) y)
include hσ hP

/-- Quantitative observation for the full matching model. -/
theorem infiniteLocalMatching_full_lowSpectral_observation
    (v₀ R E : ℝ) (hV : ∀ t, v₀ ≤ V t) (hR : v₀ < R)
    (x : domainLowSpectralSubspace (infiniteOnsiteDomain V)
      (onsitePlusBounded V (infiniteLocalBoundedCorrection D σ w P ε shift)) E) :
    ((R - ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ - E) / (R - v₀)) *
      ‖((x : infiniteOnsiteDomain V) : TileHilbert Tile)‖ ^ 2 ≤
      ‖finiteSectorProjection (hproper R).toFinset (x : infiniteOnsiteDomain V)‖ ^ 2 := by
  apply onsitePlusBounded_lowSpectral_observation V _
    (infiniteLocalBoundedCorrection_symmetric D σ w P ε shift hσ hP) v₀ R E hV hR
  intro t ht
  have hh : ¬ V t ≤ R := by
    intro h
    exact ht ((Set.Finite.mem_toFinset (hproper R)).mpr h)
  exact (lt_of_not_ge hh).le

/-- Total count of the real spectrum below the threshold, with all original
geometric multiplicities and with no nonemptiness assumption. -/
theorem infiniteLocalMatching_full_total_lowEnergy_count (R : ℝ) :
    ∃ levels : Finset ℝ,
      (∀ ev : ℝ, ev ∈ levels ↔
        ev ∈ infiniteBoundedOnsiteRealSpectrum V
          (infiniteLocalBoundedCorrection D σ w P ε shift) ∧
        ev < R - ‖infiniteLocalBoundedCorrection D σ w P ε shift‖) ∧
      (∑ ev ∈ levels,
        infiniteLocalMatchingFullMultiplicity D V σ w P ε shift a hgap hproper hsmall ev) ≤
        (hproper R).toFinset.card := by
  classical
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  let T := R - ‖B‖
  let lower := a + 1 - ‖B‖
  have hV : ∀ t, a + 1 ≤ V t := fun t => by linarith [hgap t]
  have hlo (ev : ℝ) (hev : infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift ev) :
      lower ≤ ev := by
    obtain ⟨x, hx, he⟩ := hev
    exact infiniteLocalShiftedPerturbed_eigenvalue_ge_onsite_lower_sub_norm
      D V σ w P ε shift (a + 1) hV x ev he hx
  have hfin : {ev : ℝ | infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift ev ∧ ev < T}.Finite := by
    apply (infiniteLocalMatching_full_eigenvalues_bounded_finite
      D V σ w P ε shift a hgap hproper hsmall hσ hP
      (|lower| + |T|) (add_nonneg (abs_nonneg _) (abs_nonneg _))).subset
    intro ev hev
    refine ⟨?_, hev.1⟩
    rw [Real.norm_eq_abs, abs_le]
    have hl := hlo ev hev.1
    have ht := hev.2
    constructor <;> linarith [neg_abs_le lower, le_abs_self T, abs_nonneg lower, abs_nonneg T]
  let s := hfin.toFinset
  have hs (ev : ℝ) : ev ∈ s ↔
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift ev ∧ ev < T :=
    Set.Finite.mem_toFinset hfin
  refine ⟨s, ?_, ?_⟩
  · intro ev
    rw [hs, infiniteLocalMatching_fullRealSpectrum_iff_hasFullEigenvalue
      D V σ w P ε shift a hgap hproper hsmall ev]
  · have hcount := onsitePlusBounded_sum_multiplicities_le V B
      (infiniteLocalBoundedCorrection_symmetric D σ w P ε shift hσ hP)
      (min (a + 1) (R - 1)) R
      (fun t => (min_le_left _ _).trans (hV t))
      (by have hh := min_le_right (a + 1) (R - 1); linarith)
      (hproper R).toFinset
      (fun t ht => le_of_not_gt (fun hh => ht
        ((Set.Finite.mem_toFinset (hproper R)).mpr hh.le)))
      s (fun ev hev => ((hs ev).mp hev).2)
    convert hcount using 1
    apply Finset.sum_congr rfl
    intro ev hev
    have hne : ev ≠ a := by
      intro heq
      obtain ⟨x, hx, he⟩ := ((hs ev).mp hev).1
      rw [heq] at he
      exact hx (infiniteLocalMatching_no_eigenvector_at_shift
        D V σ w P ε shift a hgap hsmall x he)
    exact (domainEigenspace_finrank_eq_fullMultiplicity
      D V σ w P ε shift a hgap hproper hsmall ev hne).symm

end
end SpectralGeometry
