module

public import SpectralGeometry.IndexedSpectralPoints
public import SpectralGeometry.InfiniteFullSpectralProduct

public section

/-!
# Exact geometric zero orders for any monotone domain eigenbasis

The infinite sequence in the min-max response API is compared to an exact
enumeration of the full geometric multiplicity tags. This enumeration is
constructed with zero matching colors and a parameter-dependent resolvent
shift; it is not inferred from the existential eigenbasis statement alone.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

/-- The paired product is entire, has exactly the real full spectrum as its
two-sided divisor, and records geometric multiplicities of the *actual*
onsite-plus-bounded operator. The existential resolvent shift is allowed to
depend on the bounded correction, while c and d are fixed. -/
@[expose] def HasExactFullSpectralProduct (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (ev : ℕ → ℝ) (c d : ℂ) : Prop :=
  ∃ (a : ℝ) (hunit : ∀ t, 1 ≤ V t - a),
    ∃ (hsmall : ‖(infiniteLocalBoundedCorrection 0
      (fun i => Fin.elim0 i) (fun _ => 0) B 1 0).comp
        (infiniteOnsiteResolventCLM V a hunit)‖ < 1),
      Differentiable ℂ (canonicalProduct ev c d) ∧
      (∀ s : ℂ, canonicalProduct ev c d s = 0 ↔
        ∃ r ∈ infiniteBoundedOnsiteRealSpectrum V B,
          s = c + d * (r : ℂ) ∨ s = c - d * (r : ℂ)) ∧
      (∀ r : ℝ, 0 < r → ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
        analyticOrderAt (canonicalProduct ev c d)
          (c + d * ((sign * r : ℝ) : ℂ)) =
        (infiniteLocalMatchingFullMultiplicity 0 V
          (fun i => Fin.elim0 i) (fun _ => 0) B 1 0
          a hunit hproper hsmall r : ℕ∞))

/-- An ordered domain eigenbasis has the same levels, at every index, as
the genuine strictly ordered exact multiplicity-tag enumeration. This is
the required bridge between the variational and divisor APIs. -/
theorem onsitePlusBounded_ordered_eq_exact_tag_levels [Infinite Tile]
    (V : Tile → ℝ) (v₀ : ℝ) (hV : ∀ t, v₀ ≤ V t)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (ev : ℕ → ℝ) (hev : Monotone ev)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev) :
    ∃ (a : ℝ) (hunit : ∀ t, 1 ≤ V t - a),
      ∃ (hsmall : ‖(infiniteLocalBoundedCorrection 0
        (fun i => Fin.elim0 i) (fun _ => 0) B 1 0).comp
          (infiniteOnsiteResolventCLM V a hunit)‖ < 1),
        ∃ (seq : ℕ → ℝ ×ₗ ℕ),
          StrictMono seq ∧
          Set.range seq = toLex ''
            infiniteLocalMatchingFullMultiplicityTags 0 V
              (fun i => Fin.elim0 i) (fun _ => 0) B 1 0
              a hunit hproper hsmall ∧
          ev = (fun n => (ofLex (seq n)).1) := by
  classical
  let σ : Fin 0 → Tile ≃ Tile := fun i => Fin.elim0 i
  let w : Fin 0 → ℝ := fun _ => 0
  have hc : infiniteLocalBoundedCorrection 0 σ w B 1 0 = B :=
    zeroMatching_correction B
  obtain ⟨a, hunit, hbare, _⟩ :=
    infiniteBoundedOnsite_exists_compact_shift V v₀ hV hproper B
  have hs : ‖(infiniteLocalBoundedCorrection 0 σ w B 1 0).comp
      (infiniteOnsiteResolventCLM V a hunit)‖ < 1 := by
    simpa only [hc] using hbare
  have hσ : ∀ i t, σ i (σ i t) = t := fun i => Fin.elim0 i
  have hP : ∀ x y, inner ℝ x (B y) = inner ℝ (B x) y :=
    fun x y => (hB x y).symm
  have hi := infiniteLocalMatching_full_tags_infinite
    0 V σ w B 1 0 a hunit hproper hs hσ hP
  have hlo (r : ℝ) (hr : infiniteLocalMatchingHasFullEigenvalue
      0 V σ w B 1 0 r) :
      v₀ - ‖infiniteLocalBoundedCorrection 0 σ w B 1 0‖ ≤ r := by
    obtain ⟨x, hx, he⟩ := hr
    exact infiniteLocalShiftedPerturbed_eigenvalue_ge_onsite_lower_sub_norm
      0 V σ w B 1 0 v₀ hV x r he hx
  obtain ⟨seq, hseq, hrange⟩ :=
    infiniteLocalMatching_full_infinite_tags_exists_strictMono_enumeration
      0 V σ w B 1 0 a hunit hproper hs hσ hP _ hlo hi
  obtain ⟨btag⟩ := infiniteLocalMatching_full_exists_domainEigenbasis
    0 V σ w B 1 0 a hunit hproper hs hσ hP seq hseq hrange
  have btag' : DomainEigenbasis (infiniteOnsiteDomain V)
      (onsitePlusBounded V B) (fun n => (ofLex (seq n)).1) := by
    simpa only [hc] using btag
  have htagmono : Monotone (fun n => (ofLex (seq n)).1) :=
    fun i j hij => Prod.Lex.monotone_fst _ _ (hseq.monotone hij)
  have heq : ev = (fun n => (ofLex (seq n)).1) :=
    DomainEigenbasis.ordered_levels_unique b btag'
      (onsitePlusBounded_symmetric V B hB) hev htagmono
  exact ⟨a, hunit, hs, seq, hseq, hrange, heq⟩

/-- Exact entire spectral divisor and geometric zero orders for *any*
monotone complete eigenbasis of an infinite proper symmetric operator.
No exact-tag enumeration is assumed for that basis: it is constructed. -/
theorem onsitePlusBounded_hasExactFullSpectralProduct [Infinite Tile]
    (V : Tile → ℝ) (v₀ : ℝ) (hV : ∀ t, v₀ ≤ V t)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (ev : ℕ → ℝ) (hev : Monotone ev)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev)
    (hp : ∀ n, 0 < ev n) (hs : Summable (fun n => 1 / (ev n) ^ 2))
    (c d : ℂ) (hd : d ≠ 0) :
    HasExactFullSpectralProduct V B hproper ev c d := by
  obtain ⟨a, hunit, hsmall, seq, hseq, hrange, heq⟩ :=
    onsitePlusBounded_ordered_eq_exact_tag_levels
      V v₀ hV hproper B hB ev hev b
  have ha : Admissible (fun n => (ofLex (seq n)).1) c d := by
    rw [← heq]
    exact fullSpectrum_admissible_of_positive_summable ev hp hs c d
  have hfull := infiniteLocalMatching_full_product_entire_exact_zeros
    0 V (fun i => Fin.elim0 i) (fun _ => 0) B 1 0
    a hunit hproper hsmall seq hseq hrange c d ha hd
  rw [← heq] at hfull
  refine ⟨a, hunit, hsmall, ?_⟩
  simpa only [zeroMatching_correction] using hfull

/-- Both indexed points are genuine zeros of the corresponding paired
product, with no need to choose an eigenvector at this index. -/
theorem indexedSpectralPoints_product_zeros (ev : ℕ → ℝ) (c d : ℂ)
    (ha : Admissible ev c d) (hd : d ≠ 0) (n : ℕ) :
    canonicalProduct ev c d (positiveSpectralPoint ev c d n) = 0 ∧
      canonicalProduct ev c d (negativeSpectralPoint ev c d n) = 0 := by
  constructor
  · exact (canonicalProduct_zero_iff ha hd _).mpr ⟨n, Or.inl rfl⟩
  · exact (canonicalProduct_zero_iff ha hd _).mpr ⟨n, Or.inr rfl⟩

#print axioms onsitePlusBounded_ordered_eq_exact_tag_levels
#print axioms onsitePlusBounded_hasExactFullSpectralProduct

end
end SpectralGeometry
