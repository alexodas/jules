import SpectralGeometry.InfiniteLocalFullRealSpectralCompleteness
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Prod.Lex.Basic

/-!
# Finite ordered spectral windows with geometric multiplicity

For the full interacting matching-family operator, earlier modules proved:
* bounded real spectral intervals contain only finitely many distinct values;
* each genuine real eigenvalue has finite positive geometric multiplicity;
* multiplicity tags (λ, k), with k < multiplicity(λ), cover exactly the real
  point spectrum.

This module proves the next ordering step: the multiplicity tags lying in
each bounded real interval form a FINITE set, hence can be represented by
a finite lexicographically sorted, duplicate-free list. It also gives such
a complete sorted list whenever the entire point spectrum is finite.

Lexicographic order puts distinct eigenvalues in increasing order and,
for equal eigenvalues, puts the distinct multiplicity indices in order.
The construction preserves the exact (λ, k) tags rather than arbitrarily
repeating eigenvalues. These local and finite-spectrum results do NOT
yet construct a global ℕ-indexed enumeration in an infinite Hilbert space.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev OrderedWindowEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- The finite eigenspace dimensions imply that a finite set of genuine
real eigenvalue parameters supports only finitely many multiplicity
tags. No symmetry is needed for this finite-fibre argument. -/
theorem infiniteLocalMatching_full_multiplicity_tags_finite_of_finite_eigenvalues
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : OrderedWindowEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hfinite :
      {λ : ℝ | infiniteLocalMatchingHasFullEigenvalue
        D V σ w P ε shift λ}.Finite) :
    (infiniteLocalMatchingFullMultiplicityTags
      D V σ w P ε shift a hgap hproper hsmall).Finite := by
  classical
  let m := infiniteLocalMatchingFullMultiplicity
    D V σ w P ε shift a hgap hproper hsmall
  let E : Set ℝ := {λ | infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift λ}
  have hfib (λ : ℝ) :
      ((fun k : ℕ => (λ, k)) '' (Set.Iio (m λ) : Set ℕ)).Finite :=
    (Set.finite_Iio (m λ)).image (fun k : ℕ => (λ, k))
  have hbig : (⋃ λ ∈ E,
      ((fun k : ℕ => (λ, k)) '' (Set.Iio (m λ) : Set ℕ))).Finite :=
    hfinite.biUnion (fun λ _ => hfib λ)
  apply hbig.subset
  rintro ⟨λ, k⟩ ⟨heigen, hk⟩
  apply Set.mem_iUnion.mpr
  refine ⟨λ, Set.mem_iUnion.mpr ⟨heigen, ?_⟩⟩
  exact ⟨k, hk, rfl⟩

/-- The real multiplicity-tagged spectrum restricted to a bounded
interval has finitely many entries, counting each spectral level once
per dimension of its eigenspace. -/
theorem infiniteLocalMatching_full_bounded_multiplicity_tags_finite
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : OrderedWindowEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (M : ℝ) (hM : 0 ≤ M) :
    {p : ℝ × ℕ |
      p ∈ infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall ∧
      ‖p.1‖ ≤ M}.Finite := by
  classical
  let m := infiniteLocalMatchingFullMultiplicity
    D V σ w P ε shift a hgap hproper hsmall
  let E : Set ℝ :=
    {λ | ‖λ‖ ≤ M ∧ infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift λ}
  have hvalues : E.Finite :=
    infiniteLocalMatching_full_eigenvalues_bounded_finite
      D V σ w P ε shift a hgap hproper hsmall hσ hP M hM
  have hfib (λ : ℝ) :
      ((fun k : ℕ => (λ, k)) '' (Set.Iio (m λ) : Set ℕ)).Finite :=
    (Set.finite_Iio (m λ)).image (fun k : ℕ => (λ, k))
  have hbig : (⋃ λ ∈ E,
      ((fun k : ℕ => (λ, k)) '' (Set.Iio (m λ) : Set ℕ))).Finite :=
    hvalues.biUnion (fun λ _ => hfib λ)
  apply hbig.subset
  rintro ⟨λ, k⟩ ⟨⟨heigen, hk⟩, hbound⟩
  apply Set.mem_iUnion.mpr
  refine ⟨λ, Set.mem_iUnion.mpr ⟨⟨hbound, heigen⟩, ?_⟩⟩
  exact ⟨k, hk, rfl⟩

/-- Any finite collection of multiplicity tags has an exact, finite
lexicographically ordered representation. A pair (λ, k) is included
once and only once; no duplicates can be inserted by sorting. -/
theorem spectralTags_exists_lex_sorted_list
    (S : Set (ℝ × ℕ)) (hfinite : S.Finite) :
    ∃ l : List (ℝ ×ₗ ℕ),
      l.Pairwise (· ≤ ·) ∧
      l.Nodup ∧
      (∀ p : ℝ ×ₗ ℕ, p ∈ l ↔ (ofLex p) ∈ S) := by
  classical
  let T : Set (ℝ ×ₗ ℕ) := toLex '' S
  have hT : T.Finite := hfinite.image toLex
  let l : List (ℝ ×ₗ ℕ) := hT.toFinset.sort (· ≤ ·)
  refine ⟨l, Finset.pairwise_sort _ _, Finset.sort_nodup _ _, ?_⟩
  intro p
  change p ∈ hT.toFinset.sort (· ≤ ·) ↔ (ofLex p) ∈ S
  rw [Finset.mem_sort, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨q, hq, heq⟩
    have h : ofLex p = q := by
      rw [← heq]
      rfl
    exact h ▸ hq
  · intro hp
    exact ⟨ofLex p, hp, by simp⟩

/-- At every finite radius, the genuine real point spectrum of the
full interacting operator admits a finite lexicographically ordered
multiplicity-tagged list. Its members are exactly the full-operator
eigenvalues inside the radius, each with precisely its admissible
indices k < geometric multiplicity. -/
theorem infiniteLocalMatching_full_bounded_tags_exists_lex_sorted_list
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : OrderedWindowEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ l : List (ℝ ×ₗ ℕ),
      l.Pairwise (· ≤ ·) ∧
      l.Nodup ∧
      (∀ p : ℝ ×ₗ ℕ, p ∈ l ↔
        (ofLex p) ∈ infiniteLocalMatchingFullMultiplicityTags
          D V σ w P ε shift a hgap hproper hsmall ∧
        ‖(ofLex p).1‖ ≤ M) := by
  exact spectralTags_exists_lex_sorted_list
    {p : ℝ × ℕ |
      p ∈ infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall ∧
      ‖p.1‖ ≤ M}
    (infiniteLocalMatching_full_bounded_multiplicity_tags_finite
      D V σ w P ε shift a hgap hproper hsmall hσ hP M hM)

/-- If the full real point spectrum is finite (as for a finite tiling
patch), the *entire* tagged point spectrum admits an exact ordered
finite list. No nonemptiness hypothesis is needed: an empty spectrum
is represented by the empty list. -/
theorem infiniteLocalMatching_full_finite_spectrum_exists_lex_sorted_list
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : OrderedWindowEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hfinite :
      {λ : ℝ | infiniteLocalMatchingHasFullEigenvalue
        D V σ w P ε shift λ}.Finite) :
    ∃ l : List (ℝ ×ₗ ℕ),
      l.Pairwise (· ≤ ·) ∧
      l.Nodup ∧
      (∀ p : ℝ ×ₗ ℕ, p ∈ l ↔
        (ofLex p) ∈ infiniteLocalMatchingFullMultiplicityTags
          D V σ w P ε shift a hgap hproper hsmall) := by
  exact spectralTags_exists_lex_sorted_list _
    (infiniteLocalMatching_full_multiplicity_tags_finite_of_finite_eigenvalues
      D V σ w P ε shift a hgap hproper hsmall hfinite)

end SpectralGeometry
