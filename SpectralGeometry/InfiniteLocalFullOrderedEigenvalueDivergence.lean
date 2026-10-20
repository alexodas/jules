module

public import SpectralGeometry.InfiniteLocalFullGlobalOrderedEnumeration
public import Mathlib.Order.Filter.Cofinite

public section

/-!
# Divergence to positive infinity of the globally ordered real spectrum

Under the explicit hypotheses used for the infinite ordered full-operator
multiplicity-tag enumeration in §4.37, each bounded real interval contains
only finitely many *tags* (not merely finitely many distinct eigenvalues).
Because the ordered tagged enumeration is injective, only finitely many
indices can have first coordinate below any fixed real threshold. On ℕ,
the cofinite and atTop filters coincide, so the first coordinates tend to
+∞.

This is an asymptotic divergence theorem for an existing, complete,
multiplicity-aware enumeration of the full interacting operator's real
point spectrum. It does not prove lower bounds of the form
λₙ ≥ c n^α, nor inverse-square summability, nor that every geometric
model satisfies the explicit lower-boundedness/infinitude hypotheses.
-/

namespace SpectralGeometry

open Filter

/-- A real sequence for which every strict lower level set of indices
is finite must tend to positive infinity. No monotonicity is required. -/
theorem real_tendsto_atTop_of_finite_sublevel_indices
    (f : ℕ → ℝ)
    (hfinite : ∀ B : ℝ, {n : ℕ | f n < B}.Finite) :
    Tendsto f atTop atTop := by
  rw [← Nat.cofinite_eq_atTop]
  apply tendsto_atTop.mpr
  intro B
  exact eventually_cofinite.mpr (by simpa only [not_le] using hfinite B)

variable {Tile : Type*} [DecidableEq Tile]

abbrev DivergenceEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- For any *injective* global tagged enumeration of the full real
spectrum, the set of indices whose eigenvalues lie below a fixed bound
is finite, provided the real spectrum has the stated global lower bound.
This is the key finite-multiplicity strengthening of local spectral
finiteness. -/
theorem infiniteLocalMatching_full_ordered_tags_sublevel_indices_finite
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : DivergenceEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (lower : ℝ)
    (hbelow : ∀ eigenvalue : ℝ,
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue →
      lower ≤ eigenvalue)
    (seq : ℕ → ℝ ×ₗ ℕ) (hinj : Function.Injective seq)
    (hrange : Set.range seq =
      toLex '' (infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall))
    (B : ℝ) :
    {n : ℕ | (ofLex (seq n)).1 < B}.Finite := by
  classical
  let tags := infiniteLocalMatchingFullMultiplicityTags
    D V σ w P ε shift a hgap hproper hsmall
  let M : ℝ := |lower| + |B|
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hwindow :
      {p : ℝ × ℕ | p ∈ tags ∧ ‖p.1‖ ≤ M}.Finite :=
    infiniteLocalMatching_full_bounded_multiplicity_tags_finite
      D V σ w P ε shift a hgap hproper hsmall hσ hP M hM
  have hmaps :
      Set.MapsTo (fun n : ℕ => ofLex (seq n))
        {n : ℕ | (ofLex (seq n)).1 < B}
        {p : ℝ × ℕ | p ∈ tags ∧ ‖p.1‖ ≤ M} := by
    intro n hn
    have htag : ofLex (seq n) ∈ tags := by
      have hr : seq n ∈ Set.range seq := Set.mem_range_self n
      rw [hrange] at hr
      obtain ⟨p, hp, heq⟩ := hr
      have hval : p = ofLex (seq n) := by
        have hh := congrArg ofLex heq
        simpa using hh
      rw [← hval]
      exact hp
    have hlo : lower ≤ (ofLex (seq n)).1 := hbelow _ htag.1
    have hlo' : -|lower| ≤ lower := neg_abs_le lower
    have hhi : (ofLex (seq n)).1 ≤ |B| :=
      (le_of_lt hn).trans (le_abs_self B)
    have hleft : -M ≤ (ofLex (seq n)).1 := by
      calc
        -M ≤ -|lower| := by dsimp [M]; linarith [abs_nonneg B]
        _ ≤ lower := hlo'
        _ ≤ (ofLex (seq n)).1 := hlo
    have hright : (ofLex (seq n)).1 ≤ M := by
      calc
        (ofLex (seq n)).1 ≤ |B| := hhi
        _ ≤ M := by dsimp [M]; linarith [abs_nonneg lower]
    exact ⟨htag, by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨hleft, hright⟩⟩
  have hinjOn :
      Set.InjOn (fun n : ℕ => ofLex (seq n))
        {n : ℕ | (ofLex (seq n)).1 < B} := by
    intro i _ j _ heq
    apply hinj
    change seq i = seq j at heq
    exact heq
  exact Set.Finite.of_injOn hmaps hinjOn hwindow

/-- Every strictly increasing, surjective, globally ordered enumeration
of the infinite multiplicity-tagged real spectrum, under its stated
compactness, symmetry and lower-bound assumptions, has eigenvalues
tending to +∞. -/
theorem infiniteLocalMatching_full_global_ordered_eigenvalues_tendsto_atTop
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : DivergenceEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (lower : ℝ)
    (hbelow : ∀ eigenvalue : ℝ,
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue →
      lower ≤ eigenvalue)
    (seq : ℕ → ℝ ×ₗ ℕ) (hmono : StrictMono seq)
    (hrange : Set.range seq =
      toLex '' (infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall)) :
    Tendsto (fun n : ℕ => (ofLex (seq n)).1) atTop atTop := by
  apply real_tendsto_atTop_of_finite_sublevel_indices
  intro B
  exact infiniteLocalMatching_full_ordered_tags_sublevel_indices_finite
    D V σ w P ε shift a hgap hproper hsmall hσ hP
    lower hbelow seq hmono.injective hrange B

/-- In the infinite lower-bounded case, there exists a single sequence
of full-operator multiplicity tags which is strictly increasing in the
lexicographic order, covers every tag exactly once, and whose real
eigenvalue coordinates tend to positive infinity. -/
theorem infiniteLocalMatching_full_infinite_tags_exists_enumeration_tendsto_atTop
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : DivergenceEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (lower : ℝ)
    (hbelow : ∀ eigenvalue : ℝ,
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue →
      lower ≤ eigenvalue)
    (hinfinite : (infiniteLocalMatchingFullMultiplicityTags
      D V σ w P ε shift a hgap hproper hsmall).Infinite) :
    ∃ seq : ℕ → ℝ ×ₗ ℕ,
      StrictMono seq ∧
      Set.range seq =
        toLex '' (infiniteLocalMatchingFullMultiplicityTags
          D V σ w P ε shift a hgap hproper hsmall) ∧
      Tendsto (fun n : ℕ => (ofLex (seq n)).1) atTop atTop := by
  obtain ⟨seq, hmono, hrange⟩ :=
    infiniteLocalMatching_full_infinite_tags_exists_strictMono_enumeration
      D V σ w P ε shift a hgap hproper hsmall hσ hP
      lower hbelow hinfinite
  refine ⟨seq, hmono, hrange, ?_⟩
  exact infiniteLocalMatching_full_global_ordered_eigenvalues_tendsto_atTop
    D V σ w P ε shift a hgap hproper hsmall hσ hP
    lower hbelow seq hmono hrange

end SpectralGeometry
