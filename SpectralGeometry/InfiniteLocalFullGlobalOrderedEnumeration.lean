import SpectralGeometry.InfiniteLocalFullOrderedMultiplicityWindows
import Mathlib.Order.OrderIsoNat

/-!
# Globally ordered infinite real eigenvalue enumeration with geometric multiplicities

The abstract order-theoretic construction enumerates any infinite linear
order in which every element has only finitely many strict predecessors.
It assigns each element the number of its predecessors and pulls back
the increasing enumeration of the resulting infinite subset of ℕ.

For the full interacting matching-family operator, bounded real spectral
windows have finite multiplicity-tagged spectra (§4.36). When the genuine
real spectrum has a lower bound and infinitely many tags, the
lexicographically ordered tag set has finite strict initial segments.
We therefore enumerate all tags exactly once by ℕ, in increasing order.
Projecting to the real coordinate produces a nondecreasing sequence
whose level λ occurs in precisely the geometric multiplicity m(λ) slots.

These results assume infinitude and lower boundedness. Neither property
is a consequence of compact resolvent alone for an arbitrary real
self-adjoint operator. The divergence λₙ → +∞ and quantitative growth
bounds are addressed separately in the research roadmap.
-/

namespace SpectralGeometry

/-- A linear order with finite strict initial segments, when infinite,
admits a unique-in-range increasing enumeration by natural numbers.
The construction assigns each element the cardinality of its set of
strict predecessors, then inverts this rank via the ordered enumeration
of its image in ℕ. -/
theorem exists_strictMono_surjective_of_finite_predecessors
    {α : Type*} [LinearOrder α] [Infinite α]
    (hpred : ∀ x : α, {y : α | y < x}.Finite) :
    ∃ e : ℕ → α, StrictMono e ∧ Function.Surjective e := by
  classical
  let rank : α → ℕ := fun x => (hpred x).toFinset.card
  have hrank : StrictMono rank := by
    intro x y hxy
    change (hpred x).toFinset.card < (hpred y).toFinset.card
    apply Finset.card_lt_card
    apply (Set.Finite.toFinset_ssubset_toFinset).mpr
    apply (ssubset_iff_subset_ne).mpr
    constructor
    · intro z hz
      exact lt_trans hz hxy
    · intro heq
      have hx : x ∈ {z : α | z < y} := hxy
      rw [← heq] at hx
      exact (lt_irrefl x) hx
  let R : Set ℕ := Set.range rank
  have hinf : R.Infinite := Set.infinite_range_of_injective hrank.injective
  letI : Infinite R := hinf.to_subtype
  let nth : ℕ ≃o R := Nat.Subtype.orderIsoOfNat R
  let recover (r : R) : α := Classical.choose r.property
  have hrecover (r : R) : rank (recover r) = r.1 := Classical.choose_spec r.property
  let e : ℕ → α := fun n => recover (nth n)
  have he (n : ℕ) : rank (e n) = (nth n).1 := hrecover (nth n)
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    have hlt : rank (e i) < rank (e j) := by
      rw [he i, he j]
      exact nth.strictMono hij
    by_contra hnot
    have hle : e j ≤ e i := le_of_not_gt hnot
    exact (not_le_of_gt hlt) (hrank.monotone hle)
  · intro x
    obtain ⟨n, hn⟩ := nth.surjective (⟨rank x, ⟨x, rfl⟩⟩ : R)
    refine ⟨n, ?_⟩
    apply hrank.injective
    rw [he n, hn]

variable {Tile : Type*} [DecidableEq Tile]

private abbrev GlobalOrderedEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- If every genuine real eigenvalue is ≥ the specified real bound,
then each multiplicity tag has only finitely many lexicographically
preceding tags. This depends essentially on finite spectral windows,
including their finite multiplicity fibres. -/
theorem infiniteLocalMatching_full_tags_finite_lex_predecessors
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : GlobalOrderedEnd Tile)
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
    (p : {p : ℝ ×ₗ ℕ |
      (ofLex p) ∈ infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall}) :
    {q : {p : ℝ ×ₗ ℕ |
      (ofLex p) ∈ infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall} | q < p}.Finite := by
  classical
  let tags := infiniteLocalMatchingFullMultiplicityTags
    D V σ w P ε shift a hgap hproper hsmall
  let M : ℝ := |lower| + |(ofLex p.1).1|
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hfinite :
      {raw : ℝ × ℕ | raw ∈ tags ∧ ‖raw.1‖ ≤ M}.Finite :=
    infiniteLocalMatching_full_bounded_multiplicity_tags_finite
      D V σ w P ε shift a hgap hproper hsmall hσ hP M hM
  have hmaps :
      Set.MapsTo
        (fun q : {p : ℝ ×ₗ ℕ | (ofLex p) ∈ tags} => ofLex q.1)
        {q : {p : ℝ ×ₗ ℕ | (ofLex p) ∈ tags} | q < p}
        {raw : ℝ × ℕ | raw ∈ tags ∧ ‖raw.1‖ ≤ M} := by
    intro q hqp
    have htag : ofLex q.1 ∈ tags := q.property
    have hlo : lower ≤ (ofLex q.1).1 := hbelow _ htag.1
    have hhi : (ofLex q.1).1 ≤ (ofLex p.1).1 :=
      Prod.Lex.monotone_fst q.1 p.1 hqp.le
    have hlo' : -|lower| ≤ lower := neg_abs_le lower
    have hhi' : (ofLex p.1).1 ≤ |(ofLex p.1).1| := le_abs_self _
    have hbound : |(ofLex q.1).1| ≤ M :=
      abs_le.mpr ⟨by dsimp [M]; linarith, by dsimp [M]; linarith⟩
    exact ⟨htag, by simpa only [Real.norm_eq_abs] using hbound⟩
  have hinj :
      Set.InjOn
        (fun q : {p : ℝ ×ₗ ℕ | (ofLex p) ∈ tags} => ofLex q.1)
        {q : {p : ℝ ×ₗ ℕ | (ofLex p) ∈ tags} | q < p} := by
    intro x _ y _ h
    apply Subtype.ext
    have hh := congrArg ofLex h
    simpa using hh
  exact Set.Finite.of_injOn hmaps hinj hfinite

/-- An infinite lower-bounded interacting real point spectrum has
a single globally increasing, duplicate-free ℕ-indexed listing of
all multiplicity tags (λ, k). This is an exact enumeration, rather
than an arbitrary possibly repeating surjection from ℕ. -/
theorem infiniteLocalMatching_full_infinite_tags_exists_strictMono_enumeration
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : GlobalOrderedEnd Tile)
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
          D V σ w P ε shift a hgap hproper hsmall) := by
  classical
  let tags := infiniteLocalMatchingFullMultiplicityTags
    D V σ w P ε shift a hgap hproper hsmall
  let T : Set (ℝ ×ₗ ℕ) := toLex '' tags
  have hT : T.Infinite := by
    apply hinfinite.image
    intro x _ y _ hxy
    have hh := congrArg ofLex hxy
    simpa using hh
  letI : Infinite T := hT.to_subtype
  have hpred : ∀ p : T, {q : T | q < p}.Finite := by
    intro p
    exact infiniteLocalMatching_full_tags_finite_lex_predecessors
      D V σ w P ε shift a hgap hproper hsmall hσ hP lower hbelow p
  obtain ⟨e, hmono, hsurj⟩ :=
    exists_strictMono_surjective_of_finite_predecessors hpred
  refine ⟨fun n => (e n).1, ?_, ?_⟩
  · exact Subtype.strictMono_coe.comp hmono
  · ext p
    constructor
    · rintro ⟨n, rfl⟩
      exact (e n).property
    · intro hp
      obtain ⟨n, hn⟩ := hsurj ⟨p, hp⟩
      exact ⟨n, congrArg Subtype.val hn⟩


/-- Projecting the globally ordered tag enumeration to the real coordinate
gives a nondecreasing sequence of full-operator eigenvalues. Every
admissible pair (eigenvalue, copy index) occurs at exactly one position,
so the sequence repeats a given level exactly its geometric
multiplicity many times, with no spurious copies. -/
theorem infiniteLocalMatching_full_infinite_exists_ordered_sequence_exact_multiplicities
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : GlobalOrderedEnd Tile)
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
      Monotone (fun n : ℕ => (ofLex (seq n)).1) ∧
      (∀ eigenvalue : ℝ, ∀ k : ℕ,
        (∃! n : ℕ, seq n = toLex (eigenvalue, k)) ↔
          infiniteLocalMatchingHasFullEigenvalue
            D V σ w P ε shift eigenvalue ∧
          k < infiniteLocalMatchingFullMultiplicity
            D V σ w P ε shift a hgap hproper hsmall eigenvalue) := by
  obtain ⟨seq, hmono, hrange⟩ :=
    infiniteLocalMatching_full_infinite_tags_exists_strictMono_enumeration
      D V σ w P ε shift a hgap hproper hsmall hσ hP
      lower hbelow hinfinite
  refine ⟨seq, hmono, ?_, ?_⟩
  · intro i j hij
    exact Prod.Lex.monotone_fst _ _ (hmono.monotone hij)
  · intro eigenvalue k
    constructor
    · rintro ⟨n, hn, _⟩
      have htag : toLex (eigenvalue, k) ∈
          toLex '' (infiniteLocalMatchingFullMultiplicityTags
            D V σ w P ε shift a hgap hproper hsmall) := by
        rw [← hrange]
        exact ⟨n, hn⟩
      obtain ⟨q, hq, hqeq⟩ := htag
      have heq : q = (eigenvalue, k) := by
        have hh := congrArg ofLex hqeq
        simpa using hh
      subst q
      exact hq
    · intro htag
      have hmem : toLex (eigenvalue, k) ∈ Set.range seq := by
        rw [hrange]
        exact ⟨(eigenvalue, k), htag, rfl⟩
      obtain ⟨n, hn⟩ := hmem
      refine ⟨n, hn, ?_⟩
      intro j hj
      exact hmono.injective (hj.trans hn.symm)

end SpectralGeometry
