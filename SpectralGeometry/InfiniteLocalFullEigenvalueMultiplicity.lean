module

public import SpectralGeometry.InfiniteLocalFullRealResolvent
public import Mathlib.Data.Set.Countable

public section

/-!
# Countable spectral enumeration with eigenspace multiplicity tags

The earlier enumeration lists distinct genuine real eigenvalues of the
unbounded local operator without controlling repetitions. Here we attach
the finite dimension of each full eigenspace to its eigenvalue and enumerate
the corresponding pairs (eigenvalue, copy index).

The tagged spectrum is countable under the existing compact-resolvent
and self-adjointness hypotheses. This is an unordered enumeration; it
does not claim a monotone listing, a complex-spectrum statement, or
any quantitative eigenvalue-growth estimate.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

abbrev MultiplicityEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- The geometric multiplicity of a real full-operator eigenvalue is the
finite dimension of its genuine eigenspace (identified with the compact
resolvent eigenspace). The regular resolvent shift has multiplicity zero.
This definition uses the compactness hypotheses to justify finrank. -/
@[expose] noncomputable def infiniteLocalMatchingFullMultiplicity
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : MultiplicityEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) : ℕ := by
  classical
  by_cases hne : eigenvalue ≠ a
  · letI := infiniteLocalMatchingFullEigenspace_finiteDimensional
      D V σ w P ε shift a hgap hproper hsmall eigenvalue hne
    exact Module.finrank ℝ
      (infiniteLocalMatchingFullEigenspace
        D V σ w P ε shift a hgap hsmall eigenvalue hne)
  · exact 0

/-- The known resolvent shift is assigned zero eigenvalue multiplicity. -/
theorem infiniteLocalMatchingFullMultiplicity_at_shift
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : MultiplicityEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    infiniteLocalMatchingFullMultiplicity
      D V σ w P ε shift a hgap hproper hsmall a = 0 := by
  simp [infiniteLocalMatchingFullMultiplicity]

/-- A multiplicity tag is a real eigenvalue together with a natural
number strictly smaller than its finite eigenspace dimension. -/
@[expose] def infiniteLocalMatchingFullMultiplicityTags
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : MultiplicityEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1) : Set (ℝ × ℕ) :=
  {p | infiniteLocalMatchingHasFullEigenvalue
      D V σ w P ε shift p.1 ∧
    p.2 < infiniteLocalMatchingFullMultiplicity
      D V σ w P ε shift a hgap hproper hsmall p.1}

/-- The full real point spectrum, with a separate tag for every dimension
of an eigenspace, is countable. Thus multiplicities can be encoded
without accidentally using an arbitrary number of repetitions. -/
theorem infiniteLocalMatching_full_multiplicity_tags_countable
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : MultiplicityEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ) :
    (infiniteLocalMatchingFullMultiplicityTags
      D V σ w P ε shift a hgap hproper hsmall).Countable := by
  have hvalues :
      {eigenvalue : ℝ |
        infiniteLocalMatchingHasFullEigenvalue
          D V σ w P ε shift eigenvalue}.Countable :=
    infiniteLocalMatching_full_eigenvalues_countable
      D V σ w P ε shift a hgap hproper hsmall hσ hP
  have hproduct :
      ({eigenvalue : ℝ |
        infiniteLocalMatchingHasFullEigenvalue
          D V σ w P ε shift eigenvalue} ×ˢ
        (Set.univ : Set ℕ)).Countable :=
    hvalues.prod Set.countable_univ
  apply hproduct.mono
  rintro ⟨eigenvalue, k⟩ ⟨heigenvalue, _⟩
  exact ⟨heigenvalue, Set.mem_univ k⟩

/-- If at least one multiplicity tag exists, a natural-number sequence
enumerates exactly the tagged full real point spectrum. Unlike the old
untagged listing, a pair (eigenvalue, k) occurs in the range if and only if
k is below the eigenspace dimension; the sequence is not yet ordered. -/
theorem infiniteLocalMatching_full_multiplicity_tags_exists_enumeration
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : MultiplicityEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (hexists : (infiniteLocalMatchingFullMultiplicityTags
      D V σ w P ε shift a hgap hproper hsmall).Nonempty) :
    ∃ seq : ℕ → ℝ × ℕ,
      Set.range seq = infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall := by
  obtain ⟨seq, hseq⟩ :=
    (infiniteLocalMatching_full_multiplicity_tags_countable
      D V σ w P ε shift a hgap hproper hsmall hσ hP).exists_eq_range hexists
  exact ⟨seq, hseq.symm⟩

end SpectralGeometry
