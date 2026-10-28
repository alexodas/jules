module

public import SpectralGeometry.InfiniteLocalFullEigenvalueIsolation
public import Mathlib.Data.Set.Countable

public section

/-!
# Countable enumeration of the real point spectrum of the full local operator

Local finiteness on every bounded interval implies that the set of genuine
real eigenvalues is countable. If the point spectrum is nonempty, it admits
a sequence listing every real eigenvalue; the sequence need not be injective
or increasing, and it does not record eigenspace multiplicities.

These theorems concern the actual natural-domain eigenvalues of the
unbounded matching operator, not the as-yet-unformalized full spectrum of
its `LinearPMap` realization.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

abbrev EnumerationEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- Under the compact self-adjoint resolvent assumptions, the set of
genuine real eigenvalues of the full unbounded matching operator is
countable. This remains valid for finite or empty tile sets. -/
theorem infiniteLocalMatching_full_eigenvalues_countable
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : EnumerationEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ) :
    {eigenvalue : ℝ |
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue}.Countable := by
  let S : Set ℝ :=
    {eigenvalue : ℝ |
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue}
  let F : ℕ → Set ℝ := fun n =>
    {eigenvalue : ℝ |
      ‖eigenvalue‖ ≤ (n : ℝ) ∧
        infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue}
  have hfinite (n : ℕ) : (F n).Finite := by
    exact infiniteLocalMatching_full_eigenvalues_bounded_finite
      D V σ w P ε shift a hgap hproper hsmall hσ hP
      (n : ℝ) (Nat.cast_nonneg n)
  have hcount : (⋃ n : ℕ, F n).Countable :=
    Set.countable_iUnion (fun n => (hfinite n).countable)
  apply hcount.mono
  intro eigenvalue heigen
  obtain ⟨n, hn⟩ := exists_nat_gt ‖eigenvalue‖
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_⟩
  exact ⟨le_of_lt hn, heigen⟩

/-- If there is at least one real full-operator eigenvalue, there is a
sequence listing *all* such eigenvalues and containing no other values.
The list may repeat eigenvalues. Multiplicity-aware ordered enumeration
is established separately in InfiniteLocalFullGlobalOrderedEnumeration,
under its additional hypotheses. -/
theorem infiniteLocalMatching_full_eigenvalues_exists_enumeration
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : EnumerationEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (hexists : ∃ eigenvalue : ℝ,
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue) :
    ∃ seq : ℕ → ℝ,
      (∀ n, infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift (seq n)) ∧
      (∀ eigenvalue : ℝ,
        infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue →
        ∃ n, seq n = eigenvalue) := by
  let S : Set ℝ :=
    {eigenvalue : ℝ |
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue}
  have hcount : S.Countable :=
    infiniteLocalMatching_full_eigenvalues_countable
      D V σ w P ε shift a hgap hproper hsmall hσ hP
  obtain ⟨seq, hseq⟩ := hcount.exists_eq_range hexists
  refine ⟨seq, ?_, ?_⟩
  · intro n
    have hmem : seq n ∈ S := by
      rw [hseq]
      exact Set.mem_range_self n
    exact hmem
  · intro eigenvalue hmem
    have h : eigenvalue ∈ S := hmem
    rw [hseq] at h
    exact h

end SpectralGeometry
