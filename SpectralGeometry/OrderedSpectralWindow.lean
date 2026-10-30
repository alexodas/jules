module

public import Mathlib

public section

/-!
# Finite certificates for separated ordered spectral windows

Two neighboring reference levels certify a cut even when every level has
an error of at most `δ`. Two cuts isolate exactly a finite interval of
indices, including the empty interval. Repetitions inside the window are
allowed; only its boundary cuts need separation.
-/

namespace SpectralGeometry

noncomputable section

/-- A margin at a cut between indices `k - 1` and `k`. At `k = 0` only
the next level is needed. The inequalities concern reference data, not the
unknown perturbed levels or the desired zero count. -/
@[expose] def OrderedGapCertificate (q : ℕ → ℝ) (δ t : ℝ) (k : ℕ) : Prop :=
  (0 < k → q (k - 1) + δ < t) ∧ t + δ < q k

/-- A certified cut separates every perturbed level with the same index. -/
theorem orderedGapCertificate_separates (q μ : ℕ → ℝ) (hq : Monotone q)
    (δ t : ℝ) (k : ℕ) (hgap : OrderedGapCertificate q δ t k)
    (hclose : ∀ i, |μ i - q i| ≤ δ) (i : ℕ) :
    (μ i < t ↔ i < k) ∧ (t < μ i ↔ k ≤ i) := by
  have he := abs_le.mp (hclose i)
  by_cases hi : i < k
  · have hk : 0 < k := by omega
    have hq' := hq (show i ≤ k - 1 by omega)
    have ht : μ i < t := by linarith [hgap.1 hk]
    exact ⟨iff_of_true ht hi,
      iff_of_false (not_lt_of_ge ht.le) (by omega)⟩
  · have hk : k ≤ i := by omega
    have hq' := hq hk
    have ht : t < μ i := by linarith [hgap.2]
    exact ⟨iff_of_false (not_lt_of_ge ht.le) hi, iff_of_true ht hk⟩

/-- No perturbed level can lie on a certified boundary. -/
theorem orderedGapCertificate_ne (q μ : ℕ → ℝ) (hq : Monotone q)
    (δ t : ℝ) (k : ℕ) (hgap : OrderedGapCertificate q δ t k)
    (hclose : ∀ i, |μ i - q i| ≤ δ) (i : ℕ) : μ i ≠ t := by
  have hs := orderedGapCertificate_separates q μ hq δ t k hgap hclose i
  by_cases hi : i < k
  · exact ne_of_lt (hs.1.mpr hi)
  · exact ne_of_gt (hs.2.mpr (by omega))

/-- Two finite cut certificates determine the full set of indices in an
open energy window. No simple-level assumption occurs. -/
theorem orderedWindow_indices_iff (q μ : ℕ → ℝ) (hq : Monotone q)
    (δ a b : ℝ) (m n : ℕ)
    (ha : OrderedGapCertificate q δ a m) (hb : OrderedGapCertificate q δ b n)
    (hclose : ∀ i, |μ i - q i| ≤ δ) (i : ℕ) :
    a < μ i ∧ μ i < b ↔ i ∈ Finset.Ico m n := by
  have hlo := (orderedGapCertificate_separates q μ hq δ a m ha hclose i).2
  have hhi := (orderedGapCertificate_separates q μ hq δ b n hb hclose i).1
  rw [hlo, hhi, Finset.mem_Ico]

/-- The number of indices, hence the count with repetitions, is `n - m`.
The index set is proved finite, so `Nat.card` is not masking infinity. -/
theorem orderedWindow_finite_card (q μ : ℕ → ℝ) (hq : Monotone q)
    (δ a b : ℝ) (m n : ℕ)
    (ha : OrderedGapCertificate q δ a m) (hb : OrderedGapCertificate q δ b n)
    (hclose : ∀ i, |μ i - q i| ≤ δ) :
    {i : ℕ | a < μ i ∧ μ i < b}.Finite ∧
      Nat.card {i : ℕ // a < μ i ∧ μ i < b} = n - m := by
  have he : {i : ℕ | a < μ i ∧ μ i < b} = (Finset.Ico m n : Set ℕ) :=
    Set.ext (orderedWindow_indices_iff q μ hq δ a b m n ha hb hclose)
  constructor
  · rw [he]
    exact Finset.finite_toSet _
  · change Nat.card ↥{i : ℕ | a < μ i ∧ μ i < b} = _
    rw [he]
    simp

end
end SpectralGeometry
