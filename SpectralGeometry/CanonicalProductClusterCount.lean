module

public import SpectralGeometry.OrderedSpectralWindow
public import SpectralGeometry.CanonicalProductZeroOrder

public section

/-!
# Exact zero counts in certified spectral windows

Distinct levels are counted with their analytic zero orders. Saturation of
the finite index window ensures that every copy of each repeated level is
included. The certificate treats both reflected intervals on the prescribed
line, and it proves boundary exclusion as well as the total multiplicity.
-/

namespace SpectralGeometry

open scoped BigOperators

noncomputable section

/-- The finite set of distinct levels represented by an index block. -/
@[expose] def spectralWindowLevels (q : ℕ → ℝ) (m n : ℕ) : Finset ℝ := by
  classical
  exact (Finset.Ico m n).image q

/-- A saturated finite index set contains every copy of each of its levels. -/
theorem levelMultiplicity_eq_filter_card (q : ℕ → ℝ) (S : Finset ℕ)
    (hclosed : ∀ i ∈ S, ∀ j, q j = q i → j ∈ S)
    (r : ℝ) (hr : r ∈ S.image q) :
    levelMultiplicity q r = (S.filter (fun i => q i = r)).card := by
  classical
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
  let e : {j : ℕ // q j = r} ≃ ↥(S.filter (fun j => q j = r)) :=
    { toFun := fun j => ⟨j.val, Finset.mem_filter.mpr
        ⟨hclosed i hi j.val (j.property.trans hir.symm), j.property⟩⟩
      invFun := fun j => ⟨j.val, (Finset.mem_filter.mp j.property).2⟩
      left_inv := fun j => rfl
      right_inv := fun j => rfl }
  exact (Nat.card_congr e).trans (by simp)

/-- Summing level multiplicities recovers the size of a saturated index set. -/
theorem sum_levelMultiplicity_eq_card (q : ℕ → ℝ) (S : Finset ℕ)
    (hclosed : ∀ i ∈ S, ∀ j, q j = q i → j ∈ S) :
    ∑ r ∈ S.image q, levelMultiplicity q r = S.card := by
  classical
  calc
    _ = ∑ r ∈ S.image q, (S.filter (fun i => q i = r)).card :=
      Finset.sum_congr rfl (fun r hr => levelMultiplicity_eq_filter_card q S hclosed r hr)
    _ = S.card := (Finset.card_eq_sum_card_image q S).symm

/-- At a positive signed level, the product vanishes precisely when that
level occurs. Positivity excludes a collision with the opposite branch. -/
theorem canonicalProduct_zero_at_signed_level_iff
    {q : ℕ → ℝ} {c d : ℂ} (h : Admissible q c d) (hd : d ≠ 0)
    (r : ℝ) (hr : 0 < r) (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    canonicalProduct q c d (c + d * ((sign * r : ℝ) : ℂ)) = 0 ↔
      ∃ i, q i = r := by
  rw [canonicalProduct_zero_iff h hd]
  apply exists_congr
  intro i
  exact (factor_zero_iff h.positive hd i _).symm.trans
    (factor_zero_at_signed_level_iff h.positive hd r hr i sign hsign)

/-- A finite saturated block counts analytic orders, including repeated
levels, rather than merely counting distinct zero locations. -/
theorem canonicalProduct_cluster_order_sum
    {q : ℕ → ℝ} {c d : ℂ} (h : Admissible q c d) (hd : d ≠ 0)
    (S : Finset ℕ) (hclosed : ∀ i ∈ S, ∀ j, q j = q i → j ∈ S)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    (∑ r ∈ S.image q, analyticOrderAt (canonicalProduct q c d)
      (c + d * ((sign * r : ℝ) : ℂ))) = (S.card : ℕ∞) := by
  classical
  have he : (∑ r ∈ S.image q, analyticOrderAt (canonicalProduct q c d)
      (c + d * ((sign * r : ℝ) : ℂ))) =
      ∑ r ∈ S.image q, (levelMultiplicity q r : ℕ∞) := by
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact canonicalProduct_order_at_signed_level h hd (q i) (h.positive i) sign hsign
  rw [he, ← Nat.cast_sum, sum_levelMultiplicity_eq_card q S hclosed]

/-- An exact finite zero certificate on each of the two reflected line
segments. The sum runs over distinct levels and uses full analytic orders.
The closed-segment zero characterization also excludes both endpoints. -/
structure CertifiedCanonicalWindow (q : ℕ → ℝ) (c d : ℂ)
    (a b : ℝ) (m n : ℕ) : Prop where
  indices : ∀ i, a < q i ∧ q i < b ↔ i ∈ Finset.Ico m n
  zeros : ∀ r ∈ Set.Icc a b, ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
    (canonicalProduct q c d (c + d * ((sign * r : ℝ) : ℂ)) = 0 ↔
      r ∈ spectralWindowLevels q m n)
  orders : ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
    (∑ r ∈ spectralWindowLevels q m n, analyticOrderAt (canonicalProduct q c d)
      (c + d * ((sign * r : ℝ) : ℂ))) = ((n - m : ℕ) : ℕ∞)

/-- Separated reference cuts and a level-error bound certify the complete
zero cluster of the approximating product. No uniform-product-convergence
assumption is used as a substitute for the required spectral error. -/
theorem canonicalProduct_certified_window (q μ : ℕ → ℝ) (hq : Monotone q)
    (c d : ℂ) (hμ : Admissible μ c d) (hd : d ≠ 0)
    (δ a b : ℝ) (ha : 0 < a) (m n : ℕ)
    (hcutA : OrderedGapCertificate q δ a m)
    (hcutB : OrderedGapCertificate q δ b n)
    (hclose : ∀ i, |μ i - q i| ≤ δ) :
    CertifiedCanonicalWindow μ c d a b m n := by
  classical
  have hi := orderedWindow_indices_iff q μ hq δ a b m n hcutA hcutB hclose
  have hna := orderedGapCertificate_ne q μ hq δ a m hcutA hclose
  have hnb := orderedGapCertificate_ne q μ hq δ b n hcutB hclose
  refine ⟨hi, ?_, ?_⟩
  · intro r hr sign hsign
    rw [canonicalProduct_zero_at_signed_level_iff hμ hd r (ha.trans_le hr.1) sign hsign]
    constructor
    · rintro ⟨i, hir⟩
      have hia : a < μ i := lt_of_le_of_ne (by simpa [hir] using hr.1) (hna i).symm
      have hib : μ i < b := lt_of_le_of_ne (by simpa [hir] using hr.2) (hnb i)
      exact Finset.mem_image.mpr ⟨i, (hi i).mp ⟨hia, hib⟩, hir⟩
    · intro hr'
      obtain ⟨i, _, hir⟩ := Finset.mem_image.mp hr'
      exact ⟨i, hir⟩
  · intro sign hsign
    have hc : ∀ i ∈ Finset.Ico m n, ∀ j, μ j = μ i → j ∈ Finset.Ico m n := by
      intro i him j he
      apply (hi j).mp
      rw [he]
      exact (hi i).mpr him
    simpa [spectralWindowLevels] using
      canonicalProduct_cluster_order_sum hμ hd (Finset.Ico m n) hc sign hsign

end
end SpectralGeometry
