module

public import SpectralGeometry.AmmannBeenkerSummability
public import SpectralGeometry.PositiveFiniteSectorZeroResponse

public section

/-!
# Exact full spectral products and nine-level zero response

All geometric, positivity, enumeration and summability inputs are derived
for the concrete octagonal model. The products have the exact geometric
zero multiplicities of their respective full operators on the natural
domain. The affine center and nonzero direction are fixed throughout the
finite-sector intervention; no simple-eigenvalue assumption is used.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- An explicit infinite geometric operator yields entire full spectral
products and quantitative response for nine indexed zeros on each reflected
branch. This includes the complete spectral conclusion and derives all
summability hypotheses rather than assuming an admissible sequence. -/
theorem exists_nine_level_fullProducts (c d : ℂ) (hd : d ≠ 0) :
    ∃ ev : ℕ → ℝ, Monotone ev ∧
      Nonempty (DomainEigenbasis (infiniteOnsiteDomain potential)
        (onsitePlusBounded potential interaction) ev) ∧
      (∀ n : ℕ, 1 ≤ ev n) ∧
      (∀ n : ℕ, n < 9 → ev n ≤ 3) ∧
      Summable (fun n => 1 / (ev n) ^ 2) ∧
      HasExactFullSpectralProduct potential interaction potential_proper ev c d ∧
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ 4 →
        ∃ μ : ℕ → ℝ, Monotone μ ∧
          Nonempty (DomainEigenbasis (infiniteOnsiteDomain potential)
            (onsitePlusBounded potential (interaction + τ • finiteSectorProjection sector)) μ) ∧
          (∀ n : ℕ, 1 ≤ μ n) ∧
          Summable (fun n => 1 / (μ n) ^ 2) ∧
          HasExactFullSpectralProduct potential (interaction + τ • finiteSectorProjection sector)
            potential_proper μ c d ∧
          ∀ n : ℕ, n < 9 →
            (τ / 2 ≤ μ n - ev n ∧ μ n - ev n ≤ τ) ∧
            (canonicalProduct ev c d (positiveSpectralPoint ev c d n) = 0 ∧
              canonicalProduct ev c d (negativeSpectralPoint ev c d n) = 0) ∧
            (canonicalProduct μ c d (positiveSpectralPoint μ c d n) = 0 ∧
              canonicalProduct μ c d (negativeSpectralPoint μ c d n) = 0) ∧
            (positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n =
                d * ((μ n - ev n : ℝ) : ℂ) ∧
              negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n =
                -d * ((μ n - ev n : ℝ) : ℂ)) ∧
            ((‖d‖ * (τ / 2) ≤
                ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ ∧
              ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ ≤ ‖d‖ * τ) ∧
             (‖d‖ * (τ / 2) ≤
                ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ ∧
              ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ ≤ ‖d‖ * τ)) ∧
            (0 < τ →
              positiveSpectralPoint μ c d n ≠ positiveSpectralPoint ev c d n ∧
              negativeSpectralPoint μ c d n ≠ negativeSpectralPoint ev c d n) := by
  obtain ⟨ev, hev, ⟨b⟩, hgap, hwindow, hfamily⟩ := exists_nine_level_response
  have hp (n : ℕ) : 0 < ev n := lt_of_lt_of_le (by norm_num) (hgap n)
  have hs := (onsitePlusNonneg_ordered_positive_summable potential interaction
    interaction_symmetric interaction_nonneg 1 (by norm_num) potential_lower potential_proper
    potential_invSq_summable ev hev b).2.2
  have hprod := onsitePlusBounded_hasExactFullSpectralProduct potential 1 potential_lower
    potential_proper interaction interaction_symmetric ev hev b hp hs c d hd
  have ha : Admissible ev c d := admissible_of_inv_sq_summable hp hs c d
  refine ⟨ev, hev, ⟨b⟩, hgap, hwindow, hs, hprod, ?_⟩
  intro τ ht ht4
  obtain ⟨μ, hμ, ⟨bt⟩, hgapμ, hr⟩ := hfamily τ ht ht4
  have hpμ (n : ℕ) : 0 < μ n := lt_of_lt_of_le (by norm_num) (hgapμ n)
  have hsμ := (finiteSector_preserves_gap_summability potential interaction
    interaction_symmetric sector τ ht ev μ hev hμ b bt 1 (by norm_num) hgap hs).2.2
  have hsym := finiteSectorCorrection_symmetric interaction interaction_symmetric sector τ
  have hprodμ := onsitePlusBounded_hasExactFullSpectralProduct potential 1 potential_lower
    potential_proper _ hsym μ hμ bt hpμ hsμ c d hd
  have haμ : Admissible μ c d := admissible_of_inv_sq_summable hpμ hsμ c d
  refine ⟨μ, hμ, ⟨bt⟩, hgapμ, hsμ, hprodμ, ?_⟩
  intro n hn
  have hlo : (1 / 2 : ℝ) * τ ≤ μ n - ev n := by linarith [(hr n hn).1]
  have bounds := indexedSpectralPoints_norm_bounds ev μ c d (1 / 2) τ
    (by norm_num) ht n hlo (hr n hn).2
  refine ⟨hr n hn, indexedSpectralPoints_product_zeros ev c d ha hd n,
    indexedSpectralPoints_product_zeros μ c d haμ hd n,
    ⟨positiveSpectralPoint_sub ev μ c d n, negativeSpectralPoint_sub ev μ c d n⟩,
    ?_, ?_⟩
  · simpa [div_eq_mul_inv, mul_comm] using bounds
  · intro hτ
    exact indexedSpectralPoints_ne ev μ c d hd (1 / 2) τ (by norm_num) hτ n hlo

end
end SpectralGeometry.AmmannBeenker
