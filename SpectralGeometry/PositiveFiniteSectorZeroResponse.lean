module

public import SpectralGeometry.InfinitePositiveSpectralControl
public import SpectralGeometry.FiniteSectorZeroResponse

public section

/-!
# Exact spectral products and sharpened zero response for positive interactions

This application constructs ordered full spectra, their positive gaps and
inverse-square summability, and the exact operator-specific zero divisors.
Only a positive onsite lower bound is needed: a large nonnegative interaction
does not consume the gap. Properness supplies the sorted onsite enumeration.
The geometric model, its summability and a nonempty low-energy window remain
separate application obligations.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

/-- Positive bounded interactions give exact full spectral products and
the sharper indexed zero response without an interaction-norm gap or a
supplied onsite ordering. Each product records its own operator's geometric
multiplicities; repeated levels and crossings are permitted. -/
theorem finiteSector_nonneg_fullProducts_indexedZeroResponse [Infinite Tile]
    (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (B x))
    (v₀ R E : ℝ) (hv₀ : 0 < v₀) (hV : ∀ t, v₀ ≤ V t)
    (hR : v₀ < R) (hE : E < R)
    (hproper : ∀ r : ℝ, (infiniteOnsiteLowEnergyTiles V r).Finite)
    (honsite : Summable (fun t => 1 / (V t) ^ 2))
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t)
    (c d : ℂ) (hd : d ≠ 0) :
    ∃ ev : ℕ → ℝ, Monotone ev ∧
      HasExactFullSpectralProduct V B hproper ev c d ∧
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ R - v₀ →
        ∃ μ : ℕ → ℝ, Monotone μ ∧
          HasExactFullSpectralProduct V (B + τ • finiteSectorProjection F)
            hproper μ c d ∧
          ∀ n : ℕ, ev n ≤ E →
            (canonicalProduct ev c d (positiveSpectralPoint ev c d n) = 0 ∧
              canonicalProduct ev c d (negativeSpectralPoint ev c d n) = 0) ∧
            (canonicalProduct μ c d (positiveSpectralPoint μ c d n) = 0 ∧
              canonicalProduct μ c d (negativeSpectralPoint μ c d n) = 0) ∧
            (positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n =
                d * ((μ n - ev n : ℝ) : ℂ) ∧
              negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n =
                -d * ((μ n - ev n : ℝ) : ℂ)) ∧
            ((‖d‖ * (sectorResponseKappa R v₀ E 0 * τ) ≤
                ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ ∧
              ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ ≤
                ‖d‖ * τ) ∧
             (‖d‖ * (sectorResponseKappa R v₀ E 0 * τ) ≤
                ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ ∧
              ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ ≤
                ‖d‖ * τ)) ∧
            (0 < τ →
              positiveSpectralPoint μ c d n ≠ positiveSpectralPoint ev c d n ∧
              negativeSpectralPoint μ c d n ≠ negativeSpectralPoint ev c d n) := by
  classical
  have hκ : 0 < sectorResponseKappa R v₀ E 0 := by
    unfold sectorResponseKappa
    exact div_pos (by linarith) (sub_pos.mpr hR)
  obtain ⟨ev, hev, ⟨b⟩⟩ :=
    onsitePlusBounded_exists_orderedEigenbasis V v₀ hV hproper B hB
  obtain ⟨_, hp, hs⟩ := onsitePlusNonneg_ordered_positive_summable
    V B hB hpos v₀ hv₀ hV hproper honsite ev hev b
  have ha : Admissible ev c d := admissible_of_inv_sq_summable hp hs c d
  have hproduct : HasExactFullSpectralProduct V B hproper ev c d :=
    onsitePlusBounded_hasExactFullSpectralProduct V v₀ hV hproper B hB
      ev hev b hp hs c d hd
  refine ⟨ev, hev, hproduct, ?_⟩
  intro τ hτ hτR
  obtain ⟨μ, hμ, ⟨bt⟩, _, hpμ, hsμ, _, hresp⟩ :=
    finiteSector_nonneg_controlled_summable_family V B hB hpos v₀ R E hv₀ hV hR
      hproper honsite F hF ev hev b τ hτ
  have hBτ : ∀ x y,
      inner ℝ ((B + τ • finiteSectorProjection F) x) y =
        inner ℝ x ((B + τ • finiteSectorProjection F) y) :=
    finiteSectorCorrection_symmetric B hB F τ
  have hproductμ : HasExactFullSpectralProduct V
      (B + τ • finiteSectorProjection F) hproper μ c d :=
    onsitePlusBounded_hasExactFullSpectralProduct V v₀ hV hproper
      (B + τ • finiteSectorProjection F) hBτ μ hμ bt hpμ hsμ c d hd
  have haμ : Admissible μ c d := admissible_of_inv_sq_summable hpμ hsμ c d
  refine ⟨μ, hμ, hproductμ, ?_⟩
  intro n hn
  have hr : sectorResponseKappa R v₀ E 0 * τ ≤ μ n - ev n ∧ μ n - ev n ≤ τ := by
    simpa [sectorResponseKappa] using hresp n hn hτR
  have hbounds := indexedSpectralPoints_norm_bounds
    ev μ c d (sectorResponseKappa R v₀ E 0) τ hκ.le hτ n hr.1 hr.2
  refine ⟨indexedSpectralPoints_product_zeros ev c d ha hd n,
    indexedSpectralPoints_product_zeros μ c d haμ hd n,
    ⟨positiveSpectralPoint_sub ev μ c d n, negativeSpectralPoint_sub ev μ c d n⟩,
    hbounds, ?_⟩
  intro htpos
  exact indexedSpectralPoints_ne ev μ c d hd
    (sectorResponseKappa R v₀ E 0) τ hκ htpos n hr.1

end
end SpectralGeometry
