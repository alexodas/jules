module

public import SpectralGeometry.OrderedSpectralProductBridge
public import SpectralGeometry.InfiniteFullSpectralSummability

public section

/-!
# Finite-sector response of indexed canonical-product zeros

The original and perturbed operators share the natural onsite domain. The
shift used for a compact resolvent may vary with the perturbation parameter,
but the product center and direction never change. Each full spectral
product carries the geometric multiplicities of its *own* operator.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

/-- The positive coefficient in the low-energy response estimate. -/
@[expose] def sectorResponseKappa (R v₀ E C : ℝ) : ℝ :=
  (R - C - E) / (R - v₀)

/-- An effective finite-sector perturbation moves each indexed zero of
both paired full spectral products by a quantitatively controlled amount.

The products and their exact geometric zero orders are certified by
`HasExactFullSpectralProduct`. The original and perturbed ordered bases,
positivity, summability and the numerical response are *conclusions* of
existing theorems, not assumptions of this application. The index is
preserved even at repeated eigenvalues and crossings. -/
theorem finiteSector_fullProducts_indexedZeroResponse [Infinite Tile]
    (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (v₀ R E : ℝ) (hV : ∀ t, v₀ ≤ V t) (hgap : ‖B‖ < v₀)
    (hR : v₀ < R) (hE : E < R - ‖B‖)
    (hproper : ∀ r : ℝ, (infiniteOnsiteLowEnergyTiles V r).Finite)
    (e : ℕ ≃ Tile) (horder : Monotone (fun n => V (e n)))
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
            ((‖d‖ * (sectorResponseKappa R v₀ E ‖B‖ * τ) ≤
                ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ ∧
              ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ ≤
                ‖d‖ * τ) ∧
             (‖d‖ * (sectorResponseKappa R v₀ E ‖B‖ * τ) ≤
                ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ ∧
              ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ ≤
                ‖d‖ * τ)) ∧
            (0 < τ →
              positiveSpectralPoint μ c d n ≠ positiveSpectralPoint ev c d n ∧
              negativeSpectralPoint μ c d n ≠ negativeSpectralPoint ev c d n) := by
  classical
  have hκ : 0 < sectorResponseKappa R v₀ E ‖B‖ := by
    unfold sectorResponseKappa
    exact div_pos (by linarith) (sub_pos.mpr hR)
  obtain ⟨ev, hev, ⟨b⟩⟩ :=
    onsitePlusBounded_exists_orderedEigenbasis V v₀ hV hproper B hB
  obtain ⟨_, hp, hs⟩ :=
    onsitePlusBounded_ordered_positive_summable V B hB v₀ hV hgap
      hproper e horder honsite ev hev b
  have ha : Admissible ev c d :=
    fullSpectrum_admissible_of_positive_summable ev hp hs c d
  have hproduct : HasExactFullSpectralProduct V B hproper ev c d :=
    onsitePlusBounded_hasExactFullSpectralProduct V v₀ hV hproper B hB
      ev hev b hp hs c d hd
  refine ⟨ev, hev, hproduct, ?_⟩
  intro τ hτ hτR
  obtain ⟨μ, hμ, ⟨bt⟩, _, hpμ, hsμ, hresp⟩ :=
    finiteSector_controlled_summable_family V B hB v₀ R E hV hgap hR
      hproper e horder honsite F hF ev hev b τ hτ hτR
  have hBτ : ∀ x y,
      inner ℝ ((B + τ • finiteSectorProjection F) x) y =
        inner ℝ x ((B + τ • finiteSectorProjection F) y) :=
    finiteSectorCorrection_symmetric B hB F τ
  have hproductμ : HasExactFullSpectralProduct V
      (B + τ • finiteSectorProjection F) hproper μ c d :=
    onsitePlusBounded_hasExactFullSpectralProduct V v₀ hV hproper
      (B + τ • finiteSectorProjection F) hBτ μ hμ bt hpμ hsμ c d hd
  have haμ : Admissible μ c d :=
    fullSpectrum_admissible_of_positive_summable μ hpμ hsμ c d
  refine ⟨μ, hμ, hproductμ, ?_⟩
  intro n hn
  have hr := hresp n hn
  have hbounds := indexedSpectralPoints_norm_bounds
    ev μ c d (sectorResponseKappa R v₀ E ‖B‖) τ hκ.le hτ n hr.1 hr.2
  refine ⟨indexedSpectralPoints_product_zeros ev c d ha hd n,
    indexedSpectralPoints_product_zeros μ c d haμ hd n,
    ⟨positiveSpectralPoint_sub ev μ c d n,
      negativeSpectralPoint_sub ev μ c d n⟩,
    hbounds, ?_⟩
  intro htpos
  exact indexedSpectralPoints_ne ev μ c d hd
    (sectorResponseKappa R v₀ E ‖B‖) τ hκ htpos n hr.1

#print axioms finiteSector_fullProducts_indexedZeroResponse

end
end SpectralGeometry
