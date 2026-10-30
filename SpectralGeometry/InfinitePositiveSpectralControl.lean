module

public import SpectralGeometry.InfiniteOnsiteOrderedEnumeration
public import SpectralGeometry.InfiniteFullSpectralSummability

public section

/-!
# Positive-interaction gaps, summability and finite-sector response

A symmetric nonnegative bounded interaction preserves the onsite lower
gap, regardless of its norm. Properness constructs the sorted onsite
bijection used in the existing variational comparison. The same positive
form bound removes the interaction-norm penalty from finite-sector response.
All operator forms use the unchanged natural multiplication domain.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

/-- Positive interactions preserve a positive onsite gap and inverse-square
summability. The onsite ordering is constructed from properness; no bound
on the interaction norm is required. -/
theorem onsitePlusNonneg_ordered_positive_summable [Infinite Tile]
    (V : Tile → ℝ) (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (B x))
    (v₀ : ℝ) (hv₀ : 0 < v₀) (hV : ∀ t, v₀ ≤ V t)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (honsite : Summable (fun t => 1 / (V t) ^ 2))
    (ev : ℕ → ℝ) (hev : Monotone ev)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev) :
    (∀ n, v₀ ≤ ev n) ∧ (∀ n, 0 < ev n) ∧
      Summable (fun n => 1 / (ev n) ^ 2) := by
  obtain ⟨e, he⟩ := infiniteOnsite_exists_monotone_equiv V hproper
  have hc (n : ℕ) := onsitePlusBounded_ordered_ge_onsite_of_nonneg V B hB hpos e he ev hev b n
  have hlo (n : ℕ) : v₀ ≤ ev n := (hV (e n)).trans (hc n)
  refine ⟨hlo, fun n => hv₀.trans_le (hlo n), ?_⟩
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    (honsite.comp_injective e.injective)
  intro n
  apply one_div_le_one_div_of_le (sq_pos_of_pos (hv₀.trans_le (hV (e n))))
  nlinarith [hc n, hV (e n), hlo n]

/-- A positive interaction leaves the onsite sector form bound unchanged. -/
theorem onsitePlusNonneg_sector_form_bound (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hpos : ∀ x, 0 ≤ inner ℝ x (B x))
    (v₀ R : ℝ) (hV : ∀ t, v₀ ≤ V t)
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t)
    (x : infiniteOnsiteDomain V) :
    R * ‖(x : TileHilbert Tile)‖ ^ 2 - (R - v₀) * ‖finiteSectorProjection F x‖ ^ 2 ≤
      inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V B x) := by
  have hon := infiniteOnsiteOperator_sector_form_bound V v₀ R hV F hF x
  rw [onsitePlusBounded_apply, inner_add_right]
  exact hon.trans (le_add_of_nonneg_right (hpos x))

/-- A proved sector form inequality gives an ordered response estimate.
The form hypothesis precedes the spectral conclusion and is independent
of any particular eigenvalue. Crossings and repeated levels are allowed. -/
theorem finiteSector_ordered_response_of_form_bound (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (A D E : ℝ) (hD : 0 < D) (F : Finset Tile)
    (hform : ∀ x : infiniteOnsiteDomain V,
      A * ‖(x : TileHilbert Tile)‖ ^ 2 - D * ‖finiteSectorProjection F x‖ ^ 2 ≤
        inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V B x))
    (τ : ℝ) (hτ : 0 ≤ τ) (hτD : τ ≤ D)
    (ev μ : ℕ → ℝ) (hev : Monotone ev) (hμ : Monotone μ)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev)
    (bt : DomainEigenbasis (infiniteOnsiteDomain V)
      (onsitePlusBounded V (B + τ • finiteSectorProjection F)) μ)
    (n : ℕ) (hn : ev n ≤ E) :
    ((A - E) / D) * τ ≤ μ n - ev n ∧ μ n - ev n ≤ τ := by
  let r := τ / D
  have hr0 : 0 ≤ r := div_nonneg hτ hD.le
  have hr1 : r ≤ 1 := (div_le_one hD).mpr hτD
  have hrt : r * D = τ := div_mul_cancel₀ τ (ne_of_gt hD)
  have hlo := ordered_eigenvalues_affine_le b bt (onsitePlusBounded_symmetric V B hB)
    (onsitePlusBounded_symmetric V _ (finiteSectorCorrection_symmetric B hB F τ))
    hev hμ (1 - r) (r * A) (sub_nonneg.mpr hr1) (fun x => by
      have hs := mul_le_mul_of_nonneg_left (hform x) hr0
      rw [finiteSector_energy_response]
      nlinarith [hrt]) n
  have hhi := ordered_eigenvalues_affine_le bt b
    (onsitePlusBounded_symmetric V _ (finiteSectorCorrection_symmetric B hB F τ))
    (onsitePlusBounded_symmetric V B hB) hμ hev 1 (-τ) zero_le_one (fun x => by
      have hnorm : ‖finiteSectorProjection F x‖ ≤ ‖(x : TileHilbert Tile)‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (by
          simpa using mul_le_mul_of_nonneg_right (finiteSectorProjection_norm_le F)
            (norm_nonneg (x : TileHilbert Tile)))
      have hsq : ‖finiteSectorProjection F x‖ ^ 2 ≤ ‖(x : TileHilbert Tile)‖ ^ 2 := by
        nlinarith [norm_nonneg (finiteSectorProjection F x), norm_nonneg (x : TileHilbert Tile)]
      rw [finiteSector_energy_response]
      have hh := mul_le_mul_of_nonneg_left hsq hτ
      nlinarith) n
  have heq : ((A - E) / D) * τ = r * (A - E) := by dsimp [r]; ring
  constructor
  · rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hn hr0]
  · linarith

/-- The sharpened finite-sector response for a nonnegative interaction.
The lower coefficient is positive whenever E < R. No assumption that the
selected energy window is nonempty is implicit in this conditional bound. -/
theorem finiteSector_ordered_response_of_nonneg (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (B x))
    (v₀ R E : ℝ) (hV : ∀ t, v₀ ≤ V t) (hR : v₀ < R)
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t)
    (τ : ℝ) (hτ : 0 ≤ τ) (hτR : τ ≤ R - v₀)
    (ev μ : ℕ → ℝ) (hev : Monotone ev) (hμ : Monotone μ)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev)
    (bt : DomainEigenbasis (infiniteOnsiteDomain V)
      (onsitePlusBounded V (B + τ • finiteSectorProjection F)) μ)
    (n : ℕ) (hn : ev n ≤ E) :
    ((R - E) / (R - v₀)) * τ ≤ μ n - ev n ∧ μ n - ev n ≤ τ :=
  finiteSector_ordered_response_of_form_bound V B hB R (R - v₀) E (sub_pos.mpr hR) F
    (onsitePlusNonneg_sector_form_bound V B hpos v₀ R hV F hF)
    τ hτ hτR ev μ hev hμ b bt n hn

/-- All nonnegative finite-sector parameters preserve the onsite gap and
summability. The sharper response is asserted on its stated finite interval.
All ordered spectra and natural-domain eigenbases are constructed. -/
theorem finiteSector_nonneg_controlled_summable_family [Infinite Tile]
    (V : Tile → ℝ) (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (B x))
    (v₀ R E : ℝ) (hv₀ : 0 < v₀) (hV : ∀ t, v₀ ≤ V t) (hR : v₀ < R)
    (hproper : ∀ r : ℝ, (infiniteOnsiteLowEnergyTiles V r).Finite)
    (honsite : Summable (fun t => 1 / (V t) ^ 2))
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t)
    (ev : ℕ → ℝ) (hev : Monotone ev)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev) :
    ∀ τ : ℝ, 0 ≤ τ →
      ∃ μ : ℕ → ℝ, Monotone μ ∧
        Nonempty (DomainEigenbasis (infiniteOnsiteDomain V)
          (onsitePlusBounded V (B + τ • finiteSectorProjection F)) μ) ∧
        (∀ n, v₀ ≤ μ n) ∧ (∀ n, 0 < μ n) ∧
        Summable (fun n => 1 / (μ n) ^ 2) ∧
        (∀ n, ev n ≤ μ n) ∧
        ∀ n, ev n ≤ E → τ ≤ R - v₀ →
          ((R - E) / (R - v₀)) * τ ≤ μ n - ev n ∧ μ n - ev n ≤ τ := by
  have hbase := onsitePlusNonneg_ordered_positive_summable
    V B hB hpos v₀ hv₀ hV hproper honsite ev hev b
  intro τ hτ
  obtain ⟨μ, hμ, ⟨bt⟩⟩ := finiteSector_exists_orderedEigenbasis V v₀ hV hproper B hB F τ
  have hp := finiteSector_preserves_gap_summability V B hB F τ hτ
    ev μ hev hμ b bt v₀ hv₀ hbase.1 hbase.2.2
  exact ⟨μ, hμ, ⟨bt⟩, hp.1, hp.2.1, hp.2.2,
    finiteSector_ordered_mono V B hB F τ hτ ev μ hev hμ b bt,
    fun n hn hτR => finiteSector_ordered_response_of_nonneg V B hB hpos v₀ R E hV hR F hF
      τ hτ hτR ev μ hev hμ b bt n hn⟩

end
end SpectralGeometry
