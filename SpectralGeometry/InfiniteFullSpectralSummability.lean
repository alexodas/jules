module

public import SpectralGeometry.InfiniteOrderedSpectralControl
public import SpectralGeometry.InfiniteOnsitePowerGrowth

public section

/-!
# Growth transfer and stability of positive inverse-square summability

Properness and bounded-error ordered comparison transfer onsite summability.
A separate uniform lower gap supplies positivity, which summability alone
would not imply. Nonnegative finite-sector perturbations preserve both.
-/

namespace SpectralGeometry

open Filter

noncomputable section

/-- A bounded lower error does not destroy inverse-square summability of
levels tending to infinity. This lemma alone makes no positivity assertion
about the finitely many initial levels. -/
theorem invSq_summable_of_bounded_lower_error (v ev : ℕ → ℝ) (C : ℝ)
    (hv : Tendsto v atTop atTop) (hs : Summable (fun n => 1 / (v n) ^ 2))
    (he : ∀ n, v n - C ≤ ev n) : Summable (fun n => 1 / (ev n) ^ 2) := by
  apply (hs.mul_left 4).of_norm_bounded_eventually_nat
  filter_upwards [hv.eventually (eventually_ge_atTop (max 1 (2 * C)))] with n hn
  have hv1 := (le_max_left (1 : ℝ) (2 * C)).trans hn
  have hvC := (le_max_right (1 : ℝ) (2 * C)).trans hn
  have hvp : 0 < v n := by linarith
  have hl : v n / 2 ≤ ev n := by linarith [he n]
  have hsq : (v n / 2) ^ 2 ≤ (ev n) ^ 2 := by nlinarith [he n]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (ev n) ^ 2)]
  calc
    1 / (ev n) ^ 2 ≤ 1 / (v n / 2) ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos (by linarith)) hsq
    _ = 4 * (1 / (v n) ^ 2) := by field_simp; ring

variable {Tile : Type*} [DecidableEq Tile]

/-- Properness gives divergence along every injective site enumeration. -/
theorem onsite_tendsto_of_proper (V : Tile → ℝ)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (e : ℕ → Tile) (he : Function.Injective e) :
    Tendsto (fun n => V (e n)) atTop atTop := by
  apply real_tendsto_atTop_of_finite_sublevel_indices
  intro R
  exact Set.Finite.of_injOn (fun n hn => hn.le) he.injOn (hproper R)

/-- Positive full-spectrum summability from proper onsite summability,
an actual ordered eigenbasis and a strict lower gap exceeding the correction
norm. The bijection lists every onsite level, including multiplicities. -/
theorem onsitePlusBounded_ordered_positive_summable (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (v₀ : ℝ) (hV : ∀ t, v₀ ≤ V t) (hgap : ‖B‖ < v₀)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (e : ℕ ≃ Tile) (horder : Monotone (fun n => V (e n)))
    (honsite : Summable (fun t => 1 / (V t) ^ 2))
    (ev : ℕ → ℝ) (hev : Monotone ev)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev) :
    (∀ n, v₀ - ‖B‖ ≤ ev n) ∧ (∀ n, 0 < ev n) ∧
      Summable (fun n => 1 / (ev n) ^ 2) := by
  have hc (n : ℕ) := (onsitePlusBounded_ordered_comparison V B hB e horder ev hev b n).1
  have hlo (n : ℕ) : v₀ - ‖B‖ ≤ ev n := by linarith [hV (e n), hc n]
  refine ⟨hlo, fun n => lt_of_lt_of_le (sub_pos.mpr hgap) (hlo n), ?_⟩
  exact invSq_summable_of_bounded_lower_error _ ev ‖B‖
    (onsite_tendsto_of_proper V hproper e e.injective)
    (honsite.comp_injective e.injective) hc

/-- In particular, the already proved power-law onsite criterion transfers
to the complete interacting spectrum; the original site labels need not
already be the sorted onsite ordering. -/
theorem onsitePlusBounded_powerGrowth_positive_summable (V : ℕ → ℝ)
    (B : TileHilbert ℕ →L[ℝ] TileHilbert ℕ)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (v₀ : ℝ) (hV : ∀ t, v₀ ≤ V t) (hgap : ‖B‖ < v₀)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (e : ℕ ≃ ℕ) (horder : Monotone (fun n => V (e n)))
    (α : ℝ) (hα : (1 / 2 : ℝ) < α)
    (hgrowth : ∀ n, (((n + 1 : ℕ) : ℝ) ^ α) ≤ V n)
    (ev : ℕ → ℝ) (hev : Monotone ev)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev) :
    (∀ n, v₀ - ‖B‖ ≤ ev n) ∧ (∀ n, 0 < ev n) ∧
      Summable (fun n => 1 / (ev n) ^ 2) :=
  onsitePlusBounded_ordered_positive_summable V B hB v₀ hV hgap hproper e horder
    (infiniteOnsitePowerGrowth_invSq_summable V α hα hgrowth) ev hev b

/-- Every nonnegative finite-sector perturbation preserves the original
positive lower gap and inverse-square summability, without a simplicity
assumption. The ordered eigenbases make the infinite indexing explicit. -/
theorem finiteSector_preserves_gap_summability (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (F : Finset Tile) (τ : ℝ) (hτ : 0 ≤ τ)
    (ev μ : ℕ → ℝ) (hev : Monotone ev) (hμ : Monotone μ)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev)
    (bt : DomainEigenbasis (infiniteOnsiteDomain V)
      (onsitePlusBounded V (B + τ • finiteSectorProjection F)) μ)
    (γ : ℝ) (hγ : 0 < γ) (hlo : ∀ n, γ ≤ ev n)
    (hs : Summable (fun n => 1 / (ev n) ^ 2)) :
    (∀ n, γ ≤ μ n) ∧ (∀ n, 0 < μ n) ∧ Summable (fun n => 1 / (μ n) ^ 2) := by
  have hc := finiteSector_ordered_mono V B hB F τ hτ ev μ hev hμ b bt
  have hlow (n : ℕ) : γ ≤ μ n := (hlo n).trans (hc n)
  refine ⟨hlow, fun n => hγ.trans_le (hlow n), ?_⟩
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
  intro n
  apply one_div_le_one_div_of_le (sq_pos_of_pos (hγ.trans_le (hlo n)))
  nlinarith [hc n, hlo n, hlow n]

/-- Properness and the unchanged onsite lower bound provide a compact
shifted inverse for every finite-sector perturbation. The witnessing shift
may depend on the parameter; no uniform fixed-shift Neumann bound is assumed. -/
theorem finiteSector_preserves_compact_shift (V : Tile → ℝ)
    (v₀ : ℝ) (hV : ∀ t, v₀ ≤ V t)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) (F : Finset Tile) (τ : ℝ) :
    ∃ (a : ℝ) (hunit : ∀ t, 1 ≤ V t - a),
      ∃ hsmall : ‖(B + τ • finiteSectorProjection F).comp
        (infiniteOnsiteResolventCLM V a hunit)‖ < 1,
        IsCompactOperator (infiniteBoundedOnsiteResolvent V a hunit
          (B + τ • finiteSectorProjection F) hsmall) :=
  infiniteBoundedOnsite_exists_compact_shift V v₀ hV hproper _

end
end SpectralGeometry
