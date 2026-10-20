module

public import SpectralGeometry.InfiniteLocalCompactResolvent
public import SpectralGeometry.InfiniteLocalClosedGraph

public section

/-!
# Quantitative bounds and negative shifts for compact local resolvents

The continuous diagonal inverse Rₐ satisfies ‖Rₐ‖ ≤ 1/δ whenever
0 < δ ≤ V(t)-a. Hence any bounded correction B with ‖B‖ < δ
satisfies the Neumann smallness hypothesis ‖B ∘ Rₐ‖ < 1.

If V is bounded below by v₀, choose δ = ‖B‖+1 and a=v₀-δ.
Thus every bounded B admits at least one sufficiently negative real
shift at which M_V+B has a compact resolvent when the onsite potential
has finite sublevel sets, without restricting the global size of B.

For finite-color matching Laplacians we also give the explicit bound
‖L_w+εP+mI‖ ≤ 2DW+|ε|‖P‖+|m|.
This does not assert a resolvent at every shift or spectral discreteness.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

abbrev QuantEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- The onsite resolvent norm improves from one to the reciprocal of
any quantitative positive onsite gap. -/
theorem infiniteOnsiteResolventCLM_norm_le_inv_gap
    (V : Tile → ℝ) (a δ : ℝ)
    (hδ : 0 < δ) (hgap : ∀ t, δ ≤ V t - a)
    (hunit : ∀ t, 1 ≤ V t - a) :
    ‖infiniteOnsiteResolventCLM V a hunit‖ ≤ δ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (le_of_lt (inv_pos.mpr hδ))
  intro f
  have hpoint (t : Tile) :
      ‖(infiniteOnsiteResolventCLM V a hunit f) t‖ ≤
        ‖(δ⁻¹ • f) t‖ := by
    rw [infiniteOnsiteResolventCLM_apply]
    have hvt : 0 < V t - a := lt_of_lt_of_le hδ (hgap t)
    have hc : ‖(V t - a)⁻¹‖ ≤ δ⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvt)]
      have h := one_div_le_one_div_of_le hδ (hgap t)
      simpa only [one_div] using h
    have hh : ‖(V t - a)⁻¹‖ * ‖f t‖ ≤ δ⁻¹ * ‖f t‖ :=
      mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul,
      Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr hδ))] using hh
  have hn :
      ‖infiniteOnsiteResolventCLM V a hunit f‖ ≤ ‖δ⁻¹ • f‖ :=
    lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) hpoint
  simpa only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (inv_pos.mpr hδ))] using hn

/-- An explicit onsite gap larger than the norm of the bounded
correction implies the smallness condition needed for P1. -/
theorem infiniteBoundedOnsite_comp_norm_lt_one
    (V : Tile → ℝ) (a δ : ℝ)
    (hδ : 0 < δ) (hgap : ∀ t, δ ≤ V t - a)
    (hunit : ∀ t, 1 ≤ V t - a)
    (B : QuantEnd Tile) (hB : ‖B‖ < δ) :
    ‖B.comp (infiniteOnsiteResolventCLM V a hunit)‖ < 1 := by
  let R := infiniteOnsiteResolventCLM V a hunit
  have hR : ‖R‖ ≤ δ⁻¹ :=
    infiniteOnsiteResolventCLM_norm_le_inv_gap V a δ hδ hgap hunit
  calc
    ‖B.comp R‖ ≤ ‖B‖ * ‖R‖ :=
      ContinuousLinearMap.opNorm_comp_le B R
    _ ≤ ‖B‖ * δ⁻¹ :=
      mul_le_mul_of_nonneg_left hR (norm_nonneg B)
    _ < δ * δ⁻¹ :=
      mul_lt_mul_of_pos_right hB (inv_pos.mpr hδ)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hδ)

/-- With a quantitative onsite gap dominating the bounded correction,
the shifted full operator has a compact inverse on its natural domain. -/
theorem infiniteBoundedOnsiteResolvent_compact_of_gap
    (V : Tile → ℝ) (a δ : ℝ)
    (hδ : 0 < δ) (hgap : ∀ t, δ ≤ V t - a)
    (hunit : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : QuantEnd Tile) (hB : ‖B‖ < δ) :
    ∃ hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hunit)‖ < 1,
      IsCompactOperator
        (infiniteBoundedOnsiteResolvent V a hunit B hsmall) := by
  let hsmall :=
    infiniteBoundedOnsite_comp_norm_lt_one V a δ hδ hgap hunit B hB
  exact ⟨hsmall, infiniteBoundedOnsiteResolvent_compact
    V a hunit hproper B hsmall⟩

/-- Any bounded correction admits some negative enough spectral shift
with a compact inverse whenever V is bounded below and proper.
The shift depends on B; it is not a uniform statement for all shifts. -/
theorem infiniteBoundedOnsite_exists_compact_shift
    (V : Tile → ℝ) (vmin : ℝ) (hlower : ∀ t, vmin ≤ V t)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : QuantEnd Tile) :
    ∃ (a : ℝ) (hunit : ∀ t, 1 ≤ V t - a),
      ∃ hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hunit)‖ < 1,
        IsCompactOperator
          (infiniteBoundedOnsiteResolvent V a hunit B hsmall) := by
  let δ : ℝ := ‖B‖ + 1
  let a : ℝ := vmin - δ
  have hδ : 0 < δ := by
    dsimp [δ]
    have hn := norm_nonneg B
    linarith
  have hδone : 1 ≤ δ := by
    dsimp [δ]
    have hn := norm_nonneg B
    linarith
  have hgap : ∀ t, δ ≤ V t - a := by
    intro t
    dsimp [a]
    linarith [hlower t]
  have hunit : ∀ t, 1 ≤ V t - a :=
    fun t => le_trans hδone (hgap t)
  have hB : ‖B‖ < δ := by
    dsimp [δ]
    linarith
  obtain ⟨hsmall, hcompact⟩ :=
    infiniteBoundedOnsiteResolvent_compact_of_gap
      V a δ hδ hgap hunit hproper B hB
  exact ⟨a, hunit, hsmall, hcompact⟩

/-- Norm estimate for the concrete matching-family correction, including
any bounded perturbation and any real scalar shift. -/
theorem infiniteLocalBoundedCorrection_norm_le_geometric
    (D : ℕ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : QuantEnd Tile) (ε shift W : ℝ)
    (hW : 0 ≤ W) (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ W) :
    ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ ≤
      2 * (D : ℝ) * W + |ε| * ‖P‖ + |shift| := by
  let L := infiniteLocalMatchingLaplacian D σ w
  have hL : ‖L‖ ≤ 2 * (D : ℝ) * W :=
    infiniteLocalMatchingLaplacian_norm_le D σ w W hW hw0 hw
  have hid :
      ‖(ContinuousLinearMap.id ℝ (TileHilbert Tile))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  change ‖L + ε • P + shift • ContinuousLinearMap.id ℝ (TileHilbert Tile)‖ ≤
    2 * (D : ℝ) * W + |ε| * ‖P‖ + |shift|
  calc
    ‖L + ε • P + shift • ContinuousLinearMap.id ℝ (TileHilbert Tile)‖ ≤
        (‖L‖ + ‖ε • P‖) +
          ‖shift • ContinuousLinearMap.id ℝ (TileHilbert Tile)‖ := by
      exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = ‖L‖ + |ε| * ‖P‖ +
        |shift| * ‖ContinuousLinearMap.id ℝ (TileHilbert Tile)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ 2 * (D : ℝ) * W + |ε| * ‖P‖ + |shift| * 1 := by
      gcongr
    _ = 2 * (D : ℝ) * W + |ε| * ‖P‖ + |shift| := by ring

/-- The geometric gap δ>2DW+|ε|‖P‖+|m| is a concrete sufficient
condition for compact resolvent of the local matching model. -/
theorem infiniteLocalMatching_compact_resolvent_of_gap
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : QuantEnd Tile)
    (ε shift a δ W : ℝ)
    (hW : 0 ≤ W) (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ W)
    (hδ : 0 < δ) (hgap : ∀ t, δ ≤ V t - a)
    (hunit : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hbig : 2 * (D : ℝ) * W + |ε| * ‖P‖ + |shift| < δ) :
    ∃ hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
        (infiniteOnsiteResolventCLM V a hunit)‖ < 1,
      IsCompactOperator
        (infiniteBoundedOnsiteResolvent V a hunit
          (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall) := by
  have hb : ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ < δ :=
    lt_of_le_of_lt
      (infiniteLocalBoundedCorrection_norm_le_geometric
        D σ w P ε shift W hW hw0 hw) hbig
  exact infiniteBoundedOnsiteResolvent_compact_of_gap
    V a δ hδ hgap hunit hproper
      (infiniteLocalBoundedCorrection D σ w P ε shift) hb

end SpectralGeometry
