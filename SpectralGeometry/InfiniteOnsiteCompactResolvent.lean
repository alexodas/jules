import SpectralGeometry.InfiniteOnsiteResolvent
import SpectralGeometry.InfiniteOnsiteFiniteLowEnergy

/-!
# The bounded onsite resolvent: first step towards compactness

The diagonal inverse of M_V - a I is a contraction on real ℓ²
under the unit-gap assumption V(t)-a ≥ 1.

This file first packages the coordinatewise inverse as an actual
continuous linear map. A subsequent proof will establish compactness
under the additional hypothesis of finite onsite sublevel sets.
-/

namespace SpectralGeometry

variable {Tile : Type*}

/-- Coordinatewise multiplication by a real family bounded in absolute value
by one is a bounded linear operator on square-summable states. -/
noncomputable def infiniteOnsiteDiagonalContraction
    (c : Tile → ℝ) (hc : ∀ t : Tile, ‖c t‖ ≤ 1) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile := by
  let F : TileHilbert Tile →ₗ[ℝ] TileHilbert Tile :=
    { toFun := fun f =>
        ⟨(fun t : Tile => c t * f t : PreLp (fun _ : Tile => ℝ)),
          f.property.mono' (fun t => by
            calc
              ‖c t * f t‖ = ‖c t‖ * ‖f t‖ := norm_mul _ _
              _ ≤ 1 * ‖f t‖ :=
                mul_le_mul_of_nonneg_right (hc t) (norm_nonneg _)
              _ = ‖f t‖ := one_mul _)⟩
      map_add' := by
        intro f g
        apply lp.ext
        funext t
        change c t * (f t + g t) = c t * f t + c t * g t
        ring
      map_smul' := by
        intro r f
        apply lp.ext
        funext t
        change c t * (r * f t) = r * (c t * f t)
        ring }
  exact F.mkContinuous 1 (fun f => by
    calc
      ‖F f‖ ≤ ‖f‖ := lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun t => by
        change ‖c t * f t‖ ≤ ‖f t‖
        calc
          ‖c t * f t‖ = ‖c t‖ * ‖f t‖ := norm_mul _ _
          _ ≤ 1 * ‖f t‖ :=
            mul_le_mul_of_nonneg_right (hc t) (norm_nonneg _)
          _ = ‖f t‖ := one_mul _)
      _ = 1 * ‖f‖ := (one_mul _).symm)

/-- The diagonal contraction really multiplies each coordinate by c(t). -/
theorem infiniteOnsiteDiagonalContraction_apply
    (c : Tile → ℝ) (hc : ∀ t : Tile, ‖c t‖ ≤ 1)
    (f : TileHilbert Tile) (t : Tile) :
    infiniteOnsiteDiagonalContraction c hc f t = c t * f t := rfl

private theorem onsiteUnitGap_inverse_norm_le_one
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (t : Tile) : ‖(V t - a)⁻¹‖ ≤ 1 := by
  have hp : 0 < V t - a := lt_of_lt_of_le (by norm_num) (hgap t)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (hgap t)
  simpa [one_div] using h

/-- The onsite resolvent constructed by the coordinatewise inverse,
with operator norm at most one. -/
noncomputable def infiniteOnsiteResolventCLM
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  infiniteOnsiteDiagonalContraction
    (fun t => (V t - a)⁻¹) (onsiteUnitGap_inverse_norm_le_one V a hgap)

theorem infiniteOnsiteResolventCLM_apply
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (f : TileHilbert Tile) (t : Tile) :
    infiniteOnsiteResolventCLM V a hgap f t = (V t - a)⁻¹ * f t := rfl


/-- Evaluation of one tile coordinate as a continuous linear functional. -/
private noncomputable def infiniteOnsiteCoordinateCLM (t : Tile) :
    TileHilbert Tile →L[ℝ] ℝ where
  toFun := fun f => f t
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro r f
    rfl
  cont := (lp.lipschitzWith_one_eval (2 : ENNReal) t).continuous

/-- A finite sum of coordinate extraction followed by single-tile insertion.
It has finite rank by construction. -/
private noncomputable def infiniteOnsiteFiniteDiagonal
    (c : Tile → ℝ) (s : Finset Tile) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ∑ t ∈ s, (c t) •
    ((lp.singleContinuousLinearMap ℝ (fun _ : Tile => ℝ) (2 : ENNReal) t).comp
      (infiniteOnsiteCoordinateCLM t))

/-- Any such finite diagonal truncation is a compact operator. -/
private theorem infiniteOnsiteFiniteDiagonal_compact
    (c : Tile → ℝ) (s : Finset Tile) :
    IsCompactOperator (infiniteOnsiteFiniteDiagonal c s :
      TileHilbert Tile → TileHilbert Tile) := by
  classical
  unfold infiniteOnsiteFiniteDiagonal
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isCompactOperator_zero :
        IsCompactOperator (0 : TileHilbert Tile → TileHilbert Tile))
  | @insert t s ht ih =>
      have hsingle :
          IsCompactOperator
            (lp.singleContinuousLinearMap ℝ (fun _ : Tile => ℝ) (2 : ENNReal) t) :=
        isCompactOperator_of_locallyCompactSpace_rng _
      have hcomp :
          IsCompactOperator
            ((lp.singleContinuousLinearMap ℝ (fun _ : Tile => ℝ) (2 : ENNReal) t).comp
              (infiniteOnsiteCoordinateCLM t)) := by
        simpa only [ContinuousLinearMap.comp_apply] using
          hsingle.comp_clm (infiniteOnsiteCoordinateCLM t)
      have hterm :
          IsCompactOperator
            ((c t) •
              ((lp.singleContinuousLinearMap ℝ (fun _ : Tile => ℝ)
                (2 : ENNReal) t).comp (infiniteOnsiteCoordinateCLM t))) := by
        simpa only [ContinuousLinearMap.coe_smul] using hcomp.smul (c t)
      simpa only [Finset.sum_insert ht, ContinuousLinearMap.coe_add] using
        hterm.add ih

/-- A finite diagonal truncation vanishes outside its finite index set. -/
private theorem infiniteOnsiteFiniteDiagonal_apply
    (c : Tile → ℝ) (s : Finset Tile) (f : TileHilbert Tile) (t : Tile) :
    infiniteOnsiteFiniteDiagonal c s f t =
      if t ∈ s then c t * f t else 0 := by
  classical
  simp [infiniteOnsiteFiniteDiagonal, infiniteOnsiteCoordinateCLM,
    lp.singleContinuousLinearMap_apply, lp.single_apply,
    Finset.sum_ite_eq', smul_eq_mul]

end SpectralGeometry
