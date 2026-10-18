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

end SpectralGeometry
