module

public import SpectralGeometry.InfiniteOnsiteCompactResolvent

public section

/-!
# The bounded onsite resolvent is the inverse on the natural domain

The bounded coordinatewise resolvent from the compact-resolvent module
takes values in the natural domain of (possibly unbounded) onsite
multiplication. It solves the shifted equation, and applying it to the
shifted operator recovers the original domain state.

Compactness itself was already proved in the imported module; these
identities connect that compact map with the genuine shifted inverse.
-/

namespace SpectralGeometry

variable {Tile : Type*}

/-- The bounded onsite resolvent takes every ℓ² state into the natural
multiplication domain, even when the onsite potential is unbounded. -/
theorem infiniteOnsiteResolventCLM_mem_domain
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (f : TileHilbert Tile) :
    infiniteOnsiteResolventCLM V a hgap f ∈ infiniteOnsiteDomain V := by
  let x : TileHilbert Tile := infiniteOnsiteResolventCLM V a hgap f
  have hx (t : Tile) : (V t - a) * x t = f t := by
    have hpos : 0 < V t - a :=
      lt_of_lt_of_le (by norm_num) (hgap t)
    change (V t - a) * (infiniteOnsiteResolventCLM V a hgap f) t = f t
    rw [infiniteOnsiteResolventCLM_apply]
    field_simp [ne_of_gt hpos]
  have hcoordinate (t : Tile) :
      V t * x t = f t + a * x t := by
    calc
      V t * x t = (V t - a) * x t + a * x t := by ring
      _ = f t + a * x t := by rw [hx t]
  have hmem : Memℓp (fun t : Tile => V t * x t) 2 := by
    have hh : Memℓp (fun t : Tile => f t + a * x t) 2 := by
      have hh0 := f.property.add (x.property.const_mul a)
      have heq :
          ((f : Tile → ℝ) + (fun t : Tile => a * x t)) =
            (fun t : Tile => f t + a * x t) := by
        funext t
        rfl
      rw [heq] at hh0
      exact hh0
    have heq :
        (fun t : Tile => V t * x t) =
          (fun t : Tile => f t + a * x t) := by
      funext t
      exact hcoordinate t
    rw [heq]
    exact hh
  change Memℓp (fun t : Tile => V t * x t) 2
  exact hmem

/-- The canonical domain-valued solution furnished by the bounded
coordinatewise resolvent. -/
@[expose] noncomputable def infiniteOnsiteResolventSolution
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (f : TileHilbert Tile) : infiniteOnsiteDomain V :=
  ⟨infiniteOnsiteResolventCLM V a hgap f,
   infiniteOnsiteResolventCLM_mem_domain V a hgap f⟩

/-- The shifted onsite operator applied to the bounded resolvent
solution returns the original ℓ² right-hand side. -/
theorem infiniteOnsiteResolventCLM_shift_right_inverse
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (f : TileHilbert Tile) :
    infiniteOnsiteOperator V (infiniteOnsiteResolventSolution V a hgap f) -
      a • ((infiniteOnsiteResolventSolution V a hgap f).1 : TileHilbert Tile) =
      f := by
  apply lp.ext
  funext t
  change
    V t * (infiniteOnsiteResolventCLM V a hgap f) t -
      a * (infiniteOnsiteResolventCLM V a hgap f) t = f t
  rw [infiniteOnsiteResolventCLM_apply]
  have hpos : 0 < V t - a :=
    lt_of_lt_of_le (by norm_num) (hgap t)
  field_simp [ne_of_gt hpos] <;> ring

/-- Applying the bounded resolvent to the shifted onsite operator
returns any state of the natural multiplication domain. -/
theorem infiniteOnsiteResolventCLM_shift_left_inverse
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (ψ : infiniteOnsiteDomain V) :
    infiniteOnsiteResolventCLM V a hgap
      (infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile)) =
        (ψ.1 : TileHilbert Tile) := by
  apply lp.ext
  funext t
  rw [infiniteOnsiteResolventCLM_apply]
  change
    (V t - a)⁻¹ * (V t * ψ.1 t - a * ψ.1 t) = ψ.1 t
  have hpos : 0 < V t - a :=
    lt_of_lt_of_le (by norm_num) (hgap t)
  field_simp [ne_of_gt hpos] <;> ring

end SpectralGeometry
