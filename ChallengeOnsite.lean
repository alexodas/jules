module

public import Mathlib

public section

/-!
# Independent infinite-onsite spectral statements

This file imports only Mathlib, never the SpectralGeometry proof library.
The sorry placeholders are intentional challenge holes for Comparator.
The chosen statements concern ℓ² diagonal multiplication and its point
eigenvalues and energy-growth conditions, not the interacting operator.
-/

namespace SpectralGeometry

@[expose] abbrev TileHilbert (Tile : Type*) : Type _ :=
  lp (fun _ : Tile => ℝ) 2

variable {Tile : Type*}

/-- Natural domain of multiplication by a possibly unbounded potential.
Both the original state and the onsite-multiplied state must lie in ℓ². -/
@[expose] noncomputable def infiniteOnsiteDomain
    (V : Tile → ℝ) : Submodule ℝ (TileHilbert Tile) where
  carrier := {ψ | Memℓp (fun t : Tile => V t * ψ t) 2}
  zero_mem' := by
    have hz : Memℓp (fun _ : Tile => (0 : ℝ)) 2 := zero_mem_ℓp'
    simpa using hz
  add_mem' := by
    intro f g hf hg
    have h : Memℓp
        ((fun t : Tile => V t * f t) + fun t : Tile => V t * g t) 2 :=
      hf.add hg
    change Memℓp (fun t : Tile => V t * (f + g) t) 2
    have heq :
        (fun t : Tile => V t * (f + g) t) =
          ((fun t : Tile => V t * f t) + fun t : Tile => V t * g t) := by
      funext t
      simp [mul_add]
    rw [heq]
    exact h
  smul_mem' := by
    intro a f hf
    have h : Memℓp (fun t : Tile => a * (V t * f t)) 2 :=
      hf.const_mul a
    change Memℓp (fun t : Tile => V t * (a • f) t) 2
    have heq :
        (fun t : Tile => V t * (a • f) t) =
          (fun t : Tile => a * (V t * f t)) := by
      funext t
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact h

/-- The diagonal multiplication operator with its natural ℓ² domain.
It is a linear map into ℓ², even if the potential is unbounded. -/
@[expose] noncomputable def infiniteOnsiteOperator
    (V : Tile → ℝ) :
    (infiniteOnsiteDomain V) →ₗ[ℝ] TileHilbert Tile where
  toFun := fun ψ =>
    ⟨(fun t : Tile => V t * ψ.1 t : PreLp (fun _ : Tile => ℝ)), ψ.2⟩
  map_add' := by
    intro f g
    apply lp.ext
    funext t
    change V t * (f.1 t + g.1 t) =
      V t * f.1 t + V t * g.1 t
    ring
  map_smul' := by
    intro a f
    apply lp.ext
    funext t
    change V t * (a * f.1 t) = a * (V t * f.1 t)
    ring

-- Independently audited signatures from SpectralGeometry/InfiniteOnsite.lean
theorem infiniteOnsiteOperator_apply
    (V : Tile → ℝ) (ψ : infiniteOnsiteDomain V) (t : Tile) :
    infiniteOnsiteOperator V ψ t = V t * ψ.1 t := by
  sorry

theorem infiniteOnsiteOperator_local_nonneg
    (V : Tile → ℝ) (hV : ∀ t, 0 ≤ V t)
    (ψ : infiniteOnsiteDomain V) (t : Tile) :
    0 ≤ ψ.1 t * infiniteOnsiteOperator V ψ t := by
  sorry

-- Independently audited signatures from SpectralGeometry/InfiniteOnsiteDensity.lean
section
variable [DecidableEq Tile]

theorem infiniteOnsiteDomain_single
    (V : Tile → ℝ) (i : Tile) (a : ℝ) :
    lp.single (2 : ENNReal) i a ∈ infiniteOnsiteDomain V := by
  sorry

theorem infiniteOnsiteDomain_finset_sum
    (V : Tile → ℝ) (ψ : TileHilbert Tile) (s : Finset Tile) :
    (∑ i ∈ s, lp.single (2 : ENNReal) i (ψ i)) ∈
      infiniteOnsiteDomain V := by
  sorry

theorem infiniteOnsiteDomain_dense
    (V : Tile → ℝ) :
    Dense (infiniteOnsiteDomain V : Set (TileHilbert Tile)) := by
  sorry

end

-- Independently audited signatures from SpectralGeometry/InfiniteOnsiteEigenvalues.lean
section
theorem infiniteOnsiteEigenvalue_eq_at_nonzero
    (V : Tile → ℝ) (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = eigenvalue • (ψ.1 : TileHilbert Tile))
    (t : Tile) (hψ : ψ.1 t ≠ 0) :
    eigenvalue = V t := by
  sorry

theorem infiniteOnsiteEigenvector_zero_of_potential_ne
    (V : Tile → ℝ) (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = eigenvalue • (ψ.1 : TileHilbert Tile))
    (t : Tile) (hV : V t ≠ eigenvalue) :
    ψ.1 t = 0 := by
  sorry

theorem infiniteOnsiteEigenvalue_lower_bound
    (V : Tile → ℝ) (c : ℝ) (hV : ∀ t, c ≤ V t)
    (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = eigenvalue • (ψ.1 : TileHilbert Tile))
    (hψ : ∃ t, ψ.1 t ≠ 0) :
    c ≤ eigenvalue := by
  sorry

theorem infiniteOnsiteEigenvalue_pos
    (V : Tile → ℝ) (hV : ∀ t, 0 < V t)
    (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = eigenvalue • (ψ.1 : TileHilbert Tile))
    (hψ : ∃ t, ψ.1 t ≠ 0) :
    0 < eigenvalue := by
  sorry

end

-- Independently audited signatures from SpectralGeometry/InfiniteOnsiteSummability.lean
theorem infiniteOnsiteLinearGrowth_positive
    (V : ℕ → ℝ) (hGrowth : ∀ n, ((n + 1 : ℕ) : ℝ) ≤ V n)
    (n : ℕ) : 0 < V n := by
  sorry

theorem infiniteOnsiteLinearGrowth_invSq_summable
    (V : ℕ → ℝ) (hGrowth : ∀ n, ((n + 1 : ℕ) : ℝ) ≤ V n) :
    Summable (fun n : ℕ => 1 / (V n) ^ 2) := by
  sorry

-- Independently audited signatures from SpectralGeometry/InfiniteOnsitePowerGrowth.lean
theorem infiniteOnsitePowerGrowth_invSq_summable
    (V : ℕ → ℝ) (alpha : ℝ) (halpha : (1 / 2 : ℝ) < alpha)
    (hGrowth : ∀ n, (((n + 1 : ℕ) : ℝ) ^ alpha) ≤ V n) :
    Summable (fun n : ℕ => 1 / (V n) ^ 2) := by
  sorry

theorem infiniteOnsitePowerGrowth_positive
    (V : ℕ → ℝ) (alpha : ℝ)
    (hGrowth : ∀ n, (((n + 1 : ℕ) : ℝ) ^ alpha) ≤ V n)
    (n : ℕ) : 0 < V n := by
  sorry

theorem infiniteOnsiteExactPower_not_invSq_summable
    (alpha : ℝ) (halpha : alpha ≤ (1 / 2 : ℝ)) :
    ¬ Summable (fun n : ℕ =>
      1 / (((((n + 1 : ℕ) : ℝ) ^ alpha) ^ 2))) := by
  sorry

end SpectralGeometry
