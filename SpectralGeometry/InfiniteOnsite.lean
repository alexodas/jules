import SpectralGeometry.FiniteStrictPositivity

/-!
# First infinite-dimensional construction: the onsite operator

On an arbitrary (possibly infinite) set of tile labels `Tile`, a state is
a square-summable real amplitude, i.e. an element of ℓ²(Tile).

The onsite energy V(t) is allowed to be UNBOUNDED. Its multiplication
operator therefore has an explicit domain: precisely those square-summable
states for which pointwise multiplication by V remains square-summable.

We prove that this domain is a real linear subspace, construct the onsite
operator as a linear map from the domain to ℓ², and prove its pointwise
action. No local-finiteness, boundedness of V, or finiteness of Tile is
assumed. The pair interaction and ε-perturbation are future additions.

Self-adjointness, density of the domain, compact resolvent, and positivity
of the infinite operator are NOT claimed in this file.
-/

namespace SpectralGeometry

/-- Real square-summable amplitudes on an arbitrary set of tile labels. -/
abbrev TileHilbert (Tile : Type*) : Type _ :=
  lp (fun _ : Tile => ℝ) 2

variable {Tile : Type*}

/-- Natural domain of multiplication by a possibly unbounded potential.
Both the original state and the onsite-multiplied state must lie in ℓ². -/
noncomputable def infiniteOnsiteDomain
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
noncomputable def infiniteOnsiteOperator
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

/-- The operator acts at each tile by multiplying its amplitude by V(t). -/
theorem infiniteOnsiteOperator_apply
    (V : Tile → ℝ) (ψ : infiniteOnsiteDomain V) (t : Tile) :
    infiniteOnsiteOperator V ψ t = V t * ψ.1 t := rfl

/-- Nonnegative individual energies give nonnegative local onsite terms. -/
theorem infiniteOnsiteOperator_local_nonneg
    (V : Tile → ℝ) (hV : ∀ t, 0 ≤ V t)
    (ψ : infiniteOnsiteDomain V) (t : Tile) :
    0 ≤ ψ.1 t * infiniteOnsiteOperator V ψ t := by
  rw [infiniteOnsiteOperator_apply]
  convert mul_nonneg (hV t) (sq_nonneg (ψ.1 t)) using 1 <;> ring

end SpectralGeometry
