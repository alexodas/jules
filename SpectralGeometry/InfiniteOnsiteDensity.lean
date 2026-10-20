module

public import SpectralGeometry.InfiniteOnsite

public section

/-!
# Density of the natural domain of the infinite onsite operator

Every configuration supported on finitely many tiles belongs to the
natural domain of multiplication by an arbitrary real onsite potential.
Mathlib shows that finite sums of single-tile states converge to every
state in real ℓ². As a consequence, our domain is dense in ℓ², even
when the onsite potential is unbounded and the set of tiles is infinite.

Density is necessary for the Hilbert-space adjoint construction, but
this file does not yet prove self-adjointness or spectral discreteness.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- A state concentrated on one tile belongs to the natural domain of
onsite multiplication, irrespective of the size of the potential there. -/
theorem infiniteOnsiteDomain_single
    (V : Tile → ℝ) (i : Tile) (a : ℝ) :
    lp.single (2 : ENNReal) i a ∈ infiniteOnsiteDomain V := by
  classical
  have heq :
      (fun t : Tile => V t *
        (lp.single (2 : ENNReal) i a : TileHilbert Tile) t) =
        (fun t : Tile =>
          (lp.single (2 : ENNReal) i (V i * a) : TileHilbert Tile) t) := by
    funext t
    by_cases hti : t = i
    · subst t
      simp
    · simp only [lp.single_apply, Pi.single_eq_of_ne hti, mul_zero]
  have hmem : Memℓp
      (fun t : Tile => V t *
        (lp.single (2 : ENNReal) i a : TileHilbert Tile) t) 2 := by
    rw [heq]
    exact (lp.single (2 : ENNReal) i (V i * a) : TileHilbert Tile).property
  exact hmem

/-- Every finite sum of single-tile states lies in the natural domain. -/
theorem infiniteOnsiteDomain_finset_sum
    (V : Tile → ℝ) (ψ : TileHilbert Tile) (s : Finset Tile) :
    (∑ i ∈ s, lp.single (2 : ENNReal) i (ψ i)) ∈
      infiniteOnsiteDomain V := by
  classical
  apply Submodule.sum_mem
  intro i hi
  exact infiniteOnsiteDomain_single V i (ψ i)

/-- **First density theorem for the infinite geometric program.**
For every (even unbounded) real potential, the natural multiplication
domain is dense in the real square-summable state space. -/
theorem infiniteOnsiteDomain_dense
    (V : Tile → ℝ) :
    Dense (infiniteOnsiteDomain V : Set (TileHilbert Tile)) := by
  classical
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro ψ
  have hsum : HasSum
      (fun i : Tile => lp.single (2 : ENNReal) i (ψ i)) ψ :=
    lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) ψ
  apply mem_closure_of_tendsto hsum
  exact Filter.Eventually.of_forall (fun s : Finset Tile =>
    infiniteOnsiteDomain_finset_sum V ψ s)

end SpectralGeometry
