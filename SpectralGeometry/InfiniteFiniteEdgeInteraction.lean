import SpectralGeometry.InfiniteOnsiteDensity
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Finite edge interactions on an infinite square-summable state space

Even when the set of tiles is infinite, every individual geometric
edge defines an everywhere-defined linear operator on ℓ²(Tile).
A finite family of edges gives an operator acting in the SAME infinite
Hilbert space as our unbounded onsite operator.

Each nonnegative-weight edge has nonnegative quadratic energy; its
contribution is symmetric with respect to the ℓ² real inner product.
A finite sum of such edges inherits these two properties.

This is a first, genuinely infinite-state-space interaction model,
NOT a construction for an infinite set of interacting edges. It does
not prove boundedness, self-adjointness, or spectral summability.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- The real ℓ² vector of a geometric edge (a,b). -/
noncomputable def infiniteEdgeVector (a b : Tile) : TileHilbert Tile :=
  lp.single (2 : ENNReal) a (1 : ℝ) -
    lp.single (2 : ENNReal) b (1 : ℝ)

/-- A geometric edge Laplacian on the infinite Hilbert space.
It sends ψ to w(ψ(a)-ψ(b))(δₐ-δᵦ). -/
noncomputable def infiniteEdgeLaplacian (a b : Tile) (w : ℝ) :
    TileHilbert Tile →ₗ[ℝ] TileHilbert Tile where
  toFun := fun ψ => (w * (ψ a - ψ b)) • infiniteEdgeVector a b
  map_add' := by
    intro ψ φ
    change (w * ((ψ + φ) a - (ψ + φ) b)) • infiniteEdgeVector a b =
      (w * (ψ a - ψ b)) • infiniteEdgeVector a b +
        (w * (φ a - φ b)) • infiniteEdgeVector a b
    have h :
        w * ((ψ + φ) a - (ψ + φ) b) =
          w * (ψ a - ψ b) + w * (φ a - φ b) := by
      simp only [lp.coeFn_add, Pi.add_apply]
      ring
    rw [h, add_smul]
  map_smul' := by
    intro r ψ
    change (w * ((r • ψ) a - (r • ψ) b)) • infiniteEdgeVector a b =
      r • ((w * (ψ a - ψ b)) • infiniteEdgeVector a b)
    have h :
        w * ((r • ψ) a - (r • ψ) b) =
          r * (w * (ψ a - ψ b)) := by
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h, mul_smul]

/-- The ℓ² inner product of an edge contribution depends only on
the difference of amplitudes at its two endpoints. -/
theorem infiniteEdgeLaplacian_inner
    (a b : Tile) (w : ℝ) (ψ φ : TileHilbert Tile) :
    ⟪ψ, infiniteEdgeLaplacian a b w φ⟫_ℝ =
      w * (φ a - φ b) * (ψ a - ψ b) := by
  change ⟪ψ, (w * (φ a - φ b)) • infiniteEdgeVector a b⟫_ℝ = _
  rw [real_inner_smul_right]
  have he : ⟪ψ, infiniteEdgeVector a b⟫_ℝ = ψ a - ψ b := by
    simp [infiniteEdgeVector, inner_sub_right, lp.inner_single_right,
      RCLike.inner_apply]
  rw [he]
  ring

/-- An individual undirected edge interaction is symmetric. -/
theorem infiniteEdgeLaplacian_symmetric
    (a b : Tile) (w : ℝ) (ψ φ : TileHilbert Tile) :
    ⟪ψ, infiniteEdgeLaplacian a b w φ⟫_ℝ =
      ⟪infiniteEdgeLaplacian a b w ψ, φ⟫_ℝ := by
  rw [real_inner_comm]
  rw [infiniteEdgeLaplacian_inner, infiniteEdgeLaplacian_inner]
  ring

/-- Nonnegative weights give nonnegative energy on any ℓ² state. -/
theorem infiniteEdgeLaplacian_energy_nonneg
    (a b : Tile) (w : ℝ) (hw : 0 ≤ w) (ψ : TileHilbert Tile) :
    0 ≤ ⟪ψ, infiniteEdgeLaplacian a b w ψ⟫_ℝ := by
  rw [infiniteEdgeLaplacian_inner]
  convert mul_nonneg hw (sq_nonneg (ψ a - ψ b)) using 1 <;> ring

/-- A finite collection of weighted edges, possibly in an infinite
tile set, acts as a linear map ℓ²(Tile) → ℓ²(Tile). -/
noncomputable def infiniteFiniteEdgeLaplacian
    (edges : Finset (Tile × Tile)) (w : Tile × Tile → ℝ) :
    TileHilbert Tile →ₗ[ℝ] TileHilbert Tile :=
  ∑ e ∈ edges, infiniteEdgeLaplacian e.1 e.2 (w e)

/-- The quadratic energy of a finite edge interaction is nonnegative
whenever every active edge carries a nonnegative weight. -/
theorem infiniteFiniteEdgeLaplacian_energy_nonneg
    (edges : Finset (Tile × Tile)) (w : Tile × Tile → ℝ)
    (hw : ∀ e ∈ edges, 0 ≤ w e) (ψ : TileHilbert Tile) :
    0 ≤ ⟪ψ, infiniteFiniteEdgeLaplacian edges w ψ⟫_ℝ := by
  simp only [infiniteFiniteEdgeLaplacian, LinearMap.sum_apply, inner_sum]
  apply Finset.sum_nonneg
  intro e he
  exact infiniteEdgeLaplacian_energy_nonneg e.1 e.2 (w e) (hw e he) ψ

/-- Any finite collection of geometric edges remains symmetric. -/
theorem infiniteFiniteEdgeLaplacian_symmetric
    (edges : Finset (Tile × Tile)) (w : Tile × Tile → ℝ)
    (ψ φ : TileHilbert Tile) :
    ⟪ψ, infiniteFiniteEdgeLaplacian edges w φ⟫_ℝ =
      ⟪infiniteFiniteEdgeLaplacian edges w ψ, φ⟫_ℝ := by
  simp only [infiniteFiniteEdgeLaplacian, LinearMap.sum_apply,
    inner_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro e he
  exact infiniteEdgeLaplacian_symmetric e.1 e.2 (w e) ψ φ

end SpectralGeometry
