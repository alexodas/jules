module

public import SpectralGeometry.InfiniteBoundedPerturbation
public import Mathlib.Analysis.InnerProductSpace.l2Space

public section

/-!
# Infinite local matching interactions on ℓ²

A finite collection of involutive permutations of an arbitrary (possibly
infinite) tile set encodes a graph whose degree is at most the number of
permutations: each color gives at most one neighbor to a given tile.

A permutation gives an isometry of real ℓ² by reindexing coordinates.
When it is involutive, the matching Laplacian I-U is symmetric and
nonnegative, with norm at most two.

A finite nonnegative weighted sum of these infinite matchings therefore
has controlled operator norm, nonnegative energy, and symmetry.

This is a rigorous bounded-degree *matching-colorable* graph model.
The decomposition of every bounded-degree graph into such matchings
and tile-dependent weights is NOT established here. More general
bounded-degree Laplacians remain future work.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- Reindexing amplitudes by a bijection preserves square summability
and their Hilbert-space norm, for any (possibly infinite) set of tiles. -/
@[expose] noncomputable def infiniteTileReindex (σ : Tile ≃ Tile) :
    TileHilbert Tile →ₗᵢ[ℝ] TileHilbert Tile where
  toFun := fun ψ => by
    refine ⟨(fun t => ψ (σ t) : PreLp (fun _ : Tile => ℝ)), ?_⟩
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    have hsum : Summable (fun t : Tile => ‖ψ t‖ ^ (2 : ENNReal).toReal) :=
      (memℓp_gen_iff hp).mp ψ.property
    have hsum' :
        Summable (fun t : Tile => ‖ψ (σ t)‖ ^ (2 : ENNReal).toReal) :=
      (σ.summable_iff).mpr hsum
    exact (memℓp_gen_iff hp).mpr hsum'
  map_add' := by
    intro ψ φ
    apply lp.ext
    funext t
    rfl
  map_smul' := by
    intro c ψ
    apply lp.ext
    funext t
    rfl
  norm_map' := by
    intro ψ
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    let φ : TileHilbert Tile :=
      ⟨(fun t => ψ (σ t) : PreLp (fun _ : Tile => ℝ)),
        (memℓp_gen_iff hp).mpr
          ((σ.summable_iff).mpr ((memℓp_gen_iff hp).mp ψ.property))⟩
    change ‖φ‖ = ‖ψ‖
    have hsum :
        (∑' t, ‖φ t‖ ^ (2 : ENNReal).toReal) =
          (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal) := by
      change (∑' t, ‖ψ (σ t)‖ ^ (2 : ENNReal).toReal) =
        (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal)
      exact σ.tsum_eq (fun t : Tile => ‖ψ t‖ ^ (2 : ENNReal).toReal)
    calc
      ‖φ‖ =
          (∑' t, ‖φ t‖ ^ (2 : ENNReal).toReal) ^
            (1 / (2 : ENNReal).toReal) :=
        lp.norm_eq_tsum_rpow hp φ
      _ = (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal) ^
            (1 / (2 : ENNReal).toReal) := by rw [hsum]
      _ = ‖ψ‖ := (lp.norm_eq_tsum_rpow hp ψ).symm

/-- The matching permutation acts by composing a state with its
bijection of tile labels. -/
theorem infiniteTileReindex_apply (σ : Tile ≃ Tile)
    (ψ : TileHilbert Tile) (t : Tile) :
    infiniteTileReindex σ ψ t = ψ (σ t) := rfl

/-- Any reindexing is norm preserving. -/
theorem infiniteTileReindex_norm (σ : Tile ≃ Tile)
    (ψ : TileHilbert Tile) :
    ‖infiniteTileReindex σ ψ‖ = ‖ψ‖ :=
  (infiniteTileReindex σ).norm_map ψ

/-- An involutive reindexing is symmetric in the real ℓ² inner product. -/
theorem infiniteTileReindex_symmetric (σ : Tile ≃ Tile)
    (hσ : ∀ t, σ (σ t) = t)
    (ψ φ : TileHilbert Tile) :
    inner ℝ ψ (infiniteTileReindex σ φ) =
      inner ℝ (infiniteTileReindex σ ψ) φ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  change (∑' t, inner ℝ (ψ t) (φ (σ t))) =
    (∑' t, inner ℝ (ψ (σ t)) (φ t))
  calc
    (∑' t, inner ℝ (ψ t) (φ (σ t))) =
      ∑' t, inner ℝ (ψ (σ t)) (φ (σ (σ t))) := by
        exact (σ.tsum_eq (fun t => inner ℝ (ψ t) (φ (σ t)))).symm
    _ = ∑' t, inner ℝ (ψ (σ t)) (φ t) := by
      apply tsum_congr
      intro t
      rw [hσ]

/-- The bounded Laplacian of one infinite matching: L = I - U. -/
@[expose] noncomputable def infiniteMatchingLaplacian (σ : Tile ≃ Tile) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ContinuousLinearMap.id ℝ (TileHilbert Tile) -
    (infiniteTileReindex σ).toContinuousLinearMap

/-- Local action of one matching: amplitude minus its neighbor. -/
theorem infiniteMatchingLaplacian_apply (σ : Tile ≃ Tile)
    (ψ : TileHilbert Tile) (t : Tile) :
    infiniteMatchingLaplacian σ ψ t = ψ t - ψ (σ t) := by
  simp [infiniteMatchingLaplacian, infiniteTileReindex_apply]

/-- Each infinite matching Laplacian has operator norm at most two. -/
theorem infiniteMatchingLaplacian_norm_le_two (σ : Tile ≃ Tile) :
    ‖infiniteMatchingLaplacian σ‖ ≤ (2 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro ψ
  change ‖ψ - infiniteTileReindex σ ψ‖ ≤ 2 * ‖ψ‖
  calc
    ‖ψ - infiniteTileReindex σ ψ‖ ≤
        ‖ψ‖ + ‖infiniteTileReindex σ ψ‖ := norm_sub_le _ _
    _ = 2 * ‖ψ‖ := by rw [infiniteTileReindex_norm]; ring

/-- An infinite matching Laplacian is nonnegative in quadratic energy,
regardless of the size of the infinite tile set. -/
theorem infiniteMatchingLaplacian_energy_nonneg
    (σ : Tile ≃ Tile) (ψ : TileHilbert Tile) :
    0 ≤ inner ℝ ψ (infiniteMatchingLaplacian σ ψ) := by
  have hc : inner ℝ ψ (infiniteTileReindex σ ψ) ≤ ‖ψ‖ ^ 2 := by
    calc
      inner ℝ ψ (infiniteTileReindex σ ψ) ≤
          ‖ψ‖ * ‖infiniteTileReindex σ ψ‖ :=
        real_inner_le_norm _ _
      _ = ‖ψ‖ ^ 2 := by rw [infiniteTileReindex_norm]; ring
  change 0 ≤ inner ℝ ψ (ψ - infiniteTileReindex σ ψ)
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  linarith

/-- Symmetry of an infinite matching Laplacian for involutive adjacency. -/
theorem infiniteMatchingLaplacian_symmetric
    (σ : Tile ≃ Tile) (hσ : ∀ t, σ (σ t) = t)
    (ψ φ : TileHilbert Tile) :
    inner ℝ ψ (infiniteMatchingLaplacian σ φ) =
      inner ℝ (infiniteMatchingLaplacian σ ψ) φ := by
  change inner ℝ ψ (φ - infiniteTileReindex σ φ) =
    inner ℝ (ψ - infiniteTileReindex σ ψ) φ
  rw [inner_sub_right, inner_sub_left,
    infiniteTileReindex_symmetric σ hσ ψ φ]

end SpectralGeometry
