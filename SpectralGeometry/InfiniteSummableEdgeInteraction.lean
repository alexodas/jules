import SpectralGeometry.InfiniteBoundedPerturbation
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Countably many summable geometric interactions on an infinite Hilbert space

For a sequence of geometric edges, assume the real edge weights are
absolutely summable. Each geometric edge contributes the positive rank-one
operator w_n |delta_a - delta_b><delta_a - delta_b|. Its operator norm
is bounded by 4 |w_n|. Thus the infinite sum converges in operator norm.

The resulting bounded operator on ℓ²(Tile) is symmetric and has
nonnegative quadratic energy for nonnegative weights. It can be added
to an unbounded onsite operator and a bounded perturbation on the
original dense domain D(V).

The summability of the weights is an explicit hypothesis, not a
property derived from any specific aperiodic tiling. In particular,
constant weights on an infinite lattice are not covered here.
No compact resolvent, self-adjointness, or spectral summability for
the full operator is claimed.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- Any edge vector is uniformly bounded in ℓ² norm by two. -/
theorem infiniteEdgeVector_norm_le_two (a b : Tile) :
    ‖infiniteEdgeVector a b‖ ≤ (2 : ℝ) := by
  have hsingle (t : Tile) :
      ‖(lp.single (2 : ENNReal) t (1 : ℝ) : TileHilbert Tile)‖ = 1 := by
    rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    norm_num
  calc
    ‖infiniteEdgeVector a b‖ ≤
        ‖(lp.single (2 : ENNReal) a (1 : ℝ) : TileHilbert Tile)‖ +
        ‖(lp.single (2 : ENNReal) b (1 : ℝ) : TileHilbert Tile)‖ := by
          unfold infiniteEdgeVector
          exact norm_sub_le _ _
    _ = 2 := by rw [hsingle a, hsingle b]; norm_num

/-- The continuous contribution of an indexed geometric edge. -/
noncomputable def infiniteIndexedEdgeOperator
    (ends : ℕ → Tile × Tile) (w : ℕ → ℝ) (n : ℕ) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  w n • InnerProductSpace.rankOne ℝ
    (infiniteEdgeVector (ends n).1 (ends n).2)
    (infiniteEdgeVector (ends n).1 (ends n).2)

/-- The operator norm of the nth edge is bounded by four times its
absolute weight; this estimate is uniform in its endpoints. -/
theorem infiniteIndexedEdgeOperator_norm_le
    (ends : ℕ → Tile × Tile) (w : ℕ → ℝ) (n : ℕ) :
    ‖infiniteIndexedEdgeOperator ends w n‖ ≤ 4 * ‖w n‖ := by
  let v := infiniteEdgeVector (ends n).1 (ends n).2
  have hv : ‖v‖ ≤ (2 : ℝ) := infiniteEdgeVector_norm_le_two _ _
  have hn : 0 ≤ ‖v‖ := norm_nonneg _
  calc
    ‖infiniteIndexedEdgeOperator ends w n‖ =
        ‖w n‖ * (‖v‖ * ‖v‖) := by
          simp [infiniteIndexedEdgeOperator, v, InnerProductSpace.norm_rankOne]
    _ ≤ ‖w n‖ * 4 := by
      apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      nlinarith
    _ = 4 * ‖w n‖ := by ring

/-- Absolute summability of the edge weights makes the series of
operators summable in operator norm, hence also pointwise on ℓ². -/
theorem infiniteIndexedEdgeOperators_summable
    (ends : ℕ → Tile × Tile) (w : ℕ → ℝ)
    (hw : Summable (fun n => ‖w n‖)) :
    Summable (fun n => infiniteIndexedEdgeOperator ends w n) := by
  apply Summable.of_norm_bounded (hw.mul_left 4)
  intro n
  exact infiniteIndexedEdgeOperator_norm_le ends w n

/-- A true countably infinite-edge interaction operator on ℓ²(Tile).
The edge list may repeat endpoints; no finiteness of Tile is required. -/
noncomputable def infiniteSummableEdgeLaplacian
    (ends : ℕ → Tile × Tile) (w : ℕ → ℝ)
    (_hw : Summable (fun n => ‖w n‖)) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ∑' n, infiniteIndexedEdgeOperator ends w n

/-- Exact bilinear energy of one rank-one geometric edge. -/
theorem infiniteIndexedEdgeOperator_inner
    (ends : ℕ → Tile × Tile) (w : ℕ → ℝ) (n : ℕ)
    (ψ φ : TileHilbert Tile) :
    inner ℝ ψ (infiniteIndexedEdgeOperator ends w n φ) =
      w n *
        (inner ℝ (infiniteEdgeVector (ends n).1 (ends n).2) φ) *
        (inner ℝ (infiniteEdgeVector (ends n).1 (ends n).2) ψ) := by
  let v := infiniteEdgeVector (ends n).1 (ends n).2
  change inner ℝ ψ ((w n * inner ℝ v φ) • v) =
    w n * inner ℝ v φ * inner ℝ v ψ
  rw [real_inner_smul_right, real_inner_comm ψ v]
  ring

/-- Every indexed edge operator is symmetric, independently of weight sign. -/
theorem infiniteIndexedEdgeOperator_symmetric
    (ends : ℕ → Tile × Tile) (w : ℕ → ℝ) (n : ℕ)
    (ψ φ : TileHilbert Tile) :
    inner ℝ ψ (infiniteIndexedEdgeOperator ends w n φ) =
      inner ℝ (infiniteIndexedEdgeOperator ends w n ψ) φ := by
  rw [real_inner_comm φ (infiniteIndexedEdgeOperator ends w n ψ)]
  rw [infiniteIndexedEdgeOperator_inner, infiniteIndexedEdgeOperator_inner]
  ring

/-- For nonnegative weight, every indexed edge has nonnegative energy. -/
theorem infiniteIndexedEdgeOperator_energy_nonneg
    (ends : ℕ → Tile × Tile) (w : ℕ → ℝ) (n : ℕ)
    (hwn : 0 ≤ w n) (ψ : TileHilbert Tile) :
    0 ≤ inner ℝ ψ (infiniteIndexedEdgeOperator ends w n ψ) := by
  rw [infiniteIndexedEdgeOperator_inner]
  convert mul_nonneg hwn
    (sq_nonneg (inner ℝ (infiniteEdgeVector (ends n).1 (ends n).2) ψ))
    using 1 <;> ring

/-- Inner products commute with the countable operator sum, by
operator-norm summability and continuity of evaluation and pairing. -/
theorem infiniteSummableEdgeLaplacian_inner_eq_tsum
    (ends : ℕ → Tile × Tile) (w : ℕ → ℝ)
    (hw : Summable (fun n => ‖w n‖))
    (ψ φ : TileHilbert Tile) :
    inner ℝ ψ (infiniteSummableEdgeLaplacian ends w hw φ) =
      ∑' n, inner ℝ ψ (infiniteIndexedEdgeOperator ends w n φ) := by
  have hOp := infiniteIndexedEdgeOperators_summable ends w hw
  have hState :
      Summable (fun n => infiniteIndexedEdgeOperator ends w n φ) :=
    (ContinuousLinearMap.apply ℝ (TileHilbert Tile) φ).summable hOp
  change inner ℝ ψ ((∑' n, infiniteIndexedEdgeOperator ends w n) φ) = _
  rw [(ContinuousLinearMap.apply ℝ (TileHilbert Tile) φ).map_tsum hOp]
  simpa using (innerSL ℝ ψ).map_tsum hState

/-- The countably infinite interaction has nonnegative finite quadratic
energy on every square-summable state when all weights are nonnegative. -/
theorem infiniteSummableEdgeLaplacian_energy_nonneg
    (ends : ℕ → Tile × Tile) (w : ℕ → ℝ)
    (hw : Summable (fun n => ‖w n‖))
    (hwn : ∀ n, 0 ≤ w n) (ψ : TileHilbert Tile) :
    0 ≤ inner ℝ ψ (infiniteSummableEdgeLaplacian ends w hw ψ) := by
  rw [infiniteSummableEdgeLaplacian_inner_eq_tsum]
  apply tsum_nonneg
  intro n
  exact infiniteIndexedEdgeOperator_energy_nonneg ends w n (hwn n) ψ

/-- The countably infinite interaction operator is symmetric. -/
theorem infiniteSummableEdgeLaplacian_symmetric
    (ends : ℕ → Tile × Tile) (w : ℕ → ℝ)
    (hw : Summable (fun n => ‖w n‖))
    (ψ φ : TileHilbert Tile) :
    inner ℝ ψ (infiniteSummableEdgeLaplacian ends w hw φ) =
      inner ℝ (infiniteSummableEdgeLaplacian ends w hw ψ) φ := by
  rw [real_inner_comm φ (infiniteSummableEdgeLaplacian ends w hw ψ)]
  rw [infiniteSummableEdgeLaplacian_inner_eq_tsum,
    infiniteSummableEdgeLaplacian_inner_eq_tsum]
  apply tsum_congr
  intro n
  exact infiniteIndexedEdgeOperator_symmetric ends w n ψ φ |>.trans
    (real_inner_comm _ _)

/-- The full (onsite + infinitely many summable edges + bounded
perturbation) operator, on the original dense onsite domain. -/
noncomputable def infiniteSummableEdgePerturbedOperator
    (V : Tile → ℝ) (ends : ℕ → Tile × Tile) (w : ℕ → ℝ)
    (hw : Summable (fun n => ‖w n‖))
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ) :
    infiniteOnsiteDomain V →ₗ[ℝ] TileHilbert Tile :=
  infiniteOnsiteOperator V +
    (infiniteSummableEdgeLaplacian ends w hw).toLinearMap.comp
      (infiniteOnsiteDomain V).subtype +
    ε • (P.toLinearMap.comp (infiniteOnsiteDomain V).subtype)

/-- A pointwise identity for the three terms on the common domain. -/
theorem infiniteSummableEdgePerturbedOperator_apply
    (V : Tile → ℝ) (ends : ℕ → Tile × Tile) (w : ℕ → ℝ)
    (hw : Summable (fun n => ‖w n‖))
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (ψ : infiniteOnsiteDomain V) :
    infiniteSummableEdgePerturbedOperator V ends w hw P ε ψ =
      infiniteOnsiteOperator V ψ +
        infiniteSummableEdgeLaplacian ends w hw ψ.1 + ε • P ψ.1 := by
  simp [infiniteSummableEdgePerturbedOperator,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]

/-- For nonnegative onsite energies, weights, and bounded perturbation
quadratic form, the complete infinite-edge operator has nonnegative energy. -/
theorem infiniteSummableEdgePerturbedOperator_energy_nonneg
    (V : Tile → ℝ) (ends : ℕ → Tile × Tile) (w : ℕ → ℝ)
    (hw : Summable (fun n => ‖w n‖))
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hwn : ∀ n, 0 ≤ w n)
    (hP : ∀ ψ : TileHilbert Tile, 0 ≤ inner ℝ ψ (P ψ))
    (hε : 0 ≤ ε) (ψ : infiniteOnsiteDomain V) :
    0 ≤ inner ℝ ψ.1
      (infiniteSummableEdgePerturbedOperator V ends w hw P ε ψ) := by
  rw [infiniteSummableEdgePerturbedOperator_apply]
  simp only [inner_add_right, real_inner_smul_right]
  exact add_nonneg
    (add_nonneg (infiniteOnsiteOperator_energy_nonneg V hV ψ)
      (infiniteSummableEdgeLaplacian_energy_nonneg ends w hw hwn ψ.1))
    (mul_nonneg hε (hP ψ.1))

/-- Symmetry of the full infinite-edge sum given symmetric perturbations. -/
theorem infiniteSummableEdgePerturbedOperator_symmetric
    (V : Tile → ℝ) (ends : ℕ → Tile × Tile) (w : ℕ → ℝ)
    (hw : Summable (fun n => ‖w n‖))
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (ψ φ : infiniteOnsiteDomain V) :
    inner ℝ ψ.1 (infiniteSummableEdgePerturbedOperator V ends w hw P ε φ) =
      inner ℝ (infiniteSummableEdgePerturbedOperator V ends w hw P ε ψ) φ.1 := by
  rw [infiniteSummableEdgePerturbedOperator_apply,
    infiniteSummableEdgePerturbedOperator_apply]
  simp only [inner_add_right, inner_add_left,
    real_inner_smul_right, real_inner_smul_left]
  rw [infiniteOnsiteOperator_symmetric V ψ φ,
    infiniteSummableEdgeLaplacian_symmetric ends w hw ψ.1 φ.1,
    hP ψ.1 φ.1]

end SpectralGeometry
