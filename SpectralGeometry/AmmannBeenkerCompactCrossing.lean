module

public import SpectralGeometry.AmmannBeenkerCompactStates

public section

/-!
# An exact crossing of compact eigenvectors

The intervention acts on the eight neighbors of the origin. Both
eigenvector equations hold on the original infinite natural domain.
The two vectors are independent; exact multiplicity and isolation from
other spectral levels are separate obligations, not conclusions here.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

@[expose] def ringInteraction (t : ℝ) : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  interaction + t • finiteSectorProjection (neighbors origin)

@[expose] def crossingParameter : ℝ := 17 / 16 + 2 * alpha

@[expose] def crossingEnergy : ℝ := 13 / 4 + 2 * alpha

theorem ring_compactA (t : ℝ) :
    onsitePlusBounded potential (ringInteraction t) domainCompactA =
      (35 / 16 + t) • compactA := by
  rw [onsitePlusBounded_apply, onsite_compactA]
  change (2 : ℝ) • compactA +
    (interaction compactA + t • finiteSectorProjection (neighbors origin) compactA) = _
  rw [interaction_compactA, projection_compactA]
  module

theorem ring_compactB (t : ℝ) :
    onsitePlusBounded potential (ringInteraction t) domainCompactB =
      crossingEnergy • compactB := by
  rw [onsitePlusBounded_apply, onsite_compactB]
  change (3 + 2 * alpha) • compactB +
    (interaction compactB + t • finiteSectorProjection (neighbors origin) compactB) = _
  rw [interaction_compactB, projection_compactB]
  dsimp [crossingEnergy]
  module

/-- A certified crossing, with two explicit independent eigenvectors.
This asserts a lower bound on multiplicity, not exact multiplicity two. -/
theorem compact_crossing :
    LinearIndependent ℝ ![compactA, compactB] ∧
      onsitePlusBounded potential (ringInteraction crossingParameter) domainCompactA =
        crossingEnergy • compactA ∧
      onsitePlusBounded potential (ringInteraction crossingParameter) domainCompactB =
        crossingEnergy • compactB := by
  refine ⟨compact_pair_linearIndependent, ?_, ring_compactB _⟩
  rw [ring_compactA]
  congr 1
  dsimp [crossingParameter, crossingEnergy]
  ring

/-- A unit increment of the actual edge joining the two rings. -/
@[expose] def crossingEdge : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  InnerProductSpace.rankOne ℝ
    (infiniteEdgeVector compactSiteA compactSiteB)
    (infiniteEdgeVector compactSiteA compactSiteB)

theorem crossingEdge_apply (x : TileHilbert Vertex) :
    crossingEdge x = (x compactSiteA - x compactSiteB) •
      infiniteEdgeVector compactSiteA compactSiteB := by
  simp [crossingEdge, InnerProductSpace.rankOne_apply, infiniteEdgeVector,
    inner_sub_left, lp.inner_single_left, RCLike.inner_apply]
  module

theorem crossingEdge_dark : crossingEdge (compactA + compactB) = 0 := by
  rw [crossingEdge_apply]
  simp

theorem compact_sum_ne_zero : compactA + compactB ≠ 0 := by
  intro h
  have hh := congrArg (fun x : TileHilbert Vertex => x compactSiteA) h
  simpa using hh

/-- A nonzero eigenvector remains fixed after any real edge-weight change.
This alone does not establish a split spectral pair. -/
theorem crossing_dark_eigenvector (ε : ℝ) :
    onsitePlusBounded potential (ringInteraction crossingParameter + ε • crossingEdge)
      (domainCompactA + domainCompactB) = crossingEnergy • (compactA + compactB) := by
  have ha := compact_crossing.2.1
  have hb := compact_crossing.2.2
  have hbase : onsitePlusBounded potential (ringInteraction crossingParameter)
      (domainCompactA + domainCompactB) = crossingEnergy • (compactA + compactB) := by
    rw [map_add, ha, hb, smul_add]
  rw [onsitePlusBounded_apply] at hbase ⊢
  change infiniteOnsiteOperator potential (domainCompactA + domainCompactB) +
    (ringInteraction crossingParameter (compactA + compactB) +
      ε • crossingEdge (compactA + compactB)) = _
  rw [crossingEdge_dark, smul_zero, add_zero]
  exact hbase

/-- The unit direction in the crossing plane that is affected by the edge. -/
@[expose] def crossingBright : TileHilbert Vertex := (1 / 4 : ℝ) • (compactA - compactB)

@[simp] theorem crossingBright_apply (v : Vertex) :
    crossingBright v = (1 / 4 : ℝ) * (compactA v - compactB v) := rfl

@[expose] def domainCrossingBright : infiniteOnsiteDomain potential :=
  (1 / 4 : ℝ) • (domainCompactA - domainCompactB)

theorem crossingBright_norm_sq : ‖crossingBright‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq]
  have hba : inner ℝ compactB compactA = 0 := by
    rw [real_inner_comm, compactA_inner_compactB]
  simp only [crossingBright, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    compactA_inner_self, compactB_inner_self, compactA_inner_compactB, hba]
  norm_num

theorem crossingEdge_inner (x y : TileHilbert Vertex) :
    inner ℝ x (crossingEdge y) =
      (y compactSiteA - y compactSiteB) * (x compactSiteA - x compactSiteB) := by
  rw [crossingEdge_apply, real_inner_smul_right]
  simp [infiniteEdgeVector, inner_sub_right, lp.inner_single_right, RCLike.inner_apply]

/-- The edge compression in the affected unit direction is exactly 1/4.
This is a matrix element, not an eigenvalue derivative theorem. -/
theorem crossingBright_edge_energy :
    inner ℝ crossingBright (crossingEdge crossingBright) = 1 / 4 := by
  rw [crossingEdge_inner]
  norm_num only [crossingBright_apply, compactA_siteA, compactB_siteA,
    compactA_siteB, compactB_siteB]

/-- Exact Rayleigh response. An estimate for another eigenvalue still
requires a spectral-isolation theorem. -/
theorem crossingBright_energy_response (ε : ℝ) :
    inner ℝ crossingBright
      (onsitePlusBounded potential (ringInteraction crossingParameter + ε • crossingEdge)
        domainCrossingBright) = crossingEnergy + ε / 4 := by
  have hbase : onsitePlusBounded potential (ringInteraction crossingParameter)
      domainCrossingBright = crossingEnergy • crossingBright := by
    simp only [domainCrossingBright, map_smul, map_sub,
      compact_crossing.2.1, compact_crossing.2.2, crossingBright]
    module
  have he : onsitePlusBounded potential (ringInteraction crossingParameter + ε • crossingEdge)
      domainCrossingBright = crossingEnergy • crossingBright + ε • crossingEdge crossingBright := by
    rw [onsitePlusBounded_apply] at hbase ⊢
    change infiniteOnsiteOperator potential domainCrossingBright +
      ringInteraction crossingParameter crossingBright =
        crossingEnergy • crossingBright at hbase
    change infiniteOnsiteOperator potential domainCrossingBright +
      (ringInteraction crossingParameter crossingBright + ε • crossingEdge crossingBright) = _
    rw [← add_assoc, hbase]
  rw [he, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, crossingBright_norm_sq, crossingBright_edge_energy]
  ring

end
end SpectralGeometry.AmmannBeenker
