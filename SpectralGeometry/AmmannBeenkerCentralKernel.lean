module

public import SpectralGeometry.AmmannBeenkerCentralPatch
public import SpectralGeometry.AmmannBeenkerCompactCrossing

public section

/-!
# The crossing kernel of the exact central block

The principal block retains the full graph degrees, including the diagonal
contribution of edges to the exterior. Its zero space at the crossing is
parametrized by the two compact rings. The last theorem transfers this to
natural-domain eigenvectors whose support is contained in the central sector.
It does not assume or prove that every crossing eigenvector has that support.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- The actual shifted diagonal of the confined crossing operator. -/
@[expose] def centralCrossingDiagonal (i : Fin 17) : ℝ :=
  potential (centralVertex i) + ((neighbors (centralVertex i)).card : ℝ) / 16 +
    (if centralVertex i ∈ neighbors origin then crossingParameter else 0) - crossingEnergy

/-- The principal central block of `H + t* P_A - E*`, with the full vertex degrees.
Deleting the exterior neighbors from the degree would define a different operator. -/
@[expose] def centralCrossingBlock (x : Fin 17 → ℝ) (i : Fin 17) : ℝ :=
  centralCrossingDiagonal i * x i - (1 / 16 : ℝ) *
    ∑ j : Fin 17, if Adjacent (centralVertex i) (centralVertex j) then x j else 0

/-- The two alternating ring amplitudes, with zero amplitude at the origin. -/
@[expose] def centralCompactCoordinates (a b : ℝ) : Fin 17 → ℝ :=
  ![0, a, -a, a, -a, a, -a, a, -a, b, -b, b, -b, b, -b, b, -b]

theorem centralCrossingDiagonal_origin :
    centralCrossingDiagonal 0 = 3 / 2 - crossingEnergy := by
  have hn : origin ∉ neighbors origin := by
    intro h
    exact adjacent_irrefl origin ((mem_neighbors_iff _ _).1 h)
  unfold centralCrossingDiagonal
  rw [centralVertex_zero, origin_neighbors_card, if_neg hn]
  norm_num [potential, position, origin]

theorem centralCrossingDiagonal_first (i : Fin 8) :
    centralCrossingDiagonal ⟨i.val + 1, by omega⟩ = 0 := by
  have hn : firstRingVertex i ∈ neighbors origin :=
    (mem_neighbors_iff _ _).2 (origin_adjacent_firstRing i)
  change potential (firstRingVertex i) + ((neighbors (firstRingVertex i)).card : ℝ) / 16 +
    (if firstRingVertex i ∈ neighbors origin then crossingParameter else 0) - crossingEnergy = 0
  rw [firstRing_degree, if_pos hn]
  norm_num [potential, firstRing_norm, crossingParameter, crossingEnergy] <;> ring

theorem centralCrossingDiagonal_second (i : Fin 8) :
    centralCrossingDiagonal ⟨i.val + 9, by omega⟩ = 0 := by
  have hn : secondRingVertex i ∉ neighbors origin := by
    intro h
    exact origin_not_adjacent_secondRing i ((mem_neighbors_iff _ _).1 h)
  change potential (secondRingVertex i) + ((neighbors (secondRingVertex i)).card : ℝ) / 16 +
    (if secondRingVertex i ∈ neighbors origin then crossingParameter else 0) - crossingEnergy = 0
  rw [secondRing_degree, if_neg hn]
  norm_num [potential, secondRing_norm_sq, crossingEnergy] <;> ring

theorem centralCrossingDiagonal_values :
    centralCrossingDiagonal =
      ![3 / 2 - crossingEnergy, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext i
  fin_cases i
  · exact centralCrossingDiagonal_origin
  · exact centralCrossingDiagonal_first 0
  · exact centralCrossingDiagonal_first 1
  · exact centralCrossingDiagonal_first 2
  · exact centralCrossingDiagonal_first 3
  · exact centralCrossingDiagonal_first 4
  · exact centralCrossingDiagonal_first 5
  · exact centralCrossingDiagonal_first 6
  · exact centralCrossingDiagonal_first 7
  · exact centralCrossingDiagonal_second 0
  · exact centralCrossingDiagonal_second 1
  · exact centralCrossingDiagonal_second 2
  · exact centralCrossingDiagonal_second 3
  · exact centralCrossingDiagonal_second 4
  · exact centralCrossingDiagonal_second 5
  · exact centralCrossingDiagonal_second 6
  · exact centralCrossingDiagonal_second 7

set_option maxHeartbeats 6000000 in
/-- The complete central adjacency action, in the verified vertex indexing. -/
theorem central_neighbor_sum (x : Fin 17 → ℝ) :
    (fun i : Fin 17 =>
      ∑ j : Fin 17, if Adjacent (centralVertex i) (centralVertex j) then x j else 0) =
    ![x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8,
      x 0 + x 9 + x 16,
      x 0 + x 10 + x 9,
      x 0 + x 11 + x 10,
      x 0 + x 12 + x 11,
      x 0 + x 13 + x 12,
      x 0 + x 14 + x 13,
      x 0 + x 15 + x 14,
      x 0 + x 16 + x 15,
      x 1 + x 2, x 2 + x 3, x 3 + x 4, x 4 + x 5,
      x 5 + x 6, x 6 + x 7, x 7 + x 8, x 8 + x 1] := by
  funext i
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ, Adjacent, centralVertex_val, centralLift,
      basis, Fin.exists_fin_succ, funext_iff, Fin.forall_fin_succ,
      Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply] <;> ring

theorem centralCrossingBlock_values (x : Fin 17 → ℝ) :
    centralCrossingBlock x =
    ![(3 / 2 - crossingEnergy) * x 0 -
        (x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8) / 16,
      -(x 0 + x 9 + x 16) / 16,
      -(x 0 + x 10 + x 9) / 16,
      -(x 0 + x 11 + x 10) / 16,
      -(x 0 + x 12 + x 11) / 16,
      -(x 0 + x 13 + x 12) / 16,
      -(x 0 + x 14 + x 13) / 16,
      -(x 0 + x 15 + x 14) / 16,
      -(x 0 + x 16 + x 15) / 16,
      -(x 1 + x 2) / 16, -(x 2 + x 3) / 16,
      -(x 3 + x 4) / 16, -(x 4 + x 5) / 16,
      -(x 5 + x 6) / 16, -(x 6 + x 7) / 16,
      -(x 7 + x 8) / 16, -(x 8 + x 1) / 16] := by
  funext i
  change centralCrossingDiagonal i * x i - (1 / 16 : ℝ) *
    (fun k : Fin 17 =>
      ∑ j : Fin 17, if Adjacent (centralVertex k) (centralVertex j) then x j else 0) i = _
  rw [centralCrossingDiagonal_values, central_neighbor_sum]
  fin_cases i <;> norm_num <;> ring

theorem centralCompactCoordinates_injective :
    Function.Injective (fun p : ℝ × ℝ => centralCompactCoordinates p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have ha := congrFun h 1
  have hb := congrFun h 9
  norm_num [centralCompactCoordinates] at ha hb
  exact Prod.ext ha hb

theorem centralCompactCoordinates_decomposition (a b : ℝ) :
    centralCompactCoordinates a b =
      a • centralCompactCoordinates 1 0 + b • centralCompactCoordinates 0 1 := by
  funext i
  fin_cases i <;>
    norm_num [centralCompactCoordinates, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem centralCompactCoordinates_mem_kernel (a b : ℝ) :
    centralCrossingBlock (centralCompactCoordinates a b) = 0 := by
  rw [centralCrossingBlock_values]
  funext i
  fin_cases i <;> norm_num [centralCompactCoordinates] <;> ring

set_option maxHeartbeats 1000000 in
/-- All central null vectors have two freely chosen alternating ring amplitudes. -/
theorem centralCrossingBlock_kernel_representation (x : Fin 17 → ℝ)
    (hx : centralCrossingBlock x = 0) :
    x = centralCompactCoordinates (x 1) (x 9) := by
  rw [centralCrossingBlock_values] at hx
  have h0 := congrFun hx 0
  have h2 := congrFun hx 2
  have h3 := congrFun hx 3
  have h4 := congrFun hx 4
  have h5 := congrFun hx 5
  have h6 := congrFun hx 6
  have h7 := congrFun hx 7
  have h8 := congrFun hx 8
  have h9 := congrFun hx 9
  have h10 := congrFun hx 10
  have h11 := congrFun hx 11
  have h12 := congrFun hx 12
  have h13 := congrFun hx 13
  have h14 := congrFun hx 14
  have h15 := congrFun hx 15
  norm_num at h0 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  have hs : x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 = 0 := by
    linarith only [h9, h10, h11, h12, h13, h14, h15]
  have hp : (3 / 2 - crossingEnergy) * x 0 = 0 := by
    linarith only [h0, hs]
  have hc : (3 / 2 : ℝ) - crossingEnergy ≠ 0 := by
    have ha := alpha_bounds.1
    dsimp [crossingEnergy]
    linarith
  have hz : x 0 = 0 := (mul_eq_zero.mp hp).resolve_left hc
  funext i
  fin_cases i <;> norm_num [centralCompactCoordinates] <;>
    linarith only [hz, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

/-- An exact parametrization, rather than only two examples of null vectors. -/
theorem centralCrossingBlock_kernel_iff (x : Fin 17 → ℝ) :
    centralCrossingBlock x = 0 ↔ x = centralCompactCoordinates (x 1) (x 9) := by
  constructor
  · exact centralCrossingBlock_kernel_representation x
  · intro h
    rw [h]
    exact centralCompactCoordinates_mem_kernel _ _

set_option maxHeartbeats 1000000 in
theorem compactA_centralCoordinates :
    (fun i : Fin 17 => compactA (centralVertex i)) = centralCompactCoordinates 1 0 := by
  funext i
  fin_cases i <;>
    norm_num [compactA, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
      latticeSingle_apply, centralVertex_val, centralLift, centralCompactCoordinates,
      funext_iff, Fin.forall_fin_succ]

set_option maxHeartbeats 1000000 in
theorem compactB_centralCoordinates :
    (fun i : Fin 17 => compactB (centralVertex i)) = centralCompactCoordinates 0 1 := by
  funext i
  fin_cases i <;>
    norm_num [compactB, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
      latticeSingle_apply, centralVertex_val, centralLift, centralCompactCoordinates,
      funext_iff, Fin.forall_fin_succ]

/-- For a centrally supported vector, the full neighbor sum equals the finite indexed sum. -/
theorem neighbors_sum_of_sector_support (x : TileHilbert Vertex)
    (hx : ∀ w : Vertex, w ∉ sector → x w = 0) (v : Vertex) :
    (∑ w ∈ neighbors v, x w) =
      ∑ j : Fin 17, if Adjacent v (centralVertex j) then x (centralVertex j) else 0 := by
  have hs : (∑ w ∈ neighbors v, x w) = ∑ w ∈ neighbors v ∩ sector, x w := by
    symm
    apply Finset.sum_subset
    · intro w hw
      exact (Finset.mem_inter.mp hw).1
    · intro w hw hn
      exact hx w (fun h => hn (Finset.mem_inter.mpr ⟨hw, h⟩))
  have hi : neighbors v ∩ sector = sector.filter (Adjacent v) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_filter, mem_neighbors_iff]
    exact and_comm
  rw [hs, hi, Finset.sum_filter, sector_eq_centralPatch, centralPatch, Finset.sum_image]
  intro i _ j _ h
  exact centralVertex_injective h

/-- Coordinate formula with the full degree and the actual first-ring intervention. -/
theorem crossingOperator_coordinate (x : infiniteOnsiteDomain potential) (v : Vertex) :
    onsitePlusBounded potential (ringInteraction crossingParameter) x v =
      potential v * x.1 v + (1 / 16 : ℝ) *
        (((neighbors v).card : ℝ) * x.1 v - ∑ w ∈ neighbors v, x.1 w) +
        (if v ∈ neighbors origin then crossingParameter else 0) * x.1 v := by
  rw [onsitePlusBounded_apply]
  change potential v * x.1 v +
    (interaction x.1 v + crossingParameter * (finiteSectorProjection (neighbors origin) x.1) v) = _
  rw [interaction_apply, finiteSectorProjection_apply, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  split_ifs <;> ring

/-- The finite block is the actual shifted operator on centrally supported domain vectors. -/
theorem centralCrossingBlock_restriction (x : infiniteOnsiteDomain potential)
    (hx : ∀ v : Vertex, v ∉ sector → x.1 v = 0) :
    centralCrossingBlock (fun i => x.1 (centralVertex i)) =
      (fun i => onsitePlusBounded potential (ringInteraction crossingParameter) x (centralVertex i) -
        crossingEnergy * x.1 (centralVertex i)) := by
  funext i
  rw [crossingOperator_coordinate, neighbors_sum_of_sector_support x.1 hx]
  unfold centralCrossingBlock centralCrossingDiagonal
  ring

/-- Every crossing eigenvector supported in the central sector lies in the known compact plane.
The support hypothesis is explicit; excluding exterior mass remains a separate obligation. -/
theorem crossing_eigenvector_of_central_support (x : infiniteOnsiteDomain potential)
    (he : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      crossingEnergy • (x : TileHilbert Vertex))
    (hs : ∀ v : Vertex, v ∉ sector → x.1 v = 0) :
    (x : TileHilbert Vertex) =
      x.1 (centralVertex 1) • compactA + x.1 (centralVertex 9) • compactB := by
  have hk : centralCrossingBlock (fun i => x.1 (centralVertex i)) = 0 := by
    rw [centralCrossingBlock_restriction x hs]
    funext i
    have h := congrArg (fun y : TileHilbert Vertex => y (centralVertex i)) he
    change onsitePlusBounded potential (ringInteraction crossingParameter) x (centralVertex i) =
      crossingEnergy * x.1 (centralVertex i) at h
    change onsitePlusBounded potential (ringInteraction crossingParameter) x (centralVertex i) -
      crossingEnergy * x.1 (centralVertex i) = 0
    linarith only [h]
  have hr := centralCrossingBlock_kernel_representation (fun i => x.1 (centralVertex i)) hk
  apply lp.ext
  funext v
  change x.1 v = x.1 (centralVertex 1) * compactA v + x.1 (centralVertex 9) * compactB v
  by_cases hv : v ∈ sector
  · rw [sector_eq_centralPatch] at hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    rw [show compactA (centralVertex i) = centralCompactCoordinates 1 0 i from
      congrFun compactA_centralCoordinates i]
    rw [show compactB (centralVertex i) = centralCompactCoordinates 0 1 i from
      congrFun compactB_centralCoordinates i]
    rw [show x.1 (centralVertex i) =
      centralCompactCoordinates (x.1 (centralVertex 1)) (x.1 (centralVertex 9)) i from congrFun hr i]
    exact congrFun (centralCompactCoordinates_decomposition
      (x.1 (centralVertex 1)) (x.1 (centralVertex 9))) i
  · have ha : compactA v = 0 := compactA_eq_zero_of_not_ring v (by
      intro i h
      apply hv
      rw [h]
      exact firstRing_mem_sector i)
    have hb : compactB v = 0 := compactB_eq_zero_of_not_ring v (by
      intro i h
      apply hv
      rw [h]
      exact secondRing_mem_sector i)
    rw [hs v hv, ha, hb]
    ring

end
end SpectralGeometry.AmmannBeenker
