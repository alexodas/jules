module

public import SpectralGeometry.AmmannBeenkerRadialGap
public import SpectralGeometry.AmmannBeenkerCompactStates

public section

/-!
# The exact central seventeen-vertex patch

The radius-two sector consists of the origin and the two compact rings.
This supplies a finite indexing for a later central-block certificate;
it does not identify the complete crossing eigenspace or prove a gap.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Origin, first ring, then second ring, each in cyclic order. -/
@[expose] def centralLift (i : Fin 17) : Lattice :=
  ![![0, 0, 0, 0],
    ![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1],
    ![-1, 0, 0, 0],
    ![0, -1, 0, 0],
    ![0, 0, -1, 0],
    ![0, 0, 0, -1],
    ![1, 1, 0, 0],
    ![0, 1, 1, 0],
    ![0, 0, 1, 1],
    ![-1, 0, 0, 1],
    ![-1, -1, 0, 0],
    ![0, -1, -1, 0],
    ![0, 0, -1, -1],
    ![1, 0, 0, -1]] i

set_option maxHeartbeats 3000000 in
theorem centralLift_injective : Function.Injective centralLift := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl | norm_num [centralLift, funext_iff, Fin.forall_fin_succ] at h

theorem centralLift_admitted (i : Fin 17) : Admitted (centralLift i) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  fin_cases i <;> norm_num [centralLift, Admitted, Window, internal, abs_lt]
  all_goals repeat' constructor
  all_goals linarith

theorem centralLift_radius (i : Fin 17) : ‖physical (centralLift i)‖ ≤ 2 := by
  have hs : ‖physical (centralLift i)‖ ^ 2 ≤ 4 := by
    have ha := alpha_sq
    have hu := alpha_bounds.2
    fin_cases i <;> norm_num [centralLift, physical, Complex.sq_norm, Complex.normSq_apply]
    all_goals nlinarith
  nlinarith [norm_nonneg (physical (centralLift i))]

@[expose] def centralLifts : Finset Lattice := Finset.univ.image centralLift

theorem centralLifts_card : centralLifts.card = 17 := by
  rw [centralLifts, Finset.card_image_of_injective _ centralLift_injective]
  simp

theorem centralLifts_admitted {n : Lattice} (hn : n ∈ centralLifts) : Admitted n := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact centralLift_admitted i

theorem centralLifts_radius {n : Lattice} (hn : n ∈ centralLifts) : ‖physical n‖ ≤ 2 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact centralLift_radius i

set_option maxHeartbeats 6000000 in
/-- Every admitted point of radius at most two belongs to the explicit list.
The joint norm identity bounds the integer lift; the remaining finite cases
are checked by Lean arithmetic. -/
theorem small_physical_mem_centralLifts {n : Lattice} (hn : Admitted n)
    (hr : ‖physical n‖ ≤ 2) : n ∈ centralLifts := by
  have ha := alpha_sq
  have hal := alpha_bounds.1
  have hau := alpha_bounds.2
  have hi := internal_norm_sq_lt_two hn
  have hj := joint_norm_identity n
  have hs : ‖physical n‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (physical n)]
  have hsum : (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 +
      (n 2 : ℝ) ^ 2 + (n 3 : ℝ) ^ 2 < 3 := by nlinarith
  have h0 := sq_nonneg (n 0 : ℝ)
  have h1 := sq_nonneg (n 1 : ℝ)
  have h2 := sq_nonneg (n 2 : ℝ)
  have h3 := sq_nonneg (n 3 : ℝ)
  have hc (i : Fin 4) : -1 ≤ n i ∧ n i ≤ 1 := by
    have hsq : (n i : ℝ) ^ 2 < 4 := by
      fin_cases i <;> simp only [Fin.reduceFinMk] <;> nlinarith
    have hh : (-2 : ℝ) < n i ∧ (n i : ℝ) < 2 := by
      constructor <;> nlinarith
    have hh' : (-2 : ℤ) < n i ∧ n i < 2 := by exact_mod_cast hh
    omega
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  have hc3 := hc 3
  generalize hn0 : n 0 = a at *
  generalize hn1 : n 1 = b at *
  generalize hn2 : n 2 = c at *
  generalize hn3 : n 3 = d at *
  have he : n = ![a, b, c, d] := by
    funext i
    fin_cases i <;> simpa using (by assumption)
  rw [he] at hn hs ⊢
  clear hi hj hc hr h0 h1 h2 h3
  rcases hc0 with ⟨ha0, ha1⟩
  rcases hc1 with ⟨hb0, hb1⟩
  rcases hc2 with ⟨hc0, hc1⟩
  rcases hc3 with ⟨hd0, hd1⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d
  all_goals norm_num at hsum
  all_goals norm_num [Admitted, Window, internal, abs_lt] at hn
  all_goals norm_num [physical, Complex.sq_norm, Complex.normSq_apply] at hs
  all_goals norm_num [centralLifts, Finset.mem_image, centralLift,
    Fin.exists_fin_succ, funext_iff, Fin.forall_fin_succ]
  all_goals nlinarith [le_abs_self alpha]

/-- The complete list of admitted points in the radius-two disk. -/
theorem mem_centralLifts_iff (n : Lattice) :
    n ∈ centralLifts ↔ Admitted n ∧ ‖physical n‖ ≤ 2 := by
  exact ⟨fun h => ⟨centralLifts_admitted h, centralLifts_radius h⟩,
    fun h => small_physical_mem_centralLifts h.1 h.2⟩

/-- A finite indexing of every vertex in the central sector. -/
@[expose] def centralVertex (i : Fin 17) : Vertex :=
  latticeVertex (centralLift i) (centralLift_admitted i)

@[simp] theorem centralVertex_val (i : Fin 17) :
    (centralVertex i).val = centralLift i := rfl

theorem centralVertex_injective : Function.Injective centralVertex := by
  intro i j h
  apply centralLift_injective
  simpa only [centralVertex_val] using congrArg (fun v : Vertex => v.val) h

theorem centralVertex_zero : centralVertex 0 = origin := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

@[expose] def centralPatch : Finset Vertex := Finset.univ.image centralVertex

theorem centralPatch_card : centralPatch.card = 17 := by
  rw [centralPatch, Finset.card_image_of_injective _ centralVertex_injective]
  simp

theorem mem_centralPatch (v : Vertex) :
    v ∈ centralPatch ↔ v.val ∈ centralLifts := by
  unfold centralPatch centralLifts
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    simpa only [centralVertex_val] using congrArg (fun w : Vertex => w.val) hi
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    exact Subtype.ext hi

/-- The existing sector is exactly the origin and the two eight-site rings. -/
theorem sector_eq_centralPatch : sector = centralPatch := by
  ext v
  rw [mem_sector, mem_centralPatch]
  change ‖physical v.val‖ ≤ 2 ↔ v.val ∈ centralLifts
  exact ⟨small_physical_mem_centralLifts v.property, centralLifts_radius⟩

theorem sector_card : sector.card = 17 := by
  rw [sector_eq_centralPatch, centralPatch_card]

/-- The unit-radius ring, indexed cyclically. -/
@[expose] def firstRingVertex (i : Fin 8) : Vertex :=
  centralVertex ⟨i.val + 1, by omega⟩

/-- The second compact ring, in the same cyclic ordering. -/
@[expose] def secondRingVertex (i : Fin 8) : Vertex :=
  centralVertex ⟨i.val + 9, by omega⟩

theorem firstRing_norm (i : Fin 8) : ‖position (firstRingVertex i)‖ = 1 := by
  have hs : ‖position (firstRingVertex i)‖ ^ 2 = 1 := by
    fin_cases i <;> norm_num [position, firstRingVertex, centralVertex_val,
      centralLift, physical, Complex.sq_norm, Complex.normSq_apply]
    all_goals nlinarith [alpha_sq]
  nlinarith [norm_nonneg (position (firstRingVertex i))]

theorem secondRing_norm_sq (i : Fin 8) :
    ‖position (secondRingVertex i)‖ ^ 2 = 2 + 2 * alpha := by
  fin_cases i <;> norm_num [position, secondRingVertex, centralVertex_val,
    centralLift, physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

theorem centralVertex_cases (k : Fin 17) :
    centralVertex k = origin ∨
      (∃ i : Fin 8, centralVertex k = firstRingVertex i) ∨
      (∃ i : Fin 8, centralVertex k = secondRingVertex i) := by
  by_cases hk : k = 0
  · left
    simpa [hk] using centralVertex_zero
  have hk0 : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))
  by_cases hk9 : k.val < 9
  · let i : Fin 8 := ⟨k.val - 1, by omega⟩
    refine Or.inr (Or.inl ⟨i, ?_⟩)
    unfold firstRingVertex
    congr 1
    apply Fin.ext
    dsimp [i]
    omega
  · let i : Fin 8 := ⟨k.val - 9, by omega⟩
    refine Or.inr (Or.inr ⟨i, ?_⟩)
    unfold secondRingVertex
    congr 1
    apply Fin.ext
    dsimp [i]
    omega

theorem mem_sector_cases {v : Vertex} (hv : v ∈ sector) :
    v = origin ∨ (∃ i : Fin 8, v = firstRingVertex i) ∨
      (∃ i : Fin 8, v = secondRingVertex i) := by
  rw [sector_eq_centralPatch] at hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact centralVertex_cases i

theorem unit_norm_neighbors_mem_sector {v w : Vertex}
    (hv : ‖position v‖ = 1) (hw : Adjacent v w) : w ∈ sector := by
  have he := adjacent_unit_length hw
  have ht := dist_triangle (position w) (position v) (0 : ℂ)
  simp only [dist_zero_right] at ht
  rw [dist_comm (position w) (position v), he, hv] at ht
  exact (mem_sector w).2 (by linarith)

theorem origin_neighbors_mem_sector {w : Vertex} (hw : Adjacent origin w) :
    w ∈ sector := by
  have he := adjacent_unit_length hw
  have hn : ‖position w‖ = 1 := by simpa [position, origin, dist_comm] using he
  exact (mem_sector w).2 (by rw [hn]; norm_num)

/-- Every first-ring neighbor remains inside the exact central patch. -/
theorem firstRing_neighbors_mem_sector (i : Fin 8) {w : Vertex}
    (hw : Adjacent (firstRingVertex i) w) : w ∈ sector :=
  unit_norm_neighbors_mem_sector (firstRing_norm i) hw

/-- A central-to-exterior edge must originate on the second compact ring. -/
theorem central_boundary_secondRing {v w : Vertex} (hv : v ∈ sector)
    (hw : w ∉ sector) (hadj : Adjacent v w) :
    ∃ i : Fin 8, v = secondRingVertex i := by
  rcases mem_sector_cases hv with rfl | ⟨i, rfl⟩ | h
  · exact False.elim (hw (origin_neighbors_mem_sector hadj))
  · exact False.elim (hw (firstRing_neighbors_mem_sector i hadj))
  · exact h

theorem origin_adjacent_firstRing (i : Fin 8) : Adjacent origin (firstRingVertex i) := by
  fin_cases i <;> norm_num [Adjacent, origin, firstRingVertex, centralVertex_val,
    centralLift, basis, Fin.exists_fin_succ, funext_iff, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

theorem origin_not_adjacent_secondRing (i : Fin 8) :
    ¬ Adjacent origin (secondRingVertex i) := by
  fin_cases i <;> norm_num [Adjacent, origin, secondRingVertex, centralVertex_val,
    centralLift, basis, Fin.exists_fin_succ, funext_iff, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

set_option maxHeartbeats 3000000 in
theorem firstRing_not_adjacent (i j : Fin 8) :
    ¬ Adjacent (firstRingVertex i) (firstRingVertex j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Adjacent, firstRingVertex, centralVertex_val, centralLift, basis,
      Fin.exists_fin_succ, funext_iff, Fin.forall_fin_succ,
      Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

set_option maxHeartbeats 3000000 in
theorem secondRing_not_adjacent (i j : Fin 8) :
    ¬ Adjacent (secondRingVertex i) (secondRingVertex j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Adjacent, secondRingVertex, centralVertex_val, centralLift, basis,
      Fin.exists_fin_succ, funext_iff, Fin.forall_fin_succ,
      Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

set_option maxHeartbeats 3000000 in
/-- The two rings form a sixteen-cycle inside the central patch. -/
theorem firstRing_adjacent_secondRing (i j : Fin 8) :
    Adjacent (firstRingVertex i) (secondRingVertex j) ↔ j = i ∨ j + 1 = i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Adjacent, firstRingVertex, secondRingVertex, centralVertex_val,
      centralLift, basis, Fin.exists_fin_succ, funext_iff, Fin.forall_fin_succ,
      Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

/-- Complete first-ring adjacency, including the absence of exterior edges. -/
theorem adjacent_firstRing_iff (i : Fin 8) (w : Vertex) :
    Adjacent (firstRingVertex i) w ↔
      w = origin ∨ ∃ j : Fin 8, w = secondRingVertex j ∧ (j = i ∨ j + 1 = i) := by
  constructor
  · intro h
    rcases mem_sector_cases (firstRing_neighbors_mem_sector i h) with
      rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl rfl
    · exact False.elim (firstRing_not_adjacent i j h)
    · exact Or.inr ⟨j, rfl, (firstRing_adjacent_secondRing i j).1 h⟩
  · rintro (rfl | ⟨j, rfl, h⟩)
    · exact adjacent_symm (origin_adjacent_firstRing i)
    · exact (firstRing_adjacent_secondRing i j).2 h


theorem compactA_eq_zero_of_not_ring (v : Vertex)
    (hv : ∀ i : Fin 8, v ≠ firstRingVertex i) : compactA v = 0 := by
  have h0 : v.val ≠ ![1, 0, 0, 0] := fun h => hv 0 (Subtype.ext h)
  have h1 : v.val ≠ ![0, 1, 0, 0] := fun h => hv 1 (Subtype.ext h)
  have h2 : v.val ≠ ![0, 0, 1, 0] := fun h => hv 2 (Subtype.ext h)
  have h3 : v.val ≠ ![0, 0, 0, 1] := fun h => hv 3 (Subtype.ext h)
  have h4 : v.val ≠ ![-1, 0, 0, 0] := fun h => hv 4 (Subtype.ext h)
  have h5 : v.val ≠ ![0, -1, 0, 0] := fun h => hv 5 (Subtype.ext h)
  have h6 : v.val ≠ ![0, 0, -1, 0] := fun h => hv 6 (Subtype.ext h)
  have h7 : v.val ≠ ![0, 0, 0, -1] := fun h => hv 7 (Subtype.ext h)
  norm_num [compactA, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
    latticeSingle_apply, h0, h1, h2, h3, h4, h5, h6, h7]

theorem compactA_support {v : Vertex} (hv : compactA v ≠ 0) :
    ∃ i : Fin 8, v = firstRingVertex i := by
  by_contra h
  push Not at h
  exact hv (compactA_eq_zero_of_not_ring v h)

theorem compactA_ring_ne_zero (i : Fin 8) : compactA (firstRingVertex i) ≠ 0 := by
  fin_cases i <;>
    norm_num [compactA, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
      latticeSingle_apply, firstRingVertex, centralVertex_val, centralLift,
      funext_iff, Fin.forall_fin_succ]

theorem compactB_eq_zero_of_not_ring (v : Vertex)
    (hv : ∀ i : Fin 8, v ≠ secondRingVertex i) : compactB v = 0 := by
  have h0 : v.val ≠ ![1, 1, 0, 0] := fun h => hv 0 (Subtype.ext h)
  have h1 : v.val ≠ ![0, 1, 1, 0] := fun h => hv 1 (Subtype.ext h)
  have h2 : v.val ≠ ![0, 0, 1, 1] := fun h => hv 2 (Subtype.ext h)
  have h3 : v.val ≠ ![-1, 0, 0, 1] := fun h => hv 3 (Subtype.ext h)
  have h4 : v.val ≠ ![-1, -1, 0, 0] := fun h => hv 4 (Subtype.ext h)
  have h5 : v.val ≠ ![0, -1, -1, 0] := fun h => hv 5 (Subtype.ext h)
  have h6 : v.val ≠ ![0, 0, -1, -1] := fun h => hv 6 (Subtype.ext h)
  have h7 : v.val ≠ ![1, 0, 0, -1] := fun h => hv 7 (Subtype.ext h)
  norm_num [compactB, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
    latticeSingle_apply, h0, h1, h2, h3, h4, h5, h6, h7]

theorem compactB_support {v : Vertex} (hv : compactB v ≠ 0) :
    ∃ i : Fin 8, v = secondRingVertex i := by
  by_contra h
  push Not at h
  exact hv (compactB_eq_zero_of_not_ring v h)

theorem compactB_ring_ne_zero (i : Fin 8) : compactB (secondRingVertex i) ≠ 0 := by
  fin_cases i <;>
    norm_num [compactB, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
      latticeSingle_apply, secondRingVertex, centralVertex_val, centralLift,
      funext_iff, Fin.forall_fin_succ]

/-- A nonvanishing compact amplitude with zero neighboring amplitudes
recovers the local vertex degree from its Laplacian eigenvalue. -/
theorem degree_of_interaction_eigenvector (x : TileHilbert Vertex) (v : Vertex) (c : ℝ)
    (hx : interaction x = c • x) (hv : x v ≠ 0)
    (hzero : ∀ w ∈ neighbors v, x w = 0) : ((neighbors v).card : ℝ) = 16 * c := by
  have he := congrArg (fun y : TileHilbert Vertex => y v) hx
  change interaction x v = c * x v at he
  rw [interaction_apply] at he
  have hs : (∑ w ∈ neighbors v, (x v - x w)) = ((neighbors v).card : ℝ) * x v := by
    calc
      _ = ∑ w ∈ neighbors v, x v := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [hzero w hw, sub_zero]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hs] at he
  have hp : (((neighbors v).card : ℝ) - 16 * c) * x v = 0 := by nlinarith
  have hc := (mul_eq_zero.mp hp).resolve_right hv
  linarith

theorem firstRing_degree (i : Fin 8) : (neighbors (firstRingVertex i)).card = 3 := by
  have h := degree_of_interaction_eigenvector compactA (firstRingVertex i) (3 / 16)
    interaction_compactA (compactA_ring_ne_zero i) (by
      intro w hw
      by_contra h
      obtain ⟨j, rfl⟩ := compactA_support h
      exact firstRing_not_adjacent i j ((mem_neighbors_iff _ _).1 hw))
  have h' : ((neighbors (firstRingVertex i)).card : ℝ) = 3 := h.trans (by norm_num)
  exact_mod_cast h'

theorem secondRing_degree (i : Fin 8) : (neighbors (secondRingVertex i)).card = 4 := by
  have h := degree_of_interaction_eigenvector compactB (secondRingVertex i) (4 / 16)
    interaction_compactB (compactB_ring_ne_zero i) (by
      intro w hw
      by_contra h
      obtain ⟨j, rfl⟩ := compactB_support h
      exact secondRing_not_adjacent i j ((mem_neighbors_iff _ _).1 hw))
  have h' : ((neighbors (secondRingVertex i)).card : ℝ) = 4 := h.trans (by norm_num)
  exact_mod_cast h'

theorem firstRing_injective : Function.Injective firstRingVertex := by
  intro i j h
  have hi := congrArg Fin.val (centralVertex_injective h)
  change i.val + 1 = j.val + 1 at hi
  apply Fin.ext
  omega

theorem firstRing_ne_next (i : Fin 8) :
    firstRingVertex i ≠ firstRingVertex (i + 1) := by
  intro h
  have hi := firstRing_injective h
  fin_cases i <;> norm_num at hi

theorem firstRing_mem_sector (i : Fin 8) : firstRingVertex i ∈ sector := by
  apply (mem_sector _).2
  rw [firstRing_norm]
  norm_num

/-- Exactly two of each second-ring vertex's neighbors lie in the sector. -/
theorem secondRing_inside_neighbors (i : Fin 8) :
    neighbors (secondRingVertex i) ∩ sector =
      {firstRingVertex i, firstRingVertex (i + 1)} := by
  ext w
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hn, hs⟩
    have ha := (mem_neighbors_iff _ _).1 hn
    rcases mem_sector_cases hs with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact False.elim (origin_not_adjacent_secondRing i (adjacent_symm ha))
    · rcases (firstRing_adjacent_secondRing j i).1 (adjacent_symm ha) with h | h
      · exact Or.inl (congrArg firstRingVertex h.symm)
      · exact Or.inr (congrArg firstRingVertex h.symm)
    · exact False.elim (secondRing_not_adjacent i j ha)
  · rintro (rfl | rfl)
    · exact ⟨(mem_neighbors_iff _ _).2 (adjacent_symm
        ((firstRing_adjacent_secondRing i i).2 (Or.inl rfl))), firstRing_mem_sector i⟩
    · exact ⟨(mem_neighbors_iff _ _).2 (adjacent_symm
        ((firstRing_adjacent_secondRing (i + 1) i).2 (Or.inr rfl))),
        firstRing_mem_sector (i + 1)⟩

/-- Each second-ring vertex has exactly two exterior neighbors. -/
theorem secondRing_outside_neighbor_count (i : Fin 8) :
    (neighbors (secondRingVertex i) \ sector).card = 2 := by
  have h := Finset.card_sdiff_add_card_inter (neighbors (secondRingVertex i)) sector
  have hc : ({firstRingVertex i, firstRingVertex (i + 1)} : Finset Vertex).card = 2 := by
    simp [firstRing_ne_next i]
  rw [secondRing_inside_neighbors, hc, secondRing_degree] at h
  omega

theorem secondRing_injective : Function.Injective secondRingVertex := by
  intro i j h
  have hi := congrArg Fin.val (centralVertex_injective h)
  change i.val + 9 = j.val + 9 at hi
  apply Fin.ext
  omega

theorem centralVertex_mem_sector (i : Fin 17) : centralVertex i ∈ sector := by
  rw [sector_eq_centralPatch]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem secondRing_mem_sector (i : Fin 8) : secondRingVertex i ∈ sector :=
  centralVertex_mem_sector _

/-- Every boundary edge is oriented from the central sector to the exterior. -/
@[expose] def centralBoundaryEdges : Finset (Vertex × Vertex) :=
  (Finset.univ.sigma (fun i : Fin 8 => neighbors (secondRingVertex i) \ sector)).image
    (fun p => (secondRingVertex p.1, p.2))

/-- The finite list contains exactly all edges crossing the sector boundary. -/
theorem mem_centralBoundaryEdges (v w : Vertex) :
    (v, w) ∈ centralBoundaryEdges ↔ v ∈ sector ∧ w ∉ sector ∧ Adjacent v w := by
  constructor
  · intro h
    obtain ⟨⟨i, u⟩, hi, he⟩ := Finset.mem_image.mp h
    have hv : secondRingVertex i = v := congrArg Prod.fst he
    have hw : u = w := congrArg Prod.snd he
    subst v
    subst u
    have hn := Finset.mem_sdiff.mp (Finset.mem_sigma.mp hi).2
    exact ⟨secondRing_mem_sector i, hn.2, (mem_neighbors_iff _ _).1 hn.1⟩
  · rintro ⟨hv, hw, h⟩
    obtain ⟨i, rfl⟩ := central_boundary_secondRing hv hw h
    refine Finset.mem_image.mpr ⟨⟨i, w⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
      Finset.mem_sdiff.mpr ⟨(mem_neighbors_iff _ _).2 h, hw⟩⟩

/-- There are exactly sixteen edges joining the central patch to its exterior. -/
theorem centralBoundaryEdges_card : centralBoundaryEdges.card = 16 := by
  have hinj : Function.Injective
      (fun p : (Σ _ : Fin 8, Vertex) => (secondRingVertex p.1, p.2)) := by
    rintro ⟨i, v⟩ ⟨j, w⟩ h
    have hi := secondRing_injective (congrArg Prod.fst h)
    have hw := congrArg Prod.snd h
    cases hi
    cases hw
    rfl
  rw [centralBoundaryEdges, Finset.card_image_of_injective _ hinj, Finset.card_sigma]
  simp [secondRing_outside_neighbor_count]

end
end SpectralGeometry.AmmannBeenker
