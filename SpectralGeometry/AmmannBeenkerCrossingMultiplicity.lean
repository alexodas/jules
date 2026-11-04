module

public import SpectralGeometry.AmmannBeenkerCentralKernel

public section

/-!
# Exact multiplicity of the compact-state crossing

The central and exterior parts of a crossing eigenvector have equal shifted
energy. The first-ring equations make the central energy nonpositive, while
the exterior barrier makes the exterior energy strictly positive unless the
exterior part is zero. The complete central-kernel theorem then applies.
No explicit interval free of other spectral levels is asserted here.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- Finite coordinate projections preserve the natural onsite domain. -/
theorem finiteProjection_mem_domain (F : Finset Vertex) (x : TileHilbert Vertex) :
    finiteSectorProjection F x ∈ infiniteOnsiteDomain potential := by
  have h : finiteSectorProjection F x = ∑ v ∈ F, lp.single (2 : ENNReal) v (x v) := by
    apply lp.ext
    funext v
    simp only [finiteSectorProjection_apply, lp.coeFn_sum, Finset.sum_apply,
      lp.coeFn_single, Finset.sum_pi_single]
  rw [h]
  exact infiniteOnsiteDomain_finset_sum potential x F

/-- The central part, retained as a vector in the natural domain. -/
@[expose] def centralDomainPart (x : infiniteOnsiteDomain potential) :
    infiniteOnsiteDomain potential :=
  ⟨finiteSectorProjection sector x.1, finiteProjection_mem_domain sector x.1⟩

/-- The exterior part uses the same natural domain. -/
@[expose] def exteriorDomainPart (x : infiniteOnsiteDomain potential) :
    infiniteOnsiteDomain potential := x - centralDomainPart x

theorem centralDomainPart_apply (x : infiniteOnsiteDomain potential) (v : Vertex) :
    (centralDomainPart x).1 v = if v ∈ sector then x.1 v else 0 :=
  finiteSectorProjection_apply sector x.1 v

theorem exteriorDomainPart_apply (x : infiniteOnsiteDomain potential) (v : Vertex) :
    (exteriorDomainPart x).1 v = if v ∈ sector then 0 else x.1 v := by
  change x.1 v - (centralDomainPart x).1 v = _
  rw [centralDomainPart_apply]
  split_ifs <;> simp only [sub_self, sub_zero]

theorem centralDomainPart_outside (x : infiniteOnsiteDomain potential)
    (v : Vertex) (hv : v ∉ sector) : (centralDomainPart x).1 v = 0 := by
  rw [centralDomainPart_apply, if_neg hv]

theorem exteriorDomainPart_inside (x : infiniteOnsiteDomain potential)
    (v : Vertex) (hv : v ∈ sector) : (exteriorDomainPart x).1 v = 0 := by
  rw [exteriorDomainPart_apply, if_pos hv]

theorem exteriorDomainPart_projection (x : infiniteOnsiteDomain potential) :
    finiteSectorProjection sector (exteriorDomainPart x).1 = 0 := by
  apply lp.ext
  funext v
  change (finiteSectorProjection sector (exteriorDomainPart x).1) v = 0
  rw [finiteSectorProjection_apply]
  split_ifs with hv
  · exact exteriorDomainPart_inside x v hv
  · rfl

/-- The shifted crossing operator on its unchanged natural domain. -/
@[expose] def crossingResidual :
    infiniteOnsiteDomain potential →ₗ[ℝ] TileHilbert Vertex :=
  onsitePlusBounded potential (ringInteraction crossingParameter) -
    crossingEnergy • (infiniteOnsiteDomain potential).subtype

theorem crossingResidual_apply (x : infiniteOnsiteDomain potential) (v : Vertex) :
    crossingResidual x v =
      onsitePlusBounded potential (ringInteraction crossingParameter) x v -
        crossingEnergy * x.1 v := rfl

theorem crossingResidual_symmetric (x y : infiniteOnsiteDomain potential) :
    inner ℝ (crossingResidual x) y.1 = inner ℝ x.1 (crossingResidual y) := by
  have h := onsitePlusBounded_symmetric potential (ringInteraction crossingParameter)
    (finiteSectorCorrection_symmetric interaction interaction_symmetric
      (neighbors origin) crossingParameter) x y
  change inner ℝ
    (onsitePlusBounded potential (ringInteraction crossingParameter) x - crossingEnergy • x.1) y.1 =
    inner ℝ x.1
      (onsitePlusBounded potential (ringInteraction crossingParameter) y - crossingEnergy • y.1)
  rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, h]

/-- Exterior amplitudes cannot enter a first-ring coordinate through a single edge. -/
theorem exteriorResidual_firstRing (x : infiniteOnsiteDomain potential) (i : Fin 8) :
    crossingResidual (exteriorDomainPart x) (firstRingVertex i) = 0 := by
  have hv := exteriorDomainPart_inside x (firstRingVertex i) (firstRing_mem_sector i)
  have hs : (∑ w ∈ neighbors (firstRingVertex i), (exteriorDomainPart x).1 w) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    exact exteriorDomainPart_inside x w
      (firstRing_neighbors_mem_sector i ((mem_neighbors_iff _ _).1 hw))
  rw [crossingResidual_apply, crossingOperator_coordinate, hv, hs]
  ring

theorem centralResidual_firstRing_of_kernel (x : infiniteOnsiteDomain potential)
    (hx : crossingResidual x = 0) (i : Fin 8) :
    crossingResidual (centralDomainPart x) (firstRingVertex i) = 0 := by
  have h := exteriorResidual_firstRing x i
  unfold exteriorDomainPart at h
  rw [map_sub, hx] at h
  change (0 : ℝ) - crossingResidual (centralDomainPart x) (firstRingVertex i) = 0 at h
  linarith only [h]

/-- An inner product with finite support reduces to its actual coordinates. -/
theorem inner_eq_central_sum (x y : TileHilbert Vertex)
    (hx : ∀ v : Vertex, v ∉ sector → x v = 0) :
    inner ℝ x y = ∑ i : Fin 17, x (centralVertex i) * y (centralVertex i) := by
  calc
    inner ℝ x y = ∑' v : Vertex, x v * y v := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro v
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = ∑ v ∈ sector, x v * y v := by
      apply tsum_eq_sum
      intro v hv
      rw [hx v hv, zero_mul]
    _ = _ := by
      rw [sector_eq_centralPatch, centralPatch, Finset.sum_image]
      intro i _ j _ h
      exact centralVertex_injective h

set_option maxHeartbeats 2000000 in
/-- Every central edge meets the first ring; its energy is counted twice there. -/
theorem centralCrossingBlock_form (u : Fin 17 → ℝ) :
    (∑ i : Fin 17, u i * centralCrossingBlock u i) =
      (3 / 2 - crossingEnergy) * (u 0) ^ 2 +
        2 * ∑ i : Fin 8, u ⟨i.val + 1, by omega⟩ *
          centralCrossingBlock u ⟨i.val + 1, by omega⟩ := by
  norm_num [centralCrossingBlock_values, Fin.sum_univ_succ] <;> ring

/-- The central part of a crossing eigenvector has nonpositive shifted energy. -/
theorem centralPart_energy_of_kernel (x : infiniteOnsiteDomain potential)
    (hx : crossingResidual x = 0) :
    inner ℝ (centralDomainPart x).1 (crossingResidual (centralDomainPart x)) =
      (3 / 2 - crossingEnergy) * ((centralDomainPart x).1 (centralVertex 0)) ^ 2 := by
  let u : Fin 17 → ℝ := fun i => (centralDomainPart x).1 (centralVertex i)
  have hc (i : Fin 17) :
      crossingResidual (centralDomainPart x) (centralVertex i) = centralCrossingBlock u i := by
    exact (congrFun (centralCrossingBlock_restriction (centralDomainPart x)
      (centralDomainPart_outside x)) i).symm
  have hf : (∑ i : Fin 8, u ⟨i.val + 1, by omega⟩ *
      centralCrossingBlock u ⟨i.val + 1, by omega⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [← hc]
    change u ⟨i.val + 1, by omega⟩ *
      crossingResidual (centralDomainPart x) (firstRingVertex i) = 0
    rw [centralResidual_firstRing_of_kernel x hx i, mul_zero]
  rw [inner_eq_central_sum _ _ (centralDomainPart_outside x)]
  calc
    _ = ∑ i : Fin 17, u i * centralCrossingBlock u i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc]
    _ = _ := by
      rw [centralCrossingBlock_form, hf, mul_zero, add_zero]

/-- Symmetry and the eigenvector equation equate the two shifted energies. -/
theorem exterior_energy_eq_central_of_kernel (x : infiniteOnsiteDomain potential)
    (hx : crossingResidual x = 0) :
    inner ℝ (exteriorDomainPart x).1 (crossingResidual (exteriorDomainPart x)) =
      inner ℝ (centralDomainPart x).1 (crossingResidual (centralDomainPart x)) := by
  have hq : crossingResidual (exteriorDomainPart x) =
      -crossingResidual (centralDomainPart x) := by
    simp only [exteriorDomainPart, map_sub, hx, zero_sub]
  have hp : inner ℝ x.1 (crossingResidual (centralDomainPart x)) = 0 := by
    rw [← crossingResidual_symmetric x (centralDomainPart x), hx, zero_inner]
  rw [hq]
  change inner ℝ (x.1 - (centralDomainPart x).1)
    (-crossingResidual (centralDomainPart x)) = _
  rw [inner_sub_left, inner_neg_right, inner_neg_right, hp]
  ring

theorem crossingInteraction_nonneg (x : TileHilbert Vertex) :
    0 ≤ inner ℝ x (ringInteraction crossingParameter x) := by
  have ht : 0 ≤ crossingParameter := by
    dsimp [crossingParameter]
    linarith [alpha_bounds.1]
  change 0 ≤ inner ℝ x
    (interaction x + crossingParameter • finiteSectorProjection (neighbors origin) x)
  rw [inner_add_right, real_inner_smul_right, finiteSectorProjection_inner]
  exact add_nonneg (interaction_nonneg x) (mul_nonneg ht (sq_nonneg _))

/-- The radial barrier is strictly above the crossing energy on the exterior. -/
theorem exterior_energy_lower_bound (x : infiniteOnsiteDomain potential) :
    (3 / 4 + 2 * alpha) * ‖(exteriorDomainPart x).1‖ ^ 2 ≤
      inner ℝ (exteriorDomainPart x).1 (crossingResidual (exteriorDomainPart x)) := by
  have h := onsitePlusNonneg_sector_form_bound potential (ringInteraction crossingParameter)
    crossingInteraction_nonneg 1 (4 + 4 * alpha) potential_lower sector
    potential_outside_sector_sharp (exteriorDomainPart x)
  norm_num only [exteriorDomainPart_projection, norm_zero, zero_pow, mul_zero, sub_zero] at h
  change (3 / 4 + 2 * alpha) * ‖(exteriorDomainPart x).1‖ ^ 2 ≤
    inner ℝ (exteriorDomainPart x).1
      (onsitePlusBounded potential (ringInteraction crossingParameter) (exteriorDomainPart x) -
        crossingEnergy • (exteriorDomainPart x).1)
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  dsimp [crossingEnergy]
  nlinarith only [h]

/-- No nonzero exterior component is possible at the crossing energy. -/
theorem exteriorPart_eq_zero_of_kernel (x : infiniteOnsiteDomain potential)
    (hx : crossingResidual x = 0) : (exteriorDomainPart x).1 = 0 := by
  have hc : (0 : ℝ) < 3 / 4 + 2 * alpha := by linarith [alpha_bounds.1]
  have hd : (3 / 2 : ℝ) - crossingEnergy ≤ 0 := by
    dsimp [crossingEnergy]
    linarith [alpha_bounds.1]
  have he : inner ℝ (exteriorDomainPart x).1
      (crossingResidual (exteriorDomainPart x)) ≤ 0 := by
    rw [exterior_energy_eq_central_of_kernel x hx, centralPart_energy_of_kernel x hx]
    exact mul_nonpos_of_nonpos_of_nonneg hd (sq_nonneg _)
  have hs : ‖(exteriorDomainPart x).1‖ ^ 2 ≤ 0 := by
    apply (mul_le_mul_left hc).mp
    simpa only [mul_zero] using (exterior_energy_lower_bound x).trans he
  have hn : ‖(exteriorDomainPart x).1‖ = 0 := by
    nlinarith [norm_nonneg (exteriorDomainPart x).1]
  exact norm_eq_zero.mp hn

/-- Central support is now a conclusion of the full infinite eigenvector equation. -/
theorem crossing_eigenvector_central_support (x : infiniteOnsiteDomain potential)
    (he : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      crossingEnergy • (x : TileHilbert Vertex)) :
    ∀ v : Vertex, v ∉ sector → x.1 v = 0 := by
  have hx : crossingResidual x = 0 := by
    change onsitePlusBounded potential (ringInteraction crossingParameter) x -
      crossingEnergy • x.1 = 0
    rw [he, sub_self]
  have hq := exteriorPart_eq_zero_of_kernel x hx
  intro v hv
  have h := congrArg (fun y : TileHilbert Vertex => y v) hq
  change (exteriorDomainPart x).1 v = 0 at h
  rw [exteriorDomainPart_apply, if_neg hv] at h
  exact h

/-- Every crossing eigenvector belongs to the two explicitly known compact directions. -/
theorem crossing_eigenvector_representation (x : infiniteOnsiteDomain potential)
    (he : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      crossingEnergy • (x : TileHilbert Vertex)) :
    (x : TileHilbert Vertex) =
      x.1 (centralVertex 1) • compactA + x.1 (centralVertex 9) • compactB :=
  crossing_eigenvector_of_central_support x he (crossing_eigenvector_central_support x he)

/-- The actual crossing eigenspace inside the natural domain. -/
@[expose] def crossingEigenspace : Submodule ℝ (infiniteOnsiteDomain potential) :=
  domainEigenspace (infiniteOnsiteDomain potential)
    (onsitePlusBounded potential (ringInteraction crossingParameter)) crossingEnergy

/-- Seed amplitudes give linear coordinates on the full crossing eigenspace. -/
@[expose] def crossingEigenspaceCoordinates : crossingEigenspace ≃ₗ[ℝ] (ℝ × ℝ) := by
  let f : crossingEigenspace →ₗ[ℝ] (ℝ × ℝ) := {
    toFun := fun x => (x.1.1 (centralVertex 1), x.1.1 (centralVertex 9))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    have hx := crossing_eigenvector_representation x.1
      ((mem_domainEigenspace _ _ _ _).1 x.property)
    have hy := crossing_eigenvector_representation y.1
      ((mem_domainEigenspace _ _ _ _).1 y.property)
    have ha : x.1.1 (centralVertex 1) = y.1.1 (centralVertex 1) := congrArg Prod.fst h
    have hb : x.1.1 (centralVertex 9) = y.1.1 (centralVertex 9) := congrArg Prod.snd h
    apply Subtype.ext
    apply Subtype.ext
    rw [hx, hy, ha, hb]
  · rintro ⟨a, b⟩
    let z : infiniteOnsiteDomain potential := a • domainCompactA + b • domainCompactB
    have hz : z ∈ crossingEigenspace := by
      apply (mem_domainEigenspace _ _ _ _).2
      change onsitePlusBounded potential (ringInteraction crossingParameter)
        (a • domainCompactA + b • domainCompactB) =
          crossingEnergy • (a • compactA + b • compactB)
      rw [map_add, map_smul, map_smul, compact_crossing.2.1, compact_crossing.2.2]
      module
    refine ⟨⟨z, hz⟩, ?_⟩
    change (a * compactA compactSiteA + b * compactB compactSiteA,
      a * compactA compactSiteB + b * compactB compactSiteB) = (a, b)
    simp only [compactA_siteA, compactB_siteA, compactA_siteB, compactB_siteB,
      mul_one, mul_zero, add_zero, zero_add]

/-- Exact geometric multiplicity two for the infinite natural-domain crossing. -/
theorem crossingEigenspace_finrank : Module.finrank ℝ crossingEigenspace = 2 := by
  calc
    Module.finrank ℝ crossingEigenspace = Module.finrank ℝ (ℝ × ℝ) :=
      crossingEigenspaceCoordinates.finrank_eq
    _ = 2 := by simp

end
end SpectralGeometry.AmmannBeenker
