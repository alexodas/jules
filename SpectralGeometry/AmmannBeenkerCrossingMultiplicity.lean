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
    rw [← crossingResidual_symmetric x (centralDomainPart x), hx, inner_zero_left]
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
  calc
    (3 / 4 + 2 * alpha) * ‖(exteriorDomainPart x).1‖ ^ 2 =
        (4 + 4 * alpha) * ‖(exteriorDomainPart x).1‖ ^ 2 -
          crossingEnergy * ‖(exteriorDomainPart x).1‖ ^ 2 := by
      dsimp only [crossingEnergy]
      ring
    _ ≤ inner ℝ (exteriorDomainPart x).1
        (onsitePlusBounded potential (ringInteraction crossingParameter) (exteriorDomainPart x)) -
          crossingEnergy * ‖(exteriorDomainPart x).1‖ ^ 2 := sub_le_sub_right h _
    _ = inner ℝ (exteriorDomainPart x).1 (crossingResidual (exteriorDomainPart x)) := by
      change inner ℝ (exteriorDomainPart x).1
          (onsitePlusBounded potential (ringInteraction crossingParameter) (exteriorDomainPart x)) -
            crossingEnergy * ‖(exteriorDomainPart x).1‖ ^ 2 =
        inner ℝ (exteriorDomainPart x).1
          (onsitePlusBounded potential (ringInteraction crossingParameter) (exteriorDomainPart x) -
            crossingEnergy • (exteriorDomainPart x).1)
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]

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
    apply le_of_mul_le_mul_left ?_ hc
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


/-!
## Quantitative crossing-gap certificate: preparatory bounds

Proposed spectral exclusion radius (not yet a globally formalized theorem):
  g = 1/128.

The proof strategy is a block decomposition at the exact 17-vertex sector.
For L = K_(t*) - E*, its principal central block C has a two-dimensional
kernel, exactly the two compact modes already classified above.

A direct Fourier decomposition of the 16-cycle in
\`centralCrossingBlock_values\` gives the following **pending Lean obligation**:
  ||C u|| >= (1/24) ||u||
for every central vector u orthogonal to the two alternating modes.
For nonconstant ring Fourier frequencies k != 4, the nonzero singular
values are |cos(pi*k/8)|/8 >= sqrt(2-sqrt(2))/16 > 1/24.
The k=4 sector supplies the two known zero modes.
The constant sector, including the origin, has a 3-by-3 block
  [-d, -sqrt(2)/8, 0;
   -sqrt(2)/8, 0, -1/8;
   0, -1/8, 0]
with d=7/4+sqrt(2)>3. Its inverse has Frobenius norm squared
128+9/d^2 < 129, hence inverse norm < 12 < 24.

The 16 edges in \`centralBoundaryEdges_card\`, each with off-diagonal
weight 1/16, give a Hilbert-Schmidt bound for the cross-boundary block
||T|| <= sqrt(16*(1/16)^2) = 1/4. This operator estimate and its
identification with the block decomposition also remain to be formalized.

The exterior energy estimate, already proved as
\`exterior_energy_lower_bound\`, has coefficient 3/4+sqrt(2)>2.

For a nonzero eigenvalue displacement s, self-adjointness makes the
associated eigenvector orthogonal to the two compact eigenvectors. Writing
it as central u plus exterior q then gives
  (1/24-|s|) ||u|| <= (1/4) ||q||,
  (2-|s|) ||q|| <= (1/4) ||u||.
At |s| <= 1/128 this is impossible for a nonzero vector, since
  (1/24-1/128)*(2-1/128) - 1/16 = 81/16384 > 0.
Using the compact-resolvent spectral exhaustion would then exclude every
other spectral value in (E*-g,E*+g).

The Lean declarations below certify the exterior coefficient and the
arithmetic Schur margin. They DO NOT yet certify the full spectral gap:
a finite-block singular-value bound, the cross-boundary norm bound,
and the final global block argument are explicitly outstanding.
-/ 

/-- Conservatively proposed radius for a later full spectral-gap theorem. -/
@[expose] def crossingGapCandidate : ℝ := 1 / 128

theorem crossingGapCandidate_pos : 0 < crossingGapCandidate := by
  norm_num [crossingGapCandidate]

/-- The proved sharp exterior barrier is strictly greater than two. -/
theorem crossingExteriorCoefficient_gt_two :
    (2 : ℝ) < 3 / 4 + 2 * alpha := by
  have ha : (5 / 8 : ℝ) < alpha := by
    by_contra h
    have hle : alpha ≤ (5 / 8 : ℝ) := le_of_not_gt h
    have hnonneg : 0 ≤ (5 / 8 : ℝ) - alpha := sub_nonneg.mpr hle
    have hpositive : 0 ≤ (5 / 8 : ℝ) + alpha := by
      linarith [alpha_bounds.1]
    have hp := mul_nonneg hnonneg hpositive
    nlinarith [alpha_sq]
  linarith

/-- A simple numeric exterior energy inequality at the crossing. -/
theorem crossingExteriorEnergy_ge_two (x : infiniteOnsiteDomain potential) :
    (2 : ℝ) * ‖(exteriorDomainPart x).1‖ ^ 2 ≤
      inner ℝ (exteriorDomainPart x).1
        (crossingResidual (exteriorDomainPart x)) := by
  calc
    (2 : ℝ) * ‖(exteriorDomainPart x).1‖ ^ 2 ≤
        (3 / 4 + 2 * alpha) * ‖(exteriorDomainPart x).1‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (le_of_lt crossingExteriorCoefficient_gt_two) (sq_nonneg _)
    _ ≤ _ := exterior_energy_lower_bound x

/-- Scalar Schur-complement margin for every displacement up to g=1/128.
    The central and boundary operator bounds used in this criterion
    are not claimed as proved here. -/
theorem crossingGapCandidate_schur_margin (r : ℝ)
    (hr : 0 ≤ r ∧ r ≤ crossingGapCandidate) :
    (1 / 4 : ℝ) ^ 2 <
      ((1 / 24 : ℝ) - r) * ((3 / 4 : ℝ) + 2 * alpha - r) := by
  have hbound : r ≤ (1 / 128 : ℝ) := by
    simpa only [crossingGapCandidate] using hr.2
  have hleft : (1 / 24 : ℝ) - 1 / 128 ≤ (1 / 24 : ℝ) - r := by
    linarith
  have hright : (2 : ℝ) - 1 / 128 ≤
      (3 / 4 : ℝ) + 2 * alpha - r := by
    linarith [crossingExteriorCoefficient_gt_two]
  have hright_nonneg : 0 ≤ (2 : ℝ) - 1 / 128 := by norm_num
  have hleft_nonneg : 0 ≤ (1 / 24 : ℝ) - r := by linarith
  have hmargin : (1 / 4 : ℝ) ^ 2 <
      ((1 / 24 : ℝ) - 1 / 128) * ((2 : ℝ) - 1 / 128) := by norm_num
  exact lt_of_lt_of_le hmargin
    (mul_le_mul hleft hright hright_nonneg hleft_nonneg)


/-- The scalar block inequalities, combined with the strictly positive
Schur margin, force both nonnegative amplitudes to vanish. This is the
algebraic elimination step for a future operator-level spectral-gap proof. -/
theorem crossingGapCandidate_block_no_solution
    (r u q : ℝ)
    (hr : 0 ≤ r ∧ r ≤ crossingGapCandidate)
    (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hcentral : ((1 / 24 : ℝ) - r) * u ≤ (1 / 4 : ℝ) * q)
    (hexterior : ((3 / 4 : ℝ) + 2 * alpha - r) * q ≤ (1 / 4 : ℝ) * u) :
    u = 0 ∧ q = 0 := by
  have hr128 : r ≤ (1 / 128 : ℝ) := by
    simpa only [crossingGapCandidate] using hr.2
  have hBpos : 0 < (3 / 4 : ℝ) + 2 * alpha - r := by
    linarith [crossingExteriorCoefficient_gt_two]
  have hcomp :
      (((1 / 24 : ℝ) - r) * ((3 / 4 : ℝ) + 2 * alpha - r)) * u ≤
        ((1 / 4 : ℝ) ^ 2) * u := by
    calc
      _ = ((3 / 4 : ℝ) + 2 * alpha - r) * (((1 / 24 : ℝ) - r) * u) := by
        ring
      _ ≤ ((3 / 4 : ℝ) + 2 * alpha - r) * ((1 / 4 : ℝ) * q) :=
        mul_le_mul_of_nonneg_left hcentral (le_of_lt hBpos)
      _ = (1 / 4 : ℝ) * (((3 / 4 : ℝ) + 2 * alpha - r) * q) := by
        ring
      _ ≤ (1 / 4 : ℝ) * ((1 / 4 : ℝ) * u) :=
        mul_le_mul_of_nonneg_left hexterior (by norm_num)
      _ = ((1 / 4 : ℝ) ^ 2) * u := by ring
  have hgap := crossingGapCandidate_schur_margin r hr
  have huzero : u = 0 := by
    rcases eq_or_lt_of_le hu with hzero | hpos
    · exact hzero.symm
    · have hgt : ((1 / 4 : ℝ) ^ 2) * u <
          (((1 / 24 : ℝ) - r) * ((3 / 4 : ℝ) + 2 * alpha - r)) * u :=
        mul_lt_mul_of_pos_right hgap hpos
      exact False.elim ((not_lt_of_ge hcomp) hgt)
  have hqzero : q = 0 := by
    rcases eq_or_lt_of_le hq with hzero | hpos
    · exact hzero.symm
    · have hgt : 0 < ((3 / 4 : ℝ) + 2 * alpha - r) * q :=
        mul_pos hBpos hpos
      have hle : ((3 / 4 : ℝ) + 2 * alpha - r) * q ≤ 0 := by
        simpa only [huzero, mul_zero] using hexterior
      exact False.elim ((not_lt_of_ge hle) hgt)
  exact ⟨huzero, hqzero⟩

/-- The norm version of the abstract elimination step for the actual
central/exterior domain decomposition. To apply it to an off-crossing
eigenvector, the two displayed operator inequalities must still be proved.
This theorem does NOT by itself assert an explicit spectral gap. -/
theorem crossingGapCandidate_zero_of_block_norm_bounds
    (x : infiniteOnsiteDomain potential) (r : ℝ)
    (hr : 0 ≤ r ∧ r ≤ crossingGapCandidate)
    (hcentral : ((1 / 24 : ℝ) - r) * ‖(centralDomainPart x).1‖ ≤
      (1 / 4 : ℝ) * ‖(exteriorDomainPart x).1‖)
    (hexterior : ((3 / 4 : ℝ) + 2 * alpha - r) *
        ‖(exteriorDomainPart x).1‖ ≤
      (1 / 4 : ℝ) * ‖(centralDomainPart x).1‖) :
    (x : TileHilbert Vertex) = 0 := by
  obtain ⟨hc, hq⟩ := crossingGapCandidate_block_no_solution r
    ‖(centralDomainPart x).1‖ ‖(exteriorDomainPart x).1‖
    hr (norm_nonneg _) (norm_nonneg _) hcentral hexterior
  have hc0 : (centralDomainPart x).1 = 0 := norm_eq_zero.mp hc
  have hq0 : (exteriorDomainPart x).1 = 0 := norm_eq_zero.mp hq
  have hsum : x.1 = (centralDomainPart x).1 + (exteriorDomainPart x).1 := by
    change x.1 = (centralDomainPart x).1 + (x.1 - (centralDomainPart x).1)
    abel
  change x.1 = 0
  rw [hsum, hc0, hq0]
  simp

end
end SpectralGeometry.AmmannBeenker
