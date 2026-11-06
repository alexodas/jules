module

public import SpectralGeometry.AmmannBeenkerCrossingGapFinite

import Mathlib.Algebra.Order.Chebyshev

public section

/-!
# Off-crossing eigenvectors are orthogonal to both compact modes

This step passes from the energy inequality of the finite central block
to the correct codimension-two subspace. Every eigenvector at a
different eigenvalue is orthogonal to the exact compact eigenvectors
at crossingEnergy. The amplitudes on the two rings therefore have
zero alternating sums.

This does not by itself prove a spectral exclusion interval: the
central/exterior coupling estimates are still required.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Symmetry of the actual infinite crossing operator excludes overlap
between different eigenvalues. The second vector is a zero of the shifted
operator, not an assumed finite-support test vector. -/
theorem crossingDifferentLevel_orthogonal_kernel
    (x y : infiniteOnsiteDomain potential) (energy : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      energy • (x : TileHilbert Vertex))
    (hy : crossingResidual y = 0)
    (hne : energy ≠ crossingEnergy) :
    inner ℝ x.1 y.1 = 0 := by
  have hxres : crossingResidual x = (energy - crossingEnergy) • x.1 := by
    change onsitePlusBounded potential (ringInteraction crossingParameter) x -
      crossingEnergy • x.1 = (energy - crossingEnergy) • x.1
    rw [hx]
    module
  have hs := crossingResidual_symmetric x y
  rw [hxres, hy, inner_zero_right, real_inner_smul_left] at hs
  have hc : energy - crossingEnergy ≠ 0 := sub_ne_zero.mpr hne
  exact (mul_eq_zero.mp hs).resolve_left hc

/-- Both known compact modes lie in the zero space of crossingResidual. -/
theorem crossingResidual_compactA : crossingResidual domainCompactA = 0 := by
  change onsitePlusBounded potential (ringInteraction crossingParameter)
      domainCompactA - crossingEnergy • compactA = 0
  rw [compact_crossing.2.1, sub_self]

theorem crossingResidual_compactB : crossingResidual domainCompactB = 0 := by
  change onsitePlusBounded potential (ringInteraction crossingParameter)
      domainCompactB - crossingEnergy • compactB = 0
  rw [compact_crossing.2.2, sub_self]


/-- The A compact mode tests the corresponding alternating ring sum. -/
theorem crossingCompactA_inner_coordinates (x : infiniteOnsiteDomain potential) :
    inner ℝ x.1 compactA = (x.1 (centralVertex 1)) - (x.1 (centralVertex 2)) + (x.1 (centralVertex 3)) - (x.1 (centralVertex 4)) + (x.1 (centralVertex 5)) - (x.1 (centralVertex 6)) + (x.1 (centralVertex 7)) - (x.1 (centralVertex 8)) := by
  have hs : ∀ v : Vertex, v ∉ sector → compactA v = 0 := by
    intro v hv
    exact compactA_eq_zero_of_not_ring v (by
      intro i hi
      apply hv
      rw [hi]
      exact firstRing_mem_sector i)
  calc
    inner ℝ x.1 compactA = inner ℝ compactA x.1 := real_inner_comm _ _
    _ = ∑ i : Fin 17, (centralCompactCoordinates 1 0 i) * x.1 (centralVertex i) := by
      rw [inner_eq_central_sum compactA x.1 hs]
      apply Finset.sum_congr rfl
      intro i _
      rw [show compactA (centralVertex i) = centralCompactCoordinates 1 0 i from
        congrFun compactA_centralCoordinates i]
    _ = _ := by
      have hi1 : (Fin.succ ((0 : Fin 16)) : Fin 17) = 1 := by decide
      have hi2 : (Fin.succ (Fin.succ ((0 : Fin 15))) : Fin 17) = 2 := by decide
      have hi3 : (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 14)))) : Fin 17) = 3 := by decide
      have hi4 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 13))))) : Fin 17) = 4 := by decide
      have hi5 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 12)))))) : Fin 17) = 5 := by decide
      have hi6 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11))))))) : Fin 17) = 6 := by decide
      have hi7 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10)))))))) : Fin 17) = 7 := by decide
      have hi8 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9))))))))) : Fin 17) = 8 := by decide
      have hi9 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8)))))))))) : Fin 17) = 9 := by decide
      have hi10 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7))))))))))) : Fin 17) = 10 := by decide
      have hi11 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6)))))))))))) : Fin 17) = 11 := by decide
      have hi12 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5))))))))))))) : Fin 17) = 12 := by decide
      have hi13 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4)))))))))))))) : Fin 17) = 13 := by decide
      have hi14 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3))))))))))))))) : Fin 17) = 14 := by decide
      have hi15 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2)))))))))))))))) : Fin 17) = 15 := by decide
      have hi16 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1))))))))))))))))) : Fin 17) = 16 := by decide
      norm_num [Fin.sum_univ_succ, centralCompactCoordinates] <;>
        simp only [hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, hi12, hi13, hi14, hi15, hi16] <;> ring


/-- The B compact mode tests the corresponding alternating ring sum. -/
theorem crossingCompactB_inner_coordinates (x : infiniteOnsiteDomain potential) :
    inner ℝ x.1 compactB = (x.1 (centralVertex 9)) - (x.1 (centralVertex 10)) + (x.1 (centralVertex 11)) - (x.1 (centralVertex 12)) + (x.1 (centralVertex 13)) - (x.1 (centralVertex 14)) + (x.1 (centralVertex 15)) - (x.1 (centralVertex 16)) := by
  have hs : ∀ v : Vertex, v ∉ sector → compactB v = 0 := by
    intro v hv
    exact compactB_eq_zero_of_not_ring v (by
      intro i hi
      apply hv
      rw [hi]
      exact secondRing_mem_sector i)
  calc
    inner ℝ x.1 compactB = inner ℝ compactB x.1 := real_inner_comm _ _
    _ = ∑ i : Fin 17, (centralCompactCoordinates 0 1 i) * x.1 (centralVertex i) := by
      rw [inner_eq_central_sum compactB x.1 hs]
      apply Finset.sum_congr rfl
      intro i _
      rw [show compactB (centralVertex i) = centralCompactCoordinates 0 1 i from
        congrFun compactB_centralCoordinates i]
    _ = _ := by
      have hi1 : (Fin.succ ((0 : Fin 16)) : Fin 17) = 1 := by decide
      have hi2 : (Fin.succ (Fin.succ ((0 : Fin 15))) : Fin 17) = 2 := by decide
      have hi3 : (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 14)))) : Fin 17) = 3 := by decide
      have hi4 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 13))))) : Fin 17) = 4 := by decide
      have hi5 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 12)))))) : Fin 17) = 5 := by decide
      have hi6 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11))))))) : Fin 17) = 6 := by decide
      have hi7 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10)))))))) : Fin 17) = 7 := by decide
      have hi8 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9))))))))) : Fin 17) = 8 := by decide
      have hi9 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8)))))))))) : Fin 17) = 9 := by decide
      have hi10 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7))))))))))) : Fin 17) = 10 := by decide
      have hi11 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6)))))))))))) : Fin 17) = 11 := by decide
      have hi12 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5))))))))))))) : Fin 17) = 12 := by decide
      have hi13 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4)))))))))))))) : Fin 17) = 13 := by decide
      have hi14 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3))))))))))))))) : Fin 17) = 14 := by decide
      have hi15 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2)))))))))))))))) : Fin 17) = 15 := by decide
      have hi16 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1))))))))))))))))) : Fin 17) = 16 := by decide
      norm_num [Fin.sum_univ_succ, centralCompactCoordinates] <;>
        simp only [hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, hi12, hi13, hi14, hi15, hi16] <;> ring


/-- Different eigenvalues force first-ring and second-ring alternating
amplitudes to vanish separately. The hypothesis is on the full infinite
operator, not on a finite patch. -/
theorem crossingDifferentLevel_ring_orthogonality
    (x : infiniteOnsiteDomain potential) (energy : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      energy • (x : TileHilbert Vertex))
    (hne : energy ≠ crossingEnergy) :
    ((x.1 (centralVertex 1)) - (x.1 (centralVertex 2)) + (x.1 (centralVertex 3)) - (x.1 (centralVertex 4)) + (x.1 (centralVertex 5)) - (x.1 (centralVertex 6)) + (x.1 (centralVertex 7)) - (x.1 (centralVertex 8)) = 0) ∧
    ((x.1 (centralVertex 9)) - (x.1 (centralVertex 10)) + (x.1 (centralVertex 11)) - (x.1 (centralVertex 12)) + (x.1 (centralVertex 13)) - (x.1 (centralVertex 14)) + (x.1 (centralVertex 15)) - (x.1 (centralVertex 16)) = 0) := by
  constructor
  · rw [← crossingCompactA_inner_coordinates x]
    exact crossingDifferentLevel_orthogonal_kernel x domainCompactA energy
      hx crossingResidual_compactA hne
  · rw [← crossingCompactB_inner_coordinates x]
    exact crossingDifferentLevel_orthogonal_kernel x domainCompactB energy
      hx crossingResidual_compactB hne


/-!
## Boundary coupling: a finite Hilbert–Schmidt certificate

There are exactly sixteen oriented edges from the 17-vertex sector to
the exterior. Cauchy–Schwarz over the edge list and a comparison with
the complete product of the finite endpoint sets give a squared
bilinear bound with constant 1/16 for hopping coefficient 1/16.

This estimate is completely finite; identifying the boundary sum with
the cross term of the unbounded full operator and passing from finite
coordinate sums to Hilbert norms are subsequent steps.
-/

/-- The sum of squared weights over actual boundary edges is bounded
by the product of the squared-weight sums over the two endpoint sets. -/
private theorem crossingBoundaryCoupling_squared_weights
    (u q : Vertex → ℝ) :
    (∑ e ∈ centralBoundaryEdges, (u e.1 * q e.2) ^ 2) ≤
      (∑ v ∈ centralBoundaryEdges.image Prod.fst, (u v) ^ 2) *
      (∑ w ∈ centralBoundaryEdges.image Prod.snd, (q w) ^ 2) := by
  let S : Finset Vertex := centralBoundaryEdges.image Prod.fst
  let T : Finset Vertex := centralBoundaryEdges.image Prod.snd
  have hsubset : centralBoundaryEdges ⊆ S.product T := by
    intro e he
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst he,
       Finset.mem_image_of_mem Prod.snd he⟩
  have hle :
      (∑ e ∈ centralBoundaryEdges, (u e.1 * q e.2) ^ 2) ≤
        ∑ e ∈ S.product T, (u e.1 * q e.2) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro e _ _
      positivity)
  have hproduct :
      (∑ e ∈ S.product T, (u e.1 * q e.2) ^ 2) =
        (∑ v ∈ S, (u v) ^ 2) * (∑ w ∈ T, (q w) ^ 2) := by
    calc
      (∑ e ∈ S.product T, (u e.1 * q e.2) ^ 2) =
          ∑ v ∈ S, ∑ w ∈ T, (u v * q w) ^ 2 := by
        exact Finset.sum_product S T
          (fun e : Vertex × Vertex => (u e.1 * q e.2) ^ 2)
      _ = ∑ v ∈ S, (u v) ^ 2 * (∑ w ∈ T, (q w) ^ 2) := by
        apply Finset.sum_congr rfl
        intro v hv
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  exact hle.trans (le_of_eq hproduct)

/-- Exact sixteen-edge Hilbert–Schmidt bound for the cross-boundary
hopping pairing. The constant 1/16 is the square of the intended
operator-norm bound 1/4. -/
theorem crossingBoundaryCoupling_squared_bound
    (u q : Vertex → ℝ) :
    ((∑ e ∈ centralBoundaryEdges, u e.1 * q e.2) / 16) ^ 2 ≤
      (1 / 16 : ℝ) *
        (∑ v ∈ centralBoundaryEdges.image Prod.fst, (u v) ^ 2) *
        (∑ w ∈ centralBoundaryEdges.image Prod.snd, (q w) ^ 2) := by
  have hs :
      (∑ e ∈ centralBoundaryEdges, u e.1 * q e.2) ^ 2 ≤
        (centralBoundaryEdges.card : ℝ) *
          (∑ e ∈ centralBoundaryEdges, (u e.1 * q e.2) ^ 2) :=
    sq_sum_le_card_mul_sum_sq
  have hp := crossingBoundaryCoupling_squared_weights u q
  have hnonneg : 0 ≤ (centralBoundaryEdges.card : ℝ) := Nat.cast_nonneg _
  have hle :
      (∑ e ∈ centralBoundaryEdges, u e.1 * q e.2) ^ 2 ≤
        (16 : ℝ) *
          (∑ v ∈ centralBoundaryEdges.image Prod.fst, (u v) ^ 2) *
          (∑ w ∈ centralBoundaryEdges.image Prod.snd, (q w) ^ 2) := by
    calc
      _ ≤ (centralBoundaryEdges.card : ℝ) *
          (∑ e ∈ centralBoundaryEdges, (u e.1 * q e.2) ^ 2) := hs
      _ ≤ (centralBoundaryEdges.card : ℝ) *
          ((∑ v ∈ centralBoundaryEdges.image Prod.fst, (u v) ^ 2) *
            (∑ w ∈ centralBoundaryEdges.image Prod.snd, (q w) ^ 2)) :=
        mul_le_mul_of_nonneg_left hp hnonneg
      _ = _ := by rw [centralBoundaryEdges_card]; ring
  calc
    ((∑ e ∈ centralBoundaryEdges, u e.1 * q e.2) / 16) ^ 2 =
        (1 / 256 : ℝ) *
          (∑ e ∈ centralBoundaryEdges, u e.1 * q e.2) ^ 2 := by ring
    _ ≤ (1 / 256 : ℝ) *
          ((16 : ℝ) *
            (∑ v ∈ centralBoundaryEdges.image Prod.fst, (u v) ^ 2) *
            (∑ w ∈ centralBoundaryEdges.image Prod.snd, (q w) ^ 2)) :=
      mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = _ := by ring


/-!
## Coupling in the ambient infinite Hilbert-space norm

The preceding finite certificate becomes a genuine Hilbert-norm
estimate using the contractivity of coordinate projections. This
step makes no claim yet about identification with the mixed
crossingResidual term.
-/

/-- The square norm of a finite coordinate projection is exactly
the sum of squared amplitudes at those vertices. -/
private theorem crossingFiniteProjection_norm_sq
    (F : Finset Vertex) (x : TileHilbert Vertex) :
    (∑ v ∈ F, (x v) ^ 2) = ‖finiteSectorProjection F x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  calc
    (∑ v ∈ F, (x v) ^ 2) =
        ∑ v ∈ F, inner ℝ ((finiteSectorProjection F x) v)
          ((finiteSectorProjection F x) v) := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [finiteSectorProjection_apply, if_pos hv,
        RCLike.inner_apply, conj_trivial]
      ring
    _ = ∑' v : Vertex, inner ℝ ((finiteSectorProjection F x) v)
        ((finiteSectorProjection F x) v) := by
      symm
      apply tsum_eq_sum
      intro v hv
      simp [finiteSectorProjection_apply, hv]

/-- Any finite sum of coordinate squares is bounded by the full
square Hilbert norm. -/
theorem crossingFiniteCoordinate_energy_le
    (F : Finset Vertex) (x : TileHilbert Vertex) :
    (∑ v ∈ F, (x v) ^ 2) ≤ ‖x‖ ^ 2 := by
  rw [crossingFiniteProjection_norm_sq]
  have hnorm : ‖finiteSectorProjection F x‖ ≤ ‖x‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right
        (finiteSectorProjection_norm_le F) (norm_nonneg x))
  nlinarith [norm_nonneg (finiteSectorProjection F x), norm_nonneg x]

/-- Boundary pairing controlled by the *ambient infinite-dimensional*
Hilbert norms; the squared coefficient 1/16 corresponds to
a coupling-norm upper bound of 1/4. -/
theorem crossingBoundaryCoupling_hilbert_squared_bound
    (u q : TileHilbert Vertex) :
    ((∑ e ∈ centralBoundaryEdges, u e.1 * q e.2) / 16) ^ 2 ≤
      (1 / 16 : ℝ) * ‖u‖ ^ 2 * ‖q‖ ^ 2 := by
  let S := centralBoundaryEdges.image Prod.fst
  let T := centralBoundaryEdges.image Prod.snd
  have hU : (∑ v ∈ S, (u v) ^ 2) ≤ ‖u‖ ^ 2 :=
    crossingFiniteCoordinate_energy_le S u
  have hQ : (∑ w ∈ T, (q w) ^ 2) ≤ ‖q‖ ^ 2 :=
    crossingFiniteCoordinate_energy_le T q
  have hQnonneg : 0 ≤ (∑ w ∈ T, (q w) ^ 2) :=
    Finset.sum_nonneg (fun w hw => sq_nonneg _)
  calc
    _ ≤ (1 / 16 : ℝ) * (∑ v ∈ S, (u v) ^ 2) *
        (∑ w ∈ T, (q w) ^ 2) :=
      crossingBoundaryCoupling_squared_bound u q
    _ ≤ (1 / 16 : ℝ) * ‖u‖ ^ 2 * (∑ w ∈ T, (q w) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hU (by norm_num)) hQnonneg
    _ ≤ (1 / 16 : ℝ) * ‖u‖ ^ 2 * ‖q‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hQ
        (mul_nonneg (by norm_num) (sq_nonneg _))


/-!
## Exact identification with the infinite crossing operator

For an exterior domain vector, the shifted operator at a central
vertex sees only the neighbors across the boundary. Regrouping this
finite sum recovers exactly the sixteen oriented boundary edges.
This identifies the Hilbert–Schmidt certificate with a genuine
mixed term of the unbounded crossing operator on its natural domain.
-/

/-- On the central sector, the residual of an exterior vector
is precisely the negative hopping sum across the boundary. -/
theorem crossingResidual_exterior_at_central
    (x : infiniteOnsiteDomain potential) (v : Vertex) (hv : v ∈ sector) :
    crossingResidual (exteriorDomainPart x) v =
      - (∑ w ∈ neighbors v \ sector, (exteriorDomainPart x).1 w) / 16 := by
  have hz := exteriorDomainPart_inside x v hv
  have hneighbors :
      (∑ w ∈ neighbors v, (exteriorDomainPart x).1 w) =
        ∑ w ∈ neighbors v \ sector, (exteriorDomainPart x).1 w := by
    symm
    apply Finset.sum_subset Finset.sdiff_subset
    intro w hw hn
    have hws : w ∈ sector := by
      by_contra hnot
      exact hn (Finset.mem_sdiff.mpr ⟨hw, hnot⟩)
    exact exteriorDomainPart_inside x w hws
  rw [crossingResidual_apply, crossingOperator_coordinate, hz, hneighbors]
  ring

/-- Reindex the boundary-edge list as a sum over the
central sector and its exterior neighbors. -/
theorem crossingBoundaryEdges_sum (f : Vertex → Vertex → ℝ) :
    (∑ e ∈ centralBoundaryEdges, f e.1 e.2) =
      ∑ v ∈ sector, ∑ w ∈ neighbors v \ sector, f v w := by
  let F : Finset (Σ _ : Vertex, Vertex) :=
    sector.sigma (fun v => neighbors v \ sector)
  let toPair : (Σ _ : Vertex, Vertex) → Vertex × Vertex :=
    fun p => (p.1, p.2)
  have hinj : Function.Injective toPair := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ h
    have hp := Prod.mk.inj h
    rcases hp with ⟨rfl, rfl⟩
    rfl
  have himage : F.image toPair = centralBoundaryEdges := by
    ext e
    rcases e with ⟨v, w⟩
    constructor
    · intro he
      obtain ⟨⟨v', w'⟩, hmem, hp⟩ := Finset.mem_image.mp he
      obtain ⟨hv, hw⟩ := Finset.mem_sigma.mp hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      obtain ⟨hn, hout⟩ := Finset.mem_sdiff.mp hw
      exact (mem_centralBoundaryEdges _ _).2
        ⟨hv, hout, (mem_neighbors_iff _ _).1 hn⟩
    · intro he
      obtain ⟨hv, hout, ha⟩ := (mem_centralBoundaryEdges v w).1 he
      exact Finset.mem_image.mpr
        ⟨⟨v, w⟩, Finset.mem_sigma.mpr
          ⟨hv, Finset.mem_sdiff.mpr
            ⟨(mem_neighbors_iff _ _).2 ha, hout⟩⟩, rfl⟩
  calc
    (∑ e ∈ centralBoundaryEdges, f e.1 e.2) =
        ∑ e ∈ F.image toPair, f e.1 e.2 := by rw [himage]
    _ = ∑ e ∈ F, f e.1 e.2 := by
      rw [Finset.sum_image]
      intro e _ e' _ he
      exact hinj he
    _ = ∑ v ∈ sector, ∑ w ∈ neighbors v \ sector, f v w := by
      exact Finset.sum_sigma sector (fun v => neighbors v \ sector)
        (fun e : Σ _ : Vertex, Vertex => f e.1 e.2)

/-- The central/exterior mixed residual is EXACTLY the hopping
pairing across the sixteen boundary edges, with coefficient -1/16. -/
theorem crossingResidual_central_exterior_inner_eq_boundary
    (x y : infiniteOnsiteDomain potential) :
    inner ℝ (centralDomainPart x).1
      (crossingResidual (exteriorDomainPart y)) =
      - ((∑ e ∈ centralBoundaryEdges,
        (centralDomainPart x).1 e.1 * (exteriorDomainPart y).1 e.2) / 16) := by
  calc
    inner ℝ (centralDomainPart x).1
        (crossingResidual (exteriorDomainPart y)) =
        ∑ i : Fin 17, (centralDomainPart x).1 (centralVertex i) *
          crossingResidual (exteriorDomainPart y) (centralVertex i) :=
      inner_eq_central_sum _ _ (centralDomainPart_outside x)
    _ = ∑ v ∈ sector, (centralDomainPart x).1 v *
        crossingResidual (exteriorDomainPart y) v := by
      rw [sector_eq_centralPatch, centralPatch, Finset.sum_image]
      intro i _ j _ h
      exact centralVertex_injective h
    _ = (-1 / 16 : ℝ) *
        (∑ v ∈ sector, ∑ w ∈ neighbors v \ sector,
          (centralDomainPart x).1 v * (exteriorDomainPart y).1 w) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [crossingResidual_exterior_at_central y v hv]
      rw [← Finset.mul_sum]
      ring
    _ = - ((∑ e ∈ centralBoundaryEdges,
        (centralDomainPart x).1 e.1 * (exteriorDomainPart y).1 e.2) / 16) := by
      rw [← crossingBoundaryEdges_sum]
      ring

/-- The genuine mixed residual pairing of central/exterior domain
components obeys the certified Hilbert–Schmidt bound. -/
theorem crossingResidual_central_exterior_inner_sq_bound
    (x y : infiniteOnsiteDomain potential) :
    (inner ℝ (centralDomainPart x).1
        (crossingResidual (exteriorDomainPart y))) ^ 2 ≤
      (1 / 16 : ℝ) * ‖(centralDomainPart x).1‖ ^ 2 *
        ‖(exteriorDomainPart y).1‖ ^ 2 := by
  rw [crossingResidual_central_exterior_inner_eq_boundary]
  simpa only [neg_sq] using
    (crossingBoundaryCoupling_hilbert_squared_bound
      (centralDomainPart x).1 (exteriorDomainPart y).1)


/-!
## Exterior block inequality for genuine off-crossing eigenvectors

The true infinite-dimensional mixed-term estimate and symmetry of
crossingResidual turn exterior coercivity into an eigenvector inequality.
No claim about the full spectral gap is made at this stage.
-/

/-- Absolute-value version of the mixed central/exterior bound. -/
theorem crossingResidual_central_exterior_inner_abs_bound
    (x y : infiniteOnsiteDomain potential) :
    |inner ℝ (centralDomainPart x).1
        (crossingResidual (exteriorDomainPart y))| ≤
      (1 / 4 : ℝ) * ‖(centralDomainPart x).1‖ *
        ‖(exteriorDomainPart y).1‖ := by
  apply abs_le_of_sq_le_sq ?_ (by positivity)
  calc
    (inner ℝ (centralDomainPart x).1
        (crossingResidual (exteriorDomainPart y))) ^ 2 ≤
        (1 / 16 : ℝ) * ‖(centralDomainPart x).1‖ ^ 2 *
          ‖(exteriorDomainPart y).1‖ ^ 2 :=
      crossingResidual_central_exterior_inner_sq_bound x y
    _ = ((1 / 4 : ℝ) * ‖(centralDomainPart x).1‖ *
        ‖(exteriorDomainPart y).1‖) ^ 2 := by ring

/-- The actual central and exterior components are orthogonal. -/
theorem crossingCentralExterior_inner_zero
    (x : infiniteOnsiteDomain potential) :
    inner ℝ (exteriorDomainPart x).1 (centralDomainPart x).1 = 0 := by
  rw [lp.inner_eq_tsum]
  have hz (v : Vertex) :
      inner ℝ ((exteriorDomainPart x).1 v) ((centralDomainPart x).1 v) = 0 := by
    by_cases hv : v ∈ sector
    · rw [exteriorDomainPart_inside x v hv]
      simp
    · rw [centralDomainPart_outside x v hv]
      simp
  simp only [hz, tsum_zero]

/-- A full eigenvalue equation becomes a scalar shift of the
crossing residual, with no support hypothesis. -/
theorem crossingResidual_of_eigenvector
    (x : infiniteOnsiteDomain potential) (energy : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      energy • (x : TileHilbert Vertex)) :
    crossingResidual x = (energy - crossingEnergy) • x.1 := by
  change onsitePlusBounded potential (ringInteraction crossingParameter) x -
    crossingEnergy • x.1 = (energy - crossingEnergy) • x.1
  rw [hx]
  module

/-- For every actual eigenvector of the infinite operator,
the exterior block obeys the coercive inequality with the precise
energy displacement and coupling coefficient 1/4. -/
theorem crossingExteriorEnergy_off_crossing_bound
    (x : infiniteOnsiteDomain potential) (energy : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      energy • (x : TileHilbert Vertex)) :
    ((3 / 4 : ℝ) + 2 * alpha - |energy - crossingEnergy|) *
        ‖(exteriorDomainPart x).1‖ ^ 2 ≤
      (1 / 4 : ℝ) * ‖(centralDomainPart x).1‖ *
        ‖(exteriorDomainPart x).1‖ := by
  let c := centralDomainPart x
  let q := exteriorDomainPart x
  have hsum : x.1 = c.1 + q.1 := by
    change x.1 = (centralDomainPart x).1 +
      (x.1 - (centralDomainPart x).1)
    abel
  have horth : inner ℝ q.1 c.1 = 0 :=
    crossingCentralExterior_inner_zero x
  have hqinner : inner ℝ q.1 x.1 = ‖q.1‖ ^ 2 := by
    rw [hsum, inner_add_right, horth, real_inner_self_eq_norm_sq, zero_add]
  have hqres :
      crossingResidual q =
        (energy - crossingEnergy) • x.1 - crossingResidual c := by
    calc
      crossingResidual q = crossingResidual x - crossingResidual c := by
        change crossingResidual (x - centralDomainPart x) =
          crossingResidual x - crossingResidual (centralDomainPart x)
        rw [map_sub]
      _ = _ := by rw [crossingResidual_of_eigenvector x energy hx]
  have hsym :
      inner ℝ q.1 (crossingResidual c) =
        inner ℝ c.1 (crossingResidual q) := by
    calc
      _ = inner ℝ (crossingResidual c) q.1 := real_inner_comm _ _
      _ = _ := crossingResidual_symmetric c q
  have henergy :
      inner ℝ q.1 (crossingResidual q) =
        (energy - crossingEnergy) * ‖q.1‖ ^ 2 -
          inner ℝ c.1 (crossingResidual q) := by
    calc
      _ = inner ℝ q.1
          ((energy - crossingEnergy) • x.1 - crossingResidual c) := by
        rw [hqres]
      _ = (energy - crossingEnergy) * ‖q.1‖ ^ 2 -
          inner ℝ q.1 (crossingResidual c) := by
        rw [inner_sub_right, real_inner_smul_right, hqinner]
      _ = _ := by rw [hsym]
  have hbarrier : ((3 / 4 : ℝ) + 2 * alpha) * ‖q.1‖ ^ 2 ≤
      (energy - crossingEnergy) * ‖q.1‖ ^ 2 -
        inner ℝ c.1 (crossingResidual q) := by
    rw [← henergy]
    exact exterior_energy_lower_bound x
  have hshift :
      (energy - crossingEnergy) * ‖q.1‖ ^ 2 ≤
        |energy - crossingEnergy| * ‖q.1‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have hmix : -(inner ℝ c.1 (crossingResidual q)) ≤
      (1 / 4 : ℝ) * ‖c.1‖ * ‖q.1‖ := by
    have h := (abs_le.mp (crossingResidual_central_exterior_inner_abs_bound x x)).1
    dsimp only [c, q]
    linarith only [h]
  change ((3 / 4 : ℝ) + 2 * alpha - |energy - crossingEnergy|) *
      ‖q.1‖ ^ 2 ≤ (1 / 4 : ℝ) * ‖c.1‖ * ‖q.1‖
  nlinarith only [hbarrier, hshift, hmix]


/-!
## Lifting the 17-vertex central singular-value gap

The finite estimate is now applied to the actual central component
of a natural-domain vector. The central restriction theorem identifies
its finite block action with the central coordinates of the full
shifted operator. Both squared norms are exact Hilbert norms.

The two alternating-sum hypotheses are kept explicit here; they
follow for off-crossing eigenvectors from the orthogonality theorem.
-/

/-- The certified singular-value estimate for the 17-vertex block,
expressed using the genuine Hilbert norms of the central domain
component and the projected infinite crossing residual. -/
theorem crossingCentralResidual_projected_norm_sq_lower
    (x : infiniteOnsiteDomain potential)
    (hxa :
      (centralDomainPart x).1 (centralVertex 1) -
        (centralDomainPart x).1 (centralVertex 2) +
        (centralDomainPart x).1 (centralVertex 3) -
        (centralDomainPart x).1 (centralVertex 4) +
        (centralDomainPart x).1 (centralVertex 5) -
        (centralDomainPart x).1 (centralVertex 6) +
        (centralDomainPart x).1 (centralVertex 7) -
        (centralDomainPart x).1 (centralVertex 8) = 0)
    (hya :
      (centralDomainPart x).1 (centralVertex 9) -
        (centralDomainPart x).1 (centralVertex 10) +
        (centralDomainPart x).1 (centralVertex 11) -
        (centralDomainPart x).1 (centralVertex 12) +
        (centralDomainPart x).1 (centralVertex 13) -
        (centralDomainPart x).1 (centralVertex 14) +
        (centralDomainPart x).1 (centralVertex 15) -
        (centralDomainPart x).1 (centralVertex 16) = 0) :
    (1 / 576 : ℝ) * ‖(centralDomainPart x).1‖ ^ 2 ≤
      ‖finiteSectorProjection sector
        (crossingResidual (centralDomainPart x))‖ ^ 2 := by
  let u : Fin 17 → ℝ := fun i => (centralDomainPart x).1 (centralVertex i)
  have hblock (i : Fin 17) :
      centralCrossingBlock u i =
        crossingResidual (centralDomainPart x) (centralVertex i) := by
    have h := congrFun (centralCrossingBlock_restriction (centralDomainPart x)
      (centralDomainPart_outside x)) i
    simpa only [crossingResidual_apply] using h
  have hnormc :
      (∑ i : Fin 17, (u i) ^ 2) = ‖(centralDomainPart x).1‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      inner_eq_central_sum _ _ (centralDomainPart_outside x)]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [u]
    ring
  have hnormr :
      (∑ i : Fin 17,
        (crossingResidual (centralDomainPart x) (centralVertex i)) ^ 2) =
        ‖finiteSectorProjection sector
          (crossingResidual (centralDomainPart x))‖ ^ 2 := by
    rw [← crossingFiniteProjection_norm_sq sector
      (crossingResidual (centralDomainPart x))]
    rw [sector_eq_centralPatch, centralPatch, Finset.sum_image]
    intro i _ j _ h
    exact centralVertex_injective h
  have hfinite : (1 / 576 : ℝ) * (∑ i : Fin 17, (u i) ^ 2) ≤
      ∑ i : Fin 17, (centralCrossingBlock u i) ^ 2 :=
    crossingCentralBlock_norm_sq_lower u hxa hya
  calc
    (1 / 576 : ℝ) * ‖(centralDomainPart x).1‖ ^ 2 =
        (1 / 576 : ℝ) * (∑ i : Fin 17, (u i) ^ 2) := by
      rw [hnormc]
    _ ≤ ∑ i : Fin 17, (centralCrossingBlock u i) ^ 2 := hfinite
    _ = ∑ i : Fin 17,
        (crossingResidual (centralDomainPart x) (centralVertex i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hblock]
    _ = _ := hnormr


/-!
## Applying the central singular-value estimate to off-crossing eigenvectors

The orthogonality of distinct eigenspaces now discharges both
alternating-ring conditions required by the finite 17-vertex
singular-value certificate. The conclusion concerns the full
natural-domain infinite eigenvector, not an arbitrary finite patch.
-/

/-- The central projection preserves every coordinate in the
17-vertex sector. -/
theorem crossingCentralPart_centralVertex_apply
    (x : infiniteOnsiteDomain potential) (i : Fin 17) :
    (centralDomainPart x).1 (centralVertex i) = x.1 (centralVertex i) := by
  rw [centralDomainPart_apply, if_pos (centralVertex_mem_sector i)]

/-- Every actual eigenvector at an energy distinct from the
crossing has central coordinates in the coercive codimension-two
subspace, and hence satisfies the full projected Hilbert-norm
singular-value estimate. -/
theorem crossingDifferentLevel_central_projected_norm_sq_lower
    (x : infiniteOnsiteDomain potential) (energy : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      energy • (x : TileHilbert Vertex))
    (hne : energy ≠ crossingEnergy) :
    (1 / 576 : ℝ) * ‖(centralDomainPart x).1‖ ^ 2 ≤
      ‖finiteSectorProjection sector
        (crossingResidual (centralDomainPart x))‖ ^ 2 := by
  obtain ⟨ha, hb⟩ :=
    crossingDifferentLevel_ring_orthogonality x energy hx hne
  apply crossingCentralResidual_projected_norm_sq_lower x
  · simpa only [crossingCentralPart_centralVertex_apply] using ha
  · simpa only [crossingCentralPart_centralVertex_apply] using hb


/-!
## Operator-norm estimate for the exterior-to-central coupling

The mixed-term estimate is upgraded to a norm bound for the
central projection of the residual of a genuine exterior domain
vector. The test vector is itself the finite central projection
of that residual, so it belongs to the natural onsite domain.
-/

/-- The norm of the exterior-to-central hopping block is at most
1/4 on every exterior component of a domain vector. Unlike a
bilinear pairing estimate, this controls the entire projected
residual and is suitable for the central eigenvector equation. -/
theorem crossingResidual_exterior_projected_norm_le
    (y : infiniteOnsiteDomain potential) :
    ‖finiteSectorProjection sector
      (crossingResidual (exteriorDomainPart y))‖ ≤
      (1 / 4 : ℝ) * ‖(exteriorDomainPart y).1‖ := by
  let r := crossingResidual (exteriorDomainPart y)
  let z := finiteSectorProjection sector r
  let test : infiniteOnsiteDomain potential :=
    ⟨z, finiteProjection_mem_domain sector r⟩
  have htest : (centralDomainPart test).1 = z := by
    apply lp.ext
    funext v
    rw [centralDomainPart_apply]
    change (if v ∈ sector then z v else 0) = z v
    by_cases hv : v ∈ sector
    · simp only [if_pos hv]
    · simp [z, finiteSectorProjection_apply, hv]
  have hpair := crossingResidual_central_exterior_inner_abs_bound test y
  rw [htest] at hpair
  change |inner ℝ z r| ≤
      (1 / 4 : ℝ) * ‖z‖ * ‖(exteriorDomainPart y).1‖ at hpair
  have hself : inner ℝ z r = ‖z‖ ^ 2 := by
    calc
      _ = inner ℝ r z := real_inner_comm _ _
      _ = _ := finiteSectorProjection_inner sector r
  have hsquared :
      ‖z‖ ^ 2 ≤
        (1 / 4 : ℝ) * ‖z‖ * ‖(exteriorDomainPart y).1‖ := by
    calc
      _ = |inner ℝ z r| := by rw [hself, abs_of_nonneg (sq_nonneg _)]
      _ ≤ _ := hpair
  change ‖z‖ ≤ (1 / 4 : ℝ) * ‖(exteriorDomainPart y).1‖
  by_cases hzero : ‖z‖ = 0
  · rw [hzero]
    positivity
  · have hpos : 0 < ‖z‖ :=
      lt_of_le_of_ne (norm_nonneg z) (Ne.symm hzero)
    by_contra hn
    have hgt : (1 / 4 : ℝ) * ‖(exteriorDomainPart y).1‖ < ‖z‖ :=
      lt_of_not_ge hn
    have hcontr := mul_lt_mul_of_pos_left hgt hpos
    nlinarith only [hsquared, hcontr]


/-!
## The central block inequality for off-crossing eigenvectors

The finite singular-value certificate gives a lower bound on the
central projected residual. The eigenvalue equation, together with
the genuine exterior-to-central operator-norm estimate, gives the
matching upper bound. Their combination is precisely the central
Schur inequality, without an auxiliary coupling hypothesis.
-/

/-- The finite 17-site singular-value certificate yields the
linear central coercivity inequality in ambient Hilbert norm. -/
theorem crossingDifferentLevel_central_projected_norm_lower
    (x : infiniteOnsiteDomain potential) (energy : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      energy • (x : TileHilbert Vertex))
    (hne : energy ≠ crossingEnergy) :
    (1 / 24 : ℝ) * ‖(centralDomainPart x).1‖ ≤
      ‖finiteSectorProjection sector
        (crossingResidual (centralDomainPart x))‖ := by
  have hsqr :=
    crossingDifferentLevel_central_projected_norm_sq_lower x energy hx hne
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  calc
    ((1 / 24 : ℝ) * ‖(centralDomainPart x).1‖) ^ 2 =
        (1 / 576 : ℝ) * ‖(centralDomainPart x).1‖ ^ 2 := by ring
    _ ≤ _ := hsqr

/-- For an eigenvector with energy distinct from the crossing,
the central block satisfies the exact Schur-complement inequality:
the spectral displacement reduces its coercivity by at most its
absolute value, while the exterior-to-central coupling costs 1/4. -/
theorem crossingCentralEnergy_off_crossing_bound
    (x : infiniteOnsiteDomain potential) (energy : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      energy • (x : TileHilbert Vertex))
    (hne : energy ≠ crossingEnergy) :
    ((1 / 24 : ℝ) - |energy - crossingEnergy|) *
        ‖(centralDomainPart x).1‖ ≤
      (1 / 4 : ℝ) * ‖(exteriorDomainPart x).1‖ := by
  let c := centralDomainPart x
  let q := exteriorDomainPart x
  have hqres :
      crossingResidual q =
        (energy - crossingEnergy) • x.1 - crossingResidual c := by
    calc
      crossingResidual q = crossingResidual x - crossingResidual c := by
        change crossingResidual (x - centralDomainPart x) =
          crossingResidual x - crossingResidual (centralDomainPart x)
        rw [map_sub]
      _ = _ := by rw [crossingResidual_of_eigenvector x energy hx]
  have hcres :
      crossingResidual c =
        (energy - crossingEnergy) • x.1 - crossingResidual q := by
    rw [hqres]
    module
  have hproj :
      finiteSectorProjection sector (crossingResidual c) =
        (energy - crossingEnergy) • c.1 -
          finiteSectorProjection sector (crossingResidual q) := by
    calc
      finiteSectorProjection sector (crossingResidual c) =
          finiteSectorProjection sector
            ((energy - crossingEnergy) • x.1 - crossingResidual q) := by
        rw [hcres]
      _ = (energy - crossingEnergy) •
            finiteSectorProjection sector x.1 -
          finiteSectorProjection sector (crossingResidual q) := by
        rw [map_sub, map_smul]
      _ = _ := by rfl
  have hupper :
      ‖finiteSectorProjection sector (crossingResidual c)‖ ≤
        |energy - crossingEnergy| * ‖c.1‖ +
          (1 / 4 : ℝ) * ‖q.1‖ := by
    rw [hproj]
    calc
      ‖(energy - crossingEnergy) • c.1 -
          finiteSectorProjection sector (crossingResidual q)‖ ≤
          ‖(energy - crossingEnergy) • c.1‖ +
            ‖finiteSectorProjection sector (crossingResidual q)‖ :=
        norm_sub_le _ _
      _ = |energy - crossingEnergy| * ‖c.1‖ +
            ‖finiteSectorProjection sector (crossingResidual q)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |energy - crossingEnergy| * ‖c.1‖ +
          (1 / 4 : ℝ) * ‖q.1‖ :=
        add_le_add_right (crossingResidual_exterior_projected_norm_le x) _
  have hlower :=
    crossingDifferentLevel_central_projected_norm_lower x energy hx hne
  change ((1 / 24 : ℝ) - |energy - crossingEnergy|) * ‖c.1‖ ≤
    (1 / 4 : ℝ) * ‖q.1‖
  nlinarith only [hlower, hupper]


/-!
## Linear exterior inequality for the Schur criterion

The already certified quadratic exterior block inequality may be
cancelled by the nonzero exterior norm. If that norm vanishes, the
desired linear bound follows immediately from nonnegativity.
-/

/-- Every infinite-operator eigenvector satisfies the linear exterior
Schur estimate, without any support or nonvanishing assumption. -/
theorem crossingExteriorEnergy_off_crossing_linear_bound
    (x : infiniteOnsiteDomain potential) (energy : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      energy • (x : TileHilbert Vertex)) :
    ((3 / 4 : ℝ) + 2 * alpha - |energy - crossingEnergy|) *
        ‖(exteriorDomainPart x).1‖ ≤
      (1 / 4 : ℝ) * ‖(centralDomainPart x).1‖ := by
  have hsquared := crossingExteriorEnergy_off_crossing_bound x energy hx
  by_cases hzero : ‖(exteriorDomainPart x).1‖ = 0
  · rw [hzero, mul_zero]
    positivity
  · have hpos : 0 < ‖(exteriorDomainPart x).1‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    by_contra hn
    have hgt :
        (1 / 4 : ℝ) * ‖(centralDomainPart x).1‖ <
          ((3 / 4 : ℝ) + 2 * alpha - |energy - crossingEnergy|) *
            ‖(exteriorDomainPart x).1‖ :=
      lt_of_not_ge hn
    have hmul := mul_lt_mul_of_pos_right hgt hpos
    nlinarith only [hsquared, hmul]


/-!
## Exclusion of other eigenvalues in the explicit crossing window

Both block inequalities are now proved for every genuine eigenvector
at an energy different from crossingEnergy. Applying the already
certified strict Schur margin forces its central and exterior
components to vanish. This is an eigenvalue-exclusion theorem:
identification of the full real spectrum with genuine eigenvalues
still requires the compact-resolvent spectral theory.
-/

/-- No nonzero eigenvector at a different energy can lie within
the closed radius crossingGapCandidate around crossingEnergy. -/
theorem crossingGapCandidate_off_crossing_eigenvector_zero
    (x : infiniteOnsiteDomain potential) (energy : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      energy • (x : TileHilbert Vertex))
    (hne : energy ≠ crossingEnergy)
    (hnear : |energy - crossingEnergy| ≤ crossingGapCandidate) :
    (x : TileHilbert Vertex) = 0 := by
  exact crossingGapCandidate_zero_of_block_norm_bounds x
    |energy - crossingEnergy| ⟨abs_nonneg _, hnear⟩
    (crossingCentralEnergy_off_crossing_bound x energy hx hne)
    (crossingExteriorEnergy_off_crossing_linear_bound x energy hx)

/-- Explicit exclusion of all *other eigenvalues* in the certified
window, for the genuine full operator on its natural infinite domain.
This does not yet claim the exclusion of continuous-spectrum points. -/
theorem crossingGapCandidate_no_other_full_eigenvector
    (energy : ℝ)
    (hne : energy ≠ crossingEnergy)
    (hnear : |energy - crossingEnergy| ≤ crossingGapCandidate) :
    ¬ ∃ x : infiniteOnsiteDomain potential,
      (x : TileHilbert Vertex) ≠ 0 ∧
      onsitePlusBounded potential (ringInteraction crossingParameter) x =
        energy • (x : TileHilbert Vertex) := by
  rintro ⟨x, hxne, he⟩
  exact hxne
    (crossingGapCandidate_off_crossing_eigenvector_zero x energy he hne hnear)

end
end SpectralGeometry.AmmannBeenker
