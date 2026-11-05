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
        rw [Finset.sum_product]
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

end
end SpectralGeometry.AmmannBeenker
