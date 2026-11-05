module

public import SpectralGeometry.AmmannBeenkerCrossingGapFinite

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
    (x y : infiniteOnsiteDomain potential) (λ : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      λ • (x : TileHilbert Vertex))
    (hy : crossingResidual y = 0)
    (hne : λ ≠ crossingEnergy) :
    inner ℝ x.1 y.1 = 0 := by
  have hxres : crossingResidual x = (λ - crossingEnergy) • x.1 := by
    change onsitePlusBounded potential (ringInteraction crossingParameter) x -
      crossingEnergy • x.1 = (λ - crossingEnergy) • x.1
    rw [hx]
    module
  have hs := crossingResidual_symmetric x y
  rw [hxres, hy, inner_zero_right, real_inner_smul_left] at hs
  have hc : λ - crossingEnergy ≠ 0 := sub_ne_zero.mpr hne
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
      norm_num [Fin.sum_univ_succ, centralCompactCoordinates]


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
      norm_num [Fin.sum_univ_succ, centralCompactCoordinates]


/-- Different eigenvalues force first-ring and second-ring alternating
amplitudes to vanish separately. The hypothesis is on the full infinite
operator, not on a finite patch. -/
theorem crossingDifferentLevel_ring_orthogonality
    (x : infiniteOnsiteDomain potential) (λ : ℝ)
    (hx : onsitePlusBounded potential (ringInteraction crossingParameter) x =
      λ • (x : TileHilbert Vertex))
    (hne : λ ≠ crossingEnergy) :
    ((x.1 (centralVertex 1)) - (x.1 (centralVertex 2)) + (x.1 (centralVertex 3)) - (x.1 (centralVertex 4)) + (x.1 (centralVertex 5)) - (x.1 (centralVertex 6)) + (x.1 (centralVertex 7)) - (x.1 (centralVertex 8)) = 0) ∧
    ((x.1 (centralVertex 9)) - (x.1 (centralVertex 10)) + (x.1 (centralVertex 11)) - (x.1 (centralVertex 12)) + (x.1 (centralVertex 13)) - (x.1 (centralVertex 14)) + (x.1 (centralVertex 15)) - (x.1 (centralVertex 16)) = 0) := by
  constructor
  · rw [← crossingCompactA_inner_coordinates x]
    exact crossingDifferentLevel_orthogonal_kernel x domainCompactA λ
      hx crossingResidual_compactA hne
  · rw [← crossingCompactB_inner_coordinates x]
    exact crossingDifferentLevel_orthogonal_kernel x domainCompactB λ
      hx crossingResidual_compactB hne

end
end SpectralGeometry.AmmannBeenker
