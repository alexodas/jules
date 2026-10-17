import SpectralGeometry.InfiniteFiniteEdgeInteraction

/-!
# A common infinite domain for onsite, edge, and bounded perturbation terms

On the natural (possibly proper) dense domain D(V) of an unbounded
diagonal onsite operator, a finite-edge interaction and any bounded
linear perturbation can be added without shrinking the domain.

For nonnegative onsite energies, nonnegative edge weights, and a
nonnegative quadratic form for the perturbation at nonnegative ε,
the FULL combined quadratic energy is nonnegative.

Symmetry of the combined operator follows from the symmetric onsite
part, geometric edges, and a symmetric bounded perturbation.

IMPORTANT: finitely many active edges are considered here, though
the ambient Hilbert space may contain infinitely many tiles. No
claim of self-adjointness, infinite-range interactions, compact
resolvent, or inverse-square spectral summability is made.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- The real diagonal onsite multiplication is symmetric on its
natural domain; no boundedness of the onsite potential is assumed. -/
theorem infiniteOnsiteOperator_symmetric
    (V : Tile → ℝ) (ψ φ : infiniteOnsiteDomain V) :
    ⟪(ψ.1 : TileHilbert Tile), infiniteOnsiteOperator V φ⟫_ℝ =
      ⟪infiniteOnsiteOperator V ψ, (φ.1 : TileHilbert Tile)⟫_ℝ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro t
  simp [infiniteOnsiteOperator_apply, RCLike.inner_apply,
    mul_comm, mul_left_comm, mul_assoc]

/-- Nonnegative onsite energies imply a nonnegative global
quadratic form on D(V), not merely nonnegative local terms. -/
theorem infiniteOnsiteOperator_energy_nonneg
    (V : Tile → ℝ) (hV : ∀ t, 0 ≤ V t)
    (ψ : infiniteOnsiteDomain V) :
    0 ≤ ⟪(ψ.1 : TileHilbert Tile), infiniteOnsiteOperator V ψ⟫_ℝ := by
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro t
  simpa [RCLike.inner_apply] using
    infiniteOnsiteOperator_local_nonneg V hV ψ t

/-- The sum of the unbounded onsite operator, a finite-edge Laplacian
on ℓ²(Tile), and an arbitrary bounded perturbation P. The natural
onsite domain is shared by all three terms. -/
noncomputable def infiniteFiniteEdgePerturbedOperator
    (V : Tile → ℝ) (edges : Finset (Tile × Tile))
    (w : Tile × Tile → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ) :
    (infiniteOnsiteDomain V) →ₗ[ℝ] TileHilbert Tile :=
  infiniteOnsiteOperator V +
    (infiniteFiniteEdgeLaplacian edges w).comp
      (infiniteOnsiteDomain V).subtype +
    ε • (P.toLinearMap.comp (infiniteOnsiteDomain V).subtype)

/-- Every state in D(V) is mapped back into ℓ², with the three
terms evaluated on the same state. -/
theorem infiniteFiniteEdgePerturbedOperator_apply
    (V : Tile → ℝ) (edges : Finset (Tile × Tile))
    (w : Tile × Tile → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (ψ : infiniteOnsiteDomain V) :
    infiniteFiniteEdgePerturbedOperator V edges w P ε ψ =
      infiniteOnsiteOperator V ψ +
        infiniteFiniteEdgeLaplacian edges w (ψ.1 : TileHilbert Tile) +
        ε • P (ψ.1 : TileHilbert Tile) := by
  simp [infiniteFiniteEdgePerturbedOperator,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]

/-- Quadratic energy of the full operator decomposes EXACTLY into
onsite, interaction, and perturbation contributions. -/
theorem infiniteFiniteEdgePerturbedOperator_energy_eq
    (V : Tile → ℝ) (edges : Finset (Tile × Tile))
    (w : Tile × Tile → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (ψ : infiniteOnsiteDomain V) :
    ⟪(ψ.1 : TileHilbert Tile),
      infiniteFiniteEdgePerturbedOperator V edges w P ε ψ⟫_ℝ =
      ⟪(ψ.1 : TileHilbert Tile), infiniteOnsiteOperator V ψ⟫_ℝ +
        ⟪(ψ.1 : TileHilbert Tile),
          infiniteFiniteEdgeLaplacian edges w ψ.1⟫_ℝ +
        ε * ⟪(ψ.1 : TileHilbert Tile), P ψ.1⟫_ℝ := by
  rw [infiniteFiniteEdgePerturbedOperator_apply]
  simp only [inner_add_right, real_inner_smul_right]

/-- All three nonnegative quadratic contributions give a
nonnegative combined operator on the shared infinite domain.
Importantly, this theorem does not assert spectral summability. -/
theorem infiniteFiniteEdgePerturbedOperator_energy_nonneg
    (V : Tile → ℝ) (edges : Finset (Tile × Tile))
    (w : Tile × Tile → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (hV : ∀ t, 0 ≤ V t)
    (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hP : ∀ ψ : TileHilbert Tile, 0 ≤ ⟪ψ, P ψ⟫_ℝ)
    (hε : 0 ≤ ε) (ψ : infiniteOnsiteDomain V) :
    0 ≤ ⟪(ψ.1 : TileHilbert Tile),
      infiniteFiniteEdgePerturbedOperator V edges w P ε ψ⟫_ℝ := by
  rw [infiniteFiniteEdgePerturbedOperator_energy_eq]
  exact add_nonneg
    (add_nonneg (infiniteOnsiteOperator_energy_nonneg V hV ψ)
      (infiniteFiniteEdgeLaplacian_energy_nonneg edges w hw ψ.1))
    (mul_nonneg hε (hP ψ.1))

/-- If the bounded perturbation is symmetric, then the complete
infinite-domain operator is symmetric on D(V). Symmetric does
not by itself mean self-adjoint for an unbounded operator. -/
theorem infiniteFiniteEdgePerturbedOperator_symmetric
    (V : Tile → ℝ) (edges : Finset (Tile × Tile))
    (w : Tile × Tile → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (hP : ∀ ψ φ : TileHilbert Tile,
      ⟪ψ, P φ⟫_ℝ = ⟪P ψ, φ⟫_ℝ)
    (ψ φ : infiniteOnsiteDomain V) :
    ⟪(ψ.1 : TileHilbert Tile),
      infiniteFiniteEdgePerturbedOperator V edges w P ε φ⟫_ℝ =
      ⟪infiniteFiniteEdgePerturbedOperator V edges w P ε ψ,
        (φ.1 : TileHilbert Tile)⟫_ℝ := by
  rw [infiniteFiniteEdgePerturbedOperator_apply,
    infiniteFiniteEdgePerturbedOperator_apply]
  simp only [inner_add_right, inner_add_left,
    real_inner_smul_right, real_inner_smul_left]
  rw [infiniteOnsiteOperator_symmetric V ψ φ,
    infiniteFiniteEdgeLaplacian_symmetric edges w ψ.1 φ.1,
    hP ψ.1 φ.1]

end SpectralGeometry
