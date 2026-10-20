module

public import SpectralGeometry.InfiniteLocalEigenpairCorrespondence

public section

/-!
# Finite multiplicity and orthogonality of full infinite local eigenvectors

The previously proved eigenpair correspondence converts the nonzero
eigenspaces of the compact resolvent into genuine eigenpairs of the
unbounded matching-family operator on its natural onsite domain.
This module packages those eigenspaces as submodules, proves their
finite dimensionality, excludes the chosen resolvent shift as an
eigenvalue, and establishes orthogonality of eigenvectors with
distinct real eigenvalues under the existing symmetry hypotheses.

This does not yet prove that every full spectral point is an
eigenvalue or that full eigenvalues are isolated. Isolation and
enumeration remain separate P2 milestones.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev FullEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- The eigenspace of the full unbounded matching operator at
`eigenvalue ≠ a`, realized by its equivalent compact-resolvent
eigenspace. The membership theorem below identifies it with the
actual natural-domain eigenvalue equation for the full operator. -/
@[expose] noncomputable def infiniteLocalMatchingFullEigenspace
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (_hne : eigenvalue ≠ a) :
    Submodule ℝ (TileHilbert Tile) :=
  Module.End.eigenspace
    (infiniteBoundedOnsiteResolvent V a hgap
      (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall).toLinearMap
    (eigenvalue - a)⁻¹

/-- Membership in the full operator eigenspace is exactly existence
of a natural-domain state satisfying the corresponding eigenvalue
equation; no global boundedness of the operator is assumed. -/
theorem infiniteLocalMatchingFullEigenspace_mem_iff
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (hne : eigenvalue ≠ a)
    (f : TileHilbert Tile) :
    f ∈ infiniteLocalMatchingFullEigenspace
      D V σ w P ε shift a hgap hsmall eigenvalue hne ↔
      ∃ ψ : infiniteOnsiteDomain V,
        (ψ.1 : TileHilbert Tile) = f ∧
        infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
          eigenvalue • f := by
  unfold infiniteLocalMatchingFullEigenspace
  rw [Module.End.mem_eigenspace_iff]
  change
    infiniteBoundedOnsiteResolvent V a hgap
      (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall f =
        (eigenvalue - a)⁻¹ • f ↔
      ∃ ψ : infiniteOnsiteDomain V,
        (ψ.1 : TileHilbert Tile) = f ∧
        infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
          eigenvalue • f
  exact infiniteLocalMatching_resolvent_eigenpair_iff_of_ne
    D V σ w P ε shift a hgap hsmall eigenvalue hne f

/-- Every real eigenvalue of the full matching operator other than
the resolvent shift has a finite-dimensional eigenspace when the
onsite potential has finite sublevel sets. No symmetry is needed
for this finite-multiplicity conclusion. -/
theorem infiniteLocalMatchingFullEigenspace_finiteDimensional
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (hne : eigenvalue ≠ a) :
    FiniteDimensional ℝ
      (infiniteLocalMatchingFullEigenspace
        D V σ w P ε shift a hgap hsmall eigenvalue hne) := by
  change FiniteDimensional ℝ
    (Module.End.eigenspace
      (infiniteBoundedOnsiteResolvent V a hgap
        (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall).toLinearMap
      (eigenvalue - a)⁻¹)
  exact infiniteBoundedOnsiteResolvent_finite_dimensional_eigenspace
    V a hgap hproper
    (infiniteLocalBoundedCorrection D σ w P ε shift)
    hsmall (eigenvalue - a)⁻¹
    (inv_ne_zero (sub_ne_zero.mpr hne))

/-- The real shift used to define the inverse is not an eigenvalue
of the full matching-family operator: its only eigenvector there
is the zero state. -/
theorem infiniteLocalMatching_no_eigenvector_at_shift
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (ψ : infiniteOnsiteDomain V)
    (heigen : infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
      a • (ψ.1 : TileHilbert Tile)) :
    (ψ.1 : TileHilbert Tile) = 0 := by
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  have hshift : infiniteBoundedOnsiteShift V a B ψ = 0 := by
    rw [infiniteLocalShiftedPerturbed_eq_onsite_add_correction] at heigen
    change infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile) +
      B ψ.1 = 0
    calc
      infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile) +
          B ψ.1 =
          (infiniteOnsiteOperator V ψ + B ψ.1) -
            a • (ψ.1 : TileHilbert Tile) := by abel
      _ = a • (ψ.1 : TileHilbert Tile) -
            a • (ψ.1 : TileHilbert Tile) := by rw [heigen]
      _ = 0 := sub_self _
  have hleft :=
    infiniteBoundedOnsiteResolvent_left_inverse
      V a hgap B hsmall ψ
  rw [hshift, map_zero] at hleft
  exact hleft.symm

/-- Eigenvectors of the full local matching operator at distinct
real eigenvalues are orthogonal when matching permutations are
involutions and the bounded perturbation is symmetric. -/
theorem infiniteLocalMatching_eigenvectors_orthogonal
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullEnd Tile)
    (ε shift : ℝ)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ x y : TileHilbert Tile,
      inner ℝ x (P y) = inner ℝ (P x) y)
    (ψ φ : infiniteOnsiteDomain V) (eigenvalue eigenvalue' : ℝ)
    (hne : eigenvalue ≠ eigenvalue')
    (hψ : infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
      eigenvalue • (ψ.1 : TileHilbert Tile))
    (hφ : infiniteLocalShiftedPerturbedOperator D V σ w P ε shift φ =
      eigenvalue' • (φ.1 : TileHilbert Tile)) :
    inner ℝ (ψ.1 : TileHilbert Tile) (φ.1 : TileHilbert Tile) = 0 := by
  have hsym :
      inner ℝ (infiniteLocalShiftedPerturbedOperator
          D V σ w P ε shift ψ) (φ.1 : TileHilbert Tile) =
        inner ℝ (ψ.1 : TileHilbert Tile)
          (infiniteLocalShiftedPerturbedOperator
            D V σ w P ε shift φ) := by
    rw [infiniteLocalShiftedPerturbed_eq_onsite_add_correction,
      infiniteLocalShiftedPerturbed_eq_onsite_add_correction]
    simp only [inner_add_left, inner_add_right]
    rw [infiniteOnsiteOperator_symmetric V ψ φ,
      infiniteLocalBoundedCorrection_symmetric
        D σ w P ε shift hσ hP ψ.1 φ.1]
  have hzero :
      (eigenvalue - eigenvalue') *
        inner ℝ (ψ.1 : TileHilbert Tile) (φ.1 : TileHilbert Tile) = 0 := by
    calc
      (eigenvalue - eigenvalue') *
        inner ℝ (ψ.1 : TileHilbert Tile) (φ.1 : TileHilbert Tile) =
          inner ℝ (infiniteLocalShiftedPerturbedOperator
            D V σ w P ε shift ψ) (φ.1 : TileHilbert Tile) -
          inner ℝ (ψ.1 : TileHilbert Tile)
            (infiniteLocalShiftedPerturbedOperator
              D V σ w P ε shift φ) := by
        rw [hψ, hφ, real_inner_smul_left, real_inner_smul_right]
        ring
      _ = 0 := sub_eq_zero.mpr hsym
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

end SpectralGeometry
