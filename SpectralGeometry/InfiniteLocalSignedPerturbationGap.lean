import SpectralGeometry.InfiniteLocalEigenvalueBounds

/-!
# Stability of the point-spectrum lower bound under signed bounded perturbations

On the natural dense domain of the (possibly unbounded) onsite multiplication,
the infinite matching interaction has nonnegative quadratic energy whenever
its constant matching weights are nonnegative.

For an arbitrary bounded linear perturbation P and any real coupling ε, we
control its energy in absolute value by |ε| * ‖P‖ * ‖ψ‖². Consequently
an existing real eigenvalue of M_V + L_w + εP is at least -|ε| * ‖P‖.

We also allow an independent uniform onsite shift m I. For eigenvectors of
M_V + L_w + εP + m I, every real eigenvalue is at least m - |ε| * ‖P‖.
A positive gap therefore survives whenever m > |ε| * ‖P‖.

Unlike the previous positive-P theorem, P need not have nonnegative energy
or be symmetric for these real point-eigenvalue estimates. This file does
not assert existence or completeness of eigenvectors, self-adjointness,
compact resolvent, or discreteness of the full spectrum.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- The quadratic energy of any bounded real-linear perturbation is
controlled by its operator norm, even when it is not positive. -/
theorem infiniteLocalBoundedPerturbation_inner_abs_le
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ψ : TileHilbert Tile) :
    |inner ℝ ψ (P ψ)| ≤ ‖P‖ * ‖ψ‖ ^ 2 := by
  have hP : ‖P ψ‖ ≤ ‖P‖ * ‖ψ‖ := P.le_opNorm ψ
  have hupper : inner ℝ ψ (P ψ) ≤ ‖ψ‖ * ‖P ψ‖ :=
    real_inner_le_norm _ _
  have hlower :
      inner ℝ ψ ((-1 : ℝ) • (P ψ)) ≤ ‖ψ‖ * ‖((-1 : ℝ) • (P ψ))‖ :=
    real_inner_le_norm _ _
  have hlower' : -(inner ℝ ψ (P ψ)) ≤ ‖ψ‖ * ‖P ψ‖ := by
    simpa [real_inner_smul_right] using hlower
  have hmul : ‖ψ‖ * ‖P ψ‖ ≤ ‖P‖ * ‖ψ‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hP (norm_nonneg ψ)
    nlinarith
  apply abs_le.mpr
  constructor <;> linarith [hlower']

/-- No real point eigenvalue of the infinite local matching operator
with an arbitrary signed bounded perturbation lies below -|ε|‖P‖.
The onsite potential and matching weights are assumed nonnegative. -/
theorem infiniteLocalMatchingSignedPerturbation_eigenvalue_ge
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen :
      infiniteLocalMatchingPerturbedOperator D V σ w P ε ψ =
        eigenvalue • (ψ.1 : TileHilbert Tile))
    (hψ : (ψ.1 : TileHilbert Tile) ≠ 0) :
    -( |ε| * ‖P‖ ) ≤ eigenvalue := by
  have honsite := infiniteOnsiteOperator_energy_nonneg V hV ψ
  have hedge :=
    infiniteLocalMatchingLaplacian_energy_nonneg D σ w hw ψ.1
  have hnorm : 0 < ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hψ)
  have habs :=
    infiniteLocalBoundedPerturbation_inner_abs_le P (ψ.1 : TileHilbert Tile)
  have hperturb :
      -( |ε| * ‖P‖ ) * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
        ε * inner ℝ (ψ.1 : TileHilbert Tile) (P ψ.1) := by
    have hbound :
        |ε * inner ℝ (ψ.1 : TileHilbert Tile) (P ψ.1)| ≤
          |ε| * (‖P‖ * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left habs (abs_nonneg ε)
    calc
      -( |ε| * ‖P‖ ) * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 =
        -( |ε| * (‖P‖ * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2)) := by ring
      _ ≤ ε * inner ℝ (ψ.1 : TileHilbert Tile) (P ψ.1) :=
        (abs_le.mp hbound).1
  have heigenenergy :
      eigenvalue * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 =
        inner ℝ (ψ.1 : TileHilbert Tile) (infiniteOnsiteOperator V ψ) +
        inner ℝ (ψ.1 : TileHilbert Tile)
          (infiniteLocalMatchingLaplacian D σ w ψ.1) +
        ε * inner ℝ (ψ.1 : TileHilbert Tile) (P ψ.1) := by
    have h := congrArg
      (fun η : TileHilbert Tile => inner ℝ (ψ.1 : TileHilbert Tile) η) heigen
    rw [infiniteLocalMatchingPerturbedOperator_apply] at h
    simp only [inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at h
    exact h.symm
  have hscaled :
      -( |ε| * ‖P‖ ) * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
        eigenvalue * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
    rw [heigenenergy]
    linarith
  exact (mul_le_mul_iff_of_pos_right hnorm).mp hscaled

/-- An independently controlled identity shift adds a constant to
the full local operator without changing the natural onsite domain. -/
noncomputable def infiniteLocalShiftedPerturbedOperator
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ) :
    infiniteOnsiteDomain V →ₗ[ℝ] TileHilbert Tile :=
  infiniteLocalMatchingPerturbedOperator D V σ w P ε +
    shift • ((ContinuousLinearMap.id ℝ (TileHilbert Tile)).toLinearMap.comp
      (infiniteOnsiteDomain V).subtype)

/-- The extra constant shift acts as shift times the current state. -/
theorem infiniteLocalShiftedPerturbedOperator_apply
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ) (ψ : infiniteOnsiteDomain V) :
    infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
      infiniteLocalMatchingPerturbedOperator D V σ w P ε ψ +
        shift • (ψ.1 : TileHilbert Tile) := by
  simp [infiniteLocalShiftedPerturbedOperator, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply]

/-- The uniform shift leaves a quantitative point-spectrum lower bound
even for a signed, non-positive bounded perturbation. -/
theorem infiniteLocalShiftedPerturbed_eigenvalue_ge
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen :
      infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
        eigenvalue • (ψ.1 : TileHilbert Tile))
    (hψ : (ψ.1 : TileHilbert Tile) ≠ 0) :
    shift - |ε| * ‖P‖ ≤ eigenvalue := by
  have h := heigen
  rw [infiniteLocalShiftedPerturbedOperator_apply] at h
  have hbase :
      infiniteLocalMatchingPerturbedOperator D V σ w P ε ψ =
        (eigenvalue - shift) • (ψ.1 : TileHilbert Tile) := by
    calc
      _ = eigenvalue • (ψ.1 : TileHilbert Tile) -
          shift • (ψ.1 : TileHilbert Tile) := eq_sub_of_add_eq h
      _ = (eigenvalue - shift) • (ψ.1 : TileHilbert Tile) := by rw [sub_smul]
  have hbound := infiniteLocalMatchingSignedPerturbation_eigenvalue_ge
    D V σ w P ε hV hw ψ (eigenvalue - shift) hbase hψ
  linarith

/-- A strictly positive point-spectrum gap survives an arbitrary signed
bounded perturbation when the uniform shift exceeds its norm budget. -/
theorem infiniteLocalShiftedPerturbed_eigenvalue_pos
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (hgap : |ε| * ‖P‖ < shift)
    (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen :
      infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
        eigenvalue • (ψ.1 : TileHilbert Tile))
    (hψ : (ψ.1 : TileHilbert Tile) ≠ 0) :
    0 < eigenvalue := by
  have hbound := infiniteLocalShiftedPerturbed_eigenvalue_ge
    D V σ w P ε shift hV hw ψ eigenvalue heigen hψ
  linarith

end SpectralGeometry
