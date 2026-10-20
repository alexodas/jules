module

public import SpectralGeometry.InfiniteLocalSignedPerturbationGap

public section

/-!
# Coercive energy and residual gap for infinite local operators

The preceding point-spectrum estimates only constrain genuine eigenvectors.
Here the same geometric hypotheses yield a quantitative lower bound for the
quadratic energy of *every* state in the natural onsite domain D(V).

Write H = M_V + L_w + ε P + m I, where V and the matching weights are
nonnegative, P is any bounded real-linear map, and ε,m are real. Then

  (m - |ε| * ‖P‖) * ‖ψ‖² ≤ ⟪ψ, H ψ⟫

for all ψ in D(V), without requiring P to be positive or symmetric.

Furthermore, for any real parameter a, the residual obeys

  (m - |ε| * ‖P‖ - a) * ‖ψ‖ ≤ ‖H ψ - a ψ‖.

If a < m - |ε| * ‖P‖, the shifted operator H-aI has trivial kernel, and
unit vectors in D(V) cannot have arbitrarily small residual.

IMPORTANT: These estimates do not prove that H-aI is surjective or has a
bounded inverse, nor do they prove self-adjointness, compact resolvent or
discreteness of spectrum. Without symmetry of P, no full-spectrum claim is
made.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- Coercive quadratic-form lower bound on the entire (possibly infinite)
natural onsite domain, not only on eigenvectors. -/
theorem infiniteLocalShiftedPerturbed_energy_ge
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (ψ : infiniteOnsiteDomain V) :
    (shift - |ε| * ‖P‖) * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ) := by
  have honsite := infiniteOnsiteOperator_energy_nonneg V hV ψ
  have hedge :=
    infiniteLocalMatchingLaplacian_energy_nonneg D σ w hw ψ.1
  have habs :=
    infiniteLocalBoundedPerturbation_inner_abs_le P
      (ψ.1 : TileHilbert Tile)
  have hperturb :
      -(|ε| * ‖P‖) * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
        ε * inner ℝ (ψ.1 : TileHilbert Tile) (P ψ.1) := by
    have hbound :
        |ε * inner ℝ (ψ.1 : TileHilbert Tile) (P ψ.1)| ≤
          |ε| * (‖P‖ * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left habs (abs_nonneg ε)
    calc
      -(|ε| * ‖P‖) * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 =
          -(|ε| * (‖P‖ * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2)) := by ring
      _ ≤ ε * inner ℝ (ψ.1 : TileHilbert Tile) (P ψ.1) :=
        (abs_le.mp hbound).1
  have henergy :
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ) =
      inner ℝ (ψ.1 : TileHilbert Tile) (infiniteOnsiteOperator V ψ) +
        inner ℝ (ψ.1 : TileHilbert Tile)
          (infiniteLocalMatchingLaplacian D σ w ψ.1) +
        ε * inner ℝ (ψ.1 : TileHilbert Tile) (P ψ.1) +
        shift * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
    rw [infiniteLocalShiftedPerturbedOperator_apply,
      infiniteLocalMatchingPerturbedOperator_apply]
    simp only [inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  calc
    (shift - |ε| * ‖P‖) * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 =
        -(|ε| * ‖P‖) * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 +
          shift * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by ring
    _ ≤
        (inner ℝ (ψ.1 : TileHilbert Tile) (infiniteOnsiteOperator V ψ) +
        inner ℝ (ψ.1 : TileHilbert Tile)
          (infiniteLocalMatchingLaplacian D σ w ψ.1) +
        ε * inner ℝ (ψ.1 : TileHilbert Tile) (P ψ.1)) +
          shift * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
      linarith
    _ = inner ℝ (ψ.1 : TileHilbert Tile)
          (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ) := by
      rw [henergy]

/-- Lower bound on the residual for any real spectral parameter.
When the coefficient on the left is positive, this is a genuine
uniform bound away from zero. -/
theorem infiniteLocalShiftedPerturbed_residual_norm_ge
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift spectralParameter : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (ψ : infiniteOnsiteDomain V) :
    (shift - |ε| * ‖P‖ - spectralParameter) *
      ‖(ψ.1 : TileHilbert Tile)‖ ≤
      ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
        spectralParameter • (ψ.1 : TileHilbert Tile)‖ := by
  have hcoercive :=
    infiniteLocalShiftedPerturbed_energy_ge
      D V σ w P ε shift hV hw ψ
  have hinner :
      (shift - |ε| * ‖P‖ - spectralParameter) *
          ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
        inner ℝ (ψ.1 : TileHilbert Tile)
          (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
            spectralParameter • (ψ.1 : TileHilbert Tile)) := by
    rw [inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    nlinarith
  have hupper :
      inner ℝ (ψ.1 : TileHilbert Tile)
          (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
            spectralParameter • (ψ.1 : TileHilbert Tile)) ≤
        ‖(ψ.1 : TileHilbert Tile)‖ *
          ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
            spectralParameter • (ψ.1 : TileHilbert Tile)‖ :=
    real_inner_le_norm _ _
  by_cases hz : (ψ.1 : TileHilbert Tile) = 0
  · simpa [hz] using
      (norm_nonneg
        (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
          spectralParameter • (ψ.1 : TileHilbert Tile)))
  · have hnorm : 0 < ‖(ψ.1 : TileHilbert Tile)‖ :=
      norm_pos_iff.mpr hz
    have hscaled :
        ‖(ψ.1 : TileHilbert Tile)‖ *
          ((shift - |ε| * ‖P‖ - spectralParameter) *
            ‖(ψ.1 : TileHilbert Tile)‖) ≤
          ‖(ψ.1 : TileHilbert Tile)‖ *
            ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
              spectralParameter • (ψ.1 : TileHilbert Tile)‖ := by
      calc
        _ = (shift - |ε| * ‖P‖ - spectralParameter) *
              ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by ring
        _ ≤ _ := hinner
        _ ≤ _ := hupper
    exact (mul_le_mul_iff_of_pos_left hnorm).mp hscaled

/-- Below the coercive threshold, there is no nonzero solution
to H ψ = a ψ on the natural domain. -/
theorem infiniteLocalShiftedPerturbed_kernel_trivial_below
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift spectralParameter : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (hbelow : spectralParameter < shift - |ε| * ‖P‖)
    (ψ : infiniteOnsiteDomain V)
    (heq :
      infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
        spectralParameter • (ψ.1 : TileHilbert Tile)) :
    (ψ.1 : TileHilbert Tile) = 0 := by
  by_contra hnonzero
  have hnorm : 0 < ‖(ψ.1 : TileHilbert Tile)‖ :=
    norm_pos_iff.mpr hnonzero
  have hgap : 0 < shift - |ε| * ‖P‖ - spectralParameter := by
    linarith
  have hresidual :=
    infiniteLocalShiftedPerturbed_residual_norm_ge
      D V σ w P ε shift spectralParameter hV hw ψ
  rw [heq, sub_self, norm_zero] at hresidual
  have hpos :
      0 < (shift - |ε| * ‖P‖ - spectralParameter) *
        ‖(ψ.1 : TileHilbert Tile)‖ := mul_pos hgap hnorm
  linarith

/-- In particular, unit vectors have a uniformly non-small residual
for every real parameter strictly below the threshold. -/
theorem infiniteLocalShiftedPerturbed_unit_residual_ge
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift spectralParameter : ℝ)
    (hV : ∀ t, 0 ≤ V t) (hw : ∀ i, 0 ≤ w i)
    (ψ : infiniteOnsiteDomain V)
    (hunit : ‖(ψ.1 : TileHilbert Tile)‖ = 1) :
    shift - |ε| * ‖P‖ - spectralParameter ≤
      ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
        spectralParameter • (ψ.1 : TileHilbert Tile)‖ := by
  have hbound :=
    infiniteLocalShiftedPerturbed_residual_norm_ge
      D V σ w P ε shift spectralParameter hV hw ψ
  simpa only [hunit, mul_one] using hbound

end SpectralGeometry
