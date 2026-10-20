module

public import SpectralGeometry.InfiniteLocalFullOrderedEigenvalueDivergence
public import SpectralGeometry.InfiniteLocalCoerciveGap

public section

/-!
# Quadratic-form comparison for the full interacting operator

A quantitative comparison of the n-th *ordered* interacting eigenvalue
with the n-th diagonal onsite level requires a min--max or counting
argument in the infinite-dimensional unbounded setting. Before that
spectral counting step, the key variational hypothesis can be proved
directly on the unchanged natural onsite domain.

For H = M_V + B and bounded B = L_w + εP + shift I, we prove
  |⟪ψ,Hψ⟫ - ⟪ψ,M_V ψ⟫| ≤ ‖B‖ ‖ψ‖²
for all ψ in the natural domain, without assuming positivity, symmetry,
compactness or an existing eigenvalue.

We also transfer any uniform onsite lower bound c to a quantitative
bound c - ‖B‖ on *all* genuine real interacting eigenvalues and on
the full real bounded-inverse spectrum under the already formalized
resolvent hypotheses. A strictly positive gap follows if c > ‖B‖.

These form inequalities provide the required input to min--max,
but do not yet establish the index-wise bound
  λ_n(H) ≥ λ_n(M_V) - ‖B‖.
That final comparison respecting multiplicities is still open.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev ComparisonEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- The bounded correction changes the full quadratic form by at most
its operator norm times the square of the state norm, on the *common
natural domain* of the full and onsite unbounded operators. -/
theorem infiniteLocalShiftedPerturbed_energy_diff_abs_le_correction_norm
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : ComparisonEnd Tile)
    (ε shift : ℝ) (ψ : infiniteOnsiteDomain V) :
    |inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ) -
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteOnsiteOperator V ψ)| ≤
      ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ *
        ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
  rw [infiniteLocalShiftedPerturbed_eq_onsite_add_correction,
    inner_add_right]
  have h :
      inner ℝ (ψ.1 : TileHilbert Tile) (infiniteOnsiteOperator V ψ) +
          inner ℝ (ψ.1 : TileHilbert Tile)
            (infiniteLocalBoundedCorrection D σ w P ε shift ψ.1) -
          inner ℝ (ψ.1 : TileHilbert Tile) (infiniteOnsiteOperator V ψ) =
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalBoundedCorrection D σ w P ε shift ψ.1) := by ring
  rw [h]
  exact infiniteLocalBoundedPerturbation_inner_abs_le
    (infiniteLocalBoundedCorrection D σ w P ε shift) ψ.1

/-- The interaction's effect on *each Rayleigh numerator* is sandwiched
between minus and plus its norm, with no assumption that the
bounded correction is positive. This is the key input to min--max. -/
theorem infiniteLocalShiftedPerturbed_energy_sandwich
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : ComparisonEnd Tile)
    (ε shift : ℝ) (ψ : infiniteOnsiteDomain V) :
    inner ℝ (ψ.1 : TileHilbert Tile) (infiniteOnsiteOperator V ψ) -
        ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ *
          ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ) ∧
    inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ) ≤
      inner ℝ (ψ.1 : TileHilbert Tile) (infiniteOnsiteOperator V ψ) +
        ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ *
          ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
  have h := infiniteLocalShiftedPerturbed_energy_diff_abs_le_correction_norm
    D V σ w P ε shift ψ
  rcases abs_le.mp h with ⟨hl, hu⟩
  constructor <;> linarith

/-- A uniform lower bound on the (possibly unbounded) onsite potential
passes to its quadratic form on the full natural domain. -/
theorem infiniteOnsiteOperator_energy_ge_lower
    (V : Tile → ℝ) (c : ℝ) (hV : ∀ t, c ≤ V t)
    (ψ : infiniteOnsiteDomain V) :
    c * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
      inner ℝ (ψ.1 : TileHilbert Tile) (infiniteOnsiteOperator V ψ) := by
  have hh :
      0 ≤ inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteOnsiteOperator V ψ - c • (ψ.1 : TileHilbert Tile)) := by
    rw [lp.inner_eq_tsum]
    apply tsum_nonneg
    intro t
    have hterm :
        0 ≤ (V t - c) * ((ψ.1 t) ^ 2) :=
      mul_nonneg (sub_nonneg.mpr (hV t)) (sq_nonneg _)
    have hpoint :
        0 ≤ (ψ.1 t) * (V t * ψ.1 t - c * ψ.1 t) := by
      nlinarith [hterm]
    have hcoord :
        (infiniteOnsiteOperator V ψ -
          c • (ψ.1 : TileHilbert Tile)) t =
        V t * ψ.1 t - c * ψ.1 t := by
      change V t * ψ.1 t - c * ψ.1 t =
        V t * ψ.1 t - c * ψ.1 t
      rfl
    simpa [RCLike.inner_apply, hcoord, starRingEnd_apply, mul_comm] using hpoint
  rw [inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at hh
  linarith

/-- An onsite lower bound c implies the genuine interacting real
eigenvalue bound c - ‖B‖. It does not require symmetry of B. -/
theorem infiniteLocalShiftedPerturbed_eigenvalue_ge_onsite_lower_sub_norm
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : ComparisonEnd Tile)
    (ε shift : ℝ) (c : ℝ) (hV : ∀ t, c ≤ V t)
    (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen : infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
      eigenvalue • (ψ.1 : TileHilbert Tile))
    (hψ : (ψ.1 : TileHilbert Tile) ≠ 0) :
    c - ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ ≤ eigenvalue := by
  have hon := infiniteOnsiteOperator_energy_ge_lower V c hV ψ
  have hform := (infiniteLocalShiftedPerturbed_energy_sandwich
    D V σ w P ε shift ψ).1
  have hnorm : 0 < ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hψ)
  have heq :
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ) =
        eigenvalue * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
    rw [heigen, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hscaled :
      (c - ‖infiniteLocalBoundedCorrection D σ w P ε shift‖) *
          ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
        eigenvalue * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
    rw [← heq]
    nlinarith
  exact (mul_le_mul_iff_of_pos_right hnorm).mp hscaled

/-- Under the compact-resolvent real spectral-exhaustion hypotheses,
the *entire real bounded-inverse spectrum* satisfies the same uniform
onsite-minus-perturbation-norm lower bound, not only named eigenvectors. -/
theorem infiniteLocalMatching_full_real_spectrum_ge_onsite_lower_sub_norm
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : ComparisonEnd Tile)
    (ε shift a c : ℝ) (hV : ∀ t, c ≤ V t)
    (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ)
    (hspectrum : eigenvalue ∈ infiniteBoundedOnsiteRealSpectrum V
      (infiniteLocalBoundedCorrection D σ w P ε shift)) :
    c - ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ ≤ eigenvalue := by
  obtain ⟨ψ, hψ, heigen⟩ :=
    (infiniteLocalMatching_fullRealSpectrum_iff_hasFullEigenvalue
      D V σ w P ε shift a hgap hproper hsmall eigenvalue).mp hspectrum
  exact infiniteLocalShiftedPerturbed_eigenvalue_ge_onsite_lower_sub_norm
    D V σ w P ε shift c hV ψ eigenvalue heigen hψ

/-- The same explicit estimate becomes a strictly positive gap of the
entire real bounded-inverse spectrum if c > ‖B‖. -/
theorem infiniteLocalMatching_full_real_spectrum_pos_of_onsite_gap
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : ComparisonEnd Tile)
    (ε shift a c : ℝ) (hV : ∀ t, c ≤ V t)
    (hstrong : ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ < c)
    (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ)
    (hspectrum : eigenvalue ∈ infiniteBoundedOnsiteRealSpectrum V
      (infiniteLocalBoundedCorrection D σ w P ε shift)) :
    0 < eigenvalue := by
  have hh := infiniteLocalMatching_full_real_spectrum_ge_onsite_lower_sub_norm
    D V σ w P ε shift a c hV hgap hproper hsmall eigenvalue hspectrum
  linarith

end SpectralGeometry
