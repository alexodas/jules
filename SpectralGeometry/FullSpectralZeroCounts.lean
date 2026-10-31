module

public import SpectralGeometry.AnalyticRouche
public import SpectralGeometry.FullSpectralZeroLocalization

public section

/-!
# Exact scalar approximation counts for full spectral products

The same local controls and inverse-square tail bounds now certify the
total analytic zero multiplicity. Approximants may have split or repeated
zeros and need not be spectral products. The exact-product interface
identifies the conserved count with the original geometric eigenspace
dimension. No finite-patch operator error is supplied by these results.
-/

namespace SpectralGeometry

open Filter Metric Set
open scoped Topology

noncomputable section

/-- An independently certified partial-product error plus the existing
tail bound preserves the full local multiplicity and the power estimate. -/
theorem LocalAnalyticZeroControl.canonical_approximation_zero_count
    {q : ℕ → ℝ} {c d a : ℂ} {m : ℕ} {ρ C : ℝ}
    (h : LocalAnalyticZeroControl (canonicalProduct q c d) a m ρ C)
    (hq : ∀ n, 0 < q n) (hs : Summable (fun n => 1 / (q n) ^ 2))
    (N : ℕ) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall a ρ))
    (η : ℝ)
    (herr : ∀ z ∈ sphere a ρ, ‖g z - canonicalPartialProduct q c d N z‖ ≤ η)
    (hsmall : canonicalProductApproximationError q
      (canonicalDiskCoordinateBound c d a ρ) N + η < C * ρ ^ m) :
    analyticDiskZeroCount g a ρ = m ∧
      (∀ z ∈ sphere a ρ, g z ≠ 0) ∧
      (∀ z ∈ closedBall a ρ, g z = 0 → ‖z - a‖ ^ m ≤
        (canonicalProductApproximationError q (canonicalDiskCoordinateBound c d a ρ) N + η) / C) := by
  apply h.approximation_zero_count hg _ hsmall
  intro z hz
  exact canonicalProduct_approximation_error_add hq hs c d N
    (affine_coordinate_le_disk_bound c d a ρ (sphere_subset_closedBall hz)) (herr z hz)

/-- Every sufficiently long truncation of the fixed spectral sequence
has the exact local zero count. The cutoff is existential until a
numerical inverse-square tail bound is supplied. -/
theorem LocalAnalyticZeroControl.eventually_partial_zero_count
    {q : ℕ → ℝ} {c d a : ℂ} {m : ℕ} {ρ C : ℝ}
    (h : LocalAnalyticZeroControl (canonicalProduct q c d) a m ρ C)
    (hq : ∀ n, 0 < q n) (hs : Summable (fun n => 1 / (q n) ^ 2)) :
    ∀ᶠ N : ℕ in atTop,
      analyticDiskZeroCount (canonicalPartialProduct q c d N) a ρ = m ∧
        (∀ z ∈ sphere a ρ, canonicalPartialProduct q c d N z ≠ 0) := by
  have hpos : 0 < C * ρ ^ m := mul_pos h.constant_pos (pow_pos h.radius_pos m)
  have he := (canonicalProductApproximationError_tendsto_zero hs
    (canonicalDiskCoordinateBound c d a ρ)).eventually (gt_mem_nhds hpos)
  filter_upwards [he] with N hN
  have hp : AnalyticOnNhd ℂ (canonicalPartialProduct q c d N) (closedBall a ρ) := by
    intro z _
    exact (Differentiable.fun_finsetProd
      (fun n (_ : n ∈ Finset.range N) => factor_differentiable (q := q) (c := c) (d := d) n)).analyticAt z
  have hc := h.canonical_approximation_zero_count hq hs N hp 0
    (fun _ _ => by simp) (by simpa using hN)
  exact ⟨hc.1, hc.2.1⟩

/-- Each signed zero of an admissible sequence has a disk on which every
sufficiently accurate analytic approximant has exactly its repetition
multiplicity. Existence of the control is proved, not an input. -/
theorem canonicalProduct_exists_local_counting_control {q : ℕ → ℝ} {c d : ℂ}
    (hq : Admissible q c d) (hd : d ≠ 0) (i : ℕ)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    ∃ ρ C : ℝ, LocalAnalyticZeroControl (canonicalProduct q c d)
      (c + d * ((sign * q i : ℝ) : ℂ)) (levelMultiplicity q (q i)) ρ C ∧
      ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall (c + d * ((sign * q i : ℝ) : ℂ)) ρ) →
        ∀ ε : ℝ,
          (∀ z ∈ sphere (c + d * ((sign * q i : ℝ) : ℂ)) ρ,
            ‖g z - canonicalProduct q c d z‖ ≤ ε) →
          ε < C * ρ ^ levelMultiplicity q (q i) →
          analyticDiskZeroCount g (c + d * ((sign * q i : ℝ) : ℂ)) ρ =
            levelMultiplicity q (q i) := by
  obtain ⟨ρ, C, h⟩ := canonicalProduct_exists_local_zero_control hq hd i sign hsign
  exact ⟨ρ, C, h, fun g hg ε herr hsmall => (h.approximation_zero_count hg herr hsmall).1⟩

variable {Tile : Type*}

/-- At a full spectral zero the conserved scalar count is the geometric
multiplicity of that operator, with the same compact-resolvent witness.
All operator/domain hypotheses are those packaged by the exact-product
interface; no eigenvalue simplicity or new spectral enumeration is assumed. -/
theorem HasExactFullSpectralProduct.local_counting_controls
    {V : Tile → ℝ} {B : TileHilbert Tile →L[ℝ] TileHilbert Tile}
    {hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite}
    {ev : ℕ → ℝ} {c d : ℂ}
    (h : HasExactFullSpectralProduct V B hproper ev c d) :
    ∃ (a : ℝ) (hunit : ∀ t, 1 ≤ V t - a),
      ∃ (hsmall : ‖(infiniteLocalBoundedCorrection 0
        (fun i => Fin.elim0 i) (fun _ => 0) B 1 0).comp
          (infiniteOnsiteResolventCLM V a hunit)‖ < 1),
        ∀ r : ℝ, 0 < r → r ∈ infiniteBoundedOnsiteRealSpectrum V B →
          ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
            ∃ ρ C : ℝ, LocalAnalyticZeroControl (canonicalProduct ev c d)
              (c + d * ((sign * r : ℝ) : ℂ))
              (infiniteLocalMatchingFullMultiplicity 0 V
                (fun i => Fin.elim0 i) (fun _ => 0) B 1 0 a hunit hproper hsmall r) ρ C ∧
              ∀ g : ℂ → ℂ,
                AnalyticOnNhd ℂ g (closedBall (c + d * ((sign * r : ℝ) : ℂ)) ρ) →
                ∀ ε : ℝ,
                  (∀ z ∈ sphere (c + d * ((sign * r : ℝ) : ℂ)) ρ,
                    ‖g z - canonicalProduct ev c d z‖ ≤ ε) →
                  ε < C * ρ ^ (infiniteLocalMatchingFullMultiplicity 0 V
                    (fun i => Fin.elim0 i) (fun _ => 0) B 1 0 a hunit hproper hsmall r) →
                  analyticDiskZeroCount g (c + d * ((sign * r : ℝ) : ℂ)) ρ =
                    infiniteLocalMatchingFullMultiplicity 0 V
                      (fun i => Fin.elim0 i) (fun _ => 0) B 1 0 a hunit hproper hsmall r := by
  obtain ⟨a, hunit, hsmall, hc⟩ := h.local_zero_controls
  refine ⟨a, hunit, hsmall, ?_⟩
  intro r hr hrs sign hsign
  obtain ⟨ρ, C, hctrl⟩ := hc r hr hrs sign hsign
  exact ⟨ρ, C, hctrl, fun g hg ε herr hε => (hctrl.approximation_zero_count hg herr hε).1⟩

end
end SpectralGeometry
