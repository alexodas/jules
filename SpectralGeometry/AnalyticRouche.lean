module

public import SpectralGeometry.AnalyticDiskZeroCount
public import SpectralGeometry.AnalyticZeroLocalization

public section

/-!
# Rouché's theorem and exact local zero multiplicities

A strict relative error on a circular boundary preserves the total
analytic zero order in the disk. Combined with local cofactor control,
this yields exactly `m` zeros, counted with multiplicity, and the existing
power bound for their locations. No simplicity is required.
-/

namespace SpectralGeometry

open Filter Metric Set
open scoped Topology

noncomputable section

theorem rouche_boundary_nonzero {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (herr : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    (∀ z ∈ sphere c R, f z ≠ 0) ∧ (∀ z ∈ sphere c R, g z ≠ 0) := by
  constructor
  · intro z hz
    exact norm_pos_iff.mp ((norm_nonneg _).trans_lt (herr z hz))
  · intro z hz hgz
    have he := herr z hz
    simp [hgz] at he

/-- The boundary quotient lies in the disk of radius one about one. Its
principal logarithm is an explicit primitive of the difference of the
logarithmic derivatives along the circle. -/
theorem rouche_logDeriv_integral_eq {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (herr : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    (∮ z in C(c, R), logDeriv g z) = ∮ z in C(c, R), logDeriv f z := by
  obtain ⟨hfn, hgn⟩ := rouche_boundary_nonzero herr
  have hfi : CircleIntegrable (logDeriv f) c R :=
    ContinuousOn.circleIntegrable hR.le
      (analyticOnNhd_logDeriv (hf.mono sphere_subset_closedBall) hfn).continuousOn
  have hgi : CircleIntegrable (logDeriv g) c R :=
    ContinuousOn.circleIntegrable hR.le
      (analyticOnNhd_logDeriv (hg.mono sphere_subset_closedBall) hgn).continuousOn
  have hz : (∮ z in C(c, R), logDeriv g z - logDeriv f z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le
      (f := fun z => Complex.log (g z / f z))
    intro z hz
    have hratio : ‖g z / f z - 1‖ < 1 := by
      rw [div_sub_one (hfn z hz), norm_div]
      exact (div_lt_one (norm_pos_iff.mpr (hfn z hz))).mpr (herr z hz)
    have hslit : g z / f z ∈ Complex.slitPlane :=
      Complex.ball_one_subset_slitPlane (mem_ball_iff_norm.mpr hratio)
    have hd := ((hg z (sphere_subset_closedBall hz)).differentiableAt.hasDerivAt.div
      (hf z (sphere_subset_closedBall hz)).differentiableAt.hasDerivAt (hfn z hz)).clog hslit
    have he : ((deriv g z * f z - g z * deriv f z) / f z ^ 2) / (g z / f z) =
        logDeriv g z - logDeriv f z := by
      simp only [logDeriv_apply]
      field_simp [hfn z hz, hgn z hz]
    simp only [Pi.div_apply] at hd
    rw [he] at hd
    exact hd.hasDerivWithinAt
  rw [circleIntegral.integral_sub hgi hfi] at hz
  exact sub_eq_zero.mp hz

/-- Rouché's theorem for a positive-radius disk. Analyticity is required
on a neighborhood of the closed disk. The strict boundary inequality
also proves both boundary zero exclusions. -/
theorem analytic_disk_rouche {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (herr : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    analyticDiskZeroCount g c R = analyticDiskZeroCount f c R := by
  obtain ⟨hfn, hgn⟩ := rouche_boundary_nonzero herr
  have he := rouche_logDeriv_integral_eq hR hf hg herr
  rw [analytic_disk_argument_principle hR hg hgn,
    analytic_disk_argument_principle hR hf hfn] at he
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  exact_mod_cast mul_right_cancel₀ hc he

/-- The reference disk contains one distinct zero of order `m`. -/
theorem LocalAnalyticZeroControl.zero_count {f : ℂ → ℂ} {a : ℂ} {m : ℕ} {ρ C : ℝ}
    (h : LocalAnalyticZeroControl f a m ρ C) : analyticDiskZeroCount f a ρ = m := by
  classical
  have hb : ∀ z ∈ sphere a ρ, f z ≠ 0 := by
    intro z hz hfz
    have he := (h.zero_iff (sphere_subset_closedBall hz)).mp hfz
    have hdist := mem_sphere.mp hz
    simp only [he, dist_self] at hdist
    linarith [h.radius_pos]
  have ha : a ∈ analyticDiskZeroSet f a ρ :=
    (mem_analyticDiskZeroSet_iff h.radius_pos h.analytic hb).mpr ⟨mem_ball_self h.radius_pos, h.zero⟩
  rw [analyticDiskZeroCount_eq_sum]
  rw [Finset.sum_eq_single a]
  · have ho := analyticDisk_divisor_order h.radius_pos h.analytic hb
      (mem_closedBall_self h.radius_pos.le)
    rw [h.order] at ho
    exact_mod_cast ho.symm
  · intro z hz hza
    have hz' := (mem_analyticDiskZeroSet_iff h.radius_pos h.analytic hb).mp hz
    exact (hza ((h.zero_iff (ball_subset_closedBall hz'.1)).mp hz'.2)).elim
  · exact fun hn => (hn ha).elim

/-- A boundary error smaller than the reference lower bound preserves
exactly `m` zeros with multiplicity. The factor two needed by the earlier
existence-only proof is unnecessary for this count. -/
theorem LocalAnalyticZeroControl.approximation_zero_count
    {f g : ℂ → ℂ} {a : ℂ} {m : ℕ} {ρ C ε : ℝ}
    (h : LocalAnalyticZeroControl f a m ρ C)
    (hg : AnalyticOnNhd ℂ g (closedBall a ρ))
    (herr : ∀ z ∈ sphere a ρ, ‖g z - f z‖ ≤ ε)
    (hsmall : ε < C * ρ ^ m) :
    analyticDiskZeroCount g a ρ = m ∧
      (∀ z ∈ sphere a ρ, g z ≠ 0) ∧
      (∀ z ∈ closedBall a ρ, g z = 0 → ‖z - a‖ ^ m ≤ ε / C) := by
  have he : ∀ z ∈ sphere a ρ, ‖g z - f z‖ < ‖f z‖ := by
    intro z hz
    have hl := h.lower z (sphere_subset_closedBall hz)
    rw [mem_sphere_iff_norm.mp hz] at hl
    exact (herr z hz).trans_lt (hsmall.trans_le hl)
  refine ⟨(analytic_disk_rouche h.radius_pos h.analytic hg he).trans h.zero_count,
    (rouche_boundary_nonzero he).2, ?_⟩
  have herr' := analytic_error_le_on_closedBall h.radius_pos h.analytic hg herr
  intro z hz hgz
  have he' : ‖f z‖ ≤ ε := by simpa [hgz] using herr' z hz
  apply (le_div_iff₀ h.constant_pos).mpr
  simpa [mul_comm] using (h.lower z hz).trans he'

end
end SpectralGeometry
