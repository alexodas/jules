module

public import Mathlib

public section

/-!
# Quantitative local zeros from scalar analytic approximation

A finite zero order supplies a local lower bound with the correct power.
A boundary error certificate extends to the disk by the maximum principle.
Under an explicit smallness condition the approximant has a zero in the
disk, and every zero there satisfies the power bound. This does not assert
equality of zero counts or simplicity of the approximating zeros.
-/

namespace SpectralGeometry

open Filter Metric Set
open scoped Topology

noncomputable section

/-- Local data derived from a finite positive analytic zero order. The
constant is a lower bound for the nonvanishing analytic cofactor. -/
structure LocalAnalyticZeroControl (f : ℂ → ℂ) (a : ℂ) (m : ℕ)
    (ρ C : ℝ) : Prop where
  radius_pos : 0 < ρ
  constant_pos : 0 < C
  order_pos : 0 < m
  analytic : AnalyticOnNhd ℂ f (closedBall a ρ)
  order : analyticOrderAt f a = (m : ℕ∞)
  lower : ∀ z ∈ closedBall a ρ, C * ‖z - a‖ ^ m ≤ ‖f z‖

/-- The local constants exist for every finite-order zero; no lower-bound
certificate for the cofactor is assumed in this existence theorem. -/
theorem exists_localAnalyticZeroControl {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f a) (hm : 0 < m)
    (ho : analyticOrderAt f a = (m : ℕ∞)) :
    ∃ ρ C : ℝ, LocalAnalyticZeroControl f a m ρ C := by
  obtain ⟨g, hg, hga, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  let C := ‖g a‖ / 2
  have hC : 0 < C := half_pos (norm_pos_iff.mpr hga)
  have hClt : C < ‖g a‖ := half_lt_self (norm_pos_iff.mpr hga)
  have hgl : ∀ᶠ z in 𝓝 a, C ≤ ‖g z‖ :=
    (hg.continuousAt.norm.eventually (lt_mem_nhds hClt)).mono (fun _ hz => hz.le)
  have hfa : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ f z :=
    (isOpen_analyticAt ℂ f).eventually_mem hf
  obtain ⟨ρ, hρ, hall⟩ := nhds_basis_closedBall.mem_iff.mp (hfa.and (hfg.and hgl))
  refine ⟨ρ, C, hρ, hC, hm, fun z hz => (hall hz).1, ho, ?_⟩
  intro z hz
  have hz' := hall hz
  rw [hz'.2.1, norm_smul, norm_pow]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hz'.2.2 (pow_nonneg (norm_nonneg (z - a)) m)

theorem LocalAnalyticZeroControl.zero {f : ℂ → ℂ} {a : ℂ} {m : ℕ} {ρ C : ℝ}
    (h : LocalAnalyticZeroControl f a m ρ C) : f a = 0 := by
  apply (h.analytic a (mem_closedBall_self h.radius_pos.le)).analyticOrderAt_ne_zero.mp
  rw [h.order]
  exact_mod_cast (Nat.ne_of_gt h.order_pos)

/-- The reference disk isolates one distinct zero, with its full order. -/
theorem LocalAnalyticZeroControl.zero_iff {f : ℂ → ℂ} {a : ℂ} {m : ℕ} {ρ C : ℝ}
    (h : LocalAnalyticZeroControl f a m ρ C) {z : ℂ} (hz : z ∈ closedBall a ρ) :
    f z = 0 ↔ z = a := by
  constructor
  · intro hfz
    by_contra hza
    have hp := mul_pos h.constant_pos
      (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hza)) m)
    have hl := h.lower z hz
    simp only [hfz, norm_zero] at hl
    exact (not_le_of_gt hp) hl
  · rintro rfl
    exact h.zero

/-- A holomorphic function whose center value is strictly smaller in norm
than every boundary value must have an interior zero. -/
theorem analytic_exists_zero_of_boundary_norm_lt {g : ℂ → ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hg : DiffContOnCl ℂ g (ball a ρ))
    (hlt : ∀ z ∈ sphere a ρ, ‖g a‖ < ‖g z‖) :
    ∃ z ∈ ball a ρ, g z = 0 := by
  by_contra hn
  have hne : ∀ z ∈ closedBall a ρ, g z ≠ 0 := by
    intro z hz
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hz | hz
    · exact fun hgz => hn ⟨z, mem_ball.mpr hz, hgz⟩
    · exact norm_pos_iff.mp ((norm_nonneg (g a)).trans_lt (hlt z (mem_sphere.mpr hz)))
  have hi := hg.inv (fun z hz => hne z (by simpa [closure_ball a hρ.ne'] using hz))
  obtain ⟨z, hz, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
    isBounded_ball ⟨a, mem_ball_self hρ⟩ hi
  have hzs : z ∈ sphere a ρ := by simpa [frontier_ball a hρ.ne'] using hz
  have hbound : ‖(g a)⁻¹‖ ≤ ‖(g z)⁻¹‖ := hmax (subset_closure (mem_ball_self hρ))
  simp only [norm_inv] at hbound
  have hga : 0 < ‖g a‖ := norm_pos_iff.mpr (hne a (mem_closedBall_self hρ.le))
  exact (not_le_of_gt (inv_strictAnti₀ hga (hlt z hzs))) hbound

/-- A certified boundary error controls the whole closed disk. -/
theorem analytic_error_le_on_closedBall {f g : ℂ → ℂ} {a : ℂ} {ρ ε : ℝ}
    (hρ : 0 < ρ) (hf : AnalyticOnNhd ℂ f (closedBall a ρ))
    (hg : AnalyticOnNhd ℂ g (closedBall a ρ))
    (herr : ∀ z ∈ sphere a ρ, ‖g z - f z‖ ≤ ε) :
    ∀ z ∈ closedBall a ρ, ‖g z - f z‖ ≤ ε := by
  have hd : DiffContOnCl ℂ (fun z => g z - f z) (ball a ρ) := by
    apply DifferentiableOn.diffContOnCl
    simpa only [closure_ball a hρ.ne', Pi.sub_def] using
      hg.differentiableOn.sub hf.differentiableOn
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
    (fun w hw => herr w (by simpa [frontier_ball a hρ.ne'] using hw))
  simpa [closure_ball a hρ.ne'] using hz

/-- Boundary approximation preserves at least one zero and localizes every
zero in the disk with the multiplicity-dependent power. The strict error
threshold also excludes boundary zeros. It does not certify a zero count. -/
theorem LocalAnalyticZeroControl.approximation {f g : ℂ → ℂ} {a : ℂ} {m : ℕ}
    {ρ C ε : ℝ} (h : LocalAnalyticZeroControl f a m ρ C)
    (hg : AnalyticOnNhd ℂ g (closedBall a ρ)) (hε : 0 ≤ ε)
    (herr : ∀ z ∈ sphere a ρ, ‖g z - f z‖ ≤ ε)
    (hsmall : 2 * ε < C * ρ ^ m) :
    (∃ z ∈ ball a ρ, g z = 0) ∧
    (∀ z ∈ closedBall a ρ, g z = 0 → ‖z - a‖ ^ m ≤ ε / C) ∧
    (∀ z ∈ sphere a ρ, g z ≠ 0) := by
  have herr' := analytic_error_le_on_closedBall h.radius_pos h.analytic hg herr
  have hcenter : ‖g a‖ ≤ ε := by
    simpa [h.zero] using herr' a (mem_closedBall_self h.radius_pos.le)
  have hboundary : ∀ z ∈ sphere a ρ, ε < ‖g z‖ := by
    intro z hz
    have hl := h.lower z (sphere_subset_closedBall hz)
    rw [mem_sphere_iff_norm] at hz
    rw [hz] at hl
    have he := herr z (mem_sphere_iff_norm.mpr hz)
    have ht := norm_sub_norm_le (f z) (g z)
    rw [norm_sub_rev] at he
    linarith
  refine ⟨?_, ?_, fun z hz => norm_pos_iff.mp (hε.trans_lt (hboundary z hz))⟩
  · apply analytic_exists_zero_of_boundary_norm_lt h.radius_pos
    · apply DifferentiableOn.diffContOnCl
      simpa [closure_ball a h.radius_pos.ne'] using hg.differentiableOn
    · exact fun z hz => hcenter.trans_lt (hboundary z hz)
  · intro z hz hgz
    have he : ‖f z‖ ≤ ε := by simpa [hgz] using herr' z hz
    apply (le_div_iff₀ h.constant_pos).mpr
    simpa [mul_comm] using (h.lower z hz).trans he

/-- The power estimate written as a distance bound. Repeated zeros require
the exponent `1 / m`; no linear displacement estimate is asserted. -/
theorem LocalAnalyticZeroControl.zero_distance_le {f g : ℂ → ℂ} {a : ℂ} {m : ℕ}
    {ρ C ε : ℝ} (h : LocalAnalyticZeroControl f a m ρ C)
    (herr : ∀ z ∈ closedBall a ρ, ‖g z - f z‖ ≤ ε)
    {z : ℂ} (hz : z ∈ closedBall a ρ) (hgz : g z = 0) :
    ‖z - a‖ ≤ (ε / C) ^ (1 / (m : ℝ)) := by
  have he : ‖f z‖ ≤ ε := by simpa [hgz] using herr z hz
  have hp : ‖z - a‖ ^ m ≤ ε / C := by
    apply (le_div_iff₀ h.constant_pos).mpr
    simpa [mul_comm] using (h.lower z hz).trans he
  have hr := Real.rpow_le_rpow (pow_nonneg (norm_nonneg (z - a)) m) hp
    (inv_nonneg.mpr (Nat.cast_nonneg m : (0 : ℝ) ≤ m))
  simpa only [Real.pow_rpow_inv_natCast (norm_nonneg (z - a)) h.order_pos.ne', one_div] using hr

/-- Uniform error excludes zeros wherever the reference modulus exceeds
that error; this also certifies zero-free regions between disks. -/
theorem approximation_ne_zero_of_norm_gt {f g : ℂ → ℂ} {K : Set ℂ} {ε : ℝ}
    (herr : ∀ z ∈ K, ‖g z - f z‖ ≤ ε) {z : ℂ} (hz : z ∈ K)
    (hlower : ε < ‖f z‖) : g z ≠ 0 := by
  intro hgz
  have he : ‖f z‖ ≤ ε := by simpa [hgz] using herr z hz
  exact (not_le_of_gt hlower) he

end
end SpectralGeometry
