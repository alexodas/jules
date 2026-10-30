module

public import Mathlib

public section

/-!
# Zero counts and the argument principle on a disk

The count is a finite sum of nonnegative orders. For functions analytic
near a positive-radius closed disk and nonzero on its boundary, its
support is exactly the interior zero set and every order is finite.
-/

namespace SpectralGeometry

open Filter Metric Set
open scoped Topology ComplexConjugate

noncomputable section

/-- Finite support of the divisor on the closed disk. Its interpretation
as the zero set requires the analytic and boundary hypotheses below. -/
@[expose] def analyticDiskZeroSet (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor f (closedBall c R)).finiteSupport
    (isCompact_closedBall c R)).toFinset

/-- Total zero order on a disk, counting repetitions. The theorems below
exclude the default divisor values of nonanalytic or identically zero functions. -/
@[expose] def analyticDiskZeroCount (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℕ :=
  ∑ z ∈ analyticDiskZeroSet f c R, (MeromorphicOn.divisor f (closedBall c R) z).toNat

/-- The count is the sum of the orders on its finite zero support. -/
theorem analyticDiskZeroCount_eq_sum (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    analyticDiskZeroCount f c R = ∑ z ∈ analyticDiskZeroSet f c R,
      (MeromorphicOn.divisor f (closedBall c R) z).toNat := rfl

theorem analyticOrderAt_ne_top_on_disk {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, f z ≠ 0) {z : ℂ} (hz : z ∈ closedBall c R) :
    analyticOrderAt f z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty.mpr hR.le : (sphere c R).Nonempty)
  apply hf.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall c R).isPreconnected (sphere_subset_closedBall hw) hz
  rw [(hf w (sphere_subset_closedBall hw)).analyticOrderAt_eq_zero.mpr (hb w hw)]
  simp

/-- On the disk the natural-valued divisor equals the genuine analytic order. -/
theorem analyticDisk_divisor_order {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, f z ≠ 0) {z : ℂ} (hz : z ∈ closedBall c R) :
    analyticOrderAt f z =
      ((MeromorphicOn.divisor f (closedBall c R) z).toNat : ℕ∞) := by
  have hn := analyticOrderAt_ne_top_on_disk hR hf hb hz
  lift analyticOrderAt f z to ℕ using hn with n ho
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz, ← ho]
  simp

/-- The finite support is exactly the interior zero set; no boundary zero
or infinite-order point is silently discarded. -/
theorem mem_analyticDiskZeroSet_iff {f : ℂ → ℂ} {c z : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, f z ≠ 0) :
    z ∈ analyticDiskZeroSet f c R ↔ z ∈ ball c R ∧ f z = 0 := by
  classical
  change z ∈ ((MeromorphicOn.divisor f (closedBall c R)).finiteSupport (isCompact_closedBall c R)).toFinset ↔ _
  rw [Set.Finite.mem_toFinset, Function.mem_support]
  constructor
  · intro hd
    have hz := (MeromorphicOn.divisor f (closedBall c R)).supportWithinDomain hd
    have ho := analyticDisk_divisor_order hR hf hb hz
    have hzero : f z = 0 := by
      apply (hf z hz).analyticOrderAt_ne_zero.mp
      rw [ho]
      have hnonneg := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z
      change (0 : ℤ) ≤ MeromorphicOn.divisor f (closedBall c R) z at hnonneg
      have hn : (MeromorphicOn.divisor f (closedBall c R) z).toNat ≠ 0 := by omega
      exact_mod_cast hn
    refine ⟨?_, hzero⟩
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hlt | heq
    · exact mem_ball.mpr hlt
    · exact (hb z (mem_sphere.mpr heq) hzero).elim
  · rintro ⟨hz, hzero⟩ hd
    have ho := analyticDisk_divisor_order hR hf hb (ball_subset_closedBall hz)
    simp only [hd, Int.toNat_zero, Nat.cast_zero] at ho
    exact (hf z (ball_subset_closedBall hz)).analyticOrderAt_ne_zero.mpr hzero ho

/-- Factor out every zero with its full order. The equality holds as an
analytic germ even at the boundary of the disk. -/
theorem analytic_disk_factorization {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ z ∈ closedBall c R, g z ≠ 0) ∧
      ∀ z ∈ closedBall c R, f =ᶠ[𝓝 z]
        (fun w => (∏ u ∈ analyticDiskZeroSet f c R,
          (w - u) ^ (MeromorphicOn.divisor f (closedBall c R) u).toNat) * g w) := by
  classical
  let D := MeromorphicOn.divisor f (closedBall c R)
  have hD : D.support.Finite := D.finiteSupport (isCompact_closedBall c R)
  have hn : ∀ z : closedBall c R, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    rw [(hf z z.property).meromorphicOrderAt_eq]
    simpa using analyticOrderAt_ne_top_on_disk hR hf hb z.property
  obtain ⟨g, hg, hgn, hfg⟩ := hf.meromorphicOn.extract_zeros_poles hn hD
  let φ : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  have hφ : ∀ z, AnalyticAt ℂ φ z := fun z =>
    Function.FactorizedRational.analyticAt (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z)
  have hprod : φ = fun w => ∏ u ∈ analyticDiskZeroSet f c R, (w - u) ^ (D u).toNat := by
    dsimp [φ]
    rw [finprod_eq_prod_of_mulSupport_subset (s := analyticDiskZeroSet f c R)]
    · ext w
      simp only [Finset.prod_apply, Pi.pow_apply]
      apply Finset.prod_congr rfl
      intro u _
      conv_lhs => rw [← Int.toNat_of_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u)]
      exact zpow_natCast _ _
    · simp [Function.FactorizedRational.mulSupport, analyticDiskZeroSet, D]
  have hperfect : Preperfect (closedBall c R) := by
    simpa [closure_ball c hR.ne'] using (isOpen_ball (x := c) (ε := R)).perfect_closure.acc
  refine ⟨g, hg, fun z hz => hgn ⟨z, hz⟩, ?_⟩
  intro z hz
  have hp : AnalyticAt ℂ (φ • g) z := (hφ z).smul (hg z hz)
  have he := (hf z hz).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    hp.meromorphicAt hz hperfect hfg
  have he' := ((hf z hz).frequently_eq_iff_eventually_eq hp).mp he.frequently
  simpa only [Filter.EventuallyEq, hprod, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, D] using he'

/-- The logarithmic derivative is analytic wherever the function is analytic
and nonzero. -/
theorem analyticOnNhd_logDeriv {f : ℂ → ℂ} {s : Set ℂ}
    (hf : AnalyticOnNhd ℂ f s) (hn : ∀ z ∈ s, f z ≠ 0) :
    AnalyticOnNhd ℂ (logDeriv f) s :=
  fun z hz => (hf z hz).deriv.div (hf z hz) (hn z hz)

private theorem disk_sub_ne_zero {c z u : ℂ} {R : ℝ}
    (hz : z ∈ sphere c R) (hu : u ∈ ball c R) : z - u ≠ 0 := by
  intro h
  have he : z = u := sub_eq_zero.mp h
  have hl := mem_ball.mp hu
  have hb := mem_sphere.mp hz
  rw [he] at hb
  linarith

/-- Argument principle on a disk: the integral counts analytic orders,
including multiplicities, with no simplicity assumption. -/
theorem analytic_disk_argument_principle {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, f z ≠ 0) :
    (∮ z in C(c, R), logDeriv f z) =
      (analyticDiskZeroCount f c R : ℂ) * (2 * Real.pi * Complex.I) := by
  classical
  let s := analyticDiskZeroSet f c R
  let m := fun u => (MeromorphicOn.divisor f (closedBall c R) u).toNat
  let p := fun z => ∏ u ∈ s, (z - u) ^ m u
  have hs : ∀ u ∈ s, u ∈ ball c R := fun u hu =>
    ((mem_analyticDiskZeroSet_iff hR hf hb).mp hu).1
  obtain ⟨g, hg, hgn, hfg⟩ := analytic_disk_factorization hR hf hb
  have hglog := analyticOnNhd_logDeriv hg hgn
  have hgint : CircleIntegrable (logDeriv g) c R :=
    ContinuousOn.circleIntegrable hR.le (hglog.continuousOn.mono sphere_subset_closedBall)
  have hgz : (∮ z in C(c, R), logDeriv g z) = 0 := by
    apply DiffContOnCl.circleIntegral_eq_zero hR.le
    apply DifferentiableOn.diffContOnCl
    simpa only [closure_ball c hR.ne'] using hglog.differentiableOn
  have hterm : ∀ u ∈ s, CircleIntegrable (fun z => (m u : ℂ) * (z - u)⁻¹) c R := by
    intro u hu
    apply ContinuousOn.circleIntegrable hR.le
    exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz => disk_sub_ne_zero hz (hs u hu))).const_mul _
  have he : ∀ z ∈ sphere c R,
      logDeriv f z = (∑ u ∈ s, (m u : ℂ) * (z - u)⁻¹) + logDeriv g z := by
    intro z hz
    have hn : ∀ u ∈ s, z - u ≠ 0 := fun u hu => disk_sub_ne_zero hz (hs u hu)
    have hpn : p z ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun u hu => pow_ne_zero _ (hn u hu))
    have hpd : DifferentiableAt ℂ p z := by dsimp [p]; fun_prop
    have hp : logDeriv p z = ∑ u ∈ s, (m u : ℂ) * (z - u)⁻¹ := by
      dsimp [p]
      rw [logDeriv_fun_prod (f := fun u z : ℂ => (z - u) ^ m u) (fun u hu => pow_ne_zero _ (hn u hu)) (fun _ _ => by fun_prop)]
      apply Finset.sum_congr rfl
      intro u _
      rw [logDeriv_fun_pow (f := fun w : ℂ => w - u) (x := z) (by fun_prop)]
      simp [logDeriv_apply]
    rw [(logDeriv_congr_nhds (hfg z (sphere_subset_closedBall hz))).self_of_nhds]
    change logDeriv (p * g) z = _
    rw [logDeriv_mul z hpn (hgn z (sphere_subset_closedBall hz)) hpd
      (hg z (sphere_subset_closedBall hz)).differentiableAt, hp]
  calc
    (∮ z in C(c, R), logDeriv f z) =
        ∮ z in C(c, R), (∑ u ∈ s, (m u : ℂ) * (z - u)⁻¹) + logDeriv g z :=
      circleIntegral.integral_congr hR.le he
    _ = (∑ u ∈ s, (m u : ℂ) * (2 * Real.pi * Complex.I)) := by
      have hsum : CircleIntegrable (fun z => ∑ u ∈ s, (m u : ℂ) * (z - u)⁻¹) c R := by
        exact CircleIntegrable.fun_sum s hterm
      rw [circleIntegral.integral_add hsum hgint, hgz, add_zero,
        circleIntegral.integral_fun_sum hterm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball (hs u hu)]
    _ = (analyticDiskZeroCount f c R : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [← Finset.sum_mul]
      simp only [analyticDiskZeroCount, Nat.cast_sum, s, m]

end
end SpectralGeometry
