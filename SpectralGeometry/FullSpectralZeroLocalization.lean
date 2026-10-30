module

public import SpectralGeometry.AnalyticZeroLocalization
public import SpectralGeometry.CanonicalProductApproximation
public import SpectralGeometry.OrderedSpectralProductBridge
public import SpectralGeometry.InfinitePositiveSpectralControl

public section

/-!
# Scalar approximation certificates for full spectral zeros

Finite analytic orders give the power in the local zero certificate.
For a full spectral product that order is the actual geometric spectral
multiplicity. The finite-product tail estimate can be combined with an
independently certified error in an analytic approximant.

No operator error, simple root, zero-count equality, or finite-patch
interpretation is inferred from scalar closeness alone.
-/

namespace SpectralGeometry

open Filter Metric Set
open scoped Topology

noncomputable section

/-- Squared affine-coordinate bound on a disk about `a`. -/
@[expose] def canonicalDiskCoordinateBound (c d a : ℂ) (ρ : ℝ) : ℝ :=
  ((‖a - c‖ + ρ) / ‖d‖) ^ 2

theorem canonicalDiskCoordinateBound_nonneg (c d a : ℂ) (ρ : ℝ) :
    0 ≤ canonicalDiskCoordinateBound c d a ρ := sq_nonneg _

theorem affine_coordinate_le_disk_bound (c d a : ℂ) (ρ : ℝ) {z : ℂ}
    (hz : z ∈ closedBall a ρ) :
    ‖(z - c) / d‖ ^ 2 ≤ canonicalDiskCoordinateBound c d a ρ := by
  have hza : ‖z - a‖ ≤ ρ := mem_closedBall_iff_norm.mp hz
  have hzc : ‖z - c‖ ≤ ‖a - c‖ + ρ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub z a c
    linarith
  rw [norm_div]
  exact pow_le_pow_left₀ (by positivity)
    (div_le_div_of_nonneg_right hzc (norm_nonneg d)) 2

/-- Every indexed signed zero of an admissible product has local control
with its full repetition multiplicity, including repeated levels. -/
theorem canonicalProduct_exists_local_zero_control {q : ℕ → ℝ} {c d : ℂ}
    (hq : Admissible q c d) (hd : d ≠ 0) (i : ℕ)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    ∃ ρ C : ℝ, LocalAnalyticZeroControl (canonicalProduct q c d)
      (c + d * ((sign * q i : ℝ) : ℂ)) (levelMultiplicity q (q i)) ρ C := by
  have hf := (canonicalProduct_differentiable hq).analyticAt
    (c + d * ((sign * q i : ℝ) : ℂ))
  have ho := canonicalProduct_order_at_signed_level hq hd (q i) (hq.positive i) sign hsign
  have hz : canonicalProduct q c d (c + d * ((sign * q i : ℝ) : ℂ)) = 0 := by
    apply (canonicalProduct_zero_iff hq hd _).mpr
    refine ⟨i, ?_⟩
    rcases hsign with rfl | rfl
    · simp
    · right
      push_cast
      ring
  have hm : 0 < levelMultiplicity q (q i) := by
    apply Nat.pos_of_ne_zero
    intro hm
    have hne := hf.analyticOrderAt_ne_zero.mpr hz
    exact hne (by simpa [hm] using ho)
  exact exists_localAnalyticZeroControl hf hm ho

/-- A partial-product error plus its explicit infinite tail yields a
certificate for an arbitrary analytic approximant on the disk. In
particular, the approximant need not itself be a spectral product. -/
theorem LocalAnalyticZeroControl.canonical_approximation
    {q : ℕ → ℝ} {c d a : ℂ} {m : ℕ} {ρ C : ℝ}
    (h : LocalAnalyticZeroControl (canonicalProduct q c d) a m ρ C)
    (hq : ∀ n, 0 < q n) (hs : Summable (fun n => 1 / (q n) ^ 2))
    (N : ℕ) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall a ρ))
    (η : ℝ) (hη : 0 ≤ η)
    (herr : ∀ z ∈ sphere a ρ, ‖g z - canonicalPartialProduct q c d N z‖ ≤ η)
    (hsmall : 2 * (canonicalProductApproximationError q
      (canonicalDiskCoordinateBound c d a ρ) N + η) < C * ρ ^ m) :
    (∃ z ∈ ball a ρ, g z = 0) ∧
    (∀ z ∈ closedBall a ρ, g z = 0 → ‖z - a‖ ^ m ≤
      (canonicalProductApproximationError q (canonicalDiskCoordinateBound c d a ρ) N + η) / C) ∧
    (∀ z ∈ sphere a ρ, g z ≠ 0) := by
  apply h.approximation hg
    (add_nonneg (canonicalProductApproximationError_nonneg q
      (canonicalDiskCoordinateBound_nonneg c d a ρ) N) hη) _ hsmall
  intro z hz
  exact canonicalProduct_approximation_error_add hq hs c d N
    (affine_coordinate_le_disk_bound c d a ρ (sphere_subset_closedBall hz)) (herr z hz)

variable {Tile : Type*} [DecidableEq Tile]

/-- The exponent for a full spectral zero is its actual geometric
multiplicity, using the compact-resolvent witness of that product. -/
theorem HasExactFullSpectralProduct.local_zero_controls
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
                (fun i => Fin.elim0 i) (fun _ => 0) B 1 0
                a hunit hproper hsmall r) ρ C := by
  obtain ⟨a, hunit, hsmall, hf, hzeros, horders⟩ := h
  refine ⟨a, hunit, hsmall, ?_⟩
  intro r hr hrs sign hsign
  have hz : canonicalProduct ev c d (c + d * ((sign * r : ℝ) : ℂ)) = 0 := by
    apply (hzeros _).mpr
    refine ⟨r, hrs, ?_⟩
    rcases hsign with rfl | rfl
    · simp
    · right
      push_cast
      ring
  have ho := horders r hr sign hsign
  have ha := hf.analyticAt (c + d * ((sign * r : ℝ) : ℂ))
  apply exists_localAnalyticZeroControl ha _ ho
  apply Nat.pos_of_ne_zero
  intro hm
  exact (ha.analyticOrderAt_ne_zero.mpr hz) (by simpa [hm] using ho)

/-- Construct the full spectrum, its summability and exact geometric zero
orders, and local scalar zero controls, from positive-interaction onsite
hypotheses. All eigenbases use the natural multiplication domain. -/
theorem onsitePlusNonneg_exists_scalar_zero_control [Infinite Tile]
    (V : Tile → ℝ) (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (B x))
    (v₀ : ℝ) (hv₀ : 0 < v₀) (hV : ∀ t, v₀ ≤ V t)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (honsite : Summable (fun t => 1 / (V t) ^ 2)) (c d : ℂ) (hd : d ≠ 0) :
    ∃ ev : ℕ → ℝ, Monotone ev ∧
      Nonempty (DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev) ∧
      (∀ n, 0 < ev n) ∧ Summable (fun n => 1 / (ev n) ^ 2) ∧
      HasExactFullSpectralProduct V B hproper ev c d ∧
      ∀ i : ℕ, ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
        ∃ ρ C : ℝ, LocalAnalyticZeroControl (canonicalProduct ev c d)
          (c + d * ((sign * ev i : ℝ) : ℂ)) (levelMultiplicity ev (ev i)) ρ C := by
  obtain ⟨ev, hev, ⟨b⟩⟩ := onsitePlusBounded_exists_orderedEigenbasis V v₀ hV hproper B hB
  obtain ⟨_, hp, hs⟩ := onsitePlusNonneg_ordered_positive_summable
    V B hB hpos v₀ hv₀ hV hproper honsite ev hev b
  refine ⟨ev, hev, ⟨b⟩, hp, hs,
    onsitePlusBounded_hasExactFullSpectralProduct V v₀ hV hproper B hB
      ev hev b hp hs c d hd, ?_⟩
  exact fun i sign hsign => canonicalProduct_exists_local_zero_control
    (admissible_of_inv_sq_summable hp hs c d) hd i sign hsign

end
end SpectralGeometry
