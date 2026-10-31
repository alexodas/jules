module

public import SpectralGeometry.CanonicalProductNumericalBounds
public import SpectralGeometry.FullSpectralZeroCounts

public section

/-!
# A numerical zero certificate for the linear onsite model

For onsite multiplication by `n + 1` on its natural domain in `ℓ²(ℕ)`,
the full spectral product has an explicitly controlled zero at `1`.
The disk radius is `1/4`, the cofactor lower bound is `1/5`, and a
finite-product error certificate is given with a numerical cutoff.
This is a diagonal worked example, not a tiling or a finite-patch model.
-/

namespace SpectralGeometry

open Filter Metric Set
open scoped Topology

noncomputable section

/-- The concrete onsite potential and its complete increasing spectrum. -/
@[expose] def linearOnsitePotential (n : ℕ) : ℝ := (n : ℝ) + 1

theorem linearOnsitePotential_positive (n : ℕ) : 0 < linearOnsitePotential n := by
  unfold linearOnsitePotential
  positivity

theorem linearOnsitePotential_invSq_summable :
    Summable (fun n => 1 / (linearOnsitePotential n) ^ 2) :=
  infiniteOnsiteLinearGrowth_invSq_summable linearOnsitePotential (by intro n; simp [linearOnsitePotential])

theorem linearOnsitePotential_admissible (c d : ℂ) : Admissible linearOnsitePotential c d :=
  admissible_of_inv_sq_summable linearOnsitePotential_positive linearOnsitePotential_invSq_summable c d

/-- The concrete potential has finite sublevels, including empty ones. -/
theorem linearOnsitePotential_proper (R : ℝ) :
    (infiniteOnsiteLowEnergyTiles linearOnsitePotential R).Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt R
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro n hn
  change (n : ℝ) + 1 ≤ R at hn
  have hlt : (n : ℝ) < N := by linarith
  simpa using (show n < N by exact_mod_cast hlt)

/-- The sequence used in the numerical certificate is the full spectrum
with exact geometric multiplicities, not just a list of point eigenvalues. -/
theorem linearOnsite_hasExactFullSpectralProduct :
    HasExactFullSpectralProduct linearOnsitePotential
      (0 : TileHilbert ℕ →L[ℝ] TileHilbert ℕ) linearOnsitePotential_proper
      linearOnsitePotential 0 1 := by
  have he : onsitePlusBounded linearOnsitePotential (0 : TileHilbert ℕ →L[ℝ] TileHilbert ℕ) =
      infiniteOnsiteOperator linearOnsitePotential := by
    ext x
    simp
  have hb : DomainEigenbasis (infiniteOnsiteDomain linearOnsitePotential)
      (onsitePlusBounded linearOnsitePotential (0 : TileHilbert ℕ →L[ℝ] TileHilbert ℕ))
      linearOnsitePotential := by
    rw [he]
    simpa using onsiteDomainEigenbasis linearOnsitePotential (Equiv.refl ℕ)
  apply onsitePlusBounded_hasExactFullSpectralProduct linearOnsitePotential 1
    (fun n => by dsimp [linearOnsitePotential]; positivity) linearOnsitePotential_proper 0
    (by intro x y; simp) linearOnsitePotential _ hb
    linearOnsitePotential_positive linearOnsitePotential_invSq_summable 0 1 (by norm_num)
  intro i j hij
  exact add_le_add_right (Nat.cast_le.mpr hij) 1

/-- Numerical tails also hold for the complete spectrum after any
symmetric nonnegative bounded interaction. This supplies a tail certificate,
not a cofactor or isolation radius for that interacting operator. -/
theorem linearOnsitePlusNonneg_exists_numerical_tails
    (B : TileHilbert ℕ →L[ℝ] TileHilbert ℕ)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (B x)) :
    ∃ ev : ℕ → ℝ, Monotone ev ∧
      Nonempty (DomainEigenbasis (infiniteOnsiteDomain linearOnsitePotential)
        (onsitePlusBounded linearOnsitePotential B) ev) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ ev n) ∧
      Summable (fun n => 1 / (ev n) ^ 2) ∧
      (∀ N : ℕ, 0 < N → (∑' k, 1 / (ev (k + N)) ^ 2) ≤ 1 / (N : ℝ)) ∧
      (∀ A : ℝ, 0 ≤ A → A ≤ 2 → ∀ N : ℕ, 2 ≤ N →
        canonicalProductApproximationError ev A N ≤ 324 / (N : ℝ)) := by
  have hV : ∀ n, 1 ≤ linearOnsitePotential n := by
    intro n
    dsimp [linearOnsitePotential]
    positivity
  obtain ⟨ev, hev, ⟨b⟩⟩ := onsitePlusBounded_exists_orderedEigenbasis
    linearOnsitePotential 1 hV linearOnsitePotential_proper B hB
  have ho : Monotone (fun n => linearOnsitePotential ((Equiv.refl ℕ) n)) := by
    intro i j hij
    exact add_le_add_right (Nat.cast_le.mpr hij) 1
  have hg : ∀ n : ℕ, (n : ℝ) + 1 ≤ ev n := fun n =>
    onsitePlusBounded_ordered_ge_onsite_of_nonneg linearOnsitePotential B hB hpos
      (Equiv.refl ℕ) ho ev hev b n
  refine ⟨ev, hev, ⟨b⟩, hg, ?_, fun N hN => invSq_tail_le_of_linear_growth hg N hN,
    fun A hA hA2 N hN => canonicalProductApproximationError_le_linear_rate hg hA hA2 N hN⟩
  exact infiniteOnsiteLinearGrowth_invSq_summable ev (by simpa using hg)

private theorem linearOnsite_disk_norm {z : ℂ} (hz : z ∈ closedBall 1 (1 / 4 : ℝ)) :
    ‖z‖ ≤ 5 / 4 := by
  have hd := mem_closedBall_iff_norm.mp hz
  have ht := norm_le_norm_sub_add z 1
  norm_num at ht
  linarith

private theorem linearOnsite_cofactor_prefix_lower {z : ℂ}
    (hz : z ∈ closedBall 1 (1 / 4 : ℝ)) :
    (273 / 256 : ℝ) ≤ ‖-(z + 1) * factor linearOnsitePotential 0 1 1 z‖ := by
  have hd := mem_closedBall_iff_norm.mp hz
  have hzn := linearOnsite_disk_norm hz
  have hp : (7 / 4 : ℝ) ≤ ‖z + 1‖ := by
    have ht := norm_sub_le (z + 1) (z - 1)
    rw [show (z + 1) - (z - 1) = (2 : ℂ) by ring] at ht
    norm_num at ht
    linarith
  have hfactor1 : factor linearOnsitePotential 0 1 1 z = 1 - z ^ 2 / 4 := by
    norm_num [factor, perturb, linearOnsitePotential, sub_eq_add_neg]
  have h1 : (39 / 64 : ℝ) ≤ ‖factor linearOnsitePotential 0 1 1 z‖ := by
    have ht := norm_sub_le (1 - z ^ 2 / 4) (-(z ^ 2 / 4))
    simp only [sub_neg_eq_add, sub_add_cancel, norm_one, norm_neg, norm_div, norm_pow] at ht
    norm_num at ht
    rw [hfactor1]
    nlinarith [norm_nonneg z]
  rw [norm_mul, norm_neg]
  have hm := mul_le_mul hp h1 (by norm_num) (norm_nonneg _)
  nlinarith

/-- An explicit entire cofactor at the first zero, including its value
at the zero itself; it is not defined by division at that point. -/
@[expose] def linearOnsiteCofactor (z : ℂ) : ℂ :=
  -(z + 1) * factor linearOnsitePotential 0 1 1 z *
    canonicalProduct (fun n => linearOnsitePotential (n + 2)) 0 1 z

theorem linearOnsiteCofactor_differentiable : Differentiable ℂ linearOnsiteCofactor := by
  have ht := canonicalProduct_differentiable (admissible_of_inv_sq_summable
    (fun n => linearOnsitePotential_positive (n + 2))
    ((summable_nat_add_iff 2).mpr linearOnsitePotential_invSq_summable) 0 1)
  have hf := factor_differentiable (q := linearOnsitePotential) (c := 0) (d := 1) 1
  unfold linearOnsiteCofactor
  fun_prop

/-- The factorization is exact everywhere, including at the zero. -/
theorem linearOnsite_cofactor_factorization (z : ℂ) :
    canonicalProduct linearOnsitePotential 0 1 z = (z - 1) * linearOnsiteCofactor z := by
  rw [canonicalProduct_eq_partial_mul_tail linearOnsitePotential_positive
    linearOnsitePotential_invSq_summable 0 1 2 z]
  simp only [canonicalPartialProduct, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have hfactor0 : factor linearOnsitePotential 0 1 0 z = -(z - 1) * (z + 1) := by
    simp [factor, perturb, linearOnsitePotential]
    ring
  change (factor linearOnsitePotential 0 1 0 z * factor linearOnsitePotential 0 1 1 z) *
      (∏' k, factor linearOnsitePotential 0 1 (k + 2) z) =
    (z - 1) * (-(z + 1) * factor linearOnsitePotential 0 1 1 z *
      (∏' k, factor linearOnsitePotential 0 1 (k + 2) z))
  rw [hfactor0]
  ring

/-- A numerical lower bound for the actual analytic cofactor throughout
the closed disk, including at its center. -/
theorem linearOnsiteCofactor_norm_lower {z : ℂ} (hz : z ∈ closedBall 1 (1 / 4 : ℝ)) :
    (1 / 5 : ℝ) ≤ ‖linearOnsiteCofactor z‖ := by
  have hzn := linearOnsite_disk_norm hz
  have hzA : ‖(z - (0 : ℂ)) / 1‖ ^ 2 ≤ (25 / 16 : ℝ) := by
    simp only [sub_zero, div_one]
    nlinarith [norm_nonneg z]
  have htail : (∑' k, 1 / (linearOnsitePotential (k + 2)) ^ 2) ≤ (1 / 2 : ℝ) := by
    simpa using invSq_tail_le_of_linear_growth
      (q := linearOnsitePotential) (fun _ => le_rfl) 2 (by norm_num)
  have hl := canonicalProduct_tail_norm_lower linearOnsitePotential_positive
    linearOnsitePotential_invSq_summable 0 1 2 (by norm_num : (0 : ℝ) ≤ 25 / 16)
    hzA htail (by norm_num)
  change (1 / 5 : ℝ) ≤ ‖(-(z + 1) * factor linearOnsitePotential 0 1 1 z) *
    (∏' k, factor linearOnsitePotential 0 1 (k + 2) z)‖
  rw [norm_mul]
  have hm := mul_le_mul (linearOnsite_cofactor_prefix_lower hz) hl
    (by norm_num) (norm_nonneg _)
  nlinarith

/-- A fully numerical local control at the first spectral zero. The
cofactor lower bound is proved from two factors and the tail budget. -/
theorem linearOnsite_zero_control :
    LocalAnalyticZeroControl (canonicalProduct linearOnsitePotential 0 1) 1 1 (1 / 4) (1 / 5) := by
  have ha := linearOnsitePotential_admissible 0 1
  have hm : levelMultiplicity linearOnsitePotential 1 = 1 := by
    simp [levelMultiplicity, linearOnsitePotential]
  have ho := canonicalProduct_order_at_signed_level ha (by norm_num) 1 (by norm_num) 1 (Or.inl rfl)
  refine ⟨by norm_num, by norm_num, by norm_num,
    fun z _ => (canonicalProduct_differentiable ha).analyticAt z, ?_, ?_⟩
  · simpa [hm] using ho
  · intro z hz
    rw [linearOnsite_cofactor_factorization, norm_mul, pow_one]
    have hl := mul_le_mul_of_nonneg_left (linearOnsiteCofactor_norm_lower hz)
      (norm_nonneg (z - 1))
    simpa [mul_comm] using hl

/-- A rational error bound for every cutoff at least 16384, uniformly on
the whole closed disk. The finite product is not expanded computationally. -/
theorem linearOnsite_partial_error (N : ℕ) (hN : 16384 ≤ N)
    {z : ℂ} (hz : z ∈ closedBall 1 (1 / 4 : ℝ)) :
    ‖canonicalProduct linearOnsitePotential 0 1 z -
      canonicalPartialProduct linearOnsitePotential 0 1 N z‖ ≤ (1 / 50 : ℝ) := by
  have hzn := linearOnsite_disk_norm hz
  have hzA : ‖(z - (0 : ℂ)) / 1‖ ^ 2 ≤ (25 / 16 : ℝ) := by
    simp only [sub_zero, div_one]
    nlinarith [norm_nonneg z]
  have he := canonicalProduct_partial_error_le linearOnsitePotential_positive
    linearOnsitePotential_invSq_summable 0 1 N hzA
  have hr := canonicalProductApproximationError_le_linear_rate
    (q := linearOnsitePotential) (fun _ => le_rfl)
    (by norm_num : (0 : ℝ) ≤ 25 / 16) (by norm_num) N (by omega)
  apply he.trans (hr.trans _)
  have hNr : (16384 : ℝ) ≤ N := by exact_mod_cast hN
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < N)).mpr (by linarith)

/-- A worked scalar certificate with a nonzero additional error budget:
16384 factors and error at most 1/100 give count one and distance at most
3/20 from the first full spectral zero. -/
theorem linearOnsite_approximation_certificate (N : ℕ) (hN : 16384 ≤ N)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 1 (1 / 4 : ℝ)))
    (herr : ∀ z ∈ sphere 1 (1 / 4 : ℝ),
      ‖g z - canonicalPartialProduct linearOnsitePotential 0 1 N z‖ ≤ (1 / 100 : ℝ)) :
    analyticDiskZeroCount g 1 (1 / 4) = 1 ∧
      (∀ z ∈ sphere 1 (1 / 4 : ℝ), g z ≠ 0) ∧
      (∀ z ∈ closedBall 1 (1 / 4 : ℝ), g z = 0 → ‖z - 1‖ ≤ (3 / 20 : ℝ)) := by
  have he : ∀ z ∈ sphere 1 (1 / 4 : ℝ),
      ‖g z - canonicalProduct linearOnsitePotential 0 1 z‖ ≤ (3 / 100 : ℝ) := by
    intro z hz
    have ht := norm_sub_le_norm_sub_add_norm_sub (g z)
      (canonicalPartialProduct linearOnsitePotential 0 1 N z)
      (canonicalProduct linearOnsitePotential 0 1 z)
    have hp := linearOnsite_partial_error N hN (sphere_subset_closedBall hz)
    rw [norm_sub_rev] at hp
    linarith [herr z hz]
  have hc := linearOnsite_zero_control.approximation_zero_count hg he (by norm_num)
  simpa using hc

end
end SpectralGeometry
