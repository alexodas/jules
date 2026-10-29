module

public import SpectralGeometry.InfiniteFullSpectralSummability

public section

/-!
# Ordered spectral error and positive summability under small bounded errors

Symmetric bounded corrections on the same natural domain change every
ordered level by at most their operator norm. A correction smaller than an
existing positive gap preserves positivity and inverse-square summability,
even when the correction is not nonnegative or has infinite rank.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

theorem boundedCorrection_add_symmetric
    (B K : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y)) :
    ∀ x y, inner ℝ ((B + K) x) y = inner ℝ x ((B + K) y) := by
  intro x y
  simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, hB, hK]

theorem onsitePlusBounded_perturbation_energy (V : Tile → ℝ)
    (B K : TileHilbert Tile →L[ℝ] TileHilbert Tile) (x : infiniteOnsiteDomain V) :
    inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V B x) - ‖K‖ * ‖(x : TileHilbert Tile)‖ ^ 2 ≤
      inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V (B + K) x) ∧
    inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V (B + K) x) ≤
      inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V B x) + ‖K‖ * ‖(x : TileHilbert Tile)‖ ^ 2 := by
  have he : onsitePlusBounded V (B + K) x =
      onsitePlusBounded V B x + K x := by
    simp [onsitePlusBounded_apply, add_assoc]
  have hh := abs_le.mp (infiniteLocalBoundedPerturbation_inner_abs_le K x)
  rw [he, inner_add_right]
  constructor <;> linarith

/-- A two-sided operator-norm bound for all ordered levels, with their
complete-basis multiplicities. No simple-spectrum assumption is used. -/
theorem onsitePlusBounded_ordered_perturbation_bound (V : Tile → ℝ)
    (B K : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    (ev μ : ℕ → ℝ) (hev : Monotone ev) (hμ : Monotone μ)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev)
    (bt : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V (B + K)) μ)
    (n : ℕ) : |μ n - ev n| ≤ ‖K‖ := by
  have hBK := boundedCorrection_add_symmetric B K hB hK
  have hlo := ordered_eigenvalues_affine_le b bt (onsitePlusBounded_symmetric V B hB)
    (onsitePlusBounded_symmetric V (B + K) hBK) hev hμ 1 (-‖K‖) zero_le_one
    (fun x => by simpa using (onsitePlusBounded_perturbation_energy V B K x).1) n
  have hhi := ordered_eigenvalues_affine_le bt b
    (onsitePlusBounded_symmetric V (B + K) hBK) (onsitePlusBounded_symmetric V B hB)
    hμ hev 1 (-‖K‖) zero_le_one (fun x => by
      have hh := (onsitePlusBounded_perturbation_energy V B K x).2
      simp only [one_mul, neg_mul]
      linarith) n
  apply abs_le.mpr
  constructor <;> linarith

/-- An error strictly smaller than a baseline gap preserves positivity
and inverse-square summability. The proof gives a global multiplicative
comparison, without assuming a growth rate or divergence for `μ`. -/
theorem positive_invSq_summable_of_small_error
    (q μ : ℕ → ℝ) (γ δ : ℝ) (hδ : 0 ≤ δ) (hsmall : δ < γ)
    (hgap : ∀ n, γ ≤ q n) (hs : Summable (fun n => 1 / (q n) ^ 2))
    (he : ∀ n, q n - δ ≤ μ n) :
    (∀ n, γ - δ ≤ μ n) ∧ (∀ n, 0 < μ n) ∧
      Summable (fun n => 1 / (μ n) ^ 2) := by
  have hγ : 0 < γ := lt_of_le_of_lt hδ hsmall
  have hlow (n : ℕ) : γ - δ ≤ μ n := by linarith [hgap n, he n]
  have hpos (n : ℕ) : 0 < μ n := lt_of_lt_of_le (sub_pos.mpr hsmall) (hlow n)
  let α := (γ - δ) / γ
  have hα : 0 < α := div_pos (sub_pos.mpr hsmall) hγ
  have hscale (n : ℕ) : α * q n ≤ μ n := by
    have hm : (γ - δ) * q n ≤ γ * μ n := by
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr (hgap n)),
        mul_le_mul_of_nonneg_left (he n) hγ.le]
    have hid : γ * (α * q n) = (γ - δ) * q n := by
      dsimp [α]
      field_simp [ne_of_gt hγ]
    apply (mul_le_mul_iff_of_pos_left hγ).mp
    rw [hid]
    exact hm
  refine ⟨hlow, hpos, ?_⟩
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hs.mul_left (1 / α ^ 2))
  intro n
  have hq : 0 < q n := hγ.trans_le (hgap n)
  have hprod : 0 < α * q n := mul_pos hα hq
  calc
    1 / (μ n) ^ 2 ≤ 1 / (α * q n) ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos hprod)
        (sq_le_sq₀ hprod.le (hpos n).le |>.mpr (hscale n))
    _ = (1 / α ^ 2) * (1 / (q n) ^ 2) := by
      rw [mul_pow, one_div_mul_one_div]

/-- Small signed bounded corrections preserve a supplied positive full
spectral gap and summability, on the unchanged natural domain. -/
theorem onsitePlusBounded_small_error_preserves_summability (V : Tile → ℝ)
    (B K : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    (ev μ : ℕ → ℝ) (hev : Monotone ev) (hμ : Monotone μ)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev)
    (bt : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V (B + K)) μ)
    (γ : ℝ) (hsmall : ‖K‖ < γ) (hgap : ∀ n, γ ≤ ev n)
    (hs : Summable (fun n => 1 / (ev n) ^ 2)) :
    (∀ n, γ - ‖K‖ ≤ μ n) ∧ (∀ n, 0 < μ n) ∧
      Summable (fun n => 1 / (μ n) ^ 2) := by
  apply positive_invSq_summable_of_small_error ev μ γ ‖K‖ (norm_nonneg K) hsmall hgap hs
  intro n
  have hh := abs_le.mp (onsitePlusBounded_ordered_perturbation_bound V B K hB hK ev μ hev hμ b bt n)
  linarith

end
end SpectralGeometry
