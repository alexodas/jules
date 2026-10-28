module

public import SpectralGeometry.DomainSpectralSubspace

public section

/-!
# Quantitative finite-coordinate observation

The coordinate projection is a positive symmetric contraction. The onsite
lower bound gives a form inequality on the entire natural domain, and hence
a quantitative observation estimate on the simultaneous low-energy spectral
subspace. No simplicity assumption on eigenvalues is used.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

/-- Orthogonal coordinate projection onto a finite set of sites. -/
@[expose] def finiteSectorProjection (F : Finset Tile) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  infiniteOnsiteDiagonalContraction (fun t => if t ∈ F then 1 else 0)
    (fun t => by split_ifs <;> norm_num)

@[simp] theorem finiteSectorProjection_apply (F : Finset Tile)
    (x : TileHilbert Tile) (t : Tile) :
    finiteSectorProjection F x t = if t ∈ F then x t else 0 := by
  simp only [finiteSectorProjection, infiniteOnsiteDiagonalContraction_apply]
  split_ifs <;> simp

theorem finiteSectorProjection_norm_le (F : Finset Tile) :
    ‖finiteSectorProjection F‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro t
  rw [finiteSectorProjection_apply]
  split_ifs <;> simp

theorem finiteSectorProjection_symmetric (F : Finset Tile)
    (x y : TileHilbert Tile) :
    inner ℝ (finiteSectorProjection F x) y =
      inner ℝ x (finiteSectorProjection F y) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro t
  simp only [finiteSectorProjection_apply]
  split_ifs <;> simp

theorem finiteSectorProjection_inner (F : Finset Tile) (x : TileHilbert Tile) :
    inner ℝ x (finiteSectorProjection F x) = ‖finiteSectorProjection F x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro t
  simp only [finiteSectorProjection_apply]
  split_ifs <;> simp

/-- Onsite multiplication plus an arbitrary bounded correction, with the
unchanged natural multiplication domain. -/
@[expose] def onsitePlusBounded (V : Tile → ℝ) (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) :
    infiniteOnsiteDomain V →ₗ[ℝ] TileHilbert Tile :=
  infiniteOnsiteOperator V + B.toLinearMap.comp (infiniteOnsiteDomain V).subtype

@[simp] theorem onsitePlusBounded_apply (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) (x : infiniteOnsiteDomain V) :
    onsitePlusBounded V B x = infiniteOnsiteOperator V x + B x := rfl

theorem onsitePlusBounded_symmetric (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (x y : infiniteOnsiteDomain V) :
    inner ℝ (onsitePlusBounded V B x) (y : TileHilbert Tile) =
      inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V B y) := by
  simp only [onsitePlusBounded_apply, inner_add_left, inner_add_right,
    infiniteOnsiteOperator_symmetric V x y, hB]

/-- The finite observation sector controls the deficit from the exterior
onsite energy, on every vector in the natural domain. -/
theorem infiniteOnsiteOperator_sector_form_bound (V : Tile → ℝ)
    (v₀ R : ℝ) (hV : ∀ t, v₀ ≤ V t) (F : Finset Tile)
    (hF : ∀ t, t ∉ F → R ≤ V t) (x : infiniteOnsiteDomain V) :
    R * ‖(x : TileHilbert Tile)‖ ^ 2 -
      (R - v₀) * ‖finiteSectorProjection F x‖ ^ 2 ≤
      inner ℝ (x : TileHilbert Tile) (infiniteOnsiteOperator V x) := by
  have hp : 0 ≤ inner ℝ (x : TileHilbert Tile)
      (infiniteOnsiteOperator V x - R • (x : TileHilbert Tile) +
        (R - v₀) • finiteSectorProjection F x) := by
    rw [lp.inner_eq_tsum]
    apply tsum_nonneg
    intro t
    have hc :
        (infiniteOnsiteOperator V x - R • (x : TileHilbert Tile) +
          (R - v₀) • finiteSectorProjection F x) t =
        V t * x.1 t - R * x.1 t +
          (R - v₀) * (if t ∈ F then x.1 t else 0) := by
      change V t * x.1 t - R * x.1 t +
        (R - v₀) * (finiteSectorProjection F x) t = _
      rw [finiteSectorProjection_apply]
    rw [hc]
    simp only [RCLike.inner_apply, conj_trivial]
    by_cases ht : t ∈ F
    · rw [if_pos ht]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hV t)) (sq_nonneg (x.1 t))]
    · rw [if_neg ht]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hF t ht)) (sq_nonneg (x.1 t))]
  rw [inner_add_right, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    finiteSectorProjection_inner] at hp
  linarith

theorem onsitePlusBounded_sector_form_bound (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (v₀ R : ℝ) (hV : ∀ t, v₀ ≤ V t) (F : Finset Tile)
    (hF : ∀ t, t ∉ F → R ≤ V t) (x : infiniteOnsiteDomain V) :
    (R - ‖B‖) * ‖(x : TileHilbert Tile)‖ ^ 2 -
      (R - v₀) * ‖finiteSectorProjection F x‖ ^ 2 ≤
      inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V B x) := by
  have hon := infiniteOnsiteOperator_sector_form_bound V v₀ R hV F hF x
  have hb := (abs_le.mp (infiniteLocalBoundedPerturbation_inner_abs_le B x)).1
  rw [onsitePlusBounded_apply, inner_add_right]
  nlinarith

/-- Quantitative observation for the entire low-energy spectral subspace.
The sector may be larger than the onsite sublevel set. Compactness is not
assumed for this estimate; finite dimensionality follows from observation. -/
theorem onsitePlusBounded_lowSpectral_observation (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (v₀ R E : ℝ) (hV : ∀ t, v₀ ≤ V t) (hR : v₀ < R)
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t)
    (x : domainLowSpectralSubspace (infiniteOnsiteDomain V) (onsitePlusBounded V B) E) :
    ((R - ‖B‖ - E) / (R - v₀)) * ‖((x : infiniteOnsiteDomain V) : TileHilbert Tile)‖ ^ 2 ≤
      ‖finiteSectorProjection F (x : infiniteOnsiteDomain V)‖ ^ 2 := by
  have hlo := onsitePlusBounded_sector_form_bound V B v₀ R hV F hF (x : infiniteOnsiteDomain V)
  have hhi := domainLowSpectralSubspace_energy_le _ _
    (onsitePlusBounded_symmetric V B hB) E x
  have hd : 0 < R - v₀ := sub_pos.mpr hR
  apply (le_of_mul_le_mul_right ?_ hd)
  calc
    ((R - ‖B‖ - E) / (R - v₀)) *
        ‖((x : infiniteOnsiteDomain V) : TileHilbert Tile)‖ ^ 2 * (R - v₀) =
      (R - ‖B‖ - E) * ‖((x : infiniteOnsiteDomain V) : TileHilbert Tile)‖ ^ 2 := by
        field_simp
    _ ≤ ‖finiteSectorProjection F (x : infiniteOnsiteDomain V)‖ ^ 2 * (R - v₀) := by
      nlinarith

/-- Coordinate restriction on a domain spectral subspace. -/
@[expose] def lowSpectralRestriction (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) (E : ℝ) (F : Finset Tile) :
    domainLowSpectralSubspace (infiniteOnsiteDomain V) (onsitePlusBounded V B) E →ₗ[ℝ]
      (F → ℝ) where
  toFun x t := ((x : infiniteOnsiteDomain V) : TileHilbert Tile) t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction is injective on the simultaneous spectral subspace. -/
theorem onsitePlusBounded_lowSpectral_restriction_injective (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (v₀ R E : ℝ) (hV : ∀ t, v₀ ≤ V t) (hR : v₀ < R) (hE : E < R - ‖B‖)
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t) :
    Function.Injective (lowSpectralRestriction V B E F) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hc : lowSpectralRestriction V B E F x = 0 := hx
  have hz : finiteSectorProjection F (x : infiniteOnsiteDomain V) = 0 := by
    apply lp.ext
    funext t
    rw [finiteSectorProjection_apply]
    by_cases ht : t ∈ F
    · rw [if_pos ht]
      exact congrFun hc ⟨t, ht⟩
    · simp [ht]
  have hb := onsitePlusBounded_lowSpectral_observation V B hB v₀ R E hV hR F hF x
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hb
  have hk : 0 < (R - ‖B‖ - E) / (R - v₀) :=
    div_pos (sub_pos.mpr hE) (sub_pos.mpr hR)
  have hnorm : ‖((x : infiniteOnsiteDomain V) : TileHilbert Tile)‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖((x : infiniteOnsiteDomain V) : TileHilbert Tile)‖]
  apply Subtype.ext
  apply Subtype.ext
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- Finite dimensionality follows from observation. -/
theorem onsitePlusBounded_lowSpectral_finiteDimensional (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (v₀ R E : ℝ) (hV : ∀ t, v₀ ≤ V t) (hR : v₀ < R) (hE : E < R - ‖B‖)
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t) :
    FiniteDimensional ℝ
      (domainLowSpectralSubspace (infiniteOnsiteDomain V) (onsitePlusBounded V B) E) :=
  FiniteDimensional.of_injective (lowSpectralRestriction V B E F)
    (onsitePlusBounded_lowSpectral_restriction_injective V B hB v₀ R E hV hR hE F hF)

/-- Total low-energy dimension, including empty and finite-site cases. -/
theorem onsitePlusBounded_lowSpectral_finrank_le (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (v₀ R E : ℝ) (hV : ∀ t, v₀ ≤ V t) (hR : v₀ < R) (hE : E < R - ‖B‖)
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t) :
    Module.finrank ℝ
      (domainLowSpectralSubspace (infiniteOnsiteDomain V) (onsitePlusBounded V B) E) ≤ F.card := by
  have hi := onsitePlusBounded_lowSpectral_restriction_injective
    V B hB v₀ R E hV hR hE F hF
  have hh := LinearMap.finrank_le_finrank_of_injective hi
  simpa using hh

/-- The spectral span is closed in the ambient Hilbert space. Thus taking
its closure adds no vectors and preserves the natural-domain conclusions. -/
theorem onsitePlusBounded_lowSpectral_closed (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (v₀ R E : ℝ) (hV : ∀ t, v₀ ≤ V t) (hR : v₀ < R) (hE : E < R - ‖B‖)
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t) :
    IsClosed (((domainLowSpectralSubspace (infiniteOnsiteDomain V) (onsitePlusBounded V B) E).map
      (infiniteOnsiteDomain V).subtype : Submodule ℝ (TileHilbert Tile)) : Set (TileHilbert Tile)) := by
  letI := onsitePlusBounded_lowSpectral_finiteDimensional V B hB v₀ R E hV hR hE F hF
  exact Submodule.closed_of_finiteDimensional _

end
end SpectralGeometry
