module

public import SpectralGeometry.InfiniteLowEnergyObservation

public section

/-!
# Simultaneous low-energy counting with multiplicities

The dimension argument is applied once to the whole spectral subspace.
Orthogonality makes the sum of distinct eigenspaces injective, so the bound
counts the sum of their dimensions, not a sum of independent upper bounds.
-/

namespace SpectralGeometry

noncomputable section

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (d : Submodule ℝ H) (A : d →ₗ[ℝ] H)

/-- Summing distinct eigenspaces inside a common low-energy subspace. -/
@[expose] def domainSpectralSum (E : ℝ) (s : Finset ℝ) (hs : ∀ ev ∈ s, ev ≤ E) :
    (∀ ev : s, domainEigenspace d A ev) →ₗ[ℝ] domainLowSpectralSubspace d A E where
  toFun x := ⟨∑ ev : s, (x ev : d), Submodule.sum_mem _ (fun ev _ =>
    Submodule.mem_iSup_of_mem (⟨ev, hs ev ev.property⟩ : {ev : ℝ // ev ≤ E})
      (x ev).property)⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' c x := by
    apply Subtype.ext
    simp only [Pi.smul_apply, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply]

/-- Orthogonality proves that summing distinct eigenspaces is injective. -/
theorem domainSpectralSum_injective
    (hA : ∀ x y : d, inner ℝ (A x) (y : H) = inner ℝ (x : H) (A y))
    (E : ℝ) (s : Finset ℝ) (hs : ∀ ev ∈ s, ev ≤ E) :
    Function.Injective (domainSpectralSum d A E s hs) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hz : (∑ ev : s, ((x ev : d) : H)) = 0 := by
    have hh := congrArg (fun z : domainLowSpectralSubspace d A E => ((z : d) : H)) hx
    simpa only [domainSpectralSum, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_sum, Submodule.coe_zero] using hh
  have ho := domainEigenspaces_orthogonalFamily d A hA
    (fun ev : s => (ev : ℝ)) Subtype.val_injective
  funext ev
  have hh := ho.inner_right_fintype x ev (x ev)
  change inner ℝ ((x ev : d) : H) (∑ i : s, ((x i : d) : H)) =
    inner ℝ (x ev) (x ev) at hh
  rw [hz, inner_zero_right, real_inner_self_eq_norm_sq] at hh
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh.symm)

/-- Sum of dimensions bounded by the dimension of the common spectral
subspace, without assuming simple eigenvalues. -/
theorem domainSpectralSum_finrank_le
    (hA : ∀ x y : d, inner ℝ (A x) (y : H) = inner ℝ (x : H) (A y))
    (E : ℝ) [FiniteDimensional ℝ (domainLowSpectralSubspace d A E)]
    (s : Finset ℝ) (hs : ∀ ev ∈ s, ev ≤ E) :
    ∑ ev ∈ s, Module.finrank ℝ (domainEigenspace d A ev) ≤
      Module.finrank ℝ (domainLowSpectralSubspace d A E) := by
  have hle (ev : s) : domainEigenspace d A ev ≤ domainLowSpectralSubspace d A E :=
    le_iSup_of_le (⟨ev, hs ev ev.property⟩ : {ev : ℝ // ev ≤ E}) le_rfl
  letI (ev : s) : FiniteDimensional ℝ (domainEigenspace d A ev) :=
    FiniteDimensional.of_injective (Submodule.inclusion (hle ev))
      (Submodule.inclusion_injective _)
  have hh := LinearMap.finrank_le_finrank_of_injective
    (domainSpectralSum_injective d A hA E s hs)
  rw [Module.finrank_pi_fintype] at hh
  have heq : (∑ ev : s, Module.finrank ℝ (domainEigenspace d A ev)) =
      ∑ ev ∈ s, Module.finrank ℝ (domainEigenspace d A ev) :=
    Finset.sum_coe_sort s (fun ev : ℝ => Module.finrank ℝ (domainEigenspace d A ev))
  exact heq ▸ hh
end Abstract

variable {Tile : Type*} [DecidableEq Tile]

/-- A single observation sector bounds the sum of eigenspace dimensions
in any finite family below the threshold. -/
theorem onsitePlusBounded_sum_multiplicities_le (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (v₀ R : ℝ) (hV : ∀ t, v₀ ≤ V t) (hR : v₀ < R)
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t)
    (s : Finset ℝ) (hs : ∀ ev ∈ s, ev < R - ‖B‖) :
    ∑ ev ∈ s, Module.finrank ℝ
      (domainEigenspace (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev) ≤ F.card := by
  classical
  by_cases hne : s.Nonempty
  · let E := s.sup' hne id
    have hE : E < R - ‖B‖ := (Finset.sup'_lt_iff hne).mpr hs
    have hsE : ∀ ev ∈ s, ev ≤ E := fun ev hev => Finset.le_sup' id hev
    letI := onsitePlusBounded_lowSpectral_finiteDimensional V B hB v₀ R E hV hR hE F hF
    exact (domainSpectralSum_finrank_le _ _ (onsitePlusBounded_symmetric V B hB) E s hsE).trans
      (onsitePlusBounded_lowSpectral_finrank_le V B hB v₀ R E hV hR hE F hF)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

end
end SpectralGeometry
