module

public import SpectralGeometry.InfiniteLocalFullLowEnergyCounting

public section

/-!
# Spectral subspaces on an explicit operator domain

These algebraic constructions retain the domain of an unbounded operator.
Symmetry makes distinct eigenspaces orthogonal. Consequently the quadratic
form bound on a spectral interval holds for every finite linear combination
of its eigenvectors, rather than just for individual eigenvectors.
-/

namespace SpectralGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (d : Submodule ℝ H) (A : d →ₗ[ℝ] H)

/-- The actual eigenspace inside the specified operator domain. -/
@[expose] def domainEigenspace (ev : ℝ) : Submodule ℝ d :=
  LinearMap.ker (A - ev • d.subtype)

@[simp] theorem mem_domainEigenspace (ev : ℝ) (x : d) :
    x ∈ domainEigenspace d A ev ↔ A x = ev • (x : H) := by
  simp [domainEigenspace, sub_eq_zero]

/-- Algebraic spectral subspace at or below `E`, including all eigenspaces
and all their finite linear combinations. Its finite dimensionality and
closedness for confined onsite operators are proved separately. -/
@[expose] def domainLowSpectralSubspace (E : ℝ) : Submodule ℝ d :=
  ⨆ ev : {ev : ℝ // ev ≤ E}, domainEigenspace d A ev

variable (hA : ∀ x y : d, inner ℝ (A x) (y : H) = inner ℝ (x : H) (A y))
include hA

theorem domainEigenspaces_orthogonal {ev μ : ℝ} (hne : ev ≠ μ)
    (x : domainEigenspace d A ev) (y : domainEigenspace d A μ) :
    inner ℝ ((x : d) : H) ((y : d) : H) = 0 := by
  have hx := (mem_domainEigenspace d A ev (x : d)).mp x.property
  have hy := (mem_domainEigenspace d A μ (y : d)).mp y.property
  have hs := hA x y
  rw [hx, hy, real_inner_smul_left, real_inner_smul_right] at hs
  have hh : (ev - μ) * inner ℝ ((x : d) : H) ((y : d) : H) = 0 := by
    nlinarith [hs]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)

theorem domainEigenspaces_orthogonalFamily {ι : Type*} (ev : ι → ℝ)
    (hev : Function.Injective ev) :
    OrthogonalFamily ℝ (fun i => domainEigenspace d A (ev i))
      (fun i => d.subtypeₗᵢ.comp (domainEigenspace d A (ev i)).subtypeₗᵢ) := by
  intro i j hij x y
  exact domainEigenspaces_orthogonal d A hA (hev.ne hij) x y

/-- Exact energy of an orthogonal sum of vectors from distinct levels. -/
theorem domainEigenspaces_energy_sum {ι : Type*} (ev : ι → ℝ)
    (hev : Function.Injective ev) (s : Finset ι)
    (x : ∀ i, domainEigenspace d A (ev i)) :
    inner ℝ ((∑ i ∈ s, (x i : d) : d) : H)
      (A (∑ i ∈ s, (x i : d))) =
      ∑ i ∈ s, ev i * ‖((x i : d) : H)‖ ^ 2 := by
  have hm : A (∑ i ∈ s, (x i : d)) =
      ∑ i ∈ s, ev i • ((x i : d) : H) := by
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (mem_domainEigenspace d A (ev i) (x i : d)).mp (x i).property
  rw [hm]
  have hh := (domainEigenspaces_orthogonalFamily d A hA ev hev).inner_sum
    x (fun i => ev i • x i) s
  change inner ℝ (∑ i ∈ s, ((x i : d) : H))
    (∑ i ∈ s, (((ev i • x i) : d) : H)) =
      ∑ i ∈ s, inner ℝ (x i) (ev i • x i) at hh
  simp only [Submodule.coe_smul] at hh
  rw [Submodule.coe_sum]
  calc
    _ = ∑ i ∈ s, inner ℝ (x i) (ev i • x i) := hh
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      change inner ℝ ((x i : d) : H) (ev i • ((x i : d) : H)) = _
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]

/-- Every vector in the simultaneous low-energy subspace satisfies the
Rayleigh upper bound, even when several different eigenvalues occur. -/
theorem domainLowSpectralSubspace_energy_le (E : ℝ)
    (x : domainLowSpectralSubspace d A E) :
    inner ℝ ((x : d) : H) (A x) ≤ E * ‖((x : d) : H)‖ ^ 2 := by
  classical
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp'
    (fun ev : {ev : ℝ // ev ≤ E} => domainEigenspace d A ev) (x : d)).mp x.property
  have hx : (∑ i ∈ f.support, (f i : d)) = (x : d) := hf
  rw [← hx, domainEigenspaces_energy_sum d A hA Subtype.val Subtype.val_injective]
  have hn := (domainEigenspaces_orthogonalFamily d A hA
    (fun i : {ev : ℝ // ev ≤ E} => (i : ℝ)) Subtype.val_injective).norm_sum
      (fun i => f i) f.support
  have hn' : ‖((∑ i ∈ f.support, (f i : d) : d) : H)‖ ^ 2 =
      ∑ i ∈ f.support, ‖((f i : d) : H)‖ ^ 2 := by
    change ‖∑ i ∈ f.support, ((f i : d) : H)‖ ^ 2 =
      ∑ i ∈ f.support, ‖f i‖ ^ 2 at hn
    simpa only [Submodule.coe_sum, Submodule.norm_coe] using hn
  rw [hn', Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right i.property (sq_nonneg _))

end
end SpectralGeometry
