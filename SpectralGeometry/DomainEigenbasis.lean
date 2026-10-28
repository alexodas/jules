module

public import SpectralGeometry.InfiniteLocalFullSpectralObservation

public section

/-!
# Hilbert eigenbases on an explicit natural domain

An eigenbasis records the actual eigenvector equation on the domain, with
one orthonormal vector for each multiplicity slot. Parseval then transports
pointwise spectral inequalities to quadratic form inequalities.
-/

namespace SpectralGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A complete Hilbert basis of genuine domain eigenvectors. -/
structure DomainEigenbasis {ι : Type*} (d : Submodule ℝ H) (A : d →ₗ[ℝ] H)
    (ev : ι → ℝ) where
  basis : HilbertBasis ι ℝ H
  mem_domain : ∀ i, basis i ∈ d
  eigen : ∀ i, A ⟨basis i, mem_domain i⟩ = ev i • basis i

/-- Collect finite orthonormal bases of mutually orthogonal subspaces
whose joint orthogonal complement is zero. -/
theorem exists_hilbertBasis_subordinate [CompleteSpace H] {ι : Type*}
    (p : ι → Submodule ℝ H) [∀ i, FiniteDimensional ℝ (p i)]
    (ho : OrthogonalFamily ℝ (fun i => p i) (fun i => (p i).subtypeₗᵢ))
    (htotal : (⨆ i, p i)ᗮ = ⊥) :
    ∃ b : HilbertBasis (Σ i, Fin (Module.finrank ℝ (p i))) ℝ H,
      ∀ j, b j ∈ p j.1 := by
  classical
  let ob (i : ι) := stdOrthonormalBasis ℝ (p i)
  let v (j : Σ i, Fin (Module.finrank ℝ (p i))) : H := ob j.1 j.2
  have hv : Orthonormal ℝ v :=
    ho.orthonormal_sigma_orthonormal (fun i => (ob i).orthonormal)
  have hp : (⨆ i, p i) ≤ Submodule.span ℝ (Set.range v) := by
    apply iSup_le
    intro i x hx
    have hr := congrArg (fun y : p i => (y : H)) ((ob i).sum_repr ⟨x, hx⟩)
    rw [← hr]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨i, k⟩, rfl⟩
  have hd : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ :=
    le_antisymm ((Submodule.orthogonal_le hp).trans_eq htotal) bot_le
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot hv hd, ?_⟩
  intro j
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact (ob j.1 j.2).property

/-- Reindexing a Hilbert basis preserves completeness, including finite
and empty index types. -/
@[expose] def reindexHilbertBasis {ι κ : Type*} [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) (e : κ ≃ ι) : HilbertBasis κ ℝ H := by
  have hv := b.orthonormal.comp e e.injective
  have hr : Set.range (fun i => b (e i)) = Set.range b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  apply HilbertBasis.mk hv
  rw [hr, b.dense_span]

@[simp] theorem reindexHilbertBasis_apply {ι κ : Type*} [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) (e : κ ≃ ι) (i : κ) :
    reindexHilbertBasis b e i = b (e i) := by
  simp only [reindexHilbertBasis, HilbertBasis.coe_mk]

namespace DomainEigenbasis

variable {ι : Type*} {d : Submodule ℝ H} {A : d →ₗ[ℝ] H} {ev : ι → ℝ}
variable (b : DomainEigenbasis d A ev)
variable (hA : ∀ x y : d, inner ℝ (A x) (y : H) = inner ℝ (x : H) (A y))
include hA

/-- Symmetry computes the spectral coordinate of the image of any
natural-domain vector; no expansion of an unbounded operator is assumed. -/
theorem inner_image (x : d) (i : ι) :
    inner ℝ (b.basis i) (A x) = ev i * inner ℝ (b.basis i) (x : H) := by
  have hs := hA ⟨b.basis i, b.mem_domain i⟩ x
  rw [b.eigen, real_inner_smul_left] at hs
  exact hs.symm

/-- Exact quadratic-form expansion, with summability supplied by Parseval
applied to the two Hilbert-space vectors `x` and `A x`. -/
theorem hasSum_energy (x : d) :
    HasSum (fun i => ev i * (inner ℝ (b.basis i) (x : H)) ^ 2)
      (inner ℝ (x : H) (A x)) := by
  convert b.basis.hasSum_inner_mul_inner (x : H) (A x) using 1
  ext i
  rw [b.inner_image hA x i, real_inner_comm (x : H) (b.basis i)]
  ring

/-- Spectral support below a level implies the corresponding form bound. -/
theorem energy_le_of_support (x : d) (E : ℝ)
    (hs : ∀ i, E < ev i → inner ℝ (b.basis i) (x : H) = 0) :
    inner ℝ (x : H) (A x) ≤ E * ‖(x : H)‖ ^ 2 := by
  have hn : HasSum (fun i => (inner ℝ (b.basis i) (x : H)) ^ 2) ‖(x : H)‖ ^ 2 := by
    convert b.basis.hasSum_inner_mul_inner (x : H) (x : H) using 1
    · ext i
      rw [real_inner_comm (x : H) (b.basis i)]
      ring
    · exact (real_inner_self_eq_norm_sq _).symm
  apply HasSum.le (b.hasSum_energy hA x) (hn.mul_left E)
  intro i
  by_cases hi : ev i ≤ E
  · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  · rw [hs i (lt_of_not_ge hi)]
    simp

/-- Spectral support above a level implies the lower form bound. -/
theorem energy_ge_of_support (x : d) (E : ℝ)
    (hs : ∀ i, ev i < E → inner ℝ (b.basis i) (x : H) = 0) :
    E * ‖(x : H)‖ ^ 2 ≤ inner ℝ (x : H) (A x) := by
  have hn : HasSum (fun i => (inner ℝ (b.basis i) (x : H)) ^ 2) ‖(x : H)‖ ^ 2 := by
    convert b.basis.hasSum_inner_mul_inner (x : H) (x : H) using 1
    · ext i
      rw [real_inner_comm (x : H) (b.basis i)]
      ring
    · exact (real_inner_self_eq_norm_sq _).symm
  apply HasSum.le (hn.mul_left E) (b.hasSum_energy hA x)
  intro i
  by_cases hi : E ≤ ev i
  · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  · rw [hs i (lt_of_not_ge hi)]
    simp

end DomainEigenbasis
end
end SpectralGeometry
