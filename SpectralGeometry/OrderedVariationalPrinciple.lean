module

public import SpectralGeometry.DomainEigenbasis

public section

/-!
# A domain-aware variational principle for ordered infinite spectra

The n-th level is at most E exactly when an (n+1)-dimensional trial space
in the natural domain has energy at most E. Trial spaces are represented
by injective linear maps from `Fin (n+1) → ℝ`, so their dimension cannot be
assumed away. Repeated eigenvalues occupy distinct orthonormal slots.
-/

namespace SpectralGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {d : Submodule ℝ H} {A : d →ₗ[ℝ] H} {ev : ℕ → ℝ}

namespace DomainEigenbasis

variable (b : DomainEigenbasis d A ev)

@[expose] def domainVector (i : ℕ) : d := ⟨b.basis i, b.mem_domain i⟩

@[expose] def prefixSynthesis (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] d where
  toFun c := ∑ i, c i • b.domainVector i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum, mul_smul]

@[expose] def firstCoordinates (n : ℕ) : d →ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := inner ℝ (b.basis i) (x : H)
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp

theorem prefixSynthesis_coefficient (n : ℕ) (c : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    inner ℝ (b.basis j) ((b.prefixSynthesis n c : d) : H) = c j := by
  have ho := b.basis.orthonormal.comp (fun i : Fin (n + 1) => (i : ℕ)) Fin.val_injective
  simpa only [prefixSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_sum, Submodule.coe_smul, domainVector] using ho.inner_right_fintype c j

theorem prefixSynthesis_injective (n : ℕ) : Function.Injective (b.prefixSynthesis n) := by
  intro c e h
  funext i
  have hh := congrArg (fun x : d => inner ℝ (b.basis i) (x : H)) h
  simpa only [b.prefixSynthesis_coefficient] using hh

variable (hA : ∀ x y : d, inner ℝ (A x) (y : H) = inner ℝ (x : H) (A y))
variable (hmono : Monotone ev)
include hA hmono

/-- The first n+1 eigenvectors furnish a trial space attaining the n-th
level, including at a repeated level. -/
theorem prefixSynthesis_energy_le (n : ℕ) (c : Fin (n + 1) → ℝ) :
    inner ℝ ((b.prefixSynthesis n c : d) : H) (A (b.prefixSynthesis n c)) ≤
      ev n * ‖((b.prefixSynthesis n c : d) : H)‖ ^ 2 := by
  apply b.energy_le_of_support hA
  intro j hj
  change inner ℝ (b.basis j) ((∑ i : Fin (n + 1), c i • b.domainVector i : d) : H) = 0
  simp only [Submodule.coe_sum, Submodule.coe_smul, inner_sum, real_inner_smul_right, domainVector]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : j ≠ i.val := by
    intro heq
    subst j
    exact (not_le_of_gt hj) (hmono (by omega))
  rw [b.basis.orthonormal.2 hne, mul_zero]

/-- Vanishing first n coordinates forces energy at least the n-th level. -/
theorem energy_ge_of_firstCoordinates_zero (n : ℕ) (x : d)
    (hx : b.firstCoordinates n x = 0) :
    ev n * ‖(x : H)‖ ^ 2 ≤ inner ℝ (x : H) (A x) := by
  apply b.energy_ge_of_support hA
  intro i hi
  have hin : i < n := by
    by_contra hn
    exact (not_le_of_gt hi) (hmono (Nat.le_of_not_gt hn))
  exact congrFun hx ⟨i, hin⟩

/-- The variational lower obstruction for an arbitrary injective trial
space, proved by a dimension argument against the first n coordinates. -/
theorem eigenvalue_le_of_trial (n : ℕ) (E : ℝ)
    (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] d) (hL : Function.Injective L)
    (htrial : ∀ c, inner ℝ ((L c : d) : H) (A (L c)) ≤ E * ‖((L c : d) : H)‖ ^ 2) :
    ev n ≤ E := by
  let f := (b.firstCoordinates n).comp L
  have hex : ∃ c, c ≠ 0 ∧ f c = 0 := by
    by_contra hh
    have hi : Function.Injective f := by
      apply LinearMap.ker_eq_bot.mp
      rw [Submodule.eq_bot_iff]
      intro c hc
      by_contra hne
      exact hh ⟨c, hne, hc⟩
    have hd := LinearMap.finrank_le_finrank_of_injective hi
    simp only [Module.finrank_fin_fun] at hd
    omega
  obtain ⟨c, hc, hfc⟩ := hex
  have hLc : (L c : H) ≠ 0 := by
    intro hz
    have hz' : L c = 0 := Subtype.ext hz
    exact hc (hL (hz'.trans (map_zero L).symm))
  have hpos : 0 < ‖(L c : H)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hLc)
  have hlo := b.energy_ge_of_firstCoordinates_zero hA hmono n (L c) hfc
  exact (mul_le_mul_iff_of_pos_right hpos).mp (hlo.trans (htrial c))

/-- A min-max characterization without assuming a numerical ordering
comparison as a hypothesis. -/
theorem eigenvalue_le_iff_trial (n : ℕ) (E : ℝ) :
    ev n ≤ E ↔ ∃ L : (Fin (n + 1) → ℝ) →ₗ[ℝ] d,
      Function.Injective L ∧
      ∀ c, inner ℝ ((L c : d) : H) (A (L c)) ≤ E * ‖((L c : d) : H)‖ ^ 2 := by
  constructor
  · intro he
    refine ⟨b.prefixSynthesis n, b.prefixSynthesis_injective n, ?_⟩
    intro c
    exact (b.prefixSynthesis_energy_le hA hmono n c).trans
      (mul_le_mul_of_nonneg_right he (sq_nonneg _))
  · rintro ⟨L, hi, he⟩
    exact b.eigenvalue_le_of_trial hA hmono n E L hi he

end DomainEigenbasis

/-- Ordered levels respect a nonnegative affine comparison of quadratic
forms on a common domain. Completeness and multiplicities are recorded by
the two actual Hilbert eigenbases. -/
theorem ordered_eigenvalues_affine_le
    {K : d →ₗ[ℝ] H} {μ : ℕ → ℝ}
    (bA : DomainEigenbasis d A ev) (bK : DomainEigenbasis d K μ)
    (hA : ∀ x y : d, inner ℝ (A x) (y : H) = inner ℝ (x : H) (A y))
    (hK : ∀ x y : d, inner ℝ (K x) (y : H) = inner ℝ (x : H) (K y))
    (hmonoA : Monotone ev) (hmonoK : Monotone μ)
    (α β : ℝ) (hα : 0 ≤ α)
    (hform : ∀ x : d, α * inner ℝ (x : H) (A x) + β * ‖(x : H)‖ ^ 2 ≤
      inner ℝ (x : H) (K x)) (n : ℕ) :
    α * ev n + β ≤ μ n := by
  by_cases ha : α = 0
  · subst α
    have hh := hform (bK.domainVector n)
    have he : K (bK.domainVector n) = μ n • bK.basis n := bK.eigen n
    simpa only [zero_mul, zero_add, DomainEigenbasis.domainVector, he,
      real_inner_smul_right, real_inner_self_eq_norm_sq, bK.basis.orthonormal.1,
      one_pow, mul_one] using hh
  · have hap : 0 < α := lt_of_le_of_ne hα (Ne.symm ha)
    have he : ev n ≤ (μ n - β) / α := by
      apply bA.eigenvalue_le_of_trial hA hmonoA n _ (bK.prefixSynthesis n) (bK.prefixSynthesis_injective n)
      intro c
      have hf := hform (bK.prefixSynthesis n c)
      have hk := bK.prefixSynthesis_energy_le hK hmonoK n c
      apply (le_of_mul_le_mul_left ?_ hap)
      calc
        α * inner ℝ ((bK.prefixSynthesis n c : d) : H) (A (bK.prefixSynthesis n c)) ≤
          (μ n - β) * ‖((bK.prefixSynthesis n c : d) : H)‖ ^ 2 := by nlinarith
        _ = α * (((μ n - β) / α) * ‖((bK.prefixSynthesis n c : d) : H)‖ ^ 2) := by field_simp
    have hh := (le_div_iff₀ hap).mp he
    nlinarith

end
end SpectralGeometry
