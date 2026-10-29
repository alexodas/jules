module

public import SpectralGeometry.CanonicalProduct

public section

/-!
# Entire canonical products and exact zero locations

The existing compact majorant controls every injectively indexed subproduct.
Locally uniform limits of the finite polynomial products are entire. Absolute
summability of the perturbations prevents additional zeros of the product.
-/

namespace SpectralGeometry

open Filter
open scoped BigOperators

noncomputable section

/-- A subproduct, indexed without repeated indices. This includes finite,
empty and infinite subsets of the original factors. -/
@[expose] def canonicalProductAlong {ι : Type*} (q : ℕ → ℝ)
    (center direction : ℂ) (e : ι ↪ ℕ) (s : ℂ) : ℂ :=
  ∏' i, factor q center direction (e i) s

@[simp] theorem canonicalProductAlong_refl (q : ℕ → ℝ) (c d : ℂ) :
    canonicalProductAlong q c d (Function.Embedding.refl ℕ) = canonicalProduct q c d := rfl

variable {q : ℕ → ℝ} {c d : ℂ}

theorem factor_differentiable (n : ℕ) : Differentiable ℂ (factor q c d n) := by
  unfold factor perturb
  fun_prop

/-- The old majorant remains summable after any injective restriction. -/
theorem canonicalProductAlong_uniform_on_compact {ι : Type*}
    (h : Admissible q c d) (e : ι ↪ ℕ) (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun i s => factor q c d (e i) s)
      (canonicalProductAlong q c d e) K := by
  obtain ⟨b, hb, hbound⟩ := h.compactMajorant K hK
  unfold factor canonicalProductAlong
  exact (hb.comp_injective e.injective).hasProdUniformlyOn_one_add hK
    (Eventually.of_forall (fun i s hs => hbound (e i) s hs))
    (fun i => by unfold perturb; fun_prop)

/-- Every subproduct is entire, also at points where factors vanish. -/
theorem canonicalProductAlong_differentiable {ι : Type*}
    (h : Admissible q c d) (e : ι ↪ ℕ) :
    Differentiable ℂ (canonicalProductAlong q c d e) := by
  have hu := hasProdLocallyUniformlyOn_of_forall_compact (s := (Set.univ : Set ℂ))
    isOpen_univ (fun K _ hK => canonicalProductAlong_uniform_on_compact h e K hK)
  apply differentiableOn_univ.mp
  apply TendstoLocallyUniformlyOn.differentiableOn hu _ isOpen_univ
  apply Eventually.of_forall
  intro F
  apply Differentiable.differentiableOn
  apply Differentiable.finsetProd
  intro i hi
  exact factor_differentiable (e i)

/-- Entire holomorphy of the original paired canonical product. -/
theorem canonicalProduct_differentiable (h : Admissible q c d) :
    Differentiable ℂ (canonicalProduct q c d) := by
  simpa using canonicalProductAlong_differentiable h (Function.Embedding.refl ℕ)

/-- Summability of the perturbations at an arbitrary point. -/
theorem canonical_perturb_norm_summable (h : Admissible q c d) (s : ℂ) :
    Summable (fun n => ‖perturb q c d n s‖) := by
  obtain ⟨b, hb, hbound⟩ := h.compactMajorant ({s} : Set ℂ) isCompact_singleton
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hbound n s (by simp)) hb

/-- A subproduct is nonzero wherever all its factors are nonzero. -/
theorem canonicalProductAlong_ne_zero {ι : Type*}
    (h : Admissible q c d) (e : ι ↪ ℕ) (s : ℂ)
    (hn : ∀ i, factor q c d (e i) s ≠ 0) :
    canonicalProductAlong q c d e s ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable hn
  exact (canonical_perturb_norm_summable h s).comp_injective e.injective

/-- The two roots of an individual factor are exact. -/
theorem factor_zero_iff (hpos : ∀ n, 0 < q n) (hd : d ≠ 0) (n : ℕ) (s : ℂ) :
    factor q c d n s = 0 ↔
      s = c + d * (q n : ℂ) ∨ s = c - d * (q n : ℂ) := by
  have hq : (q n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hpos n))
  constructor
  · intro hz
    have hfrac : ((s - c) / d) ^ 2 / ((q n : ℂ) ^ 2) = 1 := by
      have hh : 1 - ((s - c) / d) ^ 2 / ((q n : ℂ) ^ 2) = 0 := by
        simpa [factor, perturb, sub_eq_add_neg] using hz
      exact (sub_eq_zero.mp hh).symm
    have hs : ((s - c) / d) ^ 2 = (q n : ℂ) ^ 2 := by
      simpa using (div_eq_iff (pow_ne_zero 2 hq)).mp hfrac
    have hp : (((s - c) / d) - (q n : ℂ)) * (((s - c) / d) + (q n : ℂ)) = 0 := by
      calc
        _ = ((s - c) / d) ^ 2 - (q n : ℂ) ^ 2 := by ring
        _ = 0 := sub_eq_zero.mpr hs
    rcases mul_eq_zero.mp hp with hp | hm
    · left
      have hh := (div_eq_iff hd).mp (sub_eq_zero.mp hp)
      linear_combination hh
    · right
      have hh := (div_eq_iff hd).mp (add_eq_zero_iff_eq_neg.mp hm)
      linear_combination hh
  · rintro (rfl | rfl)
    · exact factor_zero_at_positive_level q n (ne_of_gt (hpos n)) c d hd
    · simp only [factor, perturb]
      field_simp [hd, hq]
      ring

/-- No extra zeros can arise from the infinite tail. -/
theorem canonicalProduct_zero_iff (h : Admissible q c d) (hd : d ≠ 0) (s : ℂ) :
    canonicalProduct q c d s = 0 ↔
      ∃ n, s = c + d * (q n : ℂ) ∨ s = c - d * (q n : ℂ) := by
  constructor
  · intro hz
    by_contra hn
    have hf : ∀ n, factor q c d n s ≠ 0 := by
      intro n hf
      exact hn ⟨n, (factor_zero_iff h.positive hd n s).mp hf⟩
    exact (canonicalProductAlong_ne_zero h (Function.Embedding.refl ℕ) s hf) hz
  · rintro ⟨n, hn⟩
    exact tprod_of_exists_eq_zero ⟨n, (factor_zero_iff h.positive hd n s).mpr hn⟩

/-- Fixed-center normalization, without any convergence or positivity assumption. -/
@[simp] theorem canonicalProduct_at_center (q : ℕ → ℝ) (c d : ℂ) :
    canonicalProduct q c d c = 1 := by
  simp [canonicalProduct, factor, perturb]

/-- Paired symmetry about the prescribed center. -/
theorem canonicalProduct_reflection (q : ℕ → ℝ) (c d s : ℂ) :
    canonicalProduct q c d (2 * c - s) = canonicalProduct q c d s := by
  apply tprod_congr
  intro n
  unfold factor perturb
  congr 2
  ring

end
end SpectralGeometry
