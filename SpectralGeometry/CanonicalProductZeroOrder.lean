module

public import SpectralGeometry.CanonicalProductAnalytic

public section

/-!
# Exact zero orders of the paired canonical product

At each point only finitely many factors vanish. Splitting off precisely
those factors leaves an entire subproduct nonzero at that point. Consequently
repeated positive levels give exactly their repetition count as zero order.
-/

namespace SpectralGeometry

open scoped BigOperators

noncomputable section

variable {q : ℕ → ℝ} {c d : ℂ}

/-- The derivative of a paired factor. -/
theorem factor_hasDerivAt (n : ℕ) (s : ℂ) :
    HasDerivAt (factor q c d n)
      (-(2 * ((s - c) / d) * (1 / d) / (q n : ℂ) ^ 2)) s := by
  simpa [factor, perturb] using
    (((((hasDerivAt_id s).sub_const c).div_const d).pow 2).div_const
      ((q n : ℂ) ^ 2)).neg.const_add 1

/-- Positivity separates the two roots, so every vanishing factor has order one. -/
theorem factor_analyticOrderAt (hpos : ∀ n, 0 < q n) (hd : d ≠ 0)
    (n : ℕ) (s : ℂ) (hz : factor q c d n s = 0) :
    analyticOrderAt (factor q c d n) s = 1 := by
  have hq : (q n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hpos n))
  have hsc : s - c ≠ 0 := by
    intro hh
    have hh' : s = c := sub_eq_zero.mp hh
    simp [hh', factor, perturb] at hz
  apply (factor_differentiable n).analyticAt s |>.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
  rw [(factor_hasDerivAt n s).deriv]
  exact neg_ne_zero.mpr (div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (div_ne_zero hsc hd))
      (one_div_ne_zero hd)) (pow_ne_zero 2 hq))

/-- There cannot be infinitely many vanishing factors at a point: each
would contribute one to the summable norm of the perturbations. -/
theorem canonicalProduct_zeroIndices_finite (h : Admissible q c d) (s : ℂ) :
    {n : ℕ | factor q c d n s = 0}.Finite := by
  let Z := {n : ℕ | factor q c d n s = 0}
  have hs := (canonical_perturb_norm_summable h s).comp_injective
    (Subtype.val_injective : Function.Injective (fun n : Z => n.val))
  have hc : Summable (fun _ : Z => (1 : ℝ)) := hs.congr (fun n => by
    have hp : perturb q c d n.val s = -1 := by
      have hz := n.property
      change 1 + perturb q c d n.val s = 0 at hz
      linear_combination hz
    simp [hp])
  letI := Finite.of_summable_const (show (0 : ℝ) < 1 by norm_num) hc
  exact Set.toFinite Z

/-- Removing finitely many factors is a genuine product factorization,
including when the original product vanishes. -/
theorem canonicalProduct_split_finset (h : Admissible q c d) (F : Finset ℕ) (s : ℂ) :
    canonicalProduct q c d s =
      (∏ n ∈ F, factor q c d n s) *
        canonicalProductAlong q c d
          (⟨Subtype.val, Subtype.val_injective⟩ : {n // n ∉ F} ↪ ℕ) s := by
  let e : {n // n ∉ F} ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have ht := (canonicalProductAlong_uniform_on_compact h e {s}
    isCompact_singleton).hasProd (by simp)
  have hf : Multipliable (fun n : (F : Set ℕ) => factor q c d n s) :=
    Multipliable.of_finite
  simpa [canonicalProduct, canonicalProductAlong, e, Finset.tprod_subtype'] using
    (hf.tprod_mul_tprod_compl ht.multipliable).symm

/-- A finite product of factors vanishing at a point has order its cardinality. -/
theorem factor_finset_analyticOrderAt (hpos : ∀ n, 0 < q n) (hd : d ≠ 0)
    (F : Finset ℕ) (s : ℂ) (hz : ∀ n ∈ F, factor q c d n s = 0) :
    analyticOrderAt (fun z => ∏ n ∈ F, factor q c d n z) s = (F.card : ℕ∞) := by
  induction F using Finset.induction_on with
  | empty => simp [analyticOrderAt_eq_zero]
  | @insert n F hn ih =>
    have hf : AnalyticAt ℂ (fun z => ∏ i ∈ F, factor q c d i z) s := by
      apply Differentiable.analyticAt
      exact Differentiable.finsetProd (fun i _ => factor_differentiable i)
    have he : (fun z => ∏ i ∈ insert n F, factor q c d i z) =
        factor q c d n * (fun z => ∏ i ∈ F, factor q c d i z) := by
      ext z
      simp [Finset.prod_insert hn]
    rw [he, analyticOrderAt_mul ((factor_differentiable n).analyticAt s) hf,
      factor_analyticOrderAt hpos hd n s (hz n (by simp)),
      ih (fun i hi => hz i (by simp [hi]))]
    simp [Finset.card_insert_of_notMem hn, add_comm]

/-- The exact order at every point is the number of factors vanishing there.
The finiteness of this number was proved, not assumed. -/
theorem canonicalProduct_analyticOrderAt (h : Admissible q c d) (hd : d ≠ 0) (s : ℂ) :
    analyticOrderAt (canonicalProduct q c d) s =
      (Nat.card {n : ℕ // factor q c d n s = 0} : ℕ∞) := by
  classical
  let F := (canonicalProduct_zeroIndices_finite h s).toFinset
  have hF (n : ℕ) : n ∈ F ↔ factor q c d n s = 0 := by simp [F]
  let e : {n // n ∉ F} ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have ht := (canonicalProductAlong_differentiable h e).analyticAt s
  have htn : canonicalProductAlong q c d e s ≠ 0 :=
    canonicalProductAlong_ne_zero h e s (fun n hn => n.property ((hF n).mpr hn))
  have hp : AnalyticAt ℂ (fun z => ∏ n ∈ F, factor q c d n z) s := by
    apply Differentiable.analyticAt
    exact Differentiable.finsetProd (fun n _ => factor_differentiable n)
  have he : canonicalProduct q c d =
      (fun z => ∏ n ∈ F, factor q c d n z) * canonicalProductAlong q c d e :=
    funext (canonicalProduct_split_finset h F)
  rw [he, analyticOrderAt_mul hp ht,
    factor_finset_analyticOrderAt h.positive hd F s (fun n hn => (hF n).mp hn),
    ht.analyticOrderAt_eq_zero.mpr htn, add_zero]
  congr 1
  have hset : (F : Set ℕ) = {n : ℕ | factor q c d n s = 0} := Set.ext hF
  rw [← hset]
  simp

/-- Multiplicity of a level in a sequence. For the admissible products below
the relevant fibers are finite; full spectral tags fix these counts exactly. -/
@[expose] def levelMultiplicity (q : ℕ → ℝ) (r : ℝ) : ℕ :=
  Nat.card {n : ℕ // q n = r}

theorem factor_zero_at_signed_level_iff (hpos : ∀ n, 0 < q n) (hd : d ≠ 0)
    (r : ℝ) (hr : 0 < r) (n : ℕ) (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    factor q c d n (c + d * ((sign * r : ℝ) : ℂ)) = 0 ↔ q n = r := by
  rw [factor_zero_iff hpos hd]
  have hcast : ∀ a b : ℝ, c + d * (a : ℂ) = c + d * (b : ℂ) ↔ a = b := by
    intro a b
    simp [hd]
  have hminus : c - d * (q n : ℂ) = c + d * ((-q n : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hminus, hcast, hcast]
  rcases hsign with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;>
    constructor <;> intro hh
  · rcases hh with hh | hh <;> linarith [hpos n]
  · exact Or.inl hh.symm
  · rcases hh with hh | hh <;> linarith [hpos n]
  · exact Or.inr (by rw [hh])

/-- Each of the paired zeros has exactly the repetition multiplicity of its
positive level, with no simplicity or separation assumption on other levels. -/
theorem canonicalProduct_order_at_signed_level (h : Admissible q c d) (hd : d ≠ 0)
    (r : ℝ) (hr : 0 < r) (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    analyticOrderAt (canonicalProduct q c d) (c + d * ((sign * r : ℝ) : ℂ)) =
      (levelMultiplicity q r : ℕ∞) := by
  rw [canonicalProduct_analyticOrderAt h hd]
  have he : {n : ℕ | factor q c d n (c + d * ((sign * r : ℝ) : ℂ)) = 0} =
      {n : ℕ | q n = r} := Set.ext (fun n =>
    factor_zero_at_signed_level_iff h.positive hd r hr n sign hsign)
  change (Nat.card ↥{n : ℕ | factor q c d n (c + d * ((sign * r : ℝ) : ℂ)) = 0} : ℕ∞) = _
  rw [he]
  rfl

end
end SpectralGeometry
