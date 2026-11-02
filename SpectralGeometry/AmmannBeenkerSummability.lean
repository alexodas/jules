module

public import SpectralGeometry.AmmannBeenkerOperator

public section

/-!
# Planar coding and inverse-square summability of the octagonal model

Two lattice coordinates determine each accepted lift up to two bounded
integer residues. This gives a finite-fiber planar code and a summable
majorant for the actual quadratic onsite potential.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

abbrev WindowResidue := {k : ℤ // k ∈ Finset.Icc (-2 : ℤ) 2}

private theorem residue_bound (z : ℤ) (x : ℝ) (h : |(z : ℝ) - x| < 2) :
    z - ⌊x⌋ ∈ Finset.Icc (-2 : ℤ) 2 := by
  have hl := Int.floor_le x
  have hu := Int.lt_floor_add_one x
  have hab := abs_lt.mp h
  have hlow : (-2 : ℝ) < (z : ℝ) - (⌊x⌋ : ℝ) := by linarith
  have hhigh : (z : ℝ) - (⌊x⌋ : ℝ) < 3 := by linarith
  have hli : -2 < z - ⌊x⌋ := by exact_mod_cast hlow
  have hui : z - ⌊x⌋ < 3 := by exact_mod_cast hhigh
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

@[expose] def horizontalResidue (v : Vertex) : WindowResidue :=
  ⟨v.val 0 - ⌊alpha * ((v.val 1 : ℝ) - v.val 3)⌋, by
    apply residue_bound
    have h := v.property.1
    change |(v.val 0 : ℝ) - alpha * ((v.val 1 : ℝ) - v.val 3)| < _ at h
    exact h.trans (by linarith [alpha_bounds.2])⟩

@[expose] def verticalResidue (v : Vertex) : WindowResidue :=
  ⟨v.val 2 - ⌊alpha * ((v.val 1 : ℝ) + v.val 3)⌋, by
    apply residue_bound
    have h := v.property.2.1
    change |-(v.val 2 : ℝ) + alpha * ((v.val 1 : ℝ) + v.val 3)| < _ at h
    rw [neg_add_eq_sub, abs_sub_comm] at h
    exact h.trans (by linarith [alpha_bounds.2])⟩

@[expose] def planarCode (v : Vertex) : (ℤ × ℤ) × (WindowResidue × WindowResidue) :=
  ((v.val 1, v.val 3), horizontalResidue v, verticalResidue v)

theorem planarCode_injective : Function.Injective planarCode := by
  intro v w h
  have h1 : v.val 1 = w.val 1 := congrArg (fun c => c.1.1) h
  have h3 : v.val 3 = w.val 3 := congrArg (fun c => c.1.2) h
  have hx := congrArg (fun c => c.2.1.val) h
  have hy := congrArg (fun c => c.2.2.val) h
  change v.val 0 - ⌊alpha * ((v.val 1 : ℝ) - v.val 3)⌋ =
    w.val 0 - ⌊alpha * ((w.val 1 : ℝ) - w.val 3)⌋ at hx
  change v.val 2 - ⌊alpha * ((v.val 1 : ℝ) + v.val 3)⌋ =
    w.val 2 - ⌊alpha * ((w.val 1 : ℝ) + w.val 3)⌋ at hy
  rw [h1, h3] at hx hy
  apply Subtype.ext
  funext i
  fin_cases i
  · change v.val 0 = w.val 0; omega
  · exact h1
  · change v.val 2 = w.val 2; omega
  · exact h3

/-- The planar coordinates grow at most quadratically with onsite energy. -/
theorem planar_energy_bound (v : Vertex) :
    1 + (v.val 1 : ℝ) ^ 2 + (v.val 3 : ℝ) ^ 2 ≤ 5 * potential v := by
  have hj := joint_norm_identity v.val
  have hi := internal_norm_sq_lt_eight v.property
  unfold potential position
  nlinarith [sq_nonneg (v.val 0 : ℝ), sq_nonneg (v.val 2 : ℝ),
    sq_nonneg (‖physical v.val‖)]

private theorem integer_weight_summable :
    Summable (fun n : ℤ => 1 / (1 + (n : ℝ) ^ 2)) := by
  have hp : Summable (fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hz : Summable (fun n : ℤ => if n = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq 0 1).summable
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hz.add hp)
  intro n
  by_cases hn : n = 0
  · subst n; norm_num
  · simp only [hn, if_false, zero_add]
    apply one_div_le_one_div_of_le
    · exact sq_pos_of_ne_zero (by exact_mod_cast hn)
    · linarith

/-- Summability is proved for the actual accepted vertices, not postulated
for an arbitrary enumeration or inferred from compact resolvent alone. -/
theorem potential_invSq_summable : Summable (fun v : Vertex => 1 / (potential v) ^ 2) := by
  let g : ℤ → ℝ := fun n => 1 / (1 + (n : ℝ) ^ 2)
  have hg : Summable g := integer_weight_summable
  have hg0 : ∀ n, 0 ≤ g n := fun n => by dsimp [g]; positivity
  have hp : Summable (fun n : ℤ × ℤ => g n.1 * g n.2) :=
    hg.mul_of_nonneg hg hg0 hg0
  have hf : Summable (fun _ : WindowResidue × WindowResidue => (1 : ℝ)) := by
    exact Summable.of_finite
  have hmajor := ((hp.mul_of_nonneg hf
    (fun n => mul_nonneg (hg0 n.1) (hg0 n.2)) (fun _ => by norm_num)).mul_left 25)
      .comp_injective planarCode_injective
  apply Summable.of_nonneg_of_le (fun v => by positivity) _ hmajor
  intro v
  change 1 / (potential v) ^ 2 ≤ 25 * ((g (v.val 1) * g (v.val 3)) * 1)
  dsimp [g]
  have ha : 0 < 1 + (v.val 1 : ℝ) ^ 2 := by positivity
  have hb : 0 < 1 + (v.val 3 : ℝ) ^ 2 := by positivity
  have hv : 0 < potential v := lt_of_lt_of_le (by norm_num) (potential_lower v)
  have he := planar_energy_bound v
  have hsum : 0 ≤ 1 + (v.val 1 : ℝ) ^ 2 + (v.val 3 : ℝ) ^ 2 := by positivity
  have hs : (1 + (v.val 1 : ℝ) ^ 2 + (v.val 3 : ℝ) ^ 2) ^ 2 ≤
      25 * (potential v) ^ 2 := by nlinarith
  have hd : (1 + (v.val 1 : ℝ) ^ 2) * (1 + (v.val 3 : ℝ) ^ 2) ≤
      25 * (potential v) ^ 2 := by
    nlinarith [sq_nonneg ((v.val 1 : ℝ) ^ 2), sq_nonneg ((v.val 3 : ℝ) ^ 2),
      mul_nonneg (sq_nonneg (v.val 1 : ℝ)) (sq_nonneg (v.val 3 : ℝ))]
  rw [mul_one, div_mul_div_comm, one_mul]
  exact (div_le_div_iff₀ (sq_pos_of_pos hv) (mul_pos ha hb)).mpr (by simpa using hd)

end
end SpectralGeometry.AmmannBeenker
