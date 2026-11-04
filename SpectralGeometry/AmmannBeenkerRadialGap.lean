module

public import SpectralGeometry.AmmannBeenkerOperator

public section

/-!
# A radial gap outside the central octagonal patch

The internal octagon has squared radius less than two. Together with the
joint norm identity this reduces the small-radius classification to 81
integer lifts. Every case is checked by Lean arithmetic.
-/

namespace SpectralGeometry.AmmannBeenker

/-- A sharper bound for the internal octagonal acceptance window. -/
theorem internal_norm_sq_lt_two {n : Lattice} (hn : Admitted n) :
    ‖internal n‖ ^ 2 < 2 := by
  let x := (internal n).re
  let y := (internal n).im
  have ha := alpha_sq
  have hal := alpha_bounds.1
  have hau := alpha_bounds.2
  have hx : |x| < 1 / 2 + alpha := hn.1
  have hy : |y| < 1 / 2 + alpha := hn.2.1
  have hsum : |x| + |y| < 1 + alpha := by
    have hp := abs_lt.mp hn.2.2.1
    have hm := abs_lt.mp hn.2.2.2
    change -(1 + alpha) < x + y ∧ x + y < 1 + alpha at hp
    change -(1 + alpha) < x - y ∧ x - y < 1 + alpha at hm
    rcases le_total 0 x with hx0 | hx0 <;> rcases le_total 0 y with hy0 | hy0
    · rw [abs_of_nonneg hx0, abs_of_nonneg hy0]; linarith
    · rw [abs_of_nonneg hx0, abs_of_nonpos hy0]; linarith
    · rw [abs_of_nonpos hx0, abs_of_nonneg hy0]; linarith
    · rw [abs_of_nonpos hx0, abs_of_nonpos hy0]; linarith
  have hx0 := abs_nonneg x
  have hy0 := abs_nonneg y
  have hxy := mul_nonneg hx0 hy0
  have hbound : |x| ^ 2 + |y| ^ 2 < 2 := by
    by_cases hsmall : |x| + |y| ≤ 1 / 2 + alpha
    · have hs := mul_nonneg (sub_nonneg.mpr hsmall)
        (show 0 ≤ 1 / 2 + alpha + (|x| + |y|) by linarith)
      nlinarith
    · have hp := mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hy.le)
      have hs := mul_nonneg (sub_nonneg.mpr hsum.le)
        (show 0 ≤ (|x| + |y|) - alpha by linarith)
      nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sq_abs] at hbound
  dsimp [x, y] at hbound
  nlinarith

set_option maxHeartbeats 4000000 in
/-- An admitted vertex below the next shell lies within physical radius two. -/
theorem physical_sq_gap {n : Lattice} (hn : Admitted n)
    (hr : ‖physical n‖ ^ 2 < 3 + 4 * alpha) : ‖physical n‖ ^ 2 ≤ 4 := by
  have ha := alpha_sq
  have hal := alpha_bounds.1
  have hau := alpha_bounds.2
  have hi := internal_norm_sq_lt_two hn
  have hj := joint_norm_identity n
  have h0 := sq_nonneg (n 0 : ℝ)
  have h1 := sq_nonneg (n 1 : ℝ)
  have h2 := sq_nonneg (n 2 : ℝ)
  have h3 := sq_nonneg (n 3 : ℝ)
  have hab : alpha < 3 / 4 := by nlinarith
  have hc (i : Fin 4) : -1 ≤ n i ∧ n i ≤ 1 := by
    have hs : (n i : ℝ) ^ 2 < 4 := by
      fin_cases i <;> simp only [Fin.reduceFinMk] <;> nlinarith
    have hh : (-2 : ℝ) < n i ∧ (n i : ℝ) < 2 := by
      constructor <;> nlinarith
    have hh' : (-2 : ℤ) < n i ∧ n i < 2 := by exact_mod_cast hh
    omega
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  have hc3 := hc 3
  generalize hn0 : n 0 = a at *
  generalize hn1 : n 1 = b at *
  generalize hn2 : n 2 = c at *
  generalize hn3 : n 3 = d at *
  have he : n = ![a,b,c,d] := by
    funext i
    fin_cases i <;> simpa using (by assumption)
  rw [he] at hn hr ⊢
  clear hj hi hc h0 h1 h2 h3
  rcases hc0 with ⟨ha0, ha1⟩
  rcases hc1 with ⟨hb0, hb1⟩
  rcases hc2 with ⟨hc0, hc1⟩
  rcases hc3 with ⟨hd0, hd1⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d
  all_goals norm_num [Admitted, Window, internal, abs_lt] at hn
  all_goals norm_num [physical, Complex.sq_norm, Complex.normSq_apply] at hr ⊢
  all_goals nlinarith

/-- The first omitted shell gives the exterior barrier `4 + 2 * sqrt 2`. -/
theorem potential_outside_sector_sharp (v : Vertex) (hv : v ∉ sector) :
    4 + 4 * alpha ≤ potential v := by
  have hn : 2 < ‖position v‖ := lt_of_not_ge ((mem_sector v).not.mp hv)
  have hr : 3 + 4 * alpha ≤ ‖position v‖ ^ 2 := by
    by_contra h
    have hh := physical_sq_gap v.property (lt_of_not_ge h)
    change ‖position v‖ ^ 2 ≤ 4 at hh
    nlinarith
  unfold potential
  linarith

/-- A sharper nine-level response for the same operator and sector.
The coefficient is `4 * sqrt 2 - 5`, on the enlarged interval
`0 ≤ τ ≤ 3 + 2 * sqrt 2`. -/
theorem exists_nine_level_response_sharp :
    ∃ ev : ℕ → ℝ, Monotone ev ∧
      Nonempty (DomainEigenbasis (infiniteOnsiteDomain potential)
        (onsitePlusBounded potential interaction) ev) ∧
      (∀ n : ℕ, 1 ≤ ev n) ∧
      (∀ n : ℕ, n < 9 → ev n ≤ 3) ∧
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ 3 + 4 * alpha →
        ∃ μ : ℕ → ℝ, Monotone μ ∧
          Nonempty (DomainEigenbasis (infiniteOnsiteDomain potential)
            (onsitePlusBounded potential (interaction + τ • finiteSectorProjection sector)) μ) ∧
          (∀ n : ℕ, 1 ≤ μ n) ∧
          (∀ n : ℕ, n < 9 →
            (8 * alpha - 5) * τ ≤ μ n - ev n ∧ μ n - ev n ≤ τ) := by
  obtain ⟨ev, hev, ⟨b⟩, hgap, hl, _⟩ := exists_nine_level_response
  refine ⟨ev, hev, ⟨b⟩, hgap, hl, ?_⟩
  intro τ ht htR
  have hsym := finiteSectorCorrection_symmetric interaction interaction_symmetric sector τ
  obtain ⟨μ, hμ, ⟨bt⟩⟩ := onsitePlusBounded_exists_orderedEigenbasis
    potential 1 potential_lower potential_proper _ hsym
  have hgapμ : ∀ n : ℕ, 1 ≤ μ n := fun n => (hgap n).trans
    (finiteSector_ordered_mono potential interaction interaction_symmetric sector
      τ ht ev μ hev hμ b bt n)
  refine ⟨μ, hμ, ⟨bt⟩, hgapμ, ?_⟩
  intro n hn
  have ha := alpha_bounds.1
  have hr := finiteSector_ordered_response_of_nonneg potential interaction interaction_symmetric
    interaction_nonneg 1 (4 + 4 * alpha) 3 potential_lower (by linarith)
    sector potential_outside_sector_sharp τ ht (by linarith) ev μ hev hμ b bt n (hl n hn)
  have hc : ((4 + 4 * alpha - 3) / (4 + 4 * alpha - 1)) = 8 * alpha - 5 := by
    apply (div_eq_iff (by linarith : 4 + 4 * alpha - 1 ≠ 0)).2
    nlinarith [alpha_sq]
  simpa only [hc] using hr

end SpectralGeometry.AmmannBeenker
