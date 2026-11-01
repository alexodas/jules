module

public import Mathlib

public section

/-!
# The centered octagonal cut-and-project vertex model

The physical and internal projections of ℤ⁴ use conjugate eighth-root
embeddings. The open centered octagonal acceptance window has side one.
The vertex model and its boundary convention are explicit; polygonal
coverage and aperiodicity are separate obligations.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

abbrev Lattice := Fin 4 → ℤ

@[expose] def alpha : ℝ := Real.sqrt 2 / 2

theorem alpha_sq : alpha ^ 2 = 1 / 2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  dsimp [alpha]
  nlinarith

theorem alpha_bounds : 1 / 2 < alpha ∧ alpha < 1 := by
  have h := Real.sqrt_nonneg (2 : ℝ)
  have hs := alpha_sq
  dsimp [alpha] at *
  constructor <;> nlinarith

@[expose] def physical (n : Lattice) : ℂ :=
  ⟨n 0 + alpha * (n 1 - n 3), n 2 + alpha * (n 1 + n 3)⟩

@[expose] def internal (n : Lattice) : ℂ :=
  ⟨n 0 - alpha * (n 1 - n 3), -(n 2 : ℝ) + alpha * (n 1 + n 3)⟩

@[simp] theorem physical_zero : physical 0 = 0 := by apply Complex.ext <;> simp [physical]
@[simp] theorem internal_zero : internal 0 = 0 := by apply Complex.ext <;> simp [internal]

@[simp] theorem physical_add (m n : Lattice) : physical (m + n) = physical m + physical n := by
  apply Complex.ext <;> simp [physical] <;> ring
@[simp] theorem internal_add (m n : Lattice) : internal (m + n) = internal m + internal n := by
  apply Complex.ext <;> simp [internal] <;> ring
@[simp] theorem physical_neg (n : Lattice) : physical (-n) = -physical n := by
  apply Complex.ext <;> simp [physical] <;> ring
@[simp] theorem internal_neg (n : Lattice) : internal (-n) = -internal n := by
  apply Complex.ext <;> simp [internal] <;> ring
@[simp] theorem physical_sub (m n : Lattice) : physical (m - n) = physical m - physical n := by
  simp [sub_eq_add_neg]
@[simp] theorem internal_sub (m n : Lattice) : internal (m - n) = internal m - internal n := by
  simp [sub_eq_add_neg]

private theorem integer_coefficients (a b : ℤ)
    (h : (a : ℝ) + alpha * b = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply irrational_sqrt_two.ne_rational (-2 * a) b
    apply (eq_div_iff (by exact_mod_cast hb : (b : ℝ) ≠ 0)).mpr
    dsimp [alpha] at h
    push_cast
    linarith
  subst b
  simp only [Int.cast_zero, mul_zero, add_zero] at h
  exact ⟨by exact_mod_cast h, rfl⟩

theorem physical_injective : Function.Injective physical := by
  intro m n h
  have hx := congrArg Complex.re h
  have hy := congrArg Complex.im h
  change (m 0 : ℝ) + alpha * (m 1 - m 3) = n 0 + alpha * (n 1 - n 3) at hx
  change (m 2 : ℝ) + alpha * (m 1 + m 3) = n 2 + alpha * (n 1 + n 3) at hy
  have h0 := integer_coefficients (m 0 - n 0) (m 1 - m 3 - (n 1 - n 3)) (by
    push_cast; linarith)
  have h2 := integer_coefficients (m 2 - n 2) (m 1 + m 3 - (n 1 + n 3)) (by
    push_cast; linarith)
  rcases h0 with ⟨h00, h01⟩
  rcases h2 with ⟨h20, h21⟩
  funext i
  fin_cases i
  · change m 0 = n 0; omega
  · change m 1 = n 1; omega
  · change m 2 = n 2; omega
  · change m 3 = n 3; omega

theorem internal_injective : Function.Injective internal := by
  intro m n h
  have hx := congrArg Complex.re h
  have hy := congrArg Complex.im h
  change (m 0 : ℝ) - alpha * (m 1 - m 3) = n 0 - alpha * (n 1 - n 3) at hx
  change -(m 2 : ℝ) + alpha * (m 1 + m 3) = -n 2 + alpha * (n 1 + n 3) at hy
  have h0 := integer_coefficients (m 0 - n 0) (-(m 1 - m 3 - (n 1 - n 3))) (by
    push_cast; linarith)
  have h2 := integer_coefficients (n 2 - m 2) (m 1 + m 3 - (n 1 + n 3)) (by
    push_cast; linarith)
  rcases h0 with ⟨h00, h01⟩
  rcases h2 with ⟨h20, h21⟩
  funext i
  fin_cases i
  · change m 0 = n 0; omega
  · change m 1 = n 1; omega
  · change m 2 = n 2; omega
  · change m 3 = n 3; omega

/-- Open octagon; boundary points are excluded by definition. -/
@[expose] def Window (z : ℂ) : Prop :=
  |z.re| < 1 / 2 + alpha ∧ |z.im| < 1 / 2 + alpha ∧
    |z.re + z.im| < 1 + alpha ∧ |z.re - z.im| < 1 + alpha

@[expose] def Admitted (n : Lattice) : Prop := Window (internal n)
@[expose] def Vertex := {n : Lattice // Admitted n}
instance : DecidableEq Vertex := Classical.decEq _
@[expose] def position (v : Vertex) : ℂ := physical v.val

theorem position_injective : Function.Injective position := fun _ _ h =>
  Subtype.ext (physical_injective h)

theorem window_neg {z : ℂ} (h : Window z) : Window (-z) := by
  change |-z.re| < _ ∧ |-z.im| < _ ∧ |-z.re + -z.im| < _ ∧ |-z.re - -z.im| < _
  rw [show -z.re + -z.im = -(z.re + z.im) by ring,
    show -z.re - -z.im = -(z.re - z.im) by ring]
  simpa only [Window, abs_neg] using h

theorem admitted_zero : Admitted 0 := by
  have ha := alpha_bounds
  simp [Admitted, Window]
  constructor <;> linarith

theorem admitted_neg {n : Lattice} (h : Admitted n) : Admitted (-n) := by
  simpa [Admitted] using window_neg h

@[expose] def origin : Vertex := ⟨0, admitted_zero⟩
@[expose] def basis (i : Fin 4) : Lattice := Pi.single i 1

theorem basis_admitted (i : Fin 4) : Admitted (basis i) := by
  have ha := alpha_bounds
  have hap : 0 < alpha := by linarith
  have han : -alpha < 0 := by linarith
  fin_cases i <;>
    norm_num [Admitted, Window, internal, basis, Pi.single_apply,
      abs_of_pos hap, abs_of_neg han,
      abs_of_nonneg (show 0 ≤ alpha + alpha by linarith),
      abs_of_neg (show -alpha - alpha < 0 by linarith)] <;>
    (repeat' constructor) <;> linarith

theorem physical_basis_norm (i : Fin 4) : ‖physical (basis i)‖ = 1 := by
  have ha := alpha_sq
  have hs : ‖physical (basis i)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    fin_cases i <;> norm_num [physical, basis, Pi.single_apply, Complex.normSq_apply] <;> nlinarith
  nlinarith [norm_nonneg (physical (basis i))]

/-- Silver-unit inflation contracts the internal plane. -/
@[expose] def inflate (n : Lattice) : Lattice :=
  ![n 0 + n 1 - n 3, n 1 + n 0 + n 2, n 2 + n 1 + n 3, n 3 + n 2 - n 0]

theorem physical_inflate (n : Lattice) :
    physical (inflate n) = ((1 + 2 * alpha : ℝ) : ℂ) * physical n := by
  apply Complex.ext <;> simp [physical, inflate] <;> ring_nf <;> rw [alpha_sq] <;> ring

theorem internal_inflate (n : Lattice) :
    internal (inflate n) = ((1 - 2 * alpha : ℝ) : ℂ) * internal n := by
  apply Complex.ext <;> simp [internal, inflate] <;> ring_nf <;> rw [alpha_sq] <;> ring

theorem window_mul_real {z : ℂ} (h : Window z) {t : ℝ} (ht : |t| ≤ 1) :
    Window ((t : ℂ) * z) := by
  have hb (x : ℝ) : |t * x| ≤ |x| := by
    rw [abs_mul]
    nlinarith [abs_nonneg x]
  rcases h with ⟨h0, h1, h2, h3⟩
  simp only [Window, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  exact ⟨(hb _).trans_lt h0, (hb _).trans_lt h1,
    by rw [← mul_add]; exact (hb _).trans_lt h2,
    by rw [← mul_sub]; exact (hb _).trans_lt h3⟩

theorem admitted_inflate {n : Lattice} (h : Admitted n) : Admitted (inflate n) := by
  unfold Admitted at *
  rw [internal_inflate]
  apply window_mul_real h
  have ha := alpha_bounds
  exact abs_le.mpr ⟨by linarith, by linarith⟩

@[expose] def inflatedOriginNeighbor : ℕ → Vertex
  | 0 => ⟨basis 0, basis_admitted 0⟩
  | k + 1 => ⟨inflate (inflatedOriginNeighbor k).val,
      admitted_inflate (inflatedOriginNeighbor k).property⟩

theorem inflatedOriginNeighbor_norm (k : ℕ) :
    ‖position (inflatedOriginNeighbor k)‖ = (1 + 2 * alpha) ^ k := by
  have ha := alpha_bounds
  induction k with
  | zero => simpa [inflatedOriginNeighbor, position] using physical_basis_norm 0
  | succ k ih =>
    change ‖physical (inflate (inflatedOriginNeighbor k).val)‖ = _
    rw [physical_inflate, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1 + 2 * alpha)]
    change (1 + 2 * alpha) * ‖position (inflatedOriginNeighbor k)‖ = _
    rw [ih, pow_succ]
    ring

theorem inflatedOriginNeighbor_injective : Function.Injective inflatedOriginNeighbor := by
  intro i j h
  have hn := congrArg (fun v => ‖position v‖) h
  rw [inflatedOriginNeighbor_norm, inflatedOriginNeighbor_norm] at hn
  exact (pow_right_strictMono₀ (by linarith [alpha_bounds.1] : 1 < 1 + 2 * alpha)).injective hn

instance : Infinite Vertex := Infinite.of_injective inflatedOriginNeighbor inflatedOriginNeighbor_injective

theorem joint_norm_identity (n : Lattice) :
    ‖physical n‖ ^ 2 + ‖internal n‖ ^ 2 =
      2 * ((n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2 + (n 3 : ℝ) ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, physical, internal]
  ring_nf
  rw [alpha_sq]
  ring

theorem internal_norm_sq_lt_eight {n : Lattice} (h : Admitted n) : ‖internal n‖ ^ 2 < 8 := by
  have h0 : |(internal n).re| < 2 := h.1.trans (by linarith [alpha_bounds.2])
  have h1 : |(internal n).im| < 2 := h.2.1.trans (by linarith [alpha_bounds.2])
  rw [Complex.sq_norm, Complex.normSq_apply]
  have ha := abs_lt.mp h0
  have hb := abs_lt.mp h1
  nlinarith [sq_nonneg ((internal n).re - (internal n).im)]

theorem coordinate_bound {n : Lattice} (h : Admitted n) {R : ℝ}
    (hR : 0 ≤ R) (hp : ‖physical n‖ ≤ R) (i : Fin 4) : |(n i : ℝ)| ≤ R + 3 := by
  have hj := joint_norm_identity n
  have hi := internal_norm_sq_lt_eight h
  have hs : ‖physical n‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hp
  have ha := sq_nonneg (n 0 : ℝ)
  have hb := sq_nonneg (n 1 : ℝ)
  have hc := sq_nonneg (n 2 : ℝ)
  have hd := sq_nonneg (n 3 : ℝ)
  have hsq : (n i : ℝ) ^ 2 ≤ (R + 3) ^ 2 := by
    have hsum : 2 * ((n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2 +
        (n 3 : ℝ) ^ 2) < R ^ 2 + 8 := by linarith
    fin_cases i
    · change (n 0 : ℝ) ^ 2 ≤ (R + 3) ^ 2; nlinarith
    · change (n 1 : ℝ) ^ 2 ≤ (R + 3) ^ 2; nlinarith
    · change (n 2 : ℝ) ^ 2 ≤ (R + 3) ^ 2; nlinarith
    · change (n 3 : ℝ) ^ 2 ≤ (R + 3) ^ 2; nlinarith
  simpa [abs_of_nonneg (by linarith : 0 ≤ R + 3)] using sq_le_sq.mp hsq

/-- Physical bounded subsets of the accepted vertex set are finite. -/
theorem finite_norm_sublevel (R : ℝ) : {v : Vertex | ‖position v‖ ≤ R}.Finite := by
  classical
  by_cases hR : 0 ≤ R
  · let N : ℤ := ⌈R + 3⌉
    have hf : {n : Lattice | ∀ i, n i ∈ Set.Icc (-N) N}.Finite :=
      Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
    have hpre : {v : Vertex | ∀ i, v.val i ∈ Set.Icc (-N) N}.Finite :=
      hf.preimage Subtype.val_injective.injOn
    apply hpre.subset
    intro v hv i
    have hb := abs_le.mp (coordinate_bound v.property hR hv i)
    have hN : R + 3 ≤ (N : ℝ) := Int.le_ceil _
    constructor
    · have hl : -(N : ℝ) ≤ (v.val i : ℝ) := by linarith
      exact_mod_cast hl
    · have hu : (v.val i : ℝ) ≤ (N : ℝ) := by linarith
      exact_mod_cast hu
  · have he : {v : Vertex | ‖position v‖ ≤ R} = ∅ := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hR ((norm_nonneg _).trans h)
    rw [he]
    exact Set.finite_empty

end
end SpectralGeometry.AmmannBeenker
