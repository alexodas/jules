module

public import SpectralGeometry.InfiniteLocalCoerciveGap

public section

/-!
# Graph-norm estimates for unbounded onsite operators with local interactions

Let H = M_V + L_w + ε P + m I on the natural onsite domain D(V).
The multiplication potential V may be unbounded, while the matching
interaction L_w and the perturbation P act boundedly on all of real ℓ².

We show that the difference H - M_V is bounded, quantitatively:

  ‖H ψ - M_V ψ‖ ≤ (‖L_w‖ + |ε| ‖P‖ + |m|) ‖ψ‖.

Therefore the two graph norms, built from ‖ψ‖ and respectively
‖H ψ‖ or ‖M_V ψ‖, control each other by explicit inequalities.
Under D matching colors with nonnegative weights ≤ W,
one may substitute the geometric constant 2DW for ‖L_w‖.

These are domain-level bounds without any positivity condition on V,
symmetry condition on P, or sign restriction on ε or m. They provide
a quantitative prerequisite for the later analysis of closedness and
self-adjointness, but establish neither property here.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- The complete infinite local operator differs from the onsite
multiplication by a bounded correction, with an explicit norm estimate. -/
theorem infiniteLocalGraphNorm_correction_le
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ)
    (ψ : infiniteOnsiteDomain V) :
    ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
        infiniteOnsiteOperator V ψ‖ ≤
      (‖infiniteLocalMatchingLaplacian D σ w‖ +
        |ε| * ‖P‖ + |shift|) *
        ‖(ψ.1 : TileHilbert Tile)‖ := by
  let state : TileHilbert Tile := ψ.1
  let L := infiniteLocalMatchingLaplacian D σ w
  have hL : ‖L state‖ ≤ ‖L‖ * ‖state‖ := L.le_opNorm state
  have hP : ‖P state‖ ≤ ‖P‖ * ‖state‖ := P.le_opNorm state
  have hbounded :
      ‖L state + ε • P state + shift • state‖ ≤
        (‖L‖ + |ε| * ‖P‖ + |shift|) * ‖state‖ := by
    calc
      ‖L state + ε • P state + shift • state‖ ≤
          ‖L state + ε • P state‖ + ‖shift • state‖ :=
        norm_add_le _ _
      _ ≤ (‖L state‖ + ‖ε • P state‖) + ‖shift • state‖ :=
        add_le_add_left (norm_add_le _ _) _
      _ = (‖L state‖ + |ε| * ‖P state‖) +
          |shift| * ‖state‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ (‖L‖ * ‖state‖ + |ε| * (‖P‖ * ‖state‖)) +
          |shift| * ‖state‖ := by
        apply add_le_add_left
        exact add_le_add hL
          (mul_le_mul_of_nonneg_left hP (abs_nonneg ε))
      _ = (‖L‖ + |ε| * ‖P‖ + |shift|) * ‖state‖ := by ring
  calc
    ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
        infiniteOnsiteOperator V ψ‖ =
      ‖L state + ε • P state + shift • state‖ := by
        rw [infiniteLocalShiftedPerturbedOperator_apply,
          infiniteLocalMatchingPerturbedOperator_apply]
        congr 1
        dsimp [state, L]
        abel
    _ ≤ (‖L‖ + |ε| * ‖P‖ + |shift|) * ‖state‖ :=
      hbounded

/-- The graph norm of the full operator is bounded above by the onsite
graph contribution and the norm of the bounded correction. -/
theorem infiniteLocalGraphNorm_full_le
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ)
    (ψ : infiniteOnsiteDomain V) :
    ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ‖ ≤
      ‖infiniteOnsiteOperator V ψ‖ +
        (‖infiniteLocalMatchingLaplacian D σ w‖ +
          |ε| * ‖P‖ + |shift|) *
          ‖(ψ.1 : TileHilbert Tile)‖ := by
  have hcor :=
    infiniteLocalGraphNorm_correction_le D V σ w P ε shift ψ
  calc
    ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ‖ =
        ‖infiniteOnsiteOperator V ψ +
          (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
            infiniteOnsiteOperator V ψ)‖ := by
          congr 1
          abel
    _ ≤ ‖infiniteOnsiteOperator V ψ‖ +
          ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
            infiniteOnsiteOperator V ψ‖ := norm_add_le _ _
    _ ≤ _ := add_le_add_right hcor _

/-- Conversely, the onsite graph contribution is controlled by the full
operator graph contribution, with exactly the same bounded constant. -/
theorem infiniteLocalGraphNorm_onsite_le
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ)
    (ψ : infiniteOnsiteDomain V) :
    ‖infiniteOnsiteOperator V ψ‖ ≤
      ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ‖ +
        (‖infiniteLocalMatchingLaplacian D σ w‖ +
          |ε| * ‖P‖ + |shift|) *
          ‖(ψ.1 : TileHilbert Tile)‖ := by
  have hcor :=
    infiniteLocalGraphNorm_correction_le D V σ w P ε shift ψ
  calc
    ‖infiniteOnsiteOperator V ψ‖ =
        ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
          (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
            infiniteOnsiteOperator V ψ)‖ := by
          congr 1
          abel
    _ ≤ ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ‖ +
          ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
            infiniteOnsiteOperator V ψ‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add_right hcor _

/-- With D involutive matching colors and weights bounded by W,
the geometric constant 2DW replaces the abstract interaction norm. -/
theorem infiniteLocalGraphNorm_onsite_geometric_bound
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift W : ℝ)
    (hW : 0 ≤ W) (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ W)
    (ψ : infiniteOnsiteDomain V) :
    ‖infiniteOnsiteOperator V ψ‖ ≤
      ‖infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ‖ +
        (2 * (D : ℝ) * W + |ε| * ‖P‖ + |shift|) *
          ‖(ψ.1 : TileHilbert Tile)‖ := by
  have hL :=
    infiniteLocalMatchingLaplacian_norm_le D σ w W hW hw0 hw
  have hbase :=
    infiniteLocalGraphNorm_onsite_le D V σ w P ε shift ψ
  have hcoeff :
      ‖infiniteLocalMatchingLaplacian D σ w‖ +
        |ε| * ‖P‖ + |shift| ≤
      2 * (D : ℝ) * W + |ε| * ‖P‖ + |shift| := by
    linarith
  have hscaled :=
    mul_le_mul_of_nonneg_right hcoeff
      (norm_nonneg (ψ.1 : TileHilbert Tile))
  exact hbase.trans (add_le_add_right hscaled _)

end SpectralGeometry
