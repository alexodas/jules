import SpectralGeometry.InfiniteLocalAdjointCharacterization

/-!
# A real resolvent equation for unbounded onsite multiplication

Let V : Tile → ℝ be an arbitrary (possibly unbounded) real potential.
For a real parameter a at least one unit below every onsite energy,

    1 ≤ V t - a   for every tile t,

the shifted multiplication equation (M_V - a I) ψ = f has a unique
solution ψ in the *natural onsite domain*, for every f in real ℓ².

The solution is coordinatewise ψ(t) = f(t) / (V(t)-a). The positive
uniform gap makes this sequence square-summable; the equation itself
shows that Vψ is also square-summable.

We prove both surjectivity and injectivity of the shifted operator,
not merely absence of eigenvectors. This is a step towards building
a bounded resolvent and proving compactness under a further
finite-sublevel/growth condition.

Neither compactness nor the resolvent of the interacting operator
is established in this module.
-/

namespace SpectralGeometry

variable {Tile : Type*}

/-- Dividing every ℓ² coordinate by a real onsite gap at least one
preserves square summability. -/
theorem infiniteOnsiteUnitGap_inverse_memℓp
    (V : Tile → ℝ) (a : ℝ)
    (hgap : ∀ t : Tile, 1 ≤ V t - a)
    (f : TileHilbert Tile) :
    Memℓp (fun t : Tile => (V t - a)⁻¹ * f t) 2 := by
  apply f.property.mono'
  intro t
  have hpos : 0 < V t - a := lt_of_lt_of_le (by norm_num) (hgap t)
  have hinv : ‖(V t - a)⁻¹‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    have h :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (hgap t)
    simpa [one_div] using h
  calc
    ‖(V t - a)⁻¹ * f t‖ = ‖(V t - a)⁻¹‖ * ‖f t‖ :=
      norm_mul _ _
    _ ≤ 1 * ‖f t‖ :=
      mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _ = ‖f t‖ := one_mul _

/-- Every square-summable right-hand side admits an onsite-domain
solution to (M_V - a I) ψ = f when the pointwise gap is at least one. -/
theorem infiniteOnsiteUnitGap_shift_surjective
    (V : Tile → ℝ) (a : ℝ)
    (hgap : ∀ t : Tile, 1 ≤ V t - a) :
    Function.Surjective
      (fun ψ : infiniteOnsiteDomain V =>
        infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile)) := by
  intro f
  let x : TileHilbert Tile :=
    ⟨(fun t : Tile => (V t - a)⁻¹ * f t : PreLp (fun _ : Tile => ℝ)),
      infiniteOnsiteUnitGap_inverse_memℓp V a hgap f⟩
  have hx (t : Tile) : (V t - a) * x t = f t := by
    have hpos : 0 < V t - a :=
      lt_of_lt_of_le (by norm_num) (hgap t)
    change (V t - a) * ((V t - a)⁻¹ * f t) = f t
    field_simp [ne_of_gt hpos]
  have hcoordinate (t : Tile) :
      V t * x t = f t + a * x t := by
    calc
      V t * x t = (V t - a) * x t + a * x t := by ring
      _ = f t + a * x t := by rw [hx t]
  have hmem : Memℓp (fun t : Tile => V t * x t) 2 := by
    have hh : Memℓp (fun t : Tile => f t + a * x t) 2 := by
      have hh0 := f.property.add (x.property.const_mul a)
      have heq :
          ((f : Tile → ℝ) + (fun t : Tile => a * x t)) =
            (fun t : Tile => f t + a * x t) := by
        funext t
        rfl
      rw [heq] at hh0
      exact hh0
    have heq :
        (fun t : Tile => V t * x t) =
          (fun t : Tile => f t + a * x t) := by
      funext t
      exact hcoordinate t
    rw [heq]
    exact hh
  let ψ : infiniteOnsiteDomain V := ⟨x, hmem⟩
  refine ⟨ψ, ?_⟩
  apply lp.ext
  funext t
  change V t * x t - a * x t = f t
  rw [hcoordinate t]
  ring

/-- The same shifted multiplication has no two distinct solutions
to the same ℓ² right-hand side. -/
theorem infiniteOnsiteUnitGap_shift_injective
    (V : Tile → ℝ) (a : ℝ)
    (hgap : ∀ t : Tile, 1 ≤ V t - a) :
    Function.Injective
      (fun ψ : infiniteOnsiteDomain V =>
        infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile)) := by
  intro ψ φ heq
  apply Subtype.ext
  apply lp.ext
  funext t
  have ht := congrArg (fun x : TileHilbert Tile => x t) heq
  have hcoord :
      V t * ψ.1 t - a * ψ.1 t =
        V t * φ.1 t - a * φ.1 t := by
    have hleft :
        (infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile)) t =
          V t * ψ.1 t - a * ψ.1 t := by
      rfl
    have hright :
        (infiniteOnsiteOperator V φ - a • (φ.1 : TileHilbert Tile)) t =
          V t * φ.1 t - a * φ.1 t := by
      rfl
    exact hleft.symm.trans (ht.trans hright)
  have hmul : (V t - a) * (ψ.1 t - φ.1 t) = 0 := by
    nlinarith [hcoord]
  have hne : V t - a ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (hgap t))
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact (hne hzero).elim
  · exact sub_eq_zero.mp hzero

/-- The shifted onsite operator is bijective, so each ℓ² input has
one and only one preimage in its natural unbounded-operator domain.
A bounded-inverse/compactness assertion is intentionally separate. -/
theorem infiniteOnsiteUnitGap_shift_bijective
    (V : Tile → ℝ) (a : ℝ)
    (hgap : ∀ t : Tile, 1 ≤ V t - a) :
    Function.Bijective
      (fun ψ : infiniteOnsiteDomain V =>
        infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile)) :=
  ⟨infiniteOnsiteUnitGap_shift_injective V a hgap,
   infiniteOnsiteUnitGap_shift_surjective V a hgap⟩

end SpectralGeometry
