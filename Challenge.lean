module

public import Mathlib

public section

/-!
# Low-energy geometric multiplicity bound for an infinite interacting operator

For the genuine full matching-family operator H = M_V + B on real ℓ²(Tile),
a low-lying eigenspace has dimension at most the number of tiles with onsite
potential ≤ R. The potential may be unbounded and the tile set infinite.
B includes bounded infinite matching interactions and a bounded perturbation.

This statement is *per eigenspace*, not a bound on the sum of multiplicities
over distinct eigenvalues. It assumes onsite finite sublevel sets, a regular
resolvent shift with a unit onsite gap and a Neumann-series smallness bound,
and eigenvalue < R - ‖B‖ away from that shift. It neither establishes
index-wise min--max comparison nor inverse-square spectral summability.

This independent Challenge deliberately leaves the main theorem as a sorry.
A proof-irrelevant finite-dimensionality witness inside the multiplicity
definition is also a Challenge-only placeholder; the proved Solution
supplies the genuine compact-resolvent theorem. Neither placeholder is
admitted as part of the substantive source library.
-/

namespace SpectralGeometry

@[expose] abbrev TileHilbert (Tile : Type*) : Type _ :=
  lp (fun _ : Tile => ℝ) 2

variable {Tile : Type*}

@[expose] def infiniteOnsiteLowEnergyTiles (V : Tile → ℝ) (R : ℝ) :
    Set Tile := {t | V t ≤ R}

@[expose] noncomputable def infiniteOnsiteDiagonalContraction
    (c : Tile → ℝ) (hc : ∀ t : Tile, ‖c t‖ ≤ 1) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile := by
  let F : TileHilbert Tile →ₗ[ℝ] TileHilbert Tile :=
    { toFun := fun f =>
        ⟨(fun t : Tile => c t * f t : PreLp (fun _ : Tile => ℝ)),
          f.property.mono' (fun t => by
            calc
              ‖c t * f t‖ = ‖c t‖ * ‖f t‖ := norm_mul _ _
              _ ≤ 1 * ‖f t‖ :=
                mul_le_mul_of_nonneg_right (hc t) (norm_nonneg _)
              _ = ‖f t‖ := one_mul _)⟩
      map_add' := by
        intro f g
        apply lp.ext
        funext t
        change c t * (f t + g t) = c t * f t + c t * g t
        ring
      map_smul' := by
        intro r f
        apply lp.ext
        funext t
        change c t * (r * f t) = r * (c t * f t)
        ring }
  exact F.mkContinuous 1 (fun f => by
    calc
      ‖F f‖ ≤ ‖f‖ := lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun t => by
        change ‖c t * f t‖ ≤ ‖f t‖
        calc
          ‖c t * f t‖ = ‖c t‖ * ‖f t‖ := norm_mul _ _
          _ ≤ 1 * ‖f t‖ :=
            mul_le_mul_of_nonneg_right (hc t) (norm_nonneg _)
          _ = ‖f t‖ := one_mul _)
      _ = 1 * ‖f‖ := (one_mul _).symm)

theorem onsiteUnitGap_inverse_norm_le_one
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (t : Tile) : ‖(V t - a)⁻¹‖ ≤ 1 := by
  have hp : 0 < V t - a := lt_of_lt_of_le (by norm_num) (hgap t)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (hgap t)
  simpa [one_div] using h

@[expose] noncomputable def infiniteOnsiteResolventCLM
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  infiniteOnsiteDiagonalContraction
    (fun t => (V t - a)⁻¹) (onsiteUnitGap_inverse_norm_le_one V a hgap)

variable [DecidableEq Tile]

@[expose] noncomputable def infiniteTileReindex (σ : Tile ≃ Tile) :
    TileHilbert Tile →ₗᵢ[ℝ] TileHilbert Tile where
  toFun := fun ψ => by
    refine ⟨(fun t => ψ (σ t) : PreLp (fun _ : Tile => ℝ)), ?_⟩
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    have hsum : Summable (fun t : Tile => ‖ψ t‖ ^ (2 : ENNReal).toReal) :=
      (memℓp_gen_iff hp).mp ψ.property
    have hsum' :
        Summable (fun t : Tile => ‖ψ (σ t)‖ ^ (2 : ENNReal).toReal) :=
      (σ.summable_iff).mpr hsum
    exact (memℓp_gen_iff hp).mpr hsum'
  map_add' := by
    intro ψ φ
    apply lp.ext
    funext t
    rfl
  map_smul' := by
    intro c ψ
    apply lp.ext
    funext t
    rfl
  norm_map' := by
    intro ψ
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    let φ : TileHilbert Tile :=
      ⟨(fun t => ψ (σ t) : PreLp (fun _ : Tile => ℝ)),
        (memℓp_gen_iff hp).mpr
          ((σ.summable_iff).mpr ((memℓp_gen_iff hp).mp ψ.property))⟩
    change ‖φ‖ = ‖ψ‖
    have hsum :
        (∑' t, ‖φ t‖ ^ (2 : ENNReal).toReal) =
          (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal) := by
      change (∑' t, ‖ψ (σ t)‖ ^ (2 : ENNReal).toReal) =
        (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal)
      exact σ.tsum_eq (fun t : Tile => ‖ψ t‖ ^ (2 : ENNReal).toReal)
    calc
      ‖φ‖ =
          (∑' t, ‖φ t‖ ^ (2 : ENNReal).toReal) ^
            (1 / (2 : ENNReal).toReal) :=
        lp.norm_eq_tsum_rpow hp φ
      _ = (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal) ^
            (1 / (2 : ENNReal).toReal) := by rw [hsum]
      _ = ‖ψ‖ := (lp.norm_eq_tsum_rpow hp ψ).symm

@[expose] noncomputable def infiniteMatchingLaplacian (σ : Tile ≃ Tile) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ContinuousLinearMap.id ℝ (TileHilbert Tile) -
    (infiniteTileReindex σ).toContinuousLinearMap

@[expose] noncomputable def infiniteLocalMatchingLaplacian (D : ℕ)
    (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ∑ i : Fin D, w i • infiniteMatchingLaplacian (σ i)

@[expose] noncomputable def infiniteLocalBoundedCorrection
    (D : ℕ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  infiniteLocalMatchingLaplacian D σ w + ε • P +
    shift • ContinuousLinearMap.id ℝ (TileHilbert Tile)

abbrev OnsiteEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

@[expose] noncomputable def infiniteBoundedOnsiteCorrectionUnit
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    (OnsiteEnd Tile)ˣ :=
  Units.oneSub (-(B.comp (infiniteOnsiteResolventCLM V a hgap)))
    (by simpa only [norm_neg] using hsmall)

@[expose] noncomputable def infiniteBoundedOnsiteResolvent
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    OnsiteEnd Tile :=
  (infiniteOnsiteResolventCLM V a hgap).comp
    (↑((infiniteBoundedOnsiteCorrectionUnit V a hgap B hsmall)⁻¹) :
      OnsiteEnd Tile)

abbrev FullEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

@[expose] noncomputable def infiniteLocalMatchingFullEigenspace
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (_hne : eigenvalue ≠ a) :
    Submodule ℝ (TileHilbert Tile) :=
  Module.End.eigenspace
    (infiniteBoundedOnsiteResolvent V a hgap
      (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall).toLinearMap
    (eigenvalue - a)⁻¹

abbrev MultiplicityEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- Challenge-only signature: finite eigenspace dimension supplied by the
proven compact-resolvent result in Solution. The placeholder is not a proof. -/
theorem infiniteLocalMatchingFullEigenspace_finiteDimensional
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (hne : eigenvalue ≠ a) :
    FiniteDimensional ℝ
      (infiniteLocalMatchingFullEigenspace
        D V σ w P ε shift a hgap hsmall eigenvalue hne) := by
  sorry

@[expose] noncomputable def infiniteLocalMatchingFullMultiplicity
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : MultiplicityEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) : ℕ := by
  classical
  by_cases hne : eigenvalue ≠ a
  · letI := infiniteLocalMatchingFullEigenspace_finiteDimensional
      D V σ w P ε shift a hgap hproper hsmall eigenvalue hne
    exact Module.finrank ℝ
      (infiniteLocalMatchingFullEigenspace
        D V σ w P ε shift a hgap hsmall eigenvalue hne)
  · exact 0

abbrev CountEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

set_option maxHeartbeats 8000000

/-- Multiplicity of one low-energy full-operator real eigenspace is bounded
by the number of onsite tiles below a fixed finite-energy threshold.
The statement neither counts distinct eigenvalues nor sums over levels. -/
theorem infiniteLocalMatching_full_eigenspace_finrank_le_lowEnergyTiles
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : CountEnd Tile)
    (ε shift a R eigenvalue : ℝ)
    (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ S : ℝ, (infiniteOnsiteLowEnergyTiles V S).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hne : eigenvalue ≠ a)
    (heigenvalue :
      eigenvalue < R - ‖infiniteLocalBoundedCorrection D σ w P ε shift‖) :
    infiniteLocalMatchingFullMultiplicity
        D V σ w P ε shift a hgap hproper hsmall eigenvalue ≤
      (hproper R).toFinset.card  := by
  sorry -- Independent statement only; Solution imports the original complete Lean proof

end SpectralGeometry
