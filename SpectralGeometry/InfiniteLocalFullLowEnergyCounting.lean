import SpectralGeometry.InfiniteLocalFullVariationalComparison

/-!
# Low-energy coordinate control of interacting eigenspaces

This module advances the min-max/counting step for the genuine
unbounded full matching operator H = M_V + B on its natural domain.

The sharp quadratic-form estimate from §4.39 implies that a vector
whose coordinates vanish at all sites with V(t) < R has Rayleigh
quotient at least R - ‖B‖. Thus a nonzero eigenvector with eigenvalue
λ < R - ‖B‖ must have a nonzero coordinate at a low-onsite-energy site.

The result is stronger at the eigenspace level: when λ differs from the
regular resolvent shift, restriction to the finite set of onsite tiles
V(t) ≤ R is injective on the *whole geometric eigenspace*. Hence its
geometric multiplicity is bounded by the number of such tiles. This is
a dimension/codimension input to spectral counting; it does not yet
prove an n-th eigenvalue min-max inequality or summed spectral counting
over all eigenvalues below a threshold.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

private abbrev CountEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- The quadratic form of onsite multiplication is bounded below by
R for any state vanishing on the low-on-site-energy region V(t) < R.
The potential need not be globally bounded below by R. -/
theorem infiniteOnsiteOperator_energy_ge_of_vanish_lowEnergy
    (V : Tile → ℝ) (R : ℝ)
    (ψ : infiniteOnsiteDomain V)
    (hvanish : ∀ t : Tile, V t < R → ψ.1 t = 0) :
    R * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
      inner ℝ (ψ.1 : TileHilbert Tile) (infiniteOnsiteOperator V ψ) := by
  have hh :
      0 ≤ inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteOnsiteOperator V ψ - R • (ψ.1 : TileHilbert Tile)) := by
    rw [lp.inner_eq_tsum]
    apply tsum_nonneg
    intro t
    have hterm :
        0 ≤ (V t - R) * ((ψ.1 t) ^ 2) := by
      by_cases hlow : V t < R
      · simp [hvanish t hlow]
      · exact mul_nonneg (sub_nonneg.mpr (le_of_not_gt hlow)) (sq_nonneg _)
    have hpoint :
        0 ≤ (ψ.1 t) * (V t * ψ.1 t - R * ψ.1 t) := by
      nlinarith [hterm]
    have hcoord :
        (infiniteOnsiteOperator V ψ -
          R • (ψ.1 : TileHilbert Tile)) t =
        V t * ψ.1 t - R * ψ.1 t := by
      change V t * ψ.1 t - R * ψ.1 t =
        V t * ψ.1 t - R * ψ.1 t
      rfl
    simpa [RCLike.inner_apply, hcoord, starRingEnd_apply, mul_comm] using hpoint
  rw [inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at hh
  linarith

/-- High-onsite-energy support gives a *uniform* Rayleigh lower bound
R - ‖B‖ for the full unbounded interacting matching operator. -/
theorem infiniteLocalShiftedPerturbed_energy_ge_of_vanish_lowEnergy
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : CountEnd Tile)
    (ε shift R : ℝ)
    (ψ : infiniteOnsiteDomain V)
    (hvanish : ∀ t : Tile, V t < R → ψ.1 t = 0) :
    (R - ‖infiniteLocalBoundedCorrection D σ w P ε shift‖) *
        ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 ≤
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ) := by
  have hon := infiniteOnsiteOperator_energy_ge_of_vanish_lowEnergy V R ψ hvanish
  have hfull :=
    (infiniteLocalShiftedPerturbed_energy_sandwich
      D V σ w P ε shift ψ).1
  nlinarith

/-- No nonzero full eigenvector below R - ‖B‖ can vanish at all
tiles whose onsite potential is below R. This is the elementary
spectral-counting obstruction. -/
theorem infiniteLocalShiftedPerturbed_eigenvector_exists_lowEnergy_coordinate
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : CountEnd Tile)
    (ε shift R eigenvalue : ℝ)
    (heigenvalue :
      eigenvalue < R - ‖infiniteLocalBoundedCorrection D σ w P ε shift‖)
    (ψ : infiniteOnsiteDomain V)
    (heigen :
      infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
        eigenvalue • (ψ.1 : TileHilbert Tile))
    (hψ : (ψ.1 : TileHilbert Tile) ≠ 0) :
    ∃ t : Tile, V t < R ∧ ψ.1 t ≠ 0 := by
  classical
  by_contra hnone
  have hvanish : ∀ t : Tile, V t < R → ψ.1 t = 0 := by
    intro t ht
    by_contra hne
    exact hnone ⟨t, ht, hne⟩
  have hform :=
    infiniteLocalShiftedPerturbed_energy_ge_of_vanish_lowEnergy
      D V σ w P ε shift R ψ hvanish
  have hnorm : 0 < ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hψ)
  have heq :
      inner ℝ (ψ.1 : TileHilbert Tile)
        (infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ) =
      eigenvalue * ‖(ψ.1 : TileHilbert Tile)‖ ^ 2 := by
    rw [heigen, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [heq] at hform
  nlinarith

/-- A finite onsite low-energy set contains an observable coordinate
for every nonzero full eigenvector with sufficiently low eigenvalue. -/
theorem infiniteLocalShiftedPerturbed_lowEigenvector_observed_on_finite_sector
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : CountEnd Tile)
    (ε shift R eigenvalue : ℝ)
    (heigenvalue :
      eigenvalue < R - ‖infiniteLocalBoundedCorrection D σ w P ε shift‖)
    (ψ : infiniteOnsiteDomain V)
    (heigen :
      infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
        eigenvalue • (ψ.1 : TileHilbert Tile))
    (hψ : (ψ.1 : TileHilbert Tile) ≠ 0)
    (hfinite : (infiniteOnsiteLowEnergyTiles V R).Finite) :
    ∃ t : (hfinite.toFinset : Finset Tile),
      (ψ.1 : TileHilbert Tile) t.1 ≠ 0 := by
  obtain ⟨t, ht, hψt⟩ :=
    infiniteLocalShiftedPerturbed_eigenvector_exists_lowEnergy_coordinate
      D V σ w P ε shift R eigenvalue heigenvalue ψ heigen hψ
  exact ⟨⟨t, (Set.Finite.mem_toFinset hfinite).2 (le_of_lt ht)⟩, hψt⟩

/-- The entire real eigenspace at a spectral level below R - ‖B‖
injects into the coordinates on the finite onsite sector V(t) ≤ R.
Thus its geometric multiplicity does not exceed the number of
low-onsite-energy tiles.

This dimension bound counts one eigenspace at a time; summing over
several spectral levels to obtain an indexed min-max inequality is
still a separate proof obligation. -/
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
      (hproper R).toFinset.card := by
  classical
  let E : Submodule ℝ (TileHilbert Tile) :=
    infiniteLocalMatchingFullEigenspace
      D V σ w P ε shift a hgap hsmall eigenvalue hne
  letI : FiniteDimensional ℝ E :=
    infiniteLocalMatchingFullEigenspace_finiteDimensional
      D V σ w P ε shift a hgap hproper hsmall eigenvalue hne
  let F : Finset Tile := (hproper R).toFinset
  let coord : E →ₗ[ℝ] (F → ℝ) := {
    toFun := fun x t => (x.1 : TileHilbert Tile) (t : Tile)
    map_add' := by
      intro x y
      funext t
      rfl
    map_smul' := by
      intro c x
      funext t
      rfl
  }
  have hinj : Function.Injective coord := by
    intro x y hxy
    have hz : coord (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hz0 : (x - y : E) = 0 := by
      by_contra hn
      let z : E := x - y
      obtain ⟨ψ, hψz, heigen⟩ :=
        (infiniteLocalMatchingFullEigenspace_mem_iff
          D V σ w P ε shift a hgap hsmall eigenvalue hne
          (z.1 : TileHilbert Tile)).mp z.property
      have hψne : (ψ.1 : TileHilbert Tile) ≠ 0 := by
        intro hψzero
        apply hn
        apply Subtype.ext
        change (z.1 : TileHilbert Tile) = 0
        rw [← hψz]
        exact hψzero
      have heigen' :
          infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
            eigenvalue • (ψ.1 : TileHilbert Tile) := by
        rw [hψz]
        exact heigen
      obtain ⟨t, htlow, htne⟩ :=
        infiniteLocalShiftedPerturbed_eigenvector_exists_lowEnergy_coordinate
          D V σ w P ε shift R eigenvalue heigenvalue
          ψ heigen' hψne
      have htF : t ∈ F :=
        (Set.Finite.mem_toFinset (hproper R)).2 (le_of_lt htlow)
      have htzero : coord z ⟨t, htF⟩ = 0 := by
        have hfun : coord z = 0 := hz
        exact congrArg (fun f : F → ℝ => f ⟨t, htF⟩) hfun
      have hψtzero : (ψ.1 : TileHilbert Tile) t = 0 := by
        have hzt : (z.1 : TileHilbert Tile) t = 0 := htzero
        rw [← hψz] at hzt
        exact hzt
      exact htne hψtzero
    exact sub_eq_zero.mp hz0
  have hle : Module.finrank ℝ E ≤ F.card := by
    calc
      Module.finrank ℝ E ≤ Module.finrank ℝ (F → ℝ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
      _ = F.card := by simp [F]
  simpa [infiniteLocalMatchingFullMultiplicity, hne, E, F] using hle

end SpectralGeometry
