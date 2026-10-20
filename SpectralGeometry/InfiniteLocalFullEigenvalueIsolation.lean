module

public import SpectralGeometry.InfiniteLocalResolventSpectralIsolation

public section

/-!
# Isolation of genuine real eigenvalues of the full local operator

The nonzero real spectrum of the compact self-adjoint resolvent
Rₐ = (H - aI)⁻¹ was proved isolated in the preceding module.
Here the eigenpair correspondence converts that isolation to *actual*
real eigenvalues of the unbounded local operator H on D(V). The key
additional point is that the chosen shift a is not a full eigenvalue.

This theorem concerns the full operator's real **point spectrum**
(natural-domain eigenpairs). It does not claim to classify the whole
unbounded LinearPMap spectrum via spectral mapping.
-/

namespace SpectralGeometry

open Filter Topology Metric

variable {Tile : Type*} [DecidableEq Tile]

private abbrev FullIsolationEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- A genuine eigenvalue of the full matching-family operator is a
real number admitting a nonzero eigenvector in the natural onsite domain. -/
def infiniteLocalMatchingHasFullEigenvalue
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullIsolationEnd Tile)
    (ε shift eigenvalue : ℝ) : Prop :=
  ∃ ψ : infiniteOnsiteDomain V,
    (ψ.1 : TileHilbert Tile) ≠ 0 ∧
      infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
        eigenvalue • (ψ.1 : TileHilbert Tile)

/-- No eigenvalue of the full matching operator can coincide with a
real shift a at which the constructed two-sided resolvent exists. -/
private theorem full_local_eigenvalue_ne_resolvent_shift
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullIsolationEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (heigenvalue : infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue) :
    eigenvalue ≠ a := by
  intro heq
  rcases heigenvalue with ⟨ψ, hψne, hψ⟩
  rw [heq] at hψ
  exact hψne (infiniteLocalMatching_no_eigenvector_at_shift
    D V σ w P ε shift a hgap hsmall ψ hψ)

/-- Every genuine real eigenvalue of the unbounded full matching-family
operator on the natural onsite domain is isolated from all other
genuine real eigenvalues, under compactness and symmetry of the resolvent.

Unlike the earlier exclusion-zone theorem, this isolates an arbitrary
eigenvalue, not merely the fixed resolvent shift. -/
theorem infiniteLocalMatching_full_eigenvalue_isolated
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullIsolationEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (eigenvalue : ℝ) (heigenvalue : infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue) :
    ∃ r : ℝ, 0 < r ∧
      ∀ ν : ℝ,
        infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift ν →
        dist ν eigenvalue < r → ν = eigenvalue := by
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  have hB : ∀ ψ φ : TileHilbert Tile,
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ) := by
    intro ψ φ
    exact infiniteLocalBoundedCorrection_symmetric
      D σ w P ε shift hσ hP ψ φ
  have heigenvaluene : eigenvalue ≠ a :=
    full_local_eigenvalue_ne_resolvent_shift
      D V σ w P ε shift a hgap hsmall eigenvalue heigenvalue
  have hμne : (eigenvalue - a)⁻¹ ≠ 0 :=
    inv_ne_zero (sub_ne_zero.mpr heigenvaluene)
  have hμspec : (eigenvalue - a)⁻¹ ∈ spectrum ℝ R :=
    (infiniteLocalMatching_full_eigenpair_iff_resolvent_spectrum
      D V σ w P ε shift a hgap hproper hsmall eigenvalue heigenvaluene).mpr heigenvalue
  obtain ⟨r, hr, hiso⟩ :=
    infiniteBoundedOnsiteResolvent_nonzero_spectrum_isolated
      V a hgap hproper B hB hsmall (eigenvalue - a)⁻¹ hμne hμspec
  have hcont :
      ContinuousAt (fun x : ℝ => (x - a)⁻¹) eigenvalue := by
    exact (continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.mpr heigenvaluene)
  have hneigh :
      {ν : ℝ | dist ((ν - a)⁻¹) ((eigenvalue - a)⁻¹) < r} ∈ 𝓝 eigenvalue := by
    have hball :
        (fun x : ℝ => (x - a)⁻¹) ⁻¹'
          Metric.ball ((eigenvalue - a)⁻¹) r ∈ 𝓝 eigenvalue :=
      hcont.tendsto (Metric.ball_mem_nhds ((eigenvalue - a)⁻¹) hr)
    change ((fun x : ℝ => (x - a)⁻¹) ⁻¹'
      Metric.ball ((eigenvalue - a)⁻¹) r) ∈ 𝓝 eigenvalue
    exact hball
  obtain ⟨δ, hδ, hsubset⟩ := Metric.mem_nhds_iff.mp hneigh
  refine ⟨δ, hδ, ?_⟩
  intro ν hν hclose
  have hνne : ν ≠ a :=
    full_local_eigenvalue_ne_resolvent_shift
      D V σ w P ε shift a hgap hsmall ν hν
  have hνspec : (ν - a)⁻¹ ∈ spectrum ℝ R :=
    (infiniteLocalMatching_full_eigenpair_iff_resolvent_spectrum
      D V σ w P ε shift a hgap hproper hsmall ν hνne).mpr hν
  have hcloseres : dist ((ν - a)⁻¹) ((eigenvalue - a)⁻¹) < r :=
    hsubset (Metric.mem_ball.mpr (by simpa [dist_comm] using hclose))
  have hinv : (ν - a)⁻¹ = (eigenvalue - a)⁻¹ :=
    hiso _ hνspec hcloseres
  have hsub : ν - a = eigenvalue - a := inv_injective hinv
  linarith


/-- On every bounded real interval the full local operator has only
finitely many **distinct** genuine eigenvalues. This strengthens mere
pointwise isolation: real eigenvalues cannot accumulate at a finite
real number. No assertion about multiplicities or the entire unbounded
operator spectrum is made. -/
theorem infiniteLocalMatching_full_eigenvalues_bounded_finite
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullIsolationEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (M : ℝ) (hM : 0 ≤ M) :
    {eigenvalue : ℝ | ‖eigenvalue‖ ≤ M ∧
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue}.Finite := by
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  let d : ℝ := M + ‖a‖ + 1
  have hd : 0 < d := by
    dsimp [d]
    positivity
  let δ : ℝ := d⁻¹
  have hδ : 0 < δ := inv_pos.mpr hd
  have hB : ∀ ψ φ : TileHilbert Tile,
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ) := by
    intro ψ φ
    exact infiniteLocalBoundedCorrection_symmetric
      D σ w P ε shift hσ hP ψ φ
  let S : Set ℝ :=
    {eigenvalue : ℝ | ‖eigenvalue‖ ≤ M ∧
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift eigenvalue}
  let F : Set ℝ := {μ : ℝ | δ ≤ ‖μ‖ ∧ μ ∈ spectrum ℝ R}
  have hfinite : F.Finite :=
    infiniteBoundedOnsiteResolvent_finite_spectrum_away_zero
      V a hgap hproper B hB hsmall δ hδ
  have hmaps : Set.MapsTo (fun eigenvalue : ℝ => (eigenvalue - a)⁻¹) S F := by
    intro eigenvalue heigenvalue
    rcases heigenvalue with ⟨hsize, heigenvalueeig⟩
    have hne : eigenvalue ≠ a :=
      full_local_eigenvalue_ne_resolvent_shift
        D V σ w P ε shift a hgap hsmall eigenvalue heigenvalueeig
    have hnpos : 0 < ‖eigenvalue - a‖ :=
      (norm_pos_iff).mpr (sub_ne_zero.mpr hne)
    have hle : ‖eigenvalue - a‖ ≤ d := by
      have htri := norm_sub_le eigenvalue a
      simp only [Real.norm_eq_abs] at htri hsize
      dsimp [d]
      linarith
    have hrecip : δ ≤ ‖(eigenvalue - a)⁻¹‖ := by
      change d⁻¹ ≤ ‖(eigenvalue - a)⁻¹‖
      rw [norm_inv]
      exact inv_anti₀ hnpos hle
    have hspec : (eigenvalue - a)⁻¹ ∈ spectrum ℝ R :=
      (infiniteLocalMatching_full_eigenpair_iff_resolvent_spectrum
        D V σ w P ε shift a hgap hproper hsmall eigenvalue hne).mpr heigenvalueeig
    exact ⟨hrecip, hspec⟩
  have hinj : Set.InjOn (fun eigenvalue : ℝ => (eigenvalue - a)⁻¹) S := by
    intro eigenvalue _ ν _ heq
    have hh : eigenvalue - a = ν - a := inv_injective heq
    linarith
  exact Set.Finite.of_injOn hmaps hinj hfinite

end SpectralGeometry
