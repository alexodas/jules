import SpectralGeometry.InfiniteLocalResolventSpectralIsolation

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
    (ε shift λ : ℝ) : Prop :=
  ∃ ψ : infiniteOnsiteDomain V,
    (ψ.1 : TileHilbert Tile) ≠ 0 ∧
      infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
        λ • (ψ.1 : TileHilbert Tile)

/-- No eigenvalue of the full matching operator can coincide with a
real shift a at which the constructed two-sided resolvent exists. -/
private theorem full_local_eigenvalue_ne_resolvent_shift
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullIsolationEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (λ : ℝ) (hλ : infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift λ) :
    λ ≠ a := by
  intro heq
  rcases hλ with ⟨ψ, hψne, hψ⟩
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
    (λ : ℝ) (hλ : infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift λ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ ν : ℝ,
        infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift ν →
        dist ν λ < r → ν = λ := by
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  have hB : ∀ ψ φ : TileHilbert Tile,
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ) := by
    intro ψ φ
    exact infiniteLocalBoundedCorrection_symmetric
      D σ w P ε shift hσ hP ψ φ
  have hλne : λ ≠ a :=
    full_local_eigenvalue_ne_resolvent_shift
      D V σ w P ε shift a hgap hsmall λ hλ
  have hμne : (λ - a)⁻¹ ≠ 0 :=
    inv_ne_zero (sub_ne_zero.mpr hλne)
  have hμspec : (λ - a)⁻¹ ∈ spectrum ℝ R :=
    (infiniteLocalMatching_full_eigenpair_iff_resolvent_spectrum
      D V σ w P ε shift a hgap hproper hsmall λ hλne).mpr hλ
  obtain ⟨r, hr, hiso⟩ :=
    infiniteBoundedOnsiteResolvent_nonzero_spectrum_isolated
      V a hgap hproper B hB hsmall (λ - a)⁻¹ hμne hμspec
  have hcont :
      ContinuousAt (fun x : ℝ => (x - a)⁻¹) λ := by
    exact (continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.mpr hλne)
  have hneigh :
      {ν : ℝ | dist ((ν - a)⁻¹) ((λ - a)⁻¹) < r} ∈ 𝓝 λ := by
    have hball :
        (fun x : ℝ => (x - a)⁻¹) ⁻¹'
          Metric.ball ((λ - a)⁻¹) r ∈ 𝓝 λ :=
      hcont.tendsto (Metric.ball_mem_nhds hr)
    change ((fun x : ℝ => (x - a)⁻¹) ⁻¹'
      Metric.ball ((λ - a)⁻¹) r) ∈ 𝓝 λ
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
  have hcloseres : dist ((ν - a)⁻¹) ((λ - a)⁻¹) < r :=
    hsubset (Metric.mem_ball.mpr (by simpa [dist_comm] using hclose))
  have hinv : (ν - a)⁻¹ = (λ - a)⁻¹ :=
    hiso _ hνspec hcloseres
  have hsub : ν - a = λ - a := inv_injective hinv
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
    {λ : ℝ | ‖λ‖ ≤ M ∧
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift λ}.Finite := by
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
    {λ : ℝ | ‖λ‖ ≤ M ∧
      infiniteLocalMatchingHasFullEigenvalue D V σ w P ε shift λ}
  let F : Set ℝ := {μ : ℝ | δ ≤ ‖μ‖ ∧ μ ∈ spectrum ℝ R}
  have hfinite : F.Finite :=
    infiniteBoundedOnsiteResolvent_finite_spectrum_away_zero
      V a hgap hproper B hB hsmall δ hδ
  have hmaps : Set.MapsTo (fun λ : ℝ => (λ - a)⁻¹) S F := by
    intro λ hλ
    rcases hλ with ⟨hsize, hλeig⟩
    have hne : λ ≠ a :=
      full_local_eigenvalue_ne_resolvent_shift
        D V σ w P ε shift a hgap hsmall λ hλeig
    have hnpos : 0 < ‖λ - a‖ :=
      (norm_pos_iff).mpr (sub_ne_zero.mpr hne)
    have hle : ‖λ - a‖ ≤ d := by
      have htri := norm_sub_le λ a
      dsimp [d]
      linarith
    have hrecip : δ ≤ ‖(λ - a)⁻¹‖ := by
      change d⁻¹ ≤ ‖(λ - a)⁻¹‖
      rw [norm_inv]
      exact inv_anti₀ hnpos hle
    have hspec : (λ - a)⁻¹ ∈ spectrum ℝ R :=
      (infiniteLocalMatching_full_eigenpair_iff_resolvent_spectrum
        D V σ w P ε shift a hgap hproper hsmall λ hne).mpr hλeig
    exact ⟨hrecip, hspec⟩
  have hinj : Set.InjOn (fun λ : ℝ => (λ - a)⁻¹) S := by
    intro λ _ ν _ heq
    have hh : λ - a = ν - a := inv_injective heq
    linarith
  exact Set.Finite.of_injOn hmaps hinj hfinite

end SpectralGeometry
