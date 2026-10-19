import SpectralGeometry.InfiniteLocalResolventNormGap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max

/-!
# Isolation of nonzero spectral points of compact local resolvents

A compact self-adjoint operator has only finitely many distinct real
eigenvalues outside each neighborhood of zero. Combining this fact
with the already established Fredholm alternative gives isolation
of every nonzero point in the spectrum of the bounded resolvent.

The compactness/orthogonality proof below is adapted for real Hilbert
spaces from Adam Benenson's Apache-2.0-licensed
`CompactSelfAdjoint/SpectralFiniteness.lean` (2026). Here the compactness
contradiction is proved directly from the subsequence criterion, without
introducing the separate weak-topology infrastructure of that work.

This concerns the bounded resolvent's spectrum, not yet a standalone
spectral mapping theorem for the unbounded full local operator.
-/

namespace SpectralGeometry

open Filter Topology Metric

variable {Tile : Type*} [DecidableEq Tile]

private abbrev IsolationEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

/-- A compact operator cannot have infinitely many orthonormal eigenvectors
with eigenvalues uniformly bounded away from zero. The eigenvalues here
need not be distinct, and no self-adjointness is used in this lemma. -/
private theorem compact_no_orthonormal_eigenvectors_with_large_eigenvalues
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) (hcompact : IsCompactOperator T)
    (e : ℕ → E) (he : Orthonormal ℝ e)
    (μ : ℕ → ℝ) (heigen : ∀ n, T (e n) = μ n • e n)
    (δ : ℝ) (hδ : 0 < δ) (hbound : ∀ n, δ ≤ ‖μ n‖) : False := by
  have hK :
      IsCompact (closure ((T : E →ₛₗ[RingHom.id ℝ] E) ''
        Metric.closedBall (0 : E) 1)) := by
    simpa using
      (IsCompactOperator.isCompact_closure_image_closedBall
        (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
        (M₁ := E) (M₂ := E)
        (f := (T : E →ₛₗ[RingHom.id ℝ] E)) hcompact 1)
  let y : ℕ → E := fun n => T (e n)
  have hyK : ∀ n, y n ∈
      closure ((T : E →ₛₗ[RingHom.id ℝ] E) '' Metric.closedBall (0 : E) 1) := by
    intro n
    apply subset_closure
    refine ⟨e n, ?_, rfl⟩
    simp [Metric.mem_closedBall, dist_eq_norm, he.norm_eq_one n]
  obtain ⟨_lim, _hlimK, φ, hφmono, hlim⟩ := hK.tendsto_subseq hyK
  have hsep : Pairwise fun m n => δ ≤ dist (y m) (y n) := by
    intro m n hmn
    have hinner : inner ℝ (e m) (e n) = 0 :=
      he.inner_eq_zero hmn
    have hz : inner ℝ (μ m • e m) (μ n • e n) = 0 := by
      simp [real_inner_smul_left, real_inner_smul_right, hinner]
    have hp := norm_sub_sq_eq_norm_sq_add_norm_sq_real hz
    have hm : ‖y m‖ = ‖μ m‖ := by
      rw [show y m = μ m • e m from heigen m]
      simp [he.norm_eq_one m]
    have hn : ‖y n‖ = ‖μ n‖ := by
      rw [show y n = μ n • e n from heigen n]
      simp [he.norm_eq_one n]
    have hp' :
        ‖y m - y n‖ * ‖y m - y n‖ =
          ‖y m‖ * ‖y m‖ + ‖y n‖ * ‖y n‖ := by
      simpa [y, heigen m, heigen n] using hp
    change δ ≤ ‖y m - y n‖
    have hmn' : δ ≤ ‖y m‖ := hm.symm ▸ hbound m
    nlinarith [norm_nonneg (y m - y n), norm_nonneg (y n)]
  have hcauchy : CauchySeq (y ∘ φ) := hlim.cauchySeq
  obtain ⟨N, hN⟩ :=
    (Metric.cauchySeq_iff'.1 hcauchy) (δ / 2) (half_pos hδ)
  have hlt : dist ((y ∘ φ) (N + 1)) ((y ∘ φ) N) < δ / 2 :=
    hN (N + 1) (Nat.le_succ N)
  have hne : φ (N + 1) ≠ φ N :=
    ne_of_gt (hφmono (Nat.lt_succ_self N))
  have hge : δ ≤ dist ((y ∘ φ) (N + 1)) ((y ∘ φ) N) := by
    simpa [Function.comp_apply] using hsep hne
  linarith

/-- A compact self-adjoint real operator has finitely many distinct
eigenvalues whose absolute value is at least any fixed positive δ. -/
private theorem compact_selfAdjoint_finite_large_eigenvalues
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) (hself : IsSelfAdjoint T)
    (hcompact : IsCompactOperator T)
    (δ : ℝ) (hδ : 0 < δ) :
    {μ : ℝ | δ ≤ ‖μ‖ ∧ Module.End.HasEigenvalue T.toLinearMap μ}.Finite := by
  classical
  by_contra hfin
  let s : Set ℝ :=
    {μ : ℝ | δ ≤ ‖μ‖ ∧ Module.End.HasEigenvalue T.toLinearMap μ}
  have hsInf : s.Infinite := by
    by_contra hs
    exact hfin ((Set.not_infinite (s := s)).1 hs)
  let emb : ℕ ↪ s.Elem := Set.Infinite.natEmbedding s hsInf
  let μ : ℕ → ℝ := fun n => (emb n : s.Elem).1
  have hμinj : Function.Injective μ := by
    intro m n hmn
    apply emb.injective
    ext
    exact hmn
  have hμmem : ∀ n, μ n ∈ s := fun n => (emb n : s.Elem).property
  have hμge : ∀ n, δ ≤ ‖μ n‖ := fun n => (hμmem n).1
  have hμeig : ∀ n, Module.End.HasEigenvalue T.toLinearMap (μ n) :=
    fun n => (hμmem n).2
  choose v hv using fun n =>
    Module.End.HasEigenvalue.exists_hasEigenvector (hμeig n)
  have hv_mem : ∀ n, v n ∈ Module.End.eigenspace T.toLinearMap (μ n) :=
    fun n => (Module.End.hasEigenvector_iff.mp (hv n)).1
  have hv_ne0 : ∀ n, v n ≠ 0 :=
    fun n => (Module.End.hasEigenvector_iff.mp (hv n)).2
  let c : ℕ → ℝ := fun n => (‖v n‖)⁻¹
  let e : ℕ → E := fun n => c n • v n
  have he_mem : ∀ n, e n ∈ Module.End.eigenspace T.toLinearMap (μ n) := by
    intro n
    exact (Module.End.eigenspace T.toLinearMap (μ n)).smul_mem (c n) (hv_mem n)
  have he_norm : ∀ n, ‖e n‖ = (1 : ℝ) := by
    intro n
    simp [e, c, hv_ne0 n, norm_smul]
  have hSymm : T.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  have he : Orthonormal ℝ e := by
    refine orthonormal_iff_ite.mpr ?_
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [inner_self_eq_norm_sq_to_K, he_norm i]
    · have hμne : μ i ≠ μ j := fun h => hij (hμinj h)
      have ho : (Module.End.eigenspace T.toLinearMap (μ i)) ⟂
          (Module.End.eigenspace T.toLinearMap (μ j)) :=
        hSymm.orthogonalFamily_eigenspaces.isOrtho hμne
      have hinner : inner ℝ (e j) (e i) = 0 :=
        ho (he_mem i) (e j) (he_mem j)
      have hinner' : inner ℝ (e i) (e j) = 0 :=
        (inner_eq_zero_symm).mpr hinner
      simpa [hij] using hinner'
  have hTe : ∀ n, T (e n) = μ n • e n := by
    intro n
    exact (Module.End.mem_eigenspace_iff).mp (he_mem n)
  exact compact_no_orthonormal_eigenvectors_with_large_eigenvalues
    T hcompact e he μ hTe δ hδ hμge

/-- In the real bounded-operator spectrum of a compact self-adjoint
interacting onsite resolvent, only finitely many spectral points
have norm at least δ > 0. -/
theorem infiniteBoundedOnsiteResolvent_finite_spectrum_away_zero
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : IsolationEnd Tile)
    (hB : ∀ ψ φ : TileHilbert Tile,
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ))
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    {μ : ℝ | δ ≤ ‖μ‖ ∧
      μ ∈ spectrum ℝ (infiniteBoundedOnsiteResolvent V a hgap B hsmall)}.Finite := by
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  have hc : IsCompactOperator R :=
    infiniteBoundedOnsiteResolvent_compact V a hgap hproper B hsmall
  have hs : IsSelfAdjoint R :=
    infiniteBoundedOnsiteResolvent_isSelfAdjoint V a hgap B hB hsmall
  have hfin := compact_selfAdjoint_finite_large_eigenvalues R hs hc δ hδ
  apply hfin.subset
  rintro μ ⟨hlarge, hspec⟩
  have hμ : μ ≠ 0 := by
    intro hzero
    subst μ
    simp at hlarge
    linarith
  exact ⟨hlarge, (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hc hμ).mpr hspec⟩


/-- Every nonzero real spectral point of the bounded compact interacting
resolvent is isolated in its full real spectrum. The radius depends on
the chosen spectral point, and the assertion includes exclusion of zero
from the chosen ball. Symmetry is needed for spectral finiteness. -/
theorem infiniteBoundedOnsiteResolvent_nonzero_spectrum_isolated
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (B : IsolationEnd Tile)
    (hB : ∀ ψ φ : TileHilbert Tile,
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ))
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (μ : ℝ) (hμ : μ ≠ 0)
    (_hmem : μ ∈ spectrum ℝ (infiniteBoundedOnsiteResolvent
      V a hgap B hsmall)) :
    ∃ r : ℝ, 0 < r ∧
      ∀ ν : ℝ, ν ∈ spectrum ℝ
          (infiniteBoundedOnsiteResolvent V a hgap B hsmall) →
        dist ν μ < r → ν = μ := by
  let R := infiniteBoundedOnsiteResolvent V a hgap B hsmall
  let δ : ℝ := ‖μ‖ / 2
  have hδ : 0 < δ := half_pos ((norm_pos_iff).mpr hμ)
  let s : Set ℝ := {ν : ℝ | δ ≤ ‖ν‖ ∧ ν ∈ spectrum ℝ R}
  have hsfin : s.Finite :=
    infiniteBoundedOnsiteResolvent_finite_spectrum_away_zero
      V a hgap hproper B hB hsmall δ hδ
  have hclosed : IsClosed (s \ {μ}) :=
    (hsfin.subset Set.diff_subset).isClosed
  have hopen : IsOpen (s \ {μ})ᶜ := hclosed.isOpen_compl
  have hμopen : μ ∈ (s \ {μ})ᶜ := by simp
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hopen μ hμopen
  refine ⟨min r δ, lt_min hr hδ, ?_⟩
  intro ν hνspec hclose
  have hdist : dist ν μ < δ :=
    lt_of_lt_of_le hclose (min_le_right _ _)
  have htri : ‖μ‖ ≤ ‖μ - ν‖ + ‖ν‖ := by
    simpa [sub_eq_add_neg, add_assoc] using (norm_add_le (μ - ν) ν)
  have hsub : ‖μ - ν‖ < δ := by
    simpa [dist_eq_norm, norm_sub_rev] using hdist
  have hnorm : δ ≤ ‖ν‖ := by
    dsimp [δ] at *
    linarith
  have hνs : ν ∈ s := ⟨hnorm, hνspec⟩
  have hball : ν ∈ Metric.ball μ r := by
    apply Metric.mem_ball.mpr
    simpa [dist_comm] using lt_of_lt_of_le hclose (min_le_left _ _)
  have hnot : ν ∈ (s \ {μ})ᶜ := hrball hball
  by_contra hne
  exact hnot ⟨hνs, by simpa using hne⟩

end SpectralGeometry
