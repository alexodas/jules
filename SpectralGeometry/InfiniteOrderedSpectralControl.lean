module

public import SpectralGeometry.InfiniteLocalFullEigenbasis
public import SpectralGeometry.OrderedVariationalPrinciple

public section

/-!
# Ordered onsite comparison and finite-sector spectral response

All comparisons use genuine complete eigenbases on the common natural
multiplication domain. The preceding module constructs these from the
existing exact multiplicity-tagged matching spectra.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

/-- Onsite eigenvectors in any bijective site ordering. Monotonicity of
these levels is an explicit hypothesis when this basis is used in min-max. -/
@[expose] def onsiteDomainEigenbasis (V : Tile → ℝ) (e : ℕ ≃ Tile) :
    DomainEigenbasis (infiniteOnsiteDomain V) (infiniteOnsiteOperator V) (fun n => V (e n)) := by
  let b : HilbertBasis Tile ℝ (TileHilbert Tile) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  let bn := reindexHilbertBasis b e
  have hb (n : ℕ) : bn n = lp.single (2 : ENNReal) (e n) (1 : ℝ) := by
    rw [reindexHilbertBasis_apply, ← b.repr_symm_single]
    rfl
  have hm (n : ℕ) : bn n ∈ infiniteOnsiteDomain V := by
    rw [hb]
    exact infiniteOnsiteDomain_single V (e n) 1
  refine ⟨bn, hm, ?_⟩
  intro n
  apply lp.ext
  funext t
  change V t * bn n t = V (e n) * bn n t
  rw [hb]
  by_cases ht : t = e n
  · subst t
    rfl
  · simp [lp.single_apply, Pi.single_eq_of_ne ht]

theorem onsitePlusBounded_energy_sandwich (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) (x : infiniteOnsiteDomain V) :
    inner ℝ (x : TileHilbert Tile) (infiniteOnsiteOperator V x) - ‖B‖ * ‖(x : TileHilbert Tile)‖ ^ 2 ≤
      inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V B x) ∧
    inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V B x) ≤
      inner ℝ (x : TileHilbert Tile) (infiniteOnsiteOperator V x) + ‖B‖ * ‖(x : TileHilbert Tile)‖ ^ 2 := by
  have hh := abs_le.mp (infiniteLocalBoundedPerturbation_inner_abs_le B x)
  rw [onsitePlusBounded_apply, inner_add_right]
  constructor <;> linarith

/-- Two-sided comparison of ordered onsite and full levels, counting
multiplicity through the complete eigenbases. -/
theorem onsitePlusBounded_ordered_comparison (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (e : ℕ ≃ Tile) (hVorder : Monotone (fun n => V (e n)))
    (ev : ℕ → ℝ) (hev : Monotone ev)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev) (n : ℕ) :
    V (e n) - ‖B‖ ≤ ev n ∧ ev n ≤ V (e n) + ‖B‖ := by
  have hlo := ordered_eigenvalues_affine_le (onsiteDomainEigenbasis V e) b
    (fun x y => (infiniteOnsiteOperator_symmetric V x y).symm) (onsitePlusBounded_symmetric V B hB)
    hVorder hev 1 (-‖B‖) zero_le_one
    (fun x => by simpa using (onsitePlusBounded_energy_sandwich V B x).1) n
  have hhi := ordered_eigenvalues_affine_le b (onsiteDomainEigenbasis V e)
    (onsitePlusBounded_symmetric V B hB) (fun x y => (infiniteOnsiteOperator_symmetric V x y).symm)
    hev hVorder 1 (-‖B‖) zero_le_one
    (fun x => by have hh := (onsitePlusBounded_energy_sandwich V B x).2; simpa using (by linarith :
      inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V B x) - ‖B‖ * ‖(x : TileHilbert Tile)‖ ^ 2 ≤
      inner ℝ (x : TileHilbert Tile) (infiniteOnsiteOperator V x))) n
  constructor <;> linarith

/-- The ordered comparison for precisely the original matching-spectrum
multiplicity tags, with the existing resolvent and symmetry hypotheses. -/
theorem infiniteLocalMatching_full_ordered_comparison
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε shift a : ℝ)
    (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ x y : TileHilbert Tile, inner ℝ x (P y) = inner ℝ (P x) y)
    (seq : ℕ → ℝ ×ₗ ℕ) (hseq : StrictMono seq)
    (hrange : Set.range seq = toLex ''
      infiniteLocalMatchingFullMultiplicityTags D V σ w P ε shift a hgap hproper hsmall)
    (e : ℕ ≃ Tile) (horder : Monotone (fun n => V (e n))) (n : ℕ) :
    V (e n) - ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ ≤ (ofLex (seq n)).1 ∧
      (ofLex (seq n)).1 ≤ V (e n) + ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ := by
  obtain ⟨b⟩ := infiniteLocalMatching_full_exists_domainEigenbasis
    D V σ w P ε shift a hgap hproper hsmall hσ hP seq hseq hrange
  exact onsitePlusBounded_ordered_comparison V _
    (infiniteLocalBoundedCorrection_symmetric D σ w P ε shift hσ hP) e horder
    (fun k => (ofLex (seq k)).1)
    (fun i j hij => Prod.Lex.monotone_fst _ _ (hseq.monotone hij)) b n

/-- Positive bounded corrections sharpen the lower onsite comparison. -/
theorem onsitePlusBounded_ordered_ge_onsite_of_nonneg (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (B x))
    (e : ℕ ≃ Tile) (hVorder : Monotone (fun n => V (e n)))
    (ev : ℕ → ℝ) (hev : Monotone ev)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev) (n : ℕ) :
    V (e n) ≤ ev n := by
  have hh := ordered_eigenvalues_affine_le (onsiteDomainEigenbasis V e) b
    (fun x y => (infiniteOnsiteOperator_symmetric V x y).symm) (onsitePlusBounded_symmetric V B hB)
    hVorder hev 1 0 zero_le_one (fun x => by
      simp only [one_mul, zero_mul, add_zero, onsitePlusBounded_apply, inner_add_right]
      exact le_add_of_nonneg_right (hpos x)) n
  simpa using hh

/-- A nonnegative interaction costs nothing in the lower comparison; only
the norm of the remaining signed correction is subtracted. This applies to
the existing matching Laplacian when its weights are nonnegative. -/
theorem onsitePlusBounded_ordered_ge_of_nonneg_part (V : Tile → ℝ)
    (L Q : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ ((L + Q) x) y = inner ℝ x ((L + Q) y))
    (hL : ∀ x, 0 ≤ inner ℝ x (L x))
    (e : ℕ ≃ Tile) (horder : Monotone (fun n => V (e n)))
    (ev : ℕ → ℝ) (hev : Monotone ev)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V (L + Q)) ev)
    (n : ℕ) : V (e n) - ‖Q‖ ≤ ev n := by
  have hh := ordered_eigenvalues_affine_le (onsiteDomainEigenbasis V e) b
    (fun x y => (infiniteOnsiteOperator_symmetric V x y).symm) (onsitePlusBounded_symmetric V _ hB)
    horder hev 1 (-‖Q‖) zero_le_one (fun x => by
      have hq := (abs_le.mp (infiniteLocalBoundedPerturbation_inner_abs_le Q x)).1
      have hl := hL x
      simp only [onsitePlusBounded_apply, ContinuousLinearMap.add_apply, inner_add_right]
      nlinarith) n
  simpa using hh

/-- A positive finite-sector perturbation is still symmetric. -/
theorem finiteSectorCorrection_symmetric
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (F : Finset Tile) (τ : ℝ)
    (x y : TileHilbert Tile) :
    inner ℝ ((B + τ • finiteSectorProjection F) x) y =
      inner ℝ x ((B + τ • finiteSectorProjection F) y) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hB, finiteSectorProjection_symmetric]

/-- Exact form response on the unchanged natural domain. -/
theorem finiteSector_energy_response (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) (F : Finset Tile) (τ : ℝ)
    (x : infiniteOnsiteDomain V) :
    inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V (B + τ • finiteSectorProjection F) x) =
      inner ℝ (x : TileHilbert Tile) (onsitePlusBounded V B x) +
      τ * ‖finiteSectorProjection F x‖ ^ 2 := by
  simp only [onsitePlusBounded_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inner_add_right, real_inner_smul_right,
    finiteSectorProjection_inner]
  ring

/-- Nonnegative interventions cannot lower any ordered level. -/
theorem finiteSector_ordered_mono (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (F : Finset Tile) (τ : ℝ) (hτ : 0 ≤ τ)
    (ev μ : ℕ → ℝ) (hev : Monotone ev) (hμ : Monotone μ)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev)
    (bt : DomainEigenbasis (infiniteOnsiteDomain V)
      (onsitePlusBounded V (B + τ • finiteSectorProjection F)) μ) (n : ℕ) :
    ev n ≤ μ n := by
  have hh := ordered_eigenvalues_affine_le b bt (onsitePlusBounded_symmetric V B hB)
    (onsitePlusBounded_symmetric V _ (finiteSectorCorrection_symmetric B hB F τ))
    hev hμ 1 0 zero_le_one (fun x => by
      rw [finiteSector_energy_response]
      simp only [one_mul, zero_mul, add_zero]
      exact le_add_of_nonneg_right (mul_nonneg hτ (sq_nonneg _))) n
  simpa using hh

/-- Uniform lower and upper response for each selected low ordered level.
The proof uses the affine variational comparison, so crossings and repeated
eigenvalues are allowed. -/
theorem finiteSector_ordered_response (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (v₀ R E : ℝ) (hV : ∀ t, v₀ ≤ V t) (hR : v₀ < R)
    (F : Finset Tile) (hF : ∀ t, t ∉ F → R ≤ V t)
    (τ : ℝ) (hτ : 0 ≤ τ) (hτR : τ ≤ R - v₀)
    (ev μ : ℕ → ℝ) (hev : Monotone ev) (hμ : Monotone μ)
    (b : DomainEigenbasis (infiniteOnsiteDomain V) (onsitePlusBounded V B) ev)
    (bt : DomainEigenbasis (infiniteOnsiteDomain V)
      (onsitePlusBounded V (B + τ • finiteSectorProjection F)) μ)
    (n : ℕ) (hn : ev n ≤ E) :
    ((R - ‖B‖ - E) / (R - v₀)) * τ ≤ μ n - ev n ∧ μ n - ev n ≤ τ := by
  let r := τ / (R - v₀)
  have hd : 0 < R - v₀ := sub_pos.mpr hR
  have hr0 : 0 ≤ r := div_nonneg hτ hd.le
  have hr1 : r ≤ 1 := (div_le_one hd).mpr hτR
  have hrt : r * (R - v₀) = τ := div_mul_cancel₀ τ (ne_of_gt hd)
  have hlo := ordered_eigenvalues_affine_le b bt (onsitePlusBounded_symmetric V B hB)
    (onsitePlusBounded_symmetric V _ (finiteSectorCorrection_symmetric B hB F τ))
    hev hμ (1 - r) (r * (R - ‖B‖)) (sub_nonneg.mpr hr1) (fun x => by
      have hs := mul_le_mul_of_nonneg_left (onsitePlusBounded_sector_form_bound V B v₀ R hV F hF x) hr0
      rw [finiteSector_energy_response]
      nlinarith [hrt]) n
  have hhi := ordered_eigenvalues_affine_le bt b
    (onsitePlusBounded_symmetric V _ (finiteSectorCorrection_symmetric B hB F τ))
    (onsitePlusBounded_symmetric V B hB) hμ hev 1 (-τ) zero_le_one (fun x => by
      have hnorm : ‖finiteSectorProjection F x‖ ≤ ‖(x : TileHilbert Tile)‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (by
          simpa using mul_le_mul_of_nonneg_right (finiteSectorProjection_norm_le F) (norm_nonneg (x : TileHilbert Tile)))
      have hsq : ‖finiteSectorProjection F x‖ ^ 2 ≤ ‖(x : TileHilbert Tile)‖ ^ 2 := by
        nlinarith [norm_nonneg (finiteSectorProjection F x), norm_nonneg (x : TileHilbert Tile)]
      rw [finiteSector_energy_response]
      have hh := mul_le_mul_of_nonneg_left hsq hτ
      nlinarith) n
  have heq : ((R - ‖B‖ - E) / (R - v₀)) * τ = r * (R - ‖B‖ - E) := by
    dsimp [r]
    ring
  constructor
  · rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hn hr0]
  · linarith

end
end SpectralGeometry
