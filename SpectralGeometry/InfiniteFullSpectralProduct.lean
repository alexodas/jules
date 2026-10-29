module

public import SpectralGeometry.CanonicalProductZeroOrder
public import SpectralGeometry.InfiniteFullSpectralSummability

public section

/-!
# Entire full spectral products with geometric zero multiplicities

An exact enumeration of the existing full-operator multiplicity tags fixes
the repetition count of every level. The analytic theorem then identifies
zero order with the original finite dimension of the full eigenspace.
The final corollary obtains positivity and summability from the already
verified onsite comparison, rather than assuming them for that application.

The natural domain and real compact-resolvent hypotheses remain those of the
full spectral modules. The sequence interface is explicitly infinite; no
natural-number enumeration of a finite or empty spectrum is asserted.
-/

namespace SpectralGeometry

noncomputable section

/-- Exact multiplicity tags determine the size of every level fiber. -/
theorem levelMultiplicity_eq_of_tag_enumeration
    (m : ℝ → ℕ) (seq : ℕ → ℝ × ℕ) (hinj : Function.Injective seq)
    (hmem : ∀ n, (seq n).2 < m (seq n).1)
    (hcover : ∀ r k, k < m r → ∃ n, seq n = (r, k)) (r : ℝ) :
    levelMultiplicity (fun n => (seq n).1) r = m r := by
  let f (n : {n : ℕ // (seq n).1 = r}) : Fin (m r) :=
    ⟨(seq n).2, by rw [← n.property]; exact hmem n⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Subtype.ext
      apply hinj
      apply Prod.ext
      · exact i.property.trans j.property.symm
      · exact congrArg Fin.val hij
    · intro k
      obtain ⟨n, hn⟩ := hcover r k.val k.isLt
      refine ⟨⟨n, congrArg Prod.fst hn⟩, ?_⟩
      exact Fin.ext (congrArg Prod.snd hn)
  exact (Nat.card_congr (Equiv.ofBijective f hf)).trans (Nat.card_fin _)

variable {Tile : Type*} [DecidableEq Tile]
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε shift a : ℝ)
    (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (seq : ℕ → ℝ ×ₗ ℕ) (hseq : StrictMono seq)
    (hrange : Set.range seq = toLex ''
      infiniteLocalMatchingFullMultiplicityTags D V σ w P ε shift a hgap hproper hsmall)

/-- The number of repetitions in the original exact ordered sequence is the
geometric multiplicity, including zero for parameters outside the spectrum. -/
theorem infiniteLocalMatching_full_sequence_levelMultiplicity (r : ℝ) :
    levelMultiplicity (fun n => (ofLex (seq n)).1) r =
      infiniteLocalMatchingFullMultiplicity D V σ w P ε shift a hgap hproper hsmall r := by
  apply levelMultiplicity_eq_of_tag_enumeration
    (infiniteLocalMatchingFullMultiplicity D V σ w P ε shift a hgap hproper hsmall)
    (fun n => ofLex (seq n))
  · exact ofLex.injective.comp hseq.injective
  · intro n
    have hn : seq n ∈ toLex ''
        infiniteLocalMatchingFullMultiplicityTags D V σ w P ε shift a hgap hproper hsmall :=
      hrange ▸ Set.mem_range_self n
    obtain ⟨p, hp, he⟩ := hn
    simpa [← he] using hp.2
  · intro r k hk
    have hp : (r, k) ∈ infiniteLocalMatchingFullMultiplicityTags
        D V σ w P ε shift a hgap hproper hsmall :=
      ⟨(infiniteLocalMatching_full_eigenvalue_iff_multiplicity_pos
        D V σ w P ε shift a hgap hproper hsmall r).mpr
          (lt_of_le_of_lt (Nat.zero_le k) hk), hk⟩
    have hh : toLex (r, k) ∈ Set.range seq := by
      rw [hrange]
      exact ⟨(r, k), hp, rfl⟩
    obtain ⟨n, hn⟩ := hh
    exact ⟨n, congrArg ofLex hn⟩

/-- The paired product of the full ordered spectrum is entire. Its zeros
are exactly the paired real spectral levels, with their original geometric
multiplicities. Positivity and summability are separate analytic inputs. -/
theorem infiniteLocalMatching_full_product_entire_exact_zeros
    (c d : ℂ) (ha : Admissible (fun n => (ofLex (seq n)).1) c d) (hd : d ≠ 0) :
    Differentiable ℂ (canonicalProduct (fun n => (ofLex (seq n)).1) c d) ∧
    (∀ s : ℂ, canonicalProduct (fun n => (ofLex (seq n)).1) c d s = 0 ↔
      ∃ r ∈ infiniteBoundedOnsiteRealSpectrum V
        (infiniteLocalBoundedCorrection D σ w P ε shift),
        s = c + d * (r : ℂ) ∨ s = c - d * (r : ℂ)) ∧
    (∀ r : ℝ, 0 < r → ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
      analyticOrderAt (canonicalProduct (fun n => (ofLex (seq n)).1) c d)
        (c + d * ((sign * r : ℝ) : ℂ)) =
      (infiniteLocalMatchingFullMultiplicity D V σ w P ε shift a hgap hproper hsmall r : ℕ∞)) := by
  let ev (n : ℕ) := (ofLex (seq n)).1
  have hmem (n : ℕ) : ofLex (seq n) ∈
      infiniteLocalMatchingFullMultiplicityTags D V σ w P ε shift a hgap hproper hsmall := by
    have hn : seq n ∈ toLex ''
        infiniteLocalMatchingFullMultiplicityTags D V σ w P ε shift a hgap hproper hsmall :=
      hrange ▸ Set.mem_range_self n
    obtain ⟨p, hp, he⟩ := hn
    simpa [← he] using hp
  refine ⟨canonicalProduct_differentiable ha, ?_, ?_⟩
  · intro s
    rw [canonicalProduct_zero_iff ha hd]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨ev n, (infiniteLocalMatching_fullRealSpectrum_iff_hasFullEigenvalue
        D V σ w P ε shift a hgap hproper hsmall (ev n)).mpr (hmem n).1, hn⟩
    · rintro ⟨r, hr, hs⟩
      have hm := (infiniteLocalMatching_fullRealSpectrum_iff_multiplicity_pos
        D V σ w P ε shift a hgap hproper hsmall r).mp hr
      have ht : (r, 0) ∈ infiniteLocalMatchingFullMultiplicityTags
          D V σ w P ε shift a hgap hproper hsmall :=
        ⟨(infiniteLocalMatching_full_eigenvalue_iff_multiplicity_pos
          D V σ w P ε shift a hgap hproper hsmall r).mpr hm, hm⟩
      have hh : toLex (r, 0) ∈ Set.range seq := by
        rw [hrange]
        exact ⟨(r, 0), ht, rfl⟩
      obtain ⟨n, hn⟩ := hh
      refine ⟨n, ?_⟩
      simpa [hn] using hs
  · intro r hr sign hsign
    rw [canonicalProduct_order_at_signed_level ha hd r hr sign hsign,
      infiniteLocalMatching_full_sequence_levelMultiplicity
        D V σ w P ε shift a hgap hproper hsmall seq hseq hrange r]

/-- Onsite summability and a strict norm gap supply the analytic hypotheses
for the actual full tag sequence. Self-adjointness supplies its domain
eigenbasis; onsite ordering is an explicit input, as in the growth-transfer
theorem. The conclusion exposes the hypotheses used by the exact-zero theorem. -/
theorem infiniteLocalMatching_full_product_admissible_of_onsite
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ x y : TileHilbert Tile, inner ℝ x (P y) = inner ℝ (P x) y)
    (v₀ : ℝ) (hV : ∀ t, v₀ ≤ V t)
    (hpositive : ‖infiniteLocalBoundedCorrection D σ w P ε shift‖ < v₀)
    (e : ℕ ≃ Tile) (horder : Monotone (fun n => V (e n)))
    (honsite : Summable (fun t => 1 / (V t) ^ 2)) (c d : ℂ) :
    Admissible (fun n => (ofLex (seq n)).1) c d := by
  obtain ⟨b⟩ := infiniteLocalMatching_full_exists_domainEigenbasis
    D V σ w P ε shift a hgap hproper hsmall hσ hP seq hseq hrange
  have hm : Monotone (fun n => (ofLex (seq n)).1) := by
    intro i j hij
    exact Prod.Lex.monotone_fst _ _ (hseq.monotone hij)
  have hB : ∀ x y, inner ℝ (infiniteLocalBoundedCorrection D σ w P ε shift x) y =
      inner ℝ x (infiniteLocalBoundedCorrection D σ w P ε shift y) := by
    intro x y
    exact infiniteLocalBoundedCorrection_symmetric D σ w P ε shift hσ hP x y
  obtain ⟨_, hp, hs⟩ := onsitePlusBounded_ordered_positive_summable V
    (infiniteLocalBoundedCorrection D σ w P ε shift) hB v₀ hV hpositive hproper
    e horder honsite (fun n => (ofLex (seq n)).1) hm b
  exact admissible_of_inv_sq_summable hp hs c d

end
end SpectralGeometry
