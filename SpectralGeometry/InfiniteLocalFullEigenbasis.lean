module

public import SpectralGeometry.DomainEigenbasis

public section

/-!
# An eigenbasis for the existing exact ordered enumeration

The previously proved complete family of finite-dimensional eigenspaces
supplies a Hilbert basis with exactly one vector for every multiplicity tag.
Any exact ordered enumeration of those tags can therefore be used in a
variational argument without making a simple-spectrum assumption.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

/-- Connect the existing tag enumeration to an actual complete eigenbasis
on the original natural domain. The existence of this enumeration is the
separate infinite-tag theorem of §4.37; no infinite enumeration is asserted
for a finite or empty spectrum. -/
theorem infiniteLocalMatching_full_exists_domainEigenbasis
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
      infiniteLocalMatchingFullMultiplicityTags D V σ w P ε shift a hgap hproper hsmall) :
    Nonempty (DomainEigenbasis (infiniteOnsiteDomain V)
      (onsitePlusBounded V (infiniteLocalBoundedCorrection D σ w P ε shift))
      (fun n => (ofLex (seq n)).1)) := by
  classical
  let p (ev : {ev : ℝ // ev ≠ a}) : Submodule ℝ (TileHilbert Tile) :=
    infiniteLocalMatchingFullEigenspace D V σ w P ε shift a hgap hsmall ev ev.property
  letI (ev : {ev : ℝ // ev ≠ a}) : FiniteDimensional ℝ (p ev) :=
    infiniteLocalMatchingFullEigenspace_finiteDimensional
      D V σ w P ε shift a hgap hproper hsmall ev ev.property
  have ho : OrthogonalFamily ℝ (fun ev => p ev) (fun ev => (p ev).subtypeₗᵢ) := by
    intro ev μ hne x y
    obtain ⟨u, hu, heu⟩ :=
      (infiniteLocalMatchingFullEigenspace_mem_iff D V σ w P ε shift a hgap hsmall ev ev.property x).mp x.property
    obtain ⟨v, hv, hev⟩ :=
      (infiniteLocalMatchingFullEigenspace_mem_iff D V σ w P ε shift a hgap hsmall μ μ.property y).mp y.property
    change inner ℝ (x : TileHilbert Tile) (y : TileHilbert Tile) = 0
    rw [← hu, ← hv]
    exact infiniteLocalMatching_eigenvectors_orthogonal D V σ w P ε shift hσ hP
      u v ev μ (fun h => hne (Subtype.ext h))
      (by simpa only [hu] using heu) (by simpa only [hv] using hev)
  have hd : (⨆ ev, p ev)ᗮ = ⊥ :=
    infiniteLocalMatchingFullEigenspaces_dense D V σ w P ε shift a hgap hproper hsmall hσ hP
  obtain ⟨b, hb⟩ := exists_hilbertBasis_subordinate p ho hd
  let I := Σ ev : {ev : ℝ // ev ≠ a}, Fin (Module.finrank ℝ (p ev))
  let tags := infiniteLocalMatchingFullMultiplicityTags D V σ w P ε shift a hgap hproper hsmall
  have hm (ev : {ev : ℝ // ev ≠ a}) : Module.finrank ℝ (p ev) =
      infiniteLocalMatchingFullMultiplicity D V σ w P ε shift a hgap hproper hsmall ev := by
    simp only [infiniteLocalMatchingFullMultiplicity, dif_pos ev.property]
    rfl
  let f (i : I) : tags := by
    have hk : i.2.val < infiniteLocalMatchingFullMultiplicity D V σ w P ε shift a hgap hproper hsmall i.1 := by
      rw [← hm]
      exact i.2.property
    exact ⟨(i.1.val, i.2.val),
      (infiniteLocalMatching_full_eigenvalue_iff_multiplicity_pos
        D V σ w P ε shift a hgap hproper hsmall i.1).mpr
        (lt_of_le_of_lt (Nat.zero_le _) hk), hk⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨ev, he⟩, k⟩ ⟨⟨μ, hm'⟩, j⟩ hij
      have heq : ev = μ := congrArg (fun q : tags => q.1.1) hij
      subst μ
      have hk : k.val = j.val := congrArg (fun q : tags => q.1.2) hij
      have hkj : k = j := Fin.ext hk
      subst j
      rfl
    · intro q
      have hne : q.1.1 ≠ a := by
        intro heq
        have hk := q.property.2
        rw [heq, infiniteLocalMatchingFullMultiplicity_at_shift] at hk
        exact Nat.not_lt_zero _ hk
      have hk : q.1.2 < Module.finrank ℝ (p ⟨q.1.1, hne⟩) := by
        rw [hm]
        exact q.property.2
      exact ⟨⟨⟨q.1.1, hne⟩, ⟨q.1.2, hk⟩⟩, Subtype.ext (Prod.eta q.1)⟩
  let e₁ : I ≃ tags := Equiv.ofBijective f hf
  have htag (n : ℕ) : ofLex (seq n) ∈ tags := by
    have hmem : seq n ∈ toLex '' tags := hrange ▸ Set.mem_range_self n
    obtain ⟨q, hq, hqe⟩ := hmem
    simpa only [← hqe] using hq
  let tagseq (n : ℕ) : tags := ⟨ofLex (seq n), htag n⟩
  have ht : Function.Bijective tagseq := by
    constructor
    · intro n m h
      apply hseq.injective
      exact congrArg (fun q : tags => toLex q.1) h
    · intro q
      have hmem : toLex q.1 ∈ Set.range seq := by
        rw [hrange]
        exact ⟨q.1, q.property, rfl⟩
      obtain ⟨n, hn⟩ := hmem
      exact ⟨n, Subtype.ext (congrArg ofLex hn)⟩
  let e : ℕ ≃ I := (Equiv.ofBijective tagseq ht).trans e₁.symm
  have he (n : ℕ) : (e n).1.val = (ofLex (seq n)).1 :=
    congrArg (fun q : tags => q.1.1) (e₁.apply_symm_apply (tagseq n))
  let bn := reindexHilbertBasis b e
  have hbmem (n : ℕ) : bn n ∈ p (e n).1 := by
    simpa only [bn, reindexHilbertBasis_apply] using hb (e n)
  have hn (n : ℕ) : ∃ x : infiniteOnsiteDomain V,
      (x : TileHilbert Tile) = bn n ∧
      infiniteLocalShiftedPerturbedOperator D V σ w P ε shift x = (e n).1.val • bn n :=
    (infiniteLocalMatchingFullEigenspace_mem_iff D V σ w P ε shift a hgap hsmall
      (e n).1 (e n).1.property (bn n)).mp (hbmem n)
  choose x hx hxe using hn
  have hmemb (n : ℕ) : bn n ∈ infiniteOnsiteDomain V := by
    rw [← hx n]
    exact (x n).property
  refine ⟨⟨bn, hmemb, ?_⟩⟩
  intro n
  have hc : (⟨bn n, hmemb n⟩ : infiniteOnsiteDomain V) = x n := Subtype.ext (hx n).symm
  rw [hc, onsitePlusBounded_eq_local, hxe n, he n]

end
end SpectralGeometry
