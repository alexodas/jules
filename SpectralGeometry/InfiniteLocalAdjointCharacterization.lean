import SpectralGeometry.InfiniteLocalClosedGraph

/-!
# Adjoint-pair characterization for onsite and infinite local operators

For a densely defined real linear operator A on D(V), an adjoint pair
(η,χ) obeys ⟪Aφ,η⟫ = ⟪φ,χ⟫ for every φ ∈ D(V).
The operator is self-adjoint in the domain-and-pairing sense precisely
when these pairs form the graph of A.

The diagonal onsite multiplication M_V has exactly this property:
testing a possible adjoint pair on single-tile states forces χ(t)=V(t)η(t)
at every tile. Since χ is square-summable, η belongs to D(V).
Conversely, symmetry of real multiplication gives the pairing identity.

We also transfer this result to the full local operator M_V+B whenever
the bounded matching correction B is symmetric, using the identity
⟪(M_V+B)φ,η⟫ = ⟪M_Vφ,η⟫ + ⟪φ,Bη⟫.

The domain D(V) was previously proved dense, and both operator graphs
were previously proved closed. Here we work explicitly with the
adjoint-pair characterization; we do not claim a Mathlib
UnboundedLinearOperator/IsSelfAdjoint instance, nor compact resolvent,
discrete spectrum, or inverse-square summability.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- Multiplying a single-tile state by V rescales its sole coefficient. -/
theorem infiniteOnsiteOperator_single
    (V : Tile → ℝ) (t : Tile) (a : ℝ) :
    infiniteOnsiteOperator V
      (⟨lp.single (2 : ENNReal) t a,
        infiniteOnsiteDomain_single V t a⟩ : infiniteOnsiteDomain V) =
      lp.single (2 : ENNReal) t (V t * a) := by
  apply lp.ext
  funext s
  by_cases hs : s = t
  · subst s
    simp [infiniteOnsiteOperator_apply]
  · simp only [infiniteOnsiteOperator_apply, lp.single_apply,
      Pi.single_eq_of_ne hs, mul_zero]

/-- The diagonal onsite multiplication has no extra adjoint-domain
vectors: its adjoint pairing graph equals its original graph. -/
theorem infiniteOnsite_adjoint_pair_iff
    (V : Tile → ℝ) (η χ : TileHilbert Tile) :
    (∀ φ : infiniteOnsiteDomain V,
      inner ℝ (infiniteOnsiteOperator V φ) η =
        inner ℝ (φ.1 : TileHilbert Tile) χ) ↔
      (η, χ) ∈ infiniteOnsiteGraph V := by
  constructor
  · intro hpair
    apply (infiniteOnsiteGraph_iff V (η, χ)).2
    intro t
    let φ : infiniteOnsiteDomain V :=
      ⟨lp.single (2 : ENNReal) t (1 : ℝ),
        infiniteOnsiteDomain_single V t 1⟩
    have h := hpair φ
    have hsingle :
        infiniteOnsiteOperator V φ =
          lp.single (2 : ENNReal) t (V t) := by
      simpa [φ] using infiniteOnsiteOperator_single V t 1
    rw [hsingle] at h
    change inner ℝ (lp.single (2 : ENNReal) t (V t)) η =
      inner ℝ (lp.single (2 : ENNReal) t (1 : ℝ)) χ at h
    simpa [lp.inner_single_left, RCLike.inner_apply] using h
  · rintro ⟨ψ, hψ⟩
    have hf : (ψ.1 : TileHilbert Tile) = η :=
      congrArg Prod.fst hψ
    have hs : infiniteOnsiteOperator V ψ = χ :=
      congrArg Prod.snd hψ
    intro φ
    rw [← hf, ← hs]
    exact (infiniteOnsiteOperator_symmetric V φ ψ).symm

/-- Symmetry of the entire bounded local correction under involutive
matching permutations and a symmetric bounded perturbation. -/
theorem infiniteLocalBoundedCorrection_symmetric
    (D : ℕ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (ψ φ : TileHilbert Tile) :
    inner ℝ (infiniteLocalBoundedCorrection D σ w P ε shift ψ) φ =
      inner ℝ ψ (infiniteLocalBoundedCorrection D σ w P ε shift φ) := by
  rw [infiniteLocalBoundedCorrection_apply,
    infiniteLocalBoundedCorrection_apply]
  simp only [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [infiniteLocalMatchingLaplacian_symmetric D σ w hσ ψ φ,
    hP ψ φ]

/-- The full symmetric infinite local operator has exactly its own
adjoint pairing graph, on the same natural dense onsite domain.
This proves its self-adjointness in explicit adjoint-pair form. -/
theorem infiniteLocalShiftedPerturbed_adjoint_pair_iff
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (η χ : TileHilbert Tile) :
    (∀ φ : infiniteOnsiteDomain V,
      inner ℝ (infiniteLocalShiftedPerturbedOperator
        D V σ w P ε shift φ) η =
      inner ℝ (φ.1 : TileHilbert Tile) χ) ↔
      (η, χ) ∈ Set.range (fun ψ : infiniteOnsiteDomain V =>
        ((ψ.1 : TileHilbert Tile),
          infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ)) := by
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  have hB (ψ φ : TileHilbert Tile) :
      inner ℝ (B ψ) φ = inner ℝ ψ (B φ) :=
    infiniteLocalBoundedCorrection_symmetric D σ w P ε shift hσ hP ψ φ
  constructor
  · intro hpair
    have hOnsite : ∀ φ : infiniteOnsiteDomain V,
        inner ℝ (infiniteOnsiteOperator V φ) η =
          inner ℝ (φ.1 : TileHilbert Tile) (χ - B η) := by
      intro φ
      have h := hpair φ
      rw [infiniteLocalShiftedPerturbed_eq_onsite_add_correction] at h
      have hsym := hB (φ.1 : TileHilbert Tile) η
      have hsum :
          inner ℝ (infiniteOnsiteOperator V φ) η +
              inner ℝ (φ.1 : TileHilbert Tile) (B η) =
            inner ℝ (φ.1 : TileHilbert Tile) χ := by
        simpa only [inner_add_left, hsym] using h
      rw [inner_sub_right]
      linarith
    have hOnsiteGraph :
        (η, χ - B η) ∈ infiniteOnsiteGraph V :=
      (infiniteOnsite_adjoint_pair_iff V η (χ - B η)).mp hOnsite
    rcases hOnsiteGraph with ⟨ψ, hψ⟩
    have hf : (ψ.1 : TileHilbert Tile) = η :=
      congrArg Prod.fst hψ
    have hs : infiniteOnsiteOperator V ψ = χ - B η :=
      congrArg Prod.snd hψ
    refine ⟨ψ, ?_⟩
    apply Prod.ext
    · exact hf
    · calc
        infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
            infiniteOnsiteOperator V ψ + B ψ.1 :=
          infiniteLocalShiftedPerturbed_eq_onsite_add_correction
            D V σ w P ε shift ψ
        _ = (χ - B η) + B η := by rw [hs, hf]
        _ = χ := by abel
  · rintro ⟨ψ, hψ⟩
    have hf : (ψ.1 : TileHilbert Tile) = η :=
      congrArg Prod.fst hψ
    have hs :
        infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ = χ :=
      congrArg Prod.snd hψ
    intro φ
    rw [← hf, ← hs,
      infiniteLocalShiftedPerturbed_eq_onsite_add_correction,
      infiniteLocalShiftedPerturbed_eq_onsite_add_correction]
    simp only [inner_add_left, inner_add_right]
    rw [infiniteOnsiteOperator_symmetric V φ ψ,
      hB (φ.1 : TileHilbert Tile) (ψ.1 : TileHilbert Tile)]

end SpectralGeometry
