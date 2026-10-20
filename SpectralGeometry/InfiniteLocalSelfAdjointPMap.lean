module

public import SpectralGeometry.InfiniteLocalCompactResolventBounds
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

public section

/-!
# Genuine self-adjoint unbounded operators in Mathlib's LinearPMap API

The onsite multiplication operator and the complete local matching
operator were previously constructed as linear maps on the natural
onsite domain, with explicit adjoint-pair characterizations.

This module packages them as Mathlib's partially defined `LinearPMap`
and promotes the adjoint-pair characterizations to actual
`IsSelfAdjoint` statements in that API. The key reusable lemma
identifies the graph of the adjoint with the graph of the operator,
using density and the previously checked pairing condition.

Symmetry of matching permutations and of the bounded perturbation is
required for the full interacting operator. No discrete spectral
decomposition or eigenvalue-growth estimate is claimed here.
-/

namespace SpectralGeometry

variable {Tile : Type*} [DecidableEq Tile]

/-- A generic bridge: a densely defined partial operator whose
adjoint-pair equation characterizes exactly its graph is self-adjoint. -/
private theorem selfAdjoint_of_pairing_iff_graph
    (A : TileHilbert Tile →ₗ.[ℝ] TileHilbert Tile)
    (hdense : Dense (A.domain : Set (TileHilbert Tile)))
    (hpair : ∀ η χ : TileHilbert Tile,
      (∀ φ : A.domain,
        inner ℝ (A φ) η = inner ℝ (φ.1 : TileHilbert Tile) χ) ↔
      (η, χ) ∈ A.graph) :
    IsSelfAdjoint A := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hdense]
  apply Submodule.ext
  rintro ⟨η, χ⟩
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro ha
    apply (hpair η χ).mp
    intro φ
    have hh := ha (φ.1 : TileHilbert Tile) (A φ) (A.mem_graph φ)
    exact sub_eq_zero.mp hh
  · intro ha
    intro x y hxy
    obtain ⟨φ, hφ, hAφ⟩ := (LinearPMap.mem_graph_iff A).mp hxy
    have hp := (hpair η χ).mpr ha φ
    change inner ℝ y η - inner ℝ x χ = 0
    simp only [Prod.fst, Prod.snd] at hφ hAφ
    rw [← hφ, ← hAφ]
    exact sub_eq_zero.mpr hp

/-- The diagonal onsite operator in Mathlib's partial-operator API. -/
noncomputable def infiniteOnsitePMap (V : Tile → ℝ) :
    TileHilbert Tile →ₗ.[ℝ] TileHilbert Tile where
  domain := infiniteOnsiteDomain V
  toFun := infiniteOnsiteOperator V

/-- The Mathlib partial operator has exactly the original natural domain. -/
theorem infiniteOnsitePMap_domain (V : Tile → ℝ) :
    (infiniteOnsitePMap V).domain = infiniteOnsiteDomain V := rfl

/-- The original adjoint-pair characterization, now expressed in
Mathlib's partial-operator graph. -/
theorem infiniteOnsitePMap_pair_iff_graph
    (V : Tile → ℝ) (η χ : TileHilbert Tile) :
    (∀ φ : (infiniteOnsitePMap V).domain,
      inner ℝ (infiniteOnsitePMap V φ) η =
        inner ℝ (φ.1 : TileHilbert Tile) χ) ↔
      (η, χ) ∈ (infiniteOnsitePMap V).graph := by
  have hh := infiniteOnsite_adjoint_pair_iff V η χ
  constructor
  · intro hp
    obtain ⟨ψ, hψ⟩ := hh.mp hp
    exact (LinearPMap.mem_graph_iff' (infiniteOnsitePMap V)).mpr
      ⟨ψ, hψ⟩
  · intro hp
    obtain ⟨ψ, hψ⟩ :=
      (LinearPMap.mem_graph_iff' (infiniteOnsitePMap V)).mp hp
    exact hh.mpr ⟨ψ, hψ⟩

/-- The unbounded onsite multiplication is truly self-adjoint
according to Mathlib's `IsSelfAdjoint` predicate for `LinearPMap`. -/
theorem infiniteOnsitePMap_isSelfAdjoint (V : Tile → ℝ) :
    IsSelfAdjoint (infiniteOnsitePMap V) := by
  apply selfAdjoint_of_pairing_iff_graph
    (infiniteOnsitePMap V)
  · exact infiniteOnsiteDomain_dense V
  · exact infiniteOnsitePMap_pair_iff_graph V

/-- The full infinite local operator on the original onsite domain,
packaged as a Mathlib partially defined linear map. -/
noncomputable def infiniteLocalShiftedPerturbedPMap
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ) :
    TileHilbert Tile →ₗ.[ℝ] TileHilbert Tile where
  domain := infiniteOnsiteDomain V
  toFun := infiniteLocalShiftedPerturbedOperator D V σ w P ε shift

/-- The full local partial operator uses the unchanged natural domain. -/
theorem infiniteLocalShiftedPerturbedPMap_domain
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ) :
    (infiniteLocalShiftedPerturbedPMap D V σ w P ε shift).domain =
      infiniteOnsiteDomain V := rfl

/-- Existing local adjoint-pair equality, transferred without
weakening its domain assumptions to Mathlib's graph API. -/
theorem infiniteLocalShiftedPerturbedPMap_pair_iff_graph
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ)
    (η χ : TileHilbert Tile) :
    (∀ φ : (infiniteLocalShiftedPerturbedPMap D V σ w P ε shift).domain,
      inner ℝ (infiniteLocalShiftedPerturbedPMap D V σ w P ε shift φ) η =
        inner ℝ (φ.1 : TileHilbert Tile) χ) ↔
      (η, χ) ∈
        (infiniteLocalShiftedPerturbedPMap D V σ w P ε shift).graph := by
  have hh :=
    infiniteLocalShiftedPerturbed_adjoint_pair_iff
      D V σ w P ε shift hσ hP η χ
  constructor
  · intro hp
    obtain ⟨ψ, hψ⟩ := hh.mp hp
    exact
      (LinearPMap.mem_graph_iff'
        (infiniteLocalShiftedPerturbedPMap D V σ w P ε shift)).mpr
          ⟨ψ, hψ⟩
  · intro hp
    obtain ⟨ψ, hψ⟩ :=
      (LinearPMap.mem_graph_iff'
        (infiniteLocalShiftedPerturbedPMap D V σ w P ε shift)).mp hp
    exact hh.mpr ⟨ψ, hψ⟩

/-- The full local infinite operator is self-adjoint as a Mathlib
`LinearPMap` when all matchings are involutive and P is symmetric.
No boundedness or properness assumption on V is needed here. -/
theorem infiniteLocalShiftedPerturbedPMap_isSelfAdjoint
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ)
    (hσ : ∀ i t, σ i (σ i t) = t)
    (hP : ∀ ψ φ : TileHilbert Tile,
      inner ℝ ψ (P φ) = inner ℝ (P ψ) φ) :
    IsSelfAdjoint (infiniteLocalShiftedPerturbedPMap D V σ w P ε shift) := by
  apply selfAdjoint_of_pairing_iff_graph
    (infiniteLocalShiftedPerturbedPMap D V σ w P ε shift)
  · exact infiniteOnsiteDomain_dense V
  · exact
      infiniteLocalShiftedPerturbedPMap_pair_iff_graph
        D V σ w P ε shift hσ hP

end SpectralGeometry
