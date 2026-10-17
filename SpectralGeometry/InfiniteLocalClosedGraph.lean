import SpectralGeometry.InfiniteLocalGraphNorm

/-!
# Closed graphs for infinite onsite and local geometric operators

The natural domain of the possibly unbounded diagonal multiplication
M_V consists of square-summable states whose pointwise V-product is also
square-summable. The graph of this operator is closed in ℓ² × ℓ²:
a limit of input-output pairs still comes from its natural domain.

Adding the bounded infinite matching interaction, a bounded perturbation,
and a scalar identity shift leaves the graph closed. The proof uses the
continuity of the bounded correction and a homeomorphic change of graph
coordinates; no positivity, involution, symmetry, or boundedness of V
is needed for this closedness statement.

This is genuine closed-operator information, but it does NOT establish
self-adjointness, surjectivity, compact resolvent, or spectral discreteness.
-/

namespace SpectralGeometry

variable {Tile : Type*}

/-- The input-output graph of the unbounded onsite multiplication on its
natural domain. Its ambient space is a product of two copies of ℓ². -/
def infiniteOnsiteGraph (V : Tile → ℝ) :
    Set (TileHilbert Tile × TileHilbert Tile) :=
  Set.range (fun ψ : infiniteOnsiteDomain V =>
    ((ψ.1 : TileHilbert Tile), infiniteOnsiteOperator V ψ))

/-- An input-output pair belongs to the onsite graph precisely when
its output equals pointwise multiplication of its input by V. -/
theorem infiniteOnsiteGraph_iff (V : Tile → ℝ)
    (z : TileHilbert Tile × TileHilbert Tile) :
    z ∈ infiniteOnsiteGraph V ↔
      ∀ t : Tile, z.2 t = V t * z.1 t := by
  constructor
  · rintro ⟨ψ, rfl⟩
    intro t
    exact infiniteOnsiteOperator_apply V ψ t
  · intro hz
    have hmem : Memℓp (fun t : Tile => V t * z.1 t) 2 := by
      have heq :
          (fun t : Tile => V t * z.1 t) =
            (fun t : Tile => z.2 t) := by
        funext t
        exact (hz t).symm
      rw [heq]
      exact z.2.property
    let ψ : infiniteOnsiteDomain V := ⟨z.1, hmem⟩
    refine ⟨ψ, ?_⟩
    apply Prod.ext
    · rfl
    · apply lp.ext
      funext t
      exact (hz t).symm

/-- The natural-domain multiplication operator has a closed graph
even when V is unbounded and Tile is infinite. -/
theorem infiniteOnsiteGraph_isClosed (V : Tile → ℝ) :
    IsClosed (infiniteOnsiteGraph V) := by
  have hEval (t : Tile) :
      Continuous (fun x : TileHilbert Tile => x t) := by
    exact (lp.evalCLM ℝ (fun _ : Tile => ℝ) 2 t).continuous
  have hpiece (t : Tile) :
      IsClosed {z : TileHilbert Tile × TileHilbert Tile |
        z.2 t = V t * z.1 t} := by
    have hleft : Continuous
        (fun z : TileHilbert Tile × TileHilbert Tile => z.2 t) :=
      (hEval t).comp continuous_snd
    have hright : Continuous
        (fun z : TileHilbert Tile × TileHilbert Tile => V t * z.1 t) :=
      continuous_const.mul ((hEval t).comp continuous_fst)
    exact isClosed_eq hleft hright
  have heq :
      infiniteOnsiteGraph V =
        ⋂ t : Tile, {z : TileHilbert Tile × TileHilbert Tile |
          z.2 t = V t * z.1 t} := by
    ext z
    rw [infiniteOnsiteGraph_iff]
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  rw [heq]
  exact isClosed_iInter hpiece

variable [DecidableEq Tile]

/-- The bounded part added to the onsite multiplication operator. -/
noncomputable def infiniteLocalBoundedCorrection
    (D : ℕ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  infiniteLocalMatchingLaplacian D σ w + ε • P +
    shift • ContinuousLinearMap.id ℝ (TileHilbert Tile)

/-- The bounded correction acts as the sum of its three terms. -/
theorem infiniteLocalBoundedCorrection_apply
    (D : ℕ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ) (ψ : TileHilbert Tile) :
    infiniteLocalBoundedCorrection D σ w P ε shift ψ =
      infiniteLocalMatchingLaplacian D σ w ψ +
        ε • P ψ + shift • ψ := by
  simp [infiniteLocalBoundedCorrection,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

/-- On the common onsite domain, the full operator is onsite
multiplication plus the continuous bounded correction. -/
theorem infiniteLocalShiftedPerturbed_eq_onsite_add_correction
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ) (ψ : infiniteOnsiteDomain V) :
    infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
      infiniteOnsiteOperator V ψ +
        infiniteLocalBoundedCorrection D σ w P ε shift ψ.1 := by
  rw [infiniteLocalShiftedPerturbedOperator_apply,
    infiniteLocalMatchingPerturbedOperator_apply,
    infiniteLocalBoundedCorrection_apply]
  abel

/-- Closedness of the graph of the full infinite local operator,
without positivity hypotheses or symmetry of the bounded perturbation. -/
theorem infiniteLocalShiftedPerturbed_graph_isClosed
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ) :
    IsClosed (Set.range (fun ψ : infiniteOnsiteDomain V =>
      ((ψ.1 : TileHilbert Tile),
        infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ))) := by
  let B := infiniteLocalBoundedCorrection D σ w P ε shift
  let F : TileHilbert Tile × TileHilbert Tile →
      TileHilbert Tile × TileHilbert Tile :=
    fun z => (z.1, z.2 - B z.1)
  have hcontinuous : Continuous F := by
    exact continuous_fst.prodMk
      (continuous_snd.sub (B.continuous.comp continuous_fst))
  have heq :
      Set.range (fun ψ : infiniteOnsiteDomain V =>
        ((ψ.1 : TileHilbert Tile),
          infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ)) =
        F ⁻¹' infiniteOnsiteGraph V := by
    ext z
    constructor
    · rintro ⟨ψ, rfl⟩
      change ((ψ.1 : TileHilbert Tile),
          infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
            B ψ.1) ∈ infiniteOnsiteGraph V
      have hh :
          infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ -
            B ψ.1 = infiniteOnsiteOperator V ψ := by
        rw [infiniteLocalShiftedPerturbed_eq_onsite_add_correction]
        change infiniteOnsiteOperator V ψ + B ψ.1 - B ψ.1 =
          infiniteOnsiteOperator V ψ
        abel
      rw [hh]
      exact ⟨ψ, rfl⟩
    · intro hz
      change ((z.1 : TileHilbert Tile), z.2 - B z.1) ∈
        infiniteOnsiteGraph V at hz
      rcases hz with ⟨ψ, hψ⟩
      have hf : (ψ.1 : TileHilbert Tile) = z.1 :=
        congrArg Prod.fst hψ
      have hs : infiniteOnsiteOperator V ψ = z.2 - B z.1 :=
        congrArg Prod.snd hψ
      refine ⟨ψ, ?_⟩
      apply Prod.ext
      · exact hf
      · calc
          infiniteLocalShiftedPerturbedOperator D V σ w P ε shift ψ =
              infiniteOnsiteOperator V ψ + B ψ.1 :=
                infiniteLocalShiftedPerturbed_eq_onsite_add_correction
                  D V σ w P ε shift ψ
          _ = (z.2 - B z.1) + B z.1 := by rw [hs, hf]
          _ = z.2 := by abel
  rw [heq]
  exact (infiniteOnsiteGraph_isClosed V).preimage hcontinuous

end SpectralGeometry
