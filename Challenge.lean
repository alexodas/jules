module

public import Mathlib

public section

/-!
# Exact full spectral products and nine-level geometric zero response

The independent statement specifies the octagonal vertex graph, its matching
Laplacian, natural domain, complete ordered eigenbases and exact entire
spectral products, including operator-specific geometric zero orders. Only supporting
proposition witnesses and the target theorem have Challenge placeholders.
Solution imports the fully proved source; these placeholders are not proofs.

Each block mirrors one source module. Lean's auxiliary-proof cache is local
and is not serialized in .olean files; resetting only that cache at block
boundaries reproduces the generated helper names of separate source modules.
This does not add, remove or replace kernel declarations. All definitions and
auxiliary proofs remain subject to the unmodified Comparator and kernels.
-/

namespace SpectralGeometry

noncomputable section

-- Source module: SpectralGeometry.InfiniteOnsite
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

@[expose] abbrev TileHilbert (Tile : Type*) : Type _ :=
  lp (fun _ : Tile => ℝ) 2

variable {Tile : Type*}

@[expose] noncomputable def infiniteOnsiteDomain
    (V : Tile → ℝ) : Submodule ℝ (TileHilbert Tile) where
  carrier := {ψ | Memℓp (fun t : Tile => V t * ψ t) 2}
  zero_mem' := by
    have hz : Memℓp (fun _ : Tile => (0 : ℝ)) 2 := zero_mem_ℓp'
    simpa using hz
  add_mem' := by
    intro f g hf hg
    have h : Memℓp
        ((fun t : Tile => V t * f t) + fun t : Tile => V t * g t) 2 :=
      hf.add hg
    change Memℓp (fun t : Tile => V t * (f + g) t) 2
    have heq :
        (fun t : Tile => V t * (f + g) t) =
          ((fun t : Tile => V t * f t) + fun t : Tile => V t * g t) := by
      funext t
      simp [mul_add]
    rw [heq]
    exact h
  smul_mem' := by
    intro a f hf
    have h : Memℓp (fun t : Tile => a * (V t * f t)) 2 :=
      hf.const_mul a
    change Memℓp (fun t : Tile => V t * (a • f) t) 2
    have heq :
        (fun t : Tile => V t * (a • f) t) =
          (fun t : Tile => a * (V t * f t)) := by
      funext t
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact h

@[expose] noncomputable def infiniteOnsiteOperator
    (V : Tile → ℝ) :
    (infiniteOnsiteDomain V) →ₗ[ℝ] TileHilbert Tile where
  toFun := fun ψ =>
    ⟨(fun t : Tile => V t * ψ.1 t : PreLp (fun _ : Tile => ℝ)), ψ.2⟩
  map_add' := by
    intro f g
    apply lp.ext
    funext t
    change V t * (f.1 t + g.1 t) =
      V t * f.1 t + V t * g.1 t
    ring
  map_smul' := by
    intro a f
    apply lp.ext
    funext t
    change V t * (a * f.1 t) = a * (V t * f.1 t)
    ring

end

-- Source module: SpectralGeometry.InfiniteOnsiteFiniteLowEnergy
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*}

@[expose] def infiniteOnsiteLowEnergyTiles (V : Tile → ℝ) (R : ℝ) :
    Set Tile := {t | V t ≤ R}

end

-- Source module: SpectralGeometry.InfiniteOnsiteCompactResolvent
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*}

@[expose] noncomputable def infiniteOnsiteDiagonalContraction
    (c : Tile → ℝ) (hc : ∀ t : Tile, ‖c t‖ ≤ 1) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile := by
  let F : TileHilbert Tile →ₗ[ℝ] TileHilbert Tile :=
    { toFun := fun f =>
        ⟨(fun t : Tile => c t * f t : PreLp (fun _ : Tile => ℝ)),
          f.property.mono' (fun t => by
            calc
              ‖c t * f t‖ = ‖c t‖ * ‖f t‖ := norm_mul _ _
              _ ≤ 1 * ‖f t‖ :=
                mul_le_mul_of_nonneg_right (hc t) (norm_nonneg _)
              _ = ‖f t‖ := one_mul _)⟩
      map_add' := by
        intro f g
        apply lp.ext
        funext t
        change c t * (f t + g t) = c t * f t + c t * g t
        ring
      map_smul' := by
        intro r f
        apply lp.ext
        funext t
        change c t * (r * f t) = r * (c t * f t)
        ring }
  exact F.mkContinuous 1 (fun f => by
    calc
      ‖F f‖ ≤ ‖f‖ := lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun t => by
        change ‖c t * f t‖ ≤ ‖f t‖
        calc
          ‖c t * f t‖ = ‖c t‖ * ‖f t‖ := norm_mul _ _
          _ ≤ 1 * ‖f t‖ :=
            mul_le_mul_of_nonneg_right (hc t) (norm_nonneg _)
          _ = ‖f t‖ := one_mul _)
      _ = 1 * ‖f‖ := (one_mul _).symm)

theorem onsiteUnitGap_inverse_norm_le_one
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (t : Tile) : ‖(V t - a)⁻¹‖ ≤ 1 := by
  have hp : 0 < V t - a := lt_of_lt_of_le (by norm_num) (hgap t)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (hgap t)
  simpa [one_div] using h

@[expose] noncomputable def infiniteOnsiteResolventCLM
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  infiniteOnsiteDiagonalContraction
    (fun t => (V t - a)⁻¹) (onsiteUnitGap_inverse_norm_le_one V a hgap)

end

-- Source module: SpectralGeometry.InfiniteLocalCompactResolvent
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*}

abbrev OnsiteEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

@[expose] noncomputable def infiniteBoundedOnsiteShift
    (V : Tile → ℝ) (a : ℝ) (B : OnsiteEnd Tile)
    (ψ : infiniteOnsiteDomain V) : TileHilbert Tile :=
  infiniteOnsiteOperator V ψ - a • (ψ.1 : TileHilbert Tile) + B ψ.1

theorem infiniteBoundedOnsiteCorrection_norm_neg_lt_one
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    ‖-(B.comp (infiniteOnsiteResolventCLM V a hgap))‖ < 1 := by
  simpa only [norm_neg] using hsmall

@[expose] noncomputable def infiniteBoundedOnsiteCorrectionUnit
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    (OnsiteEnd Tile)ˣ :=
  Units.oneSub (-(B.comp (infiniteOnsiteResolventCLM V a hgap)))
    (infiniteBoundedOnsiteCorrection_norm_neg_lt_one V a hgap B hsmall)

@[expose] noncomputable def infiniteBoundedOnsiteResolvent
    (V : Tile → ℝ) (a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (B : OnsiteEnd Tile)
    (hsmall : ‖B.comp (infiniteOnsiteResolventCLM V a hgap)‖ < 1) :
    OnsiteEnd Tile :=
  (infiniteOnsiteResolventCLM V a hgap).comp
    (↑((infiniteBoundedOnsiteCorrectionUnit V a hgap B hsmall)⁻¹) :
      OnsiteEnd Tile)

end

-- Source module: SpectralGeometry.InfiniteLocalMatching
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

@[expose] noncomputable def infiniteTileReindex (σ : Tile ≃ Tile) :
    TileHilbert Tile →ₗᵢ[ℝ] TileHilbert Tile where
  toFun := fun ψ => by
    refine ⟨(fun t => ψ (σ t) : PreLp (fun _ : Tile => ℝ)), ?_⟩
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    have hsum : Summable (fun t : Tile => ‖ψ t‖ ^ (2 : ENNReal).toReal) :=
      (memℓp_gen_iff hp).mp ψ.property
    have hsum' :
        Summable (fun t : Tile => ‖ψ (σ t)‖ ^ (2 : ENNReal).toReal) :=
      (σ.summable_iff).mpr hsum
    exact (memℓp_gen_iff hp).mpr hsum'
  map_add' := by
    intro ψ φ
    apply lp.ext
    funext t
    rfl
  map_smul' := by
    intro c ψ
    apply lp.ext
    funext t
    rfl
  norm_map' := by
    intro ψ
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    let φ : TileHilbert Tile :=
      ⟨(fun t => ψ (σ t) : PreLp (fun _ : Tile => ℝ)),
        (memℓp_gen_iff hp).mpr
          ((σ.summable_iff).mpr ((memℓp_gen_iff hp).mp ψ.property))⟩
    change ‖φ‖ = ‖ψ‖
    have hsum :
        (∑' t, ‖φ t‖ ^ (2 : ENNReal).toReal) =
          (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal) := by
      change (∑' t, ‖ψ (σ t)‖ ^ (2 : ENNReal).toReal) =
        (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal)
      exact σ.tsum_eq (fun t : Tile => ‖ψ t‖ ^ (2 : ENNReal).toReal)
    calc
      ‖φ‖ =
          (∑' t, ‖φ t‖ ^ (2 : ENNReal).toReal) ^
            (1 / (2 : ENNReal).toReal) :=
        lp.norm_eq_tsum_rpow hp φ
      _ = (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal) ^
            (1 / (2 : ENNReal).toReal) := by rw [hsum]
      _ = ‖ψ‖ := (lp.norm_eq_tsum_rpow hp ψ).symm

@[expose] noncomputable def infiniteMatchingLaplacian (σ : Tile ≃ Tile) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ContinuousLinearMap.id ℝ (TileHilbert Tile) -
    (infiniteTileReindex σ).toContinuousLinearMap

end

-- Source module: SpectralGeometry.InfiniteLocalBoundedDegree
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

@[expose] noncomputable def infiniteLocalMatchingLaplacian (D : ℕ)
    (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ∑ i : Fin D, w i • infiniteMatchingLaplacian (σ i)

end

-- Source module: SpectralGeometry.InfiniteLocalClosedGraph
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*}

@[expose] def infiniteOnsiteGraph (V : Tile → ℝ) :
    Set (TileHilbert Tile × TileHilbert Tile) :=
  Set.range (fun ψ : infiniteOnsiteDomain V =>
    ((ψ.1 : TileHilbert Tile), infiniteOnsiteOperator V ψ))

variable [DecidableEq Tile]

@[expose] noncomputable def infiniteLocalBoundedCorrection
    (D : ℕ) (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (ε shift : ℝ) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  infiniteLocalMatchingLaplacian D σ w + ε • P +
    shift • ContinuousLinearMap.id ℝ (TileHilbert Tile)

end

-- Source module: SpectralGeometry.InfiniteLocalFullEigenspaces
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

abbrev FullEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

@[expose] noncomputable def infiniteLocalMatchingFullEigenspace
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (_hne : eigenvalue ≠ a) :
    Submodule ℝ (TileHilbert Tile) :=
  Module.End.eigenspace
    (infiniteBoundedOnsiteResolvent V a hgap
      (infiniteLocalBoundedCorrection D σ w P ε shift) hsmall).toLinearMap
    (eigenvalue - a)⁻¹

theorem infiniteLocalMatchingFullEigenspace_finiteDimensional
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : FullEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) (hne : eigenvalue ≠ a) :
    FiniteDimensional ℝ
      (infiniteLocalMatchingFullEigenspace
        D V σ w P ε shift a hgap hsmall eigenvalue hne) := by
  sorry

end

-- Source module: SpectralGeometry.InfiniteLocalFullEigenvalueMultiplicity
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

abbrev MultiplicityEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

@[expose] noncomputable def infiniteLocalMatchingFullMultiplicity
    (D : ℕ) (V : Tile → ℝ) (σ : Fin D → Tile ≃ Tile)
    (w : Fin D → ℝ) (P : MultiplicityEnd Tile)
    (ε shift a : ℝ) (hgap : ∀ t, 1 ≤ V t - a)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hsmall : ‖(infiniteLocalBoundedCorrection D σ w P ε shift).comp
      (infiniteOnsiteResolventCLM V a hgap)‖ < 1)
    (eigenvalue : ℝ) : ℕ := by
  classical
  by_cases hne : eigenvalue ≠ a
  · letI := infiniteLocalMatchingFullEigenspace_finiteDimensional
      D V σ w P ε shift a hgap hproper hsmall eigenvalue hne
    exact Module.finrank ℝ
      (infiniteLocalMatchingFullEigenspace
        D V σ w P ε shift a hgap hsmall eigenvalue hne)
  · exact 0

end

-- Source module: SpectralGeometry.InfiniteLocalFullRealResolvent
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

abbrev ShiftEnd (Tile : Type*) :=
  TileHilbert Tile →L[ℝ] TileHilbert Tile

@[expose] def infiniteBoundedOnsiteRealRegular
    (V : Tile → ℝ) (B : ShiftEnd Tile) (b : ℝ) : Prop :=
  ∃ Q : ShiftEnd Tile,
    (∀ f : TileHilbert Tile,
      ∃ ψ : infiniteOnsiteDomain V,
        (ψ.1 : TileHilbert Tile) = Q f ∧
          infiniteBoundedOnsiteShift V b B ψ = f) ∧
    (∀ ψ : infiniteOnsiteDomain V,
      Q (infiniteBoundedOnsiteShift V b B ψ) =
        (ψ.1 : TileHilbert Tile))

@[expose] def infiniteBoundedOnsiteRealSpectrum (V : Tile → ℝ)
    (B : ShiftEnd Tile) : Set ℝ :=
  {b | ¬ infiniteBoundedOnsiteRealRegular V B b}

end

-- Source module: SpectralGeometry.InfiniteLowEnergyObservation
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

@[expose] def finiteSectorProjection (F : Finset Tile) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  infiniteOnsiteDiagonalContraction (fun t => if t ∈ F then 1 else 0)
    (fun t => by split_ifs <;> norm_num)

@[expose] def onsitePlusBounded (V : Tile → ℝ) (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) :
    infiniteOnsiteDomain V →ₗ[ℝ] TileHilbert Tile :=
  infiniteOnsiteOperator V + B.toLinearMap.comp (infiniteOnsiteDomain V).subtype

end

-- Source module: SpectralGeometry.DomainEigenbasis
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

structure DomainEigenbasis {ι : Type*} (d : Submodule ℝ H) (A : d →ₗ[ℝ] H)
    (ev : ι → ℝ) where
  basis : HilbertBasis ι ℝ H
  mem_domain : ∀ i, basis i ∈ d
  eigen : ∀ i, A ⟨basis i, mem_domain i⟩ = ev i • basis i

end

-- Source module: SpectralGeometry.CanonicalProduct
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*}

@[expose] def perturb (q : ℕ → ℝ) (center direction : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  -(((s - center) / direction) ^ 2 / ((q n : ℂ) ^ 2))

@[expose] def factor (q : ℕ → ℝ) (center direction : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  1 + perturb q center direction n s

@[expose] def canonicalProduct (q : ℕ → ℝ) (center direction : ℂ) (s : ℂ) : ℂ :=
  ∏' n : ℕ, factor q center direction n s

end

-- Source module: SpectralGeometry.OrderedSpectralProductBridge
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

@[expose] def HasExactFullSpectralProduct (V : Tile → ℝ)
    (B : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite)
    (ev : ℕ → ℝ) (c d : ℂ) : Prop :=
  ∃ (a : ℝ) (hunit : ∀ t, 1 ≤ V t - a),
    ∃ (hsmall : ‖(infiniteLocalBoundedCorrection 0
      (fun i => Fin.elim0 i) (fun _ => 0) B 1 0).comp
        (infiniteOnsiteResolventCLM V a hunit)‖ < 1),
      Differentiable ℂ (canonicalProduct ev c d) ∧
      (∀ s : ℂ, canonicalProduct ev c d s = 0 ↔
        ∃ r ∈ infiniteBoundedOnsiteRealSpectrum V B,
          s = c + d * (r : ℂ) ∨ s = c - d * (r : ℂ)) ∧
      (∀ r : ℝ, 0 < r → ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
        analyticOrderAt (canonicalProduct ev c d)
          (c + d * ((sign * r : ℝ) : ℂ)) =
        (infiniteLocalMatchingFullMultiplicity 0 V
          (fun i => Fin.elim0 i) (fun _ => 0) B 1 0
          a hunit hproper hsmall r : ℕ∞))

end

-- Source module: SpectralGeometry.IndexedSpectralPoints
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*}

@[expose] def positiveSpectralPoint (ev : ℕ → ℝ) (c d : ℂ) (n : ℕ) : ℂ :=
  c + d * (ev n : ℂ)

@[expose] def negativeSpectralPoint (ev : ℕ → ℝ) (c d : ℂ) (n : ℕ) : ℂ :=
  c - d * (ev n : ℂ)

end

namespace AmmannBeenker

-- Source module: SpectralGeometry.AmmannBeenkerCutProject
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

abbrev Lattice := Fin 4 → ℤ

@[expose] def alpha : ℝ := Real.sqrt 2 / 2

@[expose] def physical (n : Lattice) : ℂ :=
  ⟨n 0 + alpha * (n 1 - n 3), n 2 + alpha * (n 1 + n 3)⟩

@[expose] def internal (n : Lattice) : ℂ :=
  ⟨n 0 - alpha * (n 1 - n 3), -(n 2 : ℝ) + alpha * (n 1 + n 3)⟩

@[expose] def Window (z : ℂ) : Prop :=
  |z.re| < 1 / 2 + alpha ∧ |z.im| < 1 / 2 + alpha ∧
    |z.re + z.im| < 1 + alpha ∧ |z.re - z.im| < 1 + alpha

@[expose] def Admitted (n : Lattice) : Prop := Window (internal n)

@[expose] def Vertex := {n : Lattice // Admitted n}

instance : DecidableEq Vertex := Classical.decEq _

@[expose] def position (v : Vertex) : ℂ := physical v.val

@[expose] def basis (i : Fin 4) : Lattice := Pi.single i 1

theorem finite_norm_sublevel (R : ℝ) : {v : Vertex | ‖position v‖ ≤ R}.Finite := by
  sorry

-- Source module: SpectralGeometry.AmmannBeenkerGraph
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

abbrev Color := Fin 4 × Fin 2

@[expose] def latticeMate (c : Color) (n : Lattice) : Lattice :=
  n + if n c.1 % 2 = (c.2 : ℕ) then basis c.1 else -basis c.1

@[expose] def mate (c : Color) (v : Vertex) : Vertex :=
  by
    classical
    exact if h : Admitted (latticeMate c v.val) then ⟨latticeMate c v.val, h⟩ else v

theorem mate_involutive (c : Color) : Function.Involutive (mate c) := by
  sorry

@[expose] def matching (c : Color) : Vertex ≃ Vertex :=
  ⟨mate c, mate c, mate_involutive c, mate_involutive c⟩

@[expose] def matching8 (i : Fin 8) : Vertex ≃ Vertex :=
  matching (finProdFinEquiv.symm i)

@[expose] def interaction : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  infiniteLocalMatchingLaplacian 8 matching8 (fun _ => 1 / 16)

-- Source module: SpectralGeometry.AmmannBeenkerOperator
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

@[expose] def potential (v : Vertex) : ℝ := 1 + ‖position v‖ ^ 2

theorem potential_proper (R : ℝ) : (infiniteOnsiteLowEnergyTiles potential R).Finite := by
  sorry

@[expose] def sector : Finset Vertex := (finite_norm_sublevel 2).toFinset

-- Source module: SpectralGeometry.AmmannBeenkerSpectralProducts
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

theorem exists_nine_level_fullProducts (c d : ℂ) (hd : d ≠ 0) :
    ∃ ev : ℕ → ℝ, Monotone ev ∧
      Nonempty (DomainEigenbasis (infiniteOnsiteDomain potential)
        (onsitePlusBounded potential interaction) ev) ∧
      (∀ n : ℕ, 1 ≤ ev n) ∧
      (∀ n : ℕ, n < 9 → ev n ≤ 3) ∧
      Summable (fun n => 1 / (ev n) ^ 2) ∧
      HasExactFullSpectralProduct potential interaction potential_proper ev c d ∧
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ 4 →
        ∃ μ : ℕ → ℝ, Monotone μ ∧
          Nonempty (DomainEigenbasis (infiniteOnsiteDomain potential)
            (onsitePlusBounded potential (interaction + τ • finiteSectorProjection sector)) μ) ∧
          (∀ n : ℕ, 1 ≤ μ n) ∧
          Summable (fun n => 1 / (μ n) ^ 2) ∧
          HasExactFullSpectralProduct potential (interaction + τ • finiteSectorProjection sector)
            potential_proper μ c d ∧
          ∀ n : ℕ, n < 9 →
            (τ / 2 ≤ μ n - ev n ∧ μ n - ev n ≤ τ) ∧
            (canonicalProduct ev c d (positiveSpectralPoint ev c d n) = 0 ∧
              canonicalProduct ev c d (negativeSpectralPoint ev c d n) = 0) ∧
            (canonicalProduct μ c d (positiveSpectralPoint μ c d n) = 0 ∧
              canonicalProduct μ c d (negativeSpectralPoint μ c d n) = 0) ∧
            (positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n =
                d * ((μ n - ev n : ℝ) : ℂ) ∧
              negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n =
                -d * ((μ n - ev n : ℝ) : ℂ)) ∧
            ((‖d‖ * (τ / 2) ≤
                ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ ∧
              ‖positiveSpectralPoint μ c d n - positiveSpectralPoint ev c d n‖ ≤ ‖d‖ * τ) ∧
             (‖d‖ * (τ / 2) ≤
                ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ ∧
              ‖negativeSpectralPoint μ c d n - negativeSpectralPoint ev c d n‖ ≤ ‖d‖ * τ)) ∧
            (0 < τ →
              positiveSpectralPoint μ c d n ≠ positiveSpectralPoint ev c d n ∧
              negativeSpectralPoint μ c d n ≠ negativeSpectralPoint ev c d n) := by
  sorry

end AmmannBeenker
end
end SpectralGeometry
