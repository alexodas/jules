module

public import Mathlib

public section

/-!
# Concrete nine-level finite-sector spectral response

The independent statement specifies the octagonal vertex graph, its matching
Laplacian, natural domain and complete ordered eigenbases. Only supporting
proposition witnesses and the target theorem have Challenge placeholders.
Solution imports the fully proved source; these placeholders are not proofs.
-/

namespace SpectralGeometry

noncomputable section

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

section Matching

variable [DecidableEq Tile]

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

@[expose] noncomputable def infiniteLocalMatchingLaplacian (D : ℕ)
    (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ∑ i : Fin D, w i • infiniteMatchingLaplacian (σ i)

@[expose] def finiteSectorProjection (F : Finset Tile) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  infiniteOnsiteDiagonalContraction (fun t => if t ∈ F then 1 else 0)
    (fun t => by split_ifs <;> norm_num)

@[expose] def onsitePlusBounded (V : Tile → ℝ) (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) :
    infiniteOnsiteDomain V →ₗ[ℝ] TileHilbert Tile :=
  infiniteOnsiteOperator V + B.toLinearMap.comp (infiniteOnsiteDomain V).subtype

end Matching

section Eigenbasis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

structure DomainEigenbasis {ι : Type*} (d : Submodule ℝ H) (A : d →ₗ[ℝ] H)
    (ev : ι → ℝ) where
  basis : HilbertBasis ι ℝ H
  mem_domain : ∀ i, basis i ∈ d
  eigen : ∀ i, A ⟨basis i, mem_domain i⟩ = ev i • basis i

end Eigenbasis

namespace AmmannBeenker

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

theorem finite_norm_sublevel (R : ℝ) : {v : Vertex | ‖position v‖ ≤ R}.Finite := by
  sorry

@[expose] def potential (v : Vertex) : ℝ := 1 + ‖position v‖ ^ 2

@[expose] def sector : Finset Vertex := (finite_norm_sublevel 2).toFinset

theorem exists_nine_level_response :
    ∃ ev : ℕ → ℝ, Monotone ev ∧
      Nonempty (DomainEigenbasis (infiniteOnsiteDomain potential)
        (onsitePlusBounded potential interaction) ev) ∧
      (∀ n : ℕ, 1 ≤ ev n) ∧
      (∀ n : ℕ, n < 9 → ev n ≤ 3) ∧
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ 4 →
        ∃ μ : ℕ → ℝ, Monotone μ ∧
          Nonempty (DomainEigenbasis (infiniteOnsiteDomain potential)
            (onsitePlusBounded potential (interaction + τ • finiteSectorProjection sector)) μ) ∧
          (∀ n : ℕ, 1 ≤ μ n) ∧
          (∀ n : ℕ, n < 9 → τ / 2 ≤ μ n - ev n ∧ μ n - ev n ≤ τ) := by
  sorry

end AmmannBeenker
end
end SpectralGeometry
