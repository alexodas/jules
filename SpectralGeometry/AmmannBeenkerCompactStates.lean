module

public import SpectralGeometry.AmmannBeenkerCompactModes

public section

/-!
# Natural-domain compact eigenstates and ring projection

The coordinate cancellations from `AmmannBeenkerCompactModes` are combined
with onsite multiplication, explicit norms and the first-ring projection.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- Keep concrete admitted points at the named vertex type during rewriting. -/
@[expose] def latticeVertex (n : Lattice) (hn : Admitted n) : Vertex := ⟨n, hn⟩

@[simp] theorem latticeVertex_val (n : Lattice) (hn : Admitted n) :
    (latticeVertex n hn).val = n := rfl

@[simp] theorem latticeSingle_apply (n : Lattice) (v : Vertex) :
    latticeSingle n v = if v.val = n then 1 else 0 := by
  by_cases hv : v.val = n
  · rw [ite_eq_left hv, ← hv, latticeSingle_val]
    exact lp.single_apply_self _ _ _
  · rw [ite_eq_right hv]
    by_cases hn : Admitted n
    · rw [latticeSingle_of_admitted n hn]
      exact lp.single_apply_ne _ _ _ (fun h => hv (congrArg Subtype.val h))
    · simp [latticeSingle, hn]

@[expose] def domainLatticeSingle (n : Lattice) : infiniteOnsiteDomain potential :=
  ⟨latticeSingle n, latticeSingle_mem_domain n⟩

theorem onsite_latticeSingle (n : Lattice) :
    infiniteOnsiteOperator potential (domainLatticeSingle n) =
      (1 + ‖physical n‖ ^ 2) • latticeSingle n := by
  apply lp.ext
  funext v
  rw [infiniteOnsiteOperator_apply]
  change potential v * latticeSingle n v = (1 + ‖physical n‖ ^ 2) * latticeSingle n v
  rw [latticeSingle_apply]
  split_ifs with h
  · simp [potential, position, h]
  · simp

theorem projection_latticeSingle (F : Finset Vertex) (n : Lattice) (hn : Admitted n) :
    finiteSectorProjection F (latticeSingle n) =
      if (latticeVertex n hn) ∈ F then latticeSingle n else 0 := by
  rw [latticeSingle_of_admitted n hn]
  by_cases hF : (latticeVertex n hn) ∈ F
  · rw [ite_eq_left hF]
    apply lp.ext
    funext w
    rw [finiteSectorProjection_apply]
    split_ifs with hw
    · rfl
    · have hne : w ≠ (latticeVertex n hn) := by
        intro he
        subst w
        exact hw hF
      exact (lp.single_apply_ne (α := Vertex) (E := fun _ => ℝ)
        (2 : ENNReal) (latticeVertex n hn) 1 hne).symm
  · rw [ite_eq_right hF]
    apply lp.ext
    funext w
    rw [finiteSectorProjection_apply]
    change (if w ∈ F then lp.single (α := Vertex) (E := fun _ => ℝ)
      (2 : ENNReal) (latticeVertex n hn) 1 w else 0) = 0
    split_ifs with hw
    · exact lp.single_apply_ne _ _ _ (by
        intro he
        subst w
        exact hF hw)
    · rfl

theorem mem_neighbors_origin_iff (v : Vertex) :
    v ∈ neighbors origin ↔ ∃ i : Fin 4, v.val = basis i ∨ v.val = -basis i := by
  rw [mem_neighbors_iff origin v]
  simp only [Adjacent, origin, zero_add, zero_sub]

theorem inner_latticeSingle (n : Lattice) (hn : Admitted n) (x : TileHilbert Vertex) :
    inner ℝ (latticeSingle n) x = x (latticeVertex n hn) := by
  rw [latticeSingle_of_admitted n hn]
  change inner ℝ (lp.single (α := Vertex) (E := fun _ => ℝ)
    (2 : ENNReal) (⟨n, hn⟩ : Vertex) 1) x = x (⟨n, hn⟩ : Vertex)
  simpa using (lp.inner_single_left (𝕜 := ℝ) (G := fun _ : Vertex => ℝ)
    (⟨n, hn⟩ : Vertex) (1 : ℝ) x)


private theorem admitted_A_0 : Admitted (![1, 0, 0, 0] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_A_0 : ‖physical (![1, 0, 0, 0] : Lattice)‖ ^ 2 = 1 := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_A_1 : Admitted (![0, 1, 0, 0] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_A_1 : ‖physical (![0, 1, 0, 0] : Lattice)‖ ^ 2 = 1 := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_A_2 : Admitted (![0, 0, 1, 0] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_A_2 : ‖physical (![0, 0, 1, 0] : Lattice)‖ ^ 2 = 1 := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_A_3 : Admitted (![0, 0, 0, 1] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_A_3 : ‖physical (![0, 0, 0, 1] : Lattice)‖ ^ 2 = 1 := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_A_4 : Admitted (![-1, 0, 0, 0] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_A_4 : ‖physical (![-1, 0, 0, 0] : Lattice)‖ ^ 2 = 1 := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_A_5 : Admitted (![0, -1, 0, 0] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_A_5 : ‖physical (![0, -1, 0, 0] : Lattice)‖ ^ 2 = 1 := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_A_6 : Admitted (![0, 0, -1, 0] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_A_6 : ‖physical (![0, 0, -1, 0] : Lattice)‖ ^ 2 = 1 := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_A_7 : Admitted (![0, 0, 0, -1] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_A_7 : ‖physical (![0, 0, 0, -1] : Lattice)‖ ^ 2 = 1 := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

@[expose] def domainCompactA : infiniteOnsiteDomain potential :=
  ⟨compactA, compactA_mem_domain⟩

theorem onsite_compactA : infiniteOnsiteOperator potential domainCompactA =
    (2 : ℝ) • compactA := by
  have he : domainCompactA =
      domainLatticeSingle ![1, 0, 0, 0]
        - domainLatticeSingle ![0, 1, 0, 0]
        + domainLatticeSingle ![0, 0, 1, 0]
        - domainLatticeSingle ![0, 0, 0, 1]
        + domainLatticeSingle ![-1, 0, 0, 0]
        - domainLatticeSingle ![0, -1, 0, 0]
        + domainLatticeSingle ![0, 0, -1, 0]
        - domainLatticeSingle ![0, 0, 0, -1] := by
    apply Subtype.ext
    rfl
  rw [he]
  simp only [map_add, map_sub, onsite_latticeSingle,
    norm_A_0, norm_A_1, norm_A_2, norm_A_3, norm_A_4, norm_A_5, norm_A_6, norm_A_7, compactA]
  norm_num
  module

/-- Exact compact eigenvector for the infinite confined operator. -/
theorem confined_compactA :
    onsitePlusBounded potential interaction domainCompactA =
      (35 / 16 : ℝ) • compactA := by
  rw [onsitePlusBounded_apply, onsite_compactA]
  change (2 : ℝ) • compactA + interaction compactA = _
  rw [interaction_compactA]
  module

private theorem admitted_B_0 : Admitted (![1, 1, 0, 0] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_B_0 : ‖physical (![1, 1, 0, 0] : Lattice)‖ ^ 2 = 2 + 2 * alpha := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_B_1 : Admitted (![0, 1, 1, 0] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_B_1 : ‖physical (![0, 1, 1, 0] : Lattice)‖ ^ 2 = 2 + 2 * alpha := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_B_2 : Admitted (![0, 0, 1, 1] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_B_2 : ‖physical (![0, 0, 1, 1] : Lattice)‖ ^ 2 = 2 + 2 * alpha := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_B_3 : Admitted (![-1, 0, 0, 1] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_B_3 : ‖physical (![-1, 0, 0, 1] : Lattice)‖ ^ 2 = 2 + 2 * alpha := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_B_4 : Admitted (![-1, -1, 0, 0] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_B_4 : ‖physical (![-1, -1, 0, 0] : Lattice)‖ ^ 2 = 2 + 2 * alpha := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_B_5 : Admitted (![0, -1, -1, 0] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_B_5 : ‖physical (![0, -1, -1, 0] : Lattice)‖ ^ 2 = 2 + 2 * alpha := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_B_6 : Admitted (![0, 0, -1, -1] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_B_6 : ‖physical (![0, 0, -1, -1] : Lattice)‖ ^ 2 = 2 + 2 * alpha := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

private theorem admitted_B_7 : Admitted (![1, 0, 0, -1] : Lattice) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

private theorem norm_B_7 : ‖physical (![1, 0, 0, -1] : Lattice)‖ ^ 2 = 2 + 2 * alpha := by
  norm_num [physical, Complex.sq_norm, Complex.normSq_apply]
  all_goals nlinarith [alpha_sq]

@[expose] def domainCompactB : infiniteOnsiteDomain potential :=
  ⟨compactB, compactB_mem_domain⟩

theorem onsite_compactB : infiniteOnsiteOperator potential domainCompactB =
    (3 + 2 * alpha : ℝ) • compactB := by
  have he : domainCompactB =
      domainLatticeSingle ![1, 1, 0, 0]
        - domainLatticeSingle ![0, 1, 1, 0]
        + domainLatticeSingle ![0, 0, 1, 1]
        - domainLatticeSingle ![-1, 0, 0, 1]
        + domainLatticeSingle ![-1, -1, 0, 0]
        - domainLatticeSingle ![0, -1, -1, 0]
        + domainLatticeSingle ![0, 0, -1, -1]
        - domainLatticeSingle ![1, 0, 0, -1] := by
    apply Subtype.ext
    rfl
  rw [he]
  simp only [map_add, map_sub, onsite_latticeSingle,
    norm_B_0, norm_B_1, norm_B_2, norm_B_3, norm_B_4, norm_B_5, norm_B_6, norm_B_7, compactB]
  module

/-- Exact compact eigenvector for the infinite confined operator. -/
theorem confined_compactB :
    onsitePlusBounded potential interaction domainCompactB =
      (13 / 4 + 2 * alpha : ℝ) • compactB := by
  rw [onsitePlusBounded_apply, onsite_compactB]
  change (3 + 2 * alpha : ℝ) • compactB + interaction compactB = _
  rw [interaction_compactB]
  module

theorem compactSiteA_admitted : Admitted (![1, 0, 0, 0] : Lattice) := admitted_A_0
theorem compactSiteB_admitted : Admitted (![1, 1, 0, 0] : Lattice) := admitted_B_0

/-- Endpoints of an actual edge joining the two compact rings. -/
@[expose] def compactSiteA : Vertex := latticeVertex ![1, 0, 0, 0] compactSiteA_admitted
@[expose] def compactSiteB : Vertex := latticeVertex ![1, 1, 0, 0] compactSiteB_admitted

theorem compactSites_adjacent : Adjacent compactSiteA compactSiteB := by
  refine ⟨1, Or.inl ?_⟩
  ext i
  fin_cases i <;> norm_num [compactSiteA, compactSiteB, basis, Pi.single,
    Matrix.vecHead, Matrix.vecTail, Function.update_apply]

@[simp] theorem compactA_siteA : compactA compactSiteA = 1 := by
  norm_num [compactA, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
    latticeSingle_apply, compactSiteA, funext_iff, Fin.forall_fin_succ]

@[simp] theorem compactA_siteB : compactA compactSiteB = 0 := by
  norm_num [compactA, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
    latticeSingle_apply, compactSiteB, funext_iff, Fin.forall_fin_succ]

@[simp] theorem compactB_siteA : compactB compactSiteA = 0 := by
  norm_num [compactB, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
    latticeSingle_apply, compactSiteA, funext_iff, Fin.forall_fin_succ]

@[simp] theorem compactB_siteB : compactB compactSiteB = 1 := by
  norm_num [compactB, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
    latticeSingle_apply, compactSiteB, funext_iff, Fin.forall_fin_succ]

theorem compactA_ne_zero : compactA ≠ 0 := by
  intro h
  have hh := congrArg (fun x : TileHilbert Vertex => x compactSiteA) h
  simpa using hh

theorem compactB_ne_zero : compactB ≠ 0 := by
  intro h
  have hh := congrArg (fun x : TileHilbert Vertex => x compactSiteB) h
  simpa using hh

theorem compact_pair_linearIndependent :
    LinearIndependent ℝ ![compactA, compactB] := by
  rw [linearIndependent_fin2]
  constructor
  · simpa using compactB_ne_zero
  · intro r h
    have hh := congrArg (fun x : TileHilbert Vertex => x compactSiteA) h
    simpa using hh

theorem compactA_inner_self : inner ℝ compactA compactA = 8 := by
  change inner ℝ (latticeSingle ![1, 0, 0, 0]
    - latticeSingle ![0, 1, 0, 0]
    + latticeSingle ![0, 0, 1, 0]
    - latticeSingle ![0, 0, 0, 1]
    + latticeSingle ![-1, 0, 0, 0]
    - latticeSingle ![0, -1, 0, 0]
    + latticeSingle ![0, 0, -1, 0]
    - latticeSingle ![0, 0, 0, -1]) compactA = 8
  simp only [inner_add_left, inner_sub_left]
  rw [inner_latticeSingle _ admitted_A_0,
    inner_latticeSingle _ admitted_A_1,
    inner_latticeSingle _ admitted_A_2,
    inner_latticeSingle _ admitted_A_3,
    inner_latticeSingle _ admitted_A_4,
    inner_latticeSingle _ admitted_A_5,
    inner_latticeSingle _ admitted_A_6,
    inner_latticeSingle _ admitted_A_7]
  norm_num [compactA, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
    latticeSingle_apply, funext_iff, Fin.forall_fin_succ]

theorem compactB_inner_self : inner ℝ compactB compactB = 8 := by
  change inner ℝ (latticeSingle ![1, 1, 0, 0]
    - latticeSingle ![0, 1, 1, 0]
    + latticeSingle ![0, 0, 1, 1]
    - latticeSingle ![-1, 0, 0, 1]
    + latticeSingle ![-1, -1, 0, 0]
    - latticeSingle ![0, -1, -1, 0]
    + latticeSingle ![0, 0, -1, -1]
    - latticeSingle ![1, 0, 0, -1]) compactB = 8
  simp only [inner_add_left, inner_sub_left]
  rw [inner_latticeSingle _ admitted_B_0,
    inner_latticeSingle _ admitted_B_1,
    inner_latticeSingle _ admitted_B_2,
    inner_latticeSingle _ admitted_B_3,
    inner_latticeSingle _ admitted_B_4,
    inner_latticeSingle _ admitted_B_5,
    inner_latticeSingle _ admitted_B_6,
    inner_latticeSingle _ admitted_B_7]
  norm_num [compactB, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
    latticeSingle_apply, funext_iff, Fin.forall_fin_succ]

theorem compactA_inner_compactB : inner ℝ compactA compactB = 0 := by
  change inner ℝ (latticeSingle ![1, 0, 0, 0]
    - latticeSingle ![0, 1, 0, 0]
    + latticeSingle ![0, 0, 1, 0]
    - latticeSingle ![0, 0, 0, 1]
    + latticeSingle ![-1, 0, 0, 0]
    - latticeSingle ![0, -1, 0, 0]
    + latticeSingle ![0, 0, -1, 0]
    - latticeSingle ![0, 0, 0, -1]) compactB = 0
  simp only [inner_add_left, inner_sub_left]
  rw [inner_latticeSingle _ admitted_A_0,
    inner_latticeSingle _ admitted_A_1,
    inner_latticeSingle _ admitted_A_2,
    inner_latticeSingle _ admitted_A_3,
    inner_latticeSingle _ admitted_A_4,
    inner_latticeSingle _ admitted_A_5,
    inner_latticeSingle _ admitted_A_6,
    inner_latticeSingle _ admitted_A_7]
  norm_num [compactB, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
    latticeSingle_apply, funext_iff, Fin.forall_fin_succ]

private theorem projection_A_0 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![1, 0, 0, 0]) =
      latticeSingle ![1, 0, 0, 0] := by
  rw [projection_latticeSingle _ _ admitted_A_0]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_A_1 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![0, 1, 0, 0]) =
      latticeSingle ![0, 1, 0, 0] := by
  rw [projection_latticeSingle _ _ admitted_A_1]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_A_2 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![0, 0, 1, 0]) =
      latticeSingle ![0, 0, 1, 0] := by
  rw [projection_latticeSingle _ _ admitted_A_2]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_A_3 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![0, 0, 0, 1]) =
      latticeSingle ![0, 0, 0, 1] := by
  rw [projection_latticeSingle _ _ admitted_A_3]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_A_4 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![-1, 0, 0, 0]) =
      latticeSingle ![-1, 0, 0, 0] := by
  rw [projection_latticeSingle _ _ admitted_A_4]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_A_5 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![0, -1, 0, 0]) =
      latticeSingle ![0, -1, 0, 0] := by
  rw [projection_latticeSingle _ _ admitted_A_5]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_A_6 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![0, 0, -1, 0]) =
      latticeSingle ![0, 0, -1, 0] := by
  rw [projection_latticeSingle _ _ admitted_A_6]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_A_7 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![0, 0, 0, -1]) =
      latticeSingle ![0, 0, 0, -1] := by
  rw [projection_latticeSingle _ _ admitted_A_7]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

theorem projection_compactA :
    finiteSectorProjection (neighbors origin) compactA = compactA := by
  simp only [compactA, map_add, map_sub,
    projection_A_0, projection_A_1, projection_A_2, projection_A_3, projection_A_4, projection_A_5, projection_A_6, projection_A_7]

private theorem projection_B_0 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![1, 1, 0, 0]) =
      0 := by
  rw [projection_latticeSingle _ _ admitted_B_0]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_B_1 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![0, 1, 1, 0]) =
      0 := by
  rw [projection_latticeSingle _ _ admitted_B_1]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_B_2 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![0, 0, 1, 1]) =
      0 := by
  rw [projection_latticeSingle _ _ admitted_B_2]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_B_3 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![-1, 0, 0, 1]) =
      0 := by
  rw [projection_latticeSingle _ _ admitted_B_3]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_B_4 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![-1, -1, 0, 0]) =
      0 := by
  rw [projection_latticeSingle _ _ admitted_B_4]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_B_5 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![0, -1, -1, 0]) =
      0 := by
  rw [projection_latticeSingle _ _ admitted_B_5]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_B_6 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![0, 0, -1, -1]) =
      0 := by
  rw [projection_latticeSingle _ _ admitted_B_6]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

private theorem projection_B_7 :
    finiteSectorProjection (neighbors origin) (latticeSingle ![1, 0, 0, -1]) =
      0 := by
  rw [projection_latticeSingle _ _ admitted_B_7]
  simp only [mem_neighbors_origin_iff]
  norm_num [basis, funext_iff, Fin.exists_fin_succ, Fin.forall_fin_succ,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]

theorem projection_compactB :
    finiteSectorProjection (neighbors origin) compactB = 0 := by
  simp only [compactB, map_add, map_sub,
    projection_B_0, projection_B_1, projection_B_2, projection_B_3, projection_B_4, projection_B_5, projection_B_6, projection_B_7]
  simp

end
end SpectralGeometry.AmmannBeenker
