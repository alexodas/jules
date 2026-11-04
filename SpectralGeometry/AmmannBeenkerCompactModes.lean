module

public import SpectralGeometry.AmmannBeenkerOperator

public section

/-!
# Compact states in the confined octagonal vertex model

The alternating eight-site states are the local type-A and type-B patterns
of M. O. Oktel, Phys. Rev. B 104, 014204 (2021), Section IV.
Here they are considered for the already defined positive graph Laplacian
with quadratic onsite confinement, rather than the pure hopping operator.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- A lattice coordinate contributes a unit state when it is admitted,
and the zero state otherwise. This is only a finite-support convenience. -/
@[expose] def latticeSingle (n : Lattice) : TileHilbert Vertex :=
  if h : Admitted n then lp.single (α := Vertex) (E := fun _ => ℝ) (2 : ENNReal) (⟨n, h⟩ : Vertex) 1 else 0

theorem latticeSingle_of_admitted (n : Lattice) (h : Admitted n) :
    latticeSingle n = lp.single (α := Vertex) (E := fun _ => ℝ) (2 : ENNReal) (⟨n, h⟩ : Vertex) 1 := by
  simp [latticeSingle, h]

@[simp] theorem latticeSingle_val (v : Vertex) :
    latticeSingle v.val = lp.single (α := Vertex) (E := fun _ => ℝ) (2 : ENNReal) v 1 := by
  exact latticeSingle_of_admitted v.val v.property

theorem latticeSingle_mem_domain (n : Lattice) :
    latticeSingle n ∈ infiniteOnsiteDomain potential := by
  unfold latticeSingle
  split_ifs
  · exact infiniteOnsiteDomain_single _ _ _
  · exact Submodule.zero_mem _

private theorem matching_single (c : Color) (v : Vertex) :
    infiniteMatchingLaplacian (matching c) (lp.single (α := Vertex) (E := fun _ => ℝ) (2 : ENNReal) v 1) =
      lp.single (α := Vertex) (E := fun _ => ℝ) (2 : ENNReal) v 1 - lp.single (α := Vertex) (E := fun _ => ℝ) (2 : ENNReal) (mate c v) 1 := by
  apply lp.ext
  funext w
  have he : mate c w = v ↔ w = mate c v := by
    constructor
    · intro h
      exact (mate_involutive c w).symm.trans (congrArg (mate c) h)
    · intro h
      rw [h, mate_involutive c v]
  rw [infiniteMatchingLaplacian_apply]
  change _ - lp.single (α := Vertex) (E := fun _ => ℝ) (2 : ENNReal) v 1 (mate c w) = _
  simp [lp.single_apply, Pi.single_apply, he]

/-- Finite coordinate formula for the action on a single site. -/
theorem interaction_latticeSingle (n : Lattice) (hn : Admitted n) :
    interaction (latticeSingle n) = (1 / 16 : ℝ) •
      ∑ c : Color, (latticeSingle n -
        if Admitted (latticeMate c n) then latticeSingle (latticeMate c n)
        else latticeSingle n) := by
  let v : Vertex := ⟨n, hn⟩
  have hsum := finProdFinEquiv.symm.sum_comp
    (fun c : Color => infiniteMatchingLaplacian (matching c)
      (lp.single (α := Vertex) (E := fun _ => ℝ) (2 : ENNReal) v 1))
  rw [latticeSingle_of_admitted n hn]
  simp only [interaction, infiniteLocalMatchingLaplacian,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    matching8, ← Finset.smul_sum]
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [matching_single]
  by_cases hc : Admitted (latticeMate c n)
  · simp [mate, v, hc, latticeSingle_of_admitted n hn,
      latticeSingle_of_admitted _ hc]
  · simp [mate, v, hc, latticeSingle_of_admitted n hn]


private theorem alpha_local_bounds : (707 / 1000 : ℝ) < alpha ∧ alpha < 708 / 1000 := by
  have h := alpha_sq
  have hp := alpha_bounds.1
  constructor <;> nlinarith

-- All local admission decisions are independently proved in Lean.

@[simp] private theorem local_admission_0 : ¬ Admitted (![-2, -1, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_1 : ¬ Admitted (![-2, 0, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_2 : ¬ Admitted (![-2, 0, 0, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_3 : ¬ Admitted (![-1, -2, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_4 : Admitted (![-1, -1, -1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_5 : ¬ Admitted (![-1, -1, 0, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_6 : Admitted (![-1, -1, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_7 : Admitted (![-1, -1, 0, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_8 : ¬ Admitted (![-1, -1, 1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_9 : ¬ Admitted (![-1, 0, -1, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_10 : ¬ Admitted (![-1, 0, -1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_11 : ¬ Admitted (![-1, 0, -1, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_12 : ¬ Admitted (![-1, 0, 0, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_13 : Admitted (![-1, 0, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_14 : Admitted (![-1, 0, 0, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_15 : ¬ Admitted (![-1, 0, 0, 2] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_16 : ¬ Admitted (![-1, 0, 1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_17 : Admitted (![-1, 0, 1, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_18 : ¬ Admitted (![-1, 1, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_19 : ¬ Admitted (![-1, 1, 0, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_20 : ¬ Admitted (![-1, 1, 1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_21 : ¬ Admitted (![0, -2, -1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_22 : ¬ Admitted (![0, -2, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_23 : ¬ Admitted (![0, -1, -2, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_24 : Admitted (![0, -1, -1, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_25 : Admitted (![0, -1, -1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_26 : ¬ Admitted (![0, -1, -1, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_27 : ¬ Admitted (![0, -1, 0, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_28 : Admitted (![0, -1, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_29 : ¬ Admitted (![0, -1, 0, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_30 : ¬ Admitted (![0, -1, 1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_31 : ¬ Admitted (![0, -1, 1, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_32 : ¬ Admitted (![0, 0, -2, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_33 : ¬ Admitted (![0, 0, -2, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_34 : ¬ Admitted (![0, 0, -1, -2] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_35 : Admitted (![0, 0, -1, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_36 : Admitted (![0, 0, -1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_37 : ¬ Admitted (![0, 0, -1, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_38 : ¬ Admitted (![0, 0, 0, -2] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_39 : Admitted (![0, 0, 0, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_40 : Admitted (![0, 0, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_41 : Admitted (![0, 0, 0, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_42 : ¬ Admitted (![0, 0, 0, 2] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_43 : ¬ Admitted (![0, 0, 1, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_44 : Admitted (![0, 0, 1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_45 : Admitted (![0, 0, 1, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_46 : ¬ Admitted (![0, 0, 1, 2] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_47 : ¬ Admitted (![0, 0, 2, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_48 : ¬ Admitted (![0, 0, 2, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_49 : ¬ Admitted (![0, 1, -1, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_50 : ¬ Admitted (![0, 1, -1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_51 : ¬ Admitted (![0, 1, 0, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_52 : Admitted (![0, 1, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_53 : ¬ Admitted (![0, 1, 0, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_54 : ¬ Admitted (![0, 1, 1, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_55 : Admitted (![0, 1, 1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_56 : Admitted (![0, 1, 1, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_57 : ¬ Admitted (![0, 1, 2, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_58 : ¬ Admitted (![0, 2, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_59 : ¬ Admitted (![0, 2, 1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_60 : ¬ Admitted (![1, -1, -1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_61 : ¬ Admitted (![1, -1, 0, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_62 : ¬ Admitted (![1, -1, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_63 : Admitted (![1, 0, -1, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_64 : ¬ Admitted (![1, 0, -1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_65 : ¬ Admitted (![1, 0, 0, -2] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_66 : Admitted (![1, 0, 0, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_67 : Admitted (![1, 0, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_68 : ¬ Admitted (![1, 0, 0, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_69 : ¬ Admitted (![1, 0, 1, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_70 : ¬ Admitted (![1, 0, 1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_71 : ¬ Admitted (![1, 0, 1, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_72 : ¬ Admitted (![1, 1, -1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_73 : Admitted (![1, 1, 0, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_74 : Admitted (![1, 1, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_75 : ¬ Admitted (![1, 1, 0, 1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_76 : Admitted (![1, 1, 1, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  norm_num [Admitted, Window, internal, abs_lt]
  repeat' constructor
  all_goals linarith

@[simp] private theorem local_admission_77 : ¬ Admitted (![1, 2, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_78 : ¬ Admitted (![2, 0, 0, -1] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_79 : ¬ Admitted (![2, 0, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

@[simp] private theorem local_admission_80 : ¬ Admitted (![2, 1, 0, 0] : Lattice) := by
  have hl := alpha_local_bounds.1
  have hu := alpha_local_bounds.2
  intro h
  simp only [Admitted, Window, internal, abs_lt] at h
  norm_num at h
  all_goals linarith

/-- Alternating compact type-A state on the centered eight-site ring. -/
@[expose] def compactA : TileHilbert Vertex :=
  latticeSingle ![1, 0, 0, 0]
    - latticeSingle ![0, 1, 0, 0]
    + latticeSingle ![0, 0, 1, 0]
    - latticeSingle ![0, 0, 0, 1]
    + latticeSingle ![-1, 0, 0, 0]
    - latticeSingle ![0, -1, 0, 0]
    + latticeSingle ![0, 0, -1, 0]
    - latticeSingle ![0, 0, 0, -1]

theorem compactA_mem_domain : compactA ∈ infiniteOnsiteDomain potential := by
  unfold compactA
  repeat' first | apply Submodule.add_mem | apply Submodule.sub_mem
  all_goals exact latticeSingle_mem_domain _

private theorem interaction_A_0 : interaction (latticeSingle ![1, 0, 0, 0]) =
    (1 / 16 : ℝ) • (3 • latticeSingle ![1, 0, 0, 0]
      - latticeSingle ![0, 0, 0, 0]
      - latticeSingle ![1, 1, 0, 0]
      - latticeSingle ![1, 0, 0, -1]) := by
  rw [interaction_latticeSingle _ local_admission_67]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_A_1 : interaction (latticeSingle ![0, 1, 0, 0]) =
    (1 / 16 : ℝ) • (3 • latticeSingle ![0, 1, 0, 0]
      - latticeSingle ![1, 1, 0, 0]
      - latticeSingle ![0, 0, 0, 0]
      - latticeSingle ![0, 1, 1, 0]) := by
  rw [interaction_latticeSingle _ local_admission_52]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_A_2 : interaction (latticeSingle ![0, 0, 1, 0]) =
    (1 / 16 : ℝ) • (3 • latticeSingle ![0, 0, 1, 0]
      - latticeSingle ![0, 1, 1, 0]
      - latticeSingle ![0, 0, 0, 0]
      - latticeSingle ![0, 0, 1, 1]) := by
  rw [interaction_latticeSingle _ local_admission_44]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_A_3 : interaction (latticeSingle ![0, 0, 0, 1]) =
    (1 / 16 : ℝ) • (3 • latticeSingle ![0, 0, 0, 1]
      - latticeSingle ![-1, 0, 0, 1]
      - latticeSingle ![0, 0, 1, 1]
      - latticeSingle ![0, 0, 0, 0]) := by
  rw [interaction_latticeSingle _ local_admission_41]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_A_4 : interaction (latticeSingle ![-1, 0, 0, 0]) =
    (1 / 16 : ℝ) • (3 • latticeSingle ![-1, 0, 0, 0]
      - latticeSingle ![0, 0, 0, 0]
      - latticeSingle ![-1, -1, 0, 0]
      - latticeSingle ![-1, 0, 0, 1]) := by
  rw [interaction_latticeSingle _ local_admission_13]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_A_5 : interaction (latticeSingle ![0, -1, 0, 0]) =
    (1 / 16 : ℝ) • (3 • latticeSingle ![0, -1, 0, 0]
      - latticeSingle ![-1, -1, 0, 0]
      - latticeSingle ![0, 0, 0, 0]
      - latticeSingle ![0, -1, -1, 0]) := by
  rw [interaction_latticeSingle _ local_admission_28]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_A_6 : interaction (latticeSingle ![0, 0, -1, 0]) =
    (1 / 16 : ℝ) • (3 • latticeSingle ![0, 0, -1, 0]
      - latticeSingle ![0, -1, -1, 0]
      - latticeSingle ![0, 0, 0, 0]
      - latticeSingle ![0, 0, -1, -1]) := by
  rw [interaction_latticeSingle _ local_admission_36]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_A_7 : interaction (latticeSingle ![0, 0, 0, -1]) =
    (1 / 16 : ℝ) • (3 • latticeSingle ![0, 0, 0, -1]
      - latticeSingle ![1, 0, 0, -1]
      - latticeSingle ![0, 0, -1, -1]
      - latticeSingle ![0, 0, 0, 0]) := by
  rw [interaction_latticeSingle _ local_admission_39]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

/-- The cancellation is an equality on the entire infinite state space. -/
theorem interaction_compactA : interaction compactA = (3 / 16 : ℝ) • compactA := by
  simp only [compactA, map_add, map_sub, interaction_A_0, interaction_A_1, interaction_A_2, interaction_A_3, interaction_A_4, interaction_A_5, interaction_A_6, interaction_A_7]
  module

/-- Alternating compact type-B state on the centered eight-site ring. -/
@[expose] def compactB : TileHilbert Vertex :=
  latticeSingle ![1, 1, 0, 0]
    - latticeSingle ![0, 1, 1, 0]
    + latticeSingle ![0, 0, 1, 1]
    - latticeSingle ![-1, 0, 0, 1]
    + latticeSingle ![-1, -1, 0, 0]
    - latticeSingle ![0, -1, -1, 0]
    + latticeSingle ![0, 0, -1, -1]
    - latticeSingle ![1, 0, 0, -1]

theorem compactB_mem_domain : compactB ∈ infiniteOnsiteDomain potential := by
  unfold compactB
  repeat' first | apply Submodule.add_mem | apply Submodule.sub_mem
  all_goals exact latticeSingle_mem_domain _

private theorem interaction_B_0 : interaction (latticeSingle ![1, 1, 0, 0]) =
    (1 / 16 : ℝ) • (4 • latticeSingle ![1, 1, 0, 0]
      - latticeSingle ![0, 1, 0, 0]
      - latticeSingle ![1, 0, 0, 0]
      - latticeSingle ![1, 1, 1, 0]
      - latticeSingle ![1, 1, 0, -1]) := by
  rw [interaction_latticeSingle _ local_admission_74]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_B_1 : interaction (latticeSingle ![0, 1, 1, 0]) =
    (1 / 16 : ℝ) • (4 • latticeSingle ![0, 1, 1, 0]
      - latticeSingle ![1, 1, 1, 0]
      - latticeSingle ![0, 0, 1, 0]
      - latticeSingle ![0, 1, 0, 0]
      - latticeSingle ![0, 1, 1, 1]) := by
  rw [interaction_latticeSingle _ local_admission_55]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_B_2 : interaction (latticeSingle ![0, 0, 1, 1]) =
    (1 / 16 : ℝ) • (4 • latticeSingle ![0, 0, 1, 1]
      - latticeSingle ![-1, 0, 1, 1]
      - latticeSingle ![0, 1, 1, 1]
      - latticeSingle ![0, 0, 0, 1]
      - latticeSingle ![0, 0, 1, 0]) := by
  rw [interaction_latticeSingle _ local_admission_45]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_B_3 : interaction (latticeSingle ![-1, 0, 0, 1]) =
    (1 / 16 : ℝ) • (4 • latticeSingle ![-1, 0, 0, 1]
      - latticeSingle ![0, 0, 0, 1]
      - latticeSingle ![-1, -1, 0, 1]
      - latticeSingle ![-1, 0, 1, 1]
      - latticeSingle ![-1, 0, 0, 0]) := by
  rw [interaction_latticeSingle _ local_admission_14]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_B_4 : interaction (latticeSingle ![-1, -1, 0, 0]) =
    (1 / 16 : ℝ) • (4 • latticeSingle ![-1, -1, 0, 0]
      - latticeSingle ![0, -1, 0, 0]
      - latticeSingle ![-1, 0, 0, 0]
      - latticeSingle ![-1, -1, -1, 0]
      - latticeSingle ![-1, -1, 0, 1]) := by
  rw [interaction_latticeSingle _ local_admission_6]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_B_5 : interaction (latticeSingle ![0, -1, -1, 0]) =
    (1 / 16 : ℝ) • (4 • latticeSingle ![0, -1, -1, 0]
      - latticeSingle ![-1, -1, -1, 0]
      - latticeSingle ![0, 0, -1, 0]
      - latticeSingle ![0, -1, 0, 0]
      - latticeSingle ![0, -1, -1, -1]) := by
  rw [interaction_latticeSingle _ local_admission_25]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_B_6 : interaction (latticeSingle ![0, 0, -1, -1]) =
    (1 / 16 : ℝ) • (4 • latticeSingle ![0, 0, -1, -1]
      - latticeSingle ![1, 0, -1, -1]
      - latticeSingle ![0, -1, -1, -1]
      - latticeSingle ![0, 0, 0, -1]
      - latticeSingle ![0, 0, -1, 0]) := by
  rw [interaction_latticeSingle _ local_admission_35]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

private theorem interaction_B_7 : interaction (latticeSingle ![1, 0, 0, -1]) =
    (1 / 16 : ℝ) • (4 • latticeSingle ![1, 0, 0, -1]
      - latticeSingle ![0, 0, 0, -1]
      - latticeSingle ![1, 1, 0, -1]
      - latticeSingle ![1, 0, -1, -1]
      - latticeSingle ![1, 0, 0, 0]) := by
  rw [interaction_latticeSingle _ local_admission_66]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, latticeMate, basis,
    Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply]
  module

/-- The cancellation is an equality on the entire infinite state space. -/
theorem interaction_compactB : interaction compactB = (4 / 16 : ℝ) • compactB := by
  simp only [compactB, map_add, map_sub, interaction_B_0, interaction_B_1, interaction_B_2, interaction_B_3, interaction_B_4, interaction_B_5, interaction_B_6, interaction_B_7]
  module

end
end SpectralGeometry.AmmannBeenker
