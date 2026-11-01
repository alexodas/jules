module

public import SpectralGeometry.AmmannBeenkerCutProject
public import SpectralGeometry.InfiniteLocalBoundedDegree

public section

/-!
# Coordinate edges and eight involutive matching colors

Edges join admitted lifts differing by a signed standard basis vector.
Direction and coordinate parity give eight matchings. Missing partners
are fixed points, which contribute zero to the matching Laplacian.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

abbrev Color := Fin 4 × Fin 2

@[expose] def latticeMate (c : Color) (n : Lattice) : Lattice :=
  n + if n c.1 % 2 = (c.2 : ℕ) then basis c.1 else -basis c.1

theorem latticeMate_involutive (c : Color) : Function.Involutive (latticeMate c) := by
  intro n
  funext j
  have hp := c.2.isLt
  by_cases hj : j = c.1
  · subst j
    simp only [latticeMate, Pi.add_apply, Pi.single_apply, basis, Pi.neg_apply]
    split_ifs <;> simp_all <;> omega
  · simp [latticeMate, basis, Pi.single_apply, hj, Ne.symm hj]

@[expose] def mate (c : Color) (v : Vertex) : Vertex :=
  if h : Admitted (latticeMate c v.val) then ⟨latticeMate c v.val, h⟩ else v

theorem mate_involutive (c : Color) : Function.Involutive (mate c) := by
  intro v
  by_cases h : Admitted (latticeMate c v.val)
  · have hh : Admitted (latticeMate c (latticeMate c v.val)) := by
      rw [latticeMate_involutive c]
      exact v.property
    apply Subtype.ext
    simp [mate, h, hh, latticeMate_involutive c]
  · simp [mate, h]

@[expose] def matching (c : Color) : Vertex ≃ Vertex :=
  ⟨mate c, mate c, mate_involutive c, mate_involutive c⟩

/-- Geometric edge relation, defined independently of the matching colors. -/
@[expose] def Adjacent (v w : Vertex) : Prop :=
  ∃ i : Fin 4, w.val = v.val + basis i ∨ w.val = v.val - basis i

theorem adjacent_irrefl (v : Vertex) : ¬ Adjacent v v := by
  rintro ⟨i, h | h⟩ <;> have hi := congrFun h i <;>
    simp [basis, Pi.single_apply] at hi

theorem adjacent_symm {v w : Vertex} (h : Adjacent v w) : Adjacent w v := by
  rcases h with ⟨i, h | h⟩
  · exact ⟨i, Or.inr (by rw [h]; abel)⟩
  · exact ⟨i, Or.inl (by rw [h]; abel)⟩

theorem adjacent_unit_length {v w : Vertex} (h : Adjacent v w) :
    dist (position v) (position w) = 1 := by
  rw [dist_comm, dist_eq_norm]
  change ‖physical w.val - physical v.val‖ = 1
  rcases h with ⟨i, h | h⟩
  · rw [h, physical_add, add_sub_cancel_left]
    exact physical_basis_norm i
  · rw [h, physical_sub, sub_sub_cancel_left, norm_neg]
    exact physical_basis_norm i

theorem mate_adjacent {c : Color} {v : Vertex} (h : mate c v ≠ v) :
    Adjacent v (mate c v) := by
  unfold mate at h ⊢
  split_ifs with ha
  · refine ⟨c.1, ?_⟩
    unfold latticeMate
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (by simp [sub_eq_add_neg])
  · exact (h rfl).elim

theorem adjacent_exists_mate {v w : Vertex} (h : Adjacent v w) :
    ∃ c : Color, mate c v = w := by
  rcases h with ⟨i, h | h⟩
  · let p : Fin 2 := ⟨(v.val i % 2).toNat, by omega⟩
    have hp : v.val i % 2 = (p : ℕ) := by dsimp [p]; omega
    have hm : latticeMate (i, p) v.val = w.val := by
      simp [latticeMate, hp, h]
    refine ⟨(i, p), ?_⟩
    have ha : Admitted (latticeMate (i, p) v.val) := hm ▸ w.property
    apply Subtype.ext
    simpa [mate, ha] using hm
  · let p : Fin 2 := ⟨((v.val i + 1) % 2).toNat, by omega⟩
    have hp : v.val i % 2 ≠ (p : ℕ) := by dsimp [p]; omega
    have hm : latticeMate (i, p) v.val = w.val := by
      simp [latticeMate, hp, h, sub_eq_add_neg]
    refine ⟨(i, p), ?_⟩
    have ha : Admitted (latticeMate (i, p) v.val) := hm ▸ w.property
    apply Subtype.ext
    simpa [mate, ha] using hm

@[expose] def neighbors (v : Vertex) : Finset Vertex :=
  (Finset.univ.image (fun c : Color => mate c v)).erase v

theorem mem_neighbors_iff (v w : Vertex) : w ∈ neighbors v ↔ Adjacent v w := by
  simp only [neighbors, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, c, hc⟩
    simpa [hc] using mate_adjacent (c := c) (v := v) (by simpa [hc] using hne)
  · intro h
    refine ⟨?_, adjacent_exists_mate h⟩
    rintro rfl
    exact adjacent_irrefl v h

theorem neighbors_card_le (v : Vertex) : (neighbors v).card ≤ 8 := by
  exact (Finset.card_erase_le).trans (Finset.card_image_le.trans (by simp [Color]))

@[expose] def matching8 (i : Fin 8) : Vertex ≃ Vertex :=
  matching (finProdFinEquiv.symm i)

theorem matching8_involutive (i : Fin 8) (v : Vertex) : matching8 i (matching8 i v) = v :=
  mate_involutive _ _

/-- The concrete interaction with the roadmap's edge weight 1/16. -/
@[expose] def interaction : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  infiniteLocalMatchingLaplacian 8 matching8 (fun _ => 1 / 16)

theorem interaction_norm_le : ‖interaction‖ ≤ 1 := by
  have h := infiniteLocalMatchingLaplacian_norm_le 8 matching8 (fun _ => 1 / 16)
    (1 / 16) (by norm_num) (by intro _; norm_num) (by intro _; rfl)
  norm_num at h
  exact h

theorem interaction_nonneg (x : TileHilbert Vertex) : 0 ≤ inner ℝ x (interaction x) :=
  infiniteLocalMatchingLaplacian_energy_nonneg 8 matching8 (fun _ => 1 / 16)
    (by intro _; norm_num) x

theorem interaction_symmetric (x y : TileHilbert Vertex) :
    inner ℝ (interaction x) y = inner ℝ x (interaction y) :=
  (infiniteLocalMatchingLaplacian_symmetric 8 matching8 (fun _ => 1 / 16)
    matching8_involutive x y).symm

end
end SpectralGeometry.AmmannBeenker
