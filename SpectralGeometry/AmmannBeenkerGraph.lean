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
    simp only [latticeMate, Pi.add_apply, ite_apply, basis, Pi.single_apply, Pi.neg_apply]
    split_ifs <;> simp_all <;> omega
  · simp [latticeMate, ite_apply, basis, hj]

theorem latticeMate_color_injective (n : Lattice) :
    Function.Injective (fun c => latticeMate c n) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have hp := p.isLt
  have hq := q.isLt
  have hi : i = j := by
    by_contra hij
    have he := congrFun h i
    simp [latticeMate, ite_apply, basis, hij] at he
    split_ifs at he; omega
  subst j
  have he := congrFun h i
  simp only [latticeMate, Pi.add_apply, ite_apply, basis, Pi.single_apply,
    Pi.neg_apply] at he
  have hpq : p = q := by
    apply Fin.ext
    split_ifs at he <;> omega
  subst q
  rfl

@[expose] def mate (c : Color) (v : Vertex) : Vertex :=
  by
    classical
    exact if h : Admitted (latticeMate c v.val) then ⟨latticeMate c v.val, h⟩ else v

theorem mate_involutive (c : Color) : Function.Involutive (mate c) := by
  intro v
  by_cases h : Admitted (latticeMate c v.val)
  · have hh : Admitted (latticeMate c (latticeMate c v.val)) := by
      rw [latticeMate_involutive c]
      exact v.property
    apply Subtype.ext
    simp [mate, h, hh]
    exact latticeMate_involutive c v.val
  · simp [mate, h]

theorem mate_color_unique {v : Vertex} {c d : Color}
    (hne : mate c v ≠ v) (heq : mate c v = mate d v) : c = d := by
  have hc : Admitted (latticeMate c v.val) := by
    by_contra h
    exact hne (by simp [mate, h])
  have hd : Admitted (latticeMate d v.val) := by
    by_contra h
    exact hne (by rw [heq]; simp [mate, h])
  apply latticeMate_color_injective v.val
  have h := congrArg Subtype.val heq
  simpa [mate, hc, hd] using h

theorem mate_origin_norm (c : Color) : ‖position (mate c origin)‖ = 1 := by
  rcases c with ⟨i, p⟩
  fin_cases p <;>
    simp [position, mate, origin, latticeMate, basis_admitted,
      admitted_neg, physical_basis_norm]

theorem mate_origin_ne (c : Color) : mate c origin ≠ origin := by
  intro h
  have hn := mate_origin_norm c
  rw [h] at hn
  simp [position, origin] at hn

theorem mate_origin_injective : Function.Injective (fun c => mate c origin) :=
  fun c _ h => mate_color_unique (mate_origin_ne c) h

@[expose] def matching (c : Color) : Vertex ≃ Vertex :=
  ⟨mate c, mate c, mate_involutive c, mate_involutive c⟩

/-- Geometric edge relation, defined independently of the matching colors. -/
@[expose] def Adjacent (v w : Vertex) : Prop :=
  ∃ i : Fin 4, w.val = v.val + basis i ∨ w.val = v.val - basis i

theorem adjacent_irrefl (v : Vertex) : ¬ Adjacent v v := by
  rintro ⟨i, h | h⟩
  · have hi := congrFun h i
    simp [basis] at hi
  · have hi := congrFun h i
    simp [basis] at hi
    omega

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
  by_cases ha : Admitted (latticeMate c v.val)
  · have he : (mate c v).val = latticeMate c v.val := by simp [mate, ha]
    refine ⟨c.1, ?_⟩
    rw [he]
    unfold latticeMate
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (by simp [sub_eq_add_neg])
  · exact (h (by simp [mate, ha])).elim

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
    intro heq
    subst w
    exact adjacent_irrefl v h

theorem neighbors_card_le (v : Vertex) : (neighbors v).card ≤ 8 := by
  exact (Finset.card_erase_le).trans (Finset.card_image_le.trans (by simp [Color]))

/-- The origin has exactly eight distinct neighbors, all at unit distance. -/
theorem origin_neighbors_card : (neighbors origin).card = 8 := by
  have h : origin ∉ Finset.univ.image (fun c : Color => mate c origin) := by
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] using mate_origin_ne
  rw [neighbors, Finset.erase_eq_of_notMem h,
    Finset.card_image_of_injective _ mate_origin_injective]
  simp [Color]

@[expose] def matching8 (i : Fin 8) : Vertex ≃ Vertex :=
  matching (finProdFinEquiv.symm i)

theorem matching8_involutive (i : Fin 8) (v : Vertex) : matching8 i (matching8 i v) = v :=
  mate_involutive (finProdFinEquiv.symm i) v

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


theorem sum_colors_eq_neighbors (f : Vertex → ℝ) (v : Vertex) :
    (∑ c : Color, (f v - f (mate c v))) = ∑ w ∈ neighbors v, (f v - f w) := by
  classical
  let t : Finset Color := Finset.univ.filter (fun c => mate c v ≠ v)
  have hi : t.image (fun c => mate c v) = neighbors v := by
    ext w
    simp only [t, neighbors, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨hc, c, rfl⟩
    · rintro ⟨hw, c, rfl⟩
      exact ⟨c, hw, rfl⟩
  have hs : (∑ c : Color, (f v - f (mate c v))) = ∑ c ∈ t, (f v - f (mate c v)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : mate c v = v <;> simp [h]
  rw [hs, ← hi, Finset.sum_image]
  intro c hc d _ h
  exact mate_color_unique (Finset.mem_filter.mp hc).2 h

theorem interaction_apply (f : TileHilbert Vertex) (v : Vertex) :
    interaction f v = (1 / 16 : ℝ) * ∑ w ∈ neighbors v, (f v - f w) := by
  have he : (∑ i : Fin 8, (f v - f (matching8 i v))) =
      ∑ c : Color, (f v - f (mate c v)) :=
    (finProdFinEquiv.symm.sum_comp (fun c : Color => f v - f (mate c v)))
  simp only [interaction, infiniteLocalMatchingLaplacian, sum_apply, smul_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    infiniteMatchingLaplacian_apply]
  rw [← Finset.mul_sum, he, sum_colors_eq_neighbors]


end
end SpectralGeometry.AmmannBeenker
