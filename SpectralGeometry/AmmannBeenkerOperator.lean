module

public import SpectralGeometry.AmmannBeenkerGraph
public import SpectralGeometry.InfinitePositiveSpectralControl

public section

/-!
# A confined operator on the explicit octagonal vertex graph

The onsite potential is one plus squared physical radius. Properness is
derived from the cut-and-project coordinate bound. The central star has
nine sites of onsite energy at most two, so min-max controls at least nine
full eigenvalues, counting multiplicities. No spectral summability or
canonical-product conclusion is assumed in this module.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

@[expose] def potential (v : Vertex) : ℝ := 1 + ‖position v‖ ^ 2

theorem potential_lower (v : Vertex) : 1 ≤ potential v := by
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem potential_proper (R : ℝ) : (infiniteOnsiteLowEnergyTiles potential R).Finite := by
  apply (finite_norm_sublevel (|R| + 1)).subset
  intro v hv
  change 1 + ‖position v‖ ^ 2 ≤ R at hv
  change ‖position v‖ ≤ |R| + 1
  nlinarith [le_abs_self R, norm_nonneg (position v), sq_nonneg (‖position v‖ - 1)]

@[expose] def centralStar : Finset Vertex := insert origin (neighbors origin)

theorem centralStar_card : centralStar.card = 9 := by
  have h : origin ∉ neighbors origin := by
    rw [mem_neighbors_iff]
    exact adjacent_irrefl origin
  simp [centralStar, h, origin_neighbors_card]

theorem centralStar_potential_le {v : Vertex} (hv : v ∈ centralStar) : potential v ≤ 2 := by
  rcases Finset.mem_insert.mp hv with h | h
  · subst v
    simp [potential, position, origin]
  · have he := adjacent_unit_length ((mem_neighbors_iff origin v).mp h)
    have hn : ‖position v‖ = 1 := by simpa [position, origin, dist_comm] using he
    norm_num [potential, hn]

@[expose] def sector : Finset Vertex := (finite_norm_sublevel 2).toFinset

theorem mem_sector (v : Vertex) : v ∈ sector ↔ ‖position v‖ ≤ 2 := by
  simp [sector]

theorem potential_outside_sector (v : Vertex) (hv : v ∉ sector) : 5 ≤ potential v := by
  have hn : 2 < ‖position v‖ := lt_of_not_ge ((mem_sector v).not.mp hv)
  unfold potential
  nlinarith

/-- The ninth sorted onsite level is at most two, proved from the actual
nine distinct central sites. -/
theorem ninth_onsite_le (e : ℕ ≃ Vertex) (he : Monotone (fun n => potential (e n))) :
    potential (e 8) ≤ 2 := by
  classical
  by_contra h
  have ht : 2 < potential (e 8) := lt_of_not_ge h
  let s : Finset ℕ := centralStar.image e.symm
  have hc : s.card = 9 := by
    rw [Finset.card_image_of_injective _ e.symm.injective]
    exact centralStar_card
  have hs : s ⊆ Finset.range 8 := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_range.mpr
    by_contra hn
    have hm := he (show 8 ≤ e.symm v by omega)
    simp only [Equiv.apply_symm_apply] at hm
    linarith [centralStar_potential_le hv]
  have hb := Finset.card_le_card hs
  rw [hc] at hb
  norm_num at hb

/-- The concrete graph controls nine low full levels on the common
natural domain, without assuming eigenvalue simplicity or a nonempty
window. The eigenbases for both operators are constructed. -/
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
  obtain ⟨e, he⟩ := infiniteOnsite_exists_monotone_equiv potential potential_proper
  obtain ⟨ev, hev, ⟨b⟩⟩ := onsitePlusBounded_exists_orderedEigenbasis
    potential 1 potential_lower potential_proper interaction interaction_symmetric
  have hgap : ∀ n : ℕ, 1 ≤ ev n := fun n =>
    (potential_lower (e n)).trans (onsitePlusBounded_ordered_ge_onsite_of_nonneg
      potential interaction interaction_symmetric interaction_nonneg e he ev hev b n)
  have hl : ∀ n : ℕ, n < 9 → ev n ≤ 3 := by
    intro n hn
    have hb := (onsitePlusBounded_ordered_comparison potential interaction
      interaction_symmetric e he ev hev b 8).2
    have ho := hev (show n ≤ 8 by omega)
    linarith [ninth_onsite_le e he, interaction_norm_le]
  refine ⟨ev, hev, ⟨b⟩, hgap, hl, ?_⟩
  intro τ ht ht4
  have hsym := finiteSectorCorrection_symmetric interaction interaction_symmetric sector τ
  obtain ⟨μ, hμ, ⟨bt⟩⟩ := onsitePlusBounded_exists_orderedEigenbasis
    potential 1 potential_lower potential_proper _ hsym
  have hgapμ : ∀ n : ℕ, 1 ≤ μ n := fun n => (hgap n).trans
    (finiteSector_ordered_mono potential interaction interaction_symmetric sector
      τ ht ev μ hev hμ b bt n)
  refine ⟨μ, hμ, ⟨bt⟩, hgapμ, ?_⟩
  intro n hn
  have hr := finiteSector_ordered_response_of_nonneg potential interaction interaction_symmetric
    interaction_nonneg 1 5 3 potential_lower (by norm_num) sector potential_outside_sector
    τ ht (by linarith) ev μ hev hμ b bt n (hl n hn)
  norm_num at hr
  simpa [div_eq_mul_inv, mul_comm] using hr

end
end SpectralGeometry.AmmannBeenker
