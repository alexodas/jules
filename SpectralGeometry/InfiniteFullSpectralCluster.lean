module

public import SpectralGeometry.CanonicalProductClusterCount
public import SpectralGeometry.InfiniteBoundedSpectralStability
public import SpectralGeometry.OrderedSpectralProductBridge

public section

/-!
# Certified zero clusters for full operators with a bounded error

The error certificate is an operator-norm bound on a symmetric correction
on the same natural domain. The reference cut certificates use only the
neighboring ordered levels. Complete spectra, positive summability and
exact geometric divisors are derived, not assumed for the perturbed system.

This does not identify a finite-patch operator with the infinite operator,
and it does not turn compact-uniform convergence of scalar functions into
a zero-error bound. Those require additional approximation estimates.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*} [DecidableEq Tile]

/-- An operator-error certificate gives exact multiplicity-weighted zero
counts in each separated finite window, and matches every indexed zero to
within `‖d‖ * η`. Repeated levels may split or merge inside the window.
The empty window and a cut before the first level are included. -/
theorem onsitePlusBounded_exists_certified_zero_clusters [Infinite Tile]
    (V : Tile → ℝ) (B K : TileHilbert Tile →L[ℝ] TileHilbert Tile)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    (v₀ η : ℝ) (hV : ∀ t, v₀ ≤ V t) (herror : ‖K‖ ≤ η)
    (hsmall : η < v₀ - ‖B‖)
    (hproper : ∀ r : ℝ, (infiniteOnsiteLowEnergyTiles V r).Finite)
    (e : ℕ ≃ Tile) (horder : Monotone (fun n => V (e n)))
    (honsite : Summable (fun t => 1 / (V t) ^ 2)) (c d : ℂ) (hd : d ≠ 0) :
    ∃ ev μ : ℕ → ℝ, Monotone ev ∧ Monotone μ ∧
      (∀ i, v₀ - ‖B‖ ≤ ev i) ∧ (∀ i, v₀ - ‖B‖ - η ≤ μ i) ∧
      Admissible ev c d ∧ Admissible μ c d ∧
      HasExactFullSpectralProduct V B hproper ev c d ∧
      HasExactFullSpectralProduct V (B + K) hproper μ c d ∧
      (∀ i, |μ i - ev i| ≤ η) ∧
      (∀ i, ‖positiveSpectralPoint μ c d i - positiveSpectralPoint ev c d i‖ ≤ ‖d‖ * η ∧
        ‖negativeSpectralPoint μ c d i - negativeSpectralPoint ev c d i‖ ≤ ‖d‖ * η) ∧
      ∀ a b : ℝ, 0 < a → a < b → ∀ m n : ℕ,
        OrderedGapCertificate ev η a m → OrderedGapCertificate ev η b n →
        CertifiedCanonicalWindow ev c d a b m n ∧
          CertifiedCanonicalWindow μ c d a b m n := by
  have hη : 0 ≤ η := (norm_nonneg K).trans herror
  have hbasegap : ‖B‖ < v₀ := by linarith
  have hBK := boundedCorrection_add_symmetric B K hB hK
  obtain ⟨ev, hev, ⟨be⟩⟩ := onsitePlusBounded_exists_orderedEigenbasis V v₀ hV hproper B hB
  obtain ⟨μ, hμ, ⟨bm⟩⟩ := onsitePlusBounded_exists_orderedEigenbasis V v₀ hV hproper (B + K) hBK
  obtain ⟨hlo, hp, hs⟩ := onsitePlusBounded_ordered_positive_summable V B hB
    v₀ hV hbasegap hproper e horder honsite ev hev be
  obtain ⟨hloμ, hpμ, hsμ⟩ := onsitePlusBounded_small_error_preserves_summability V B K hB hK
    ev μ hev hμ be bm (v₀ - ‖B‖) (herror.trans_lt hsmall) hlo hs
  have hloμ' (i : ℕ) : v₀ - ‖B‖ - η ≤ μ i := by linarith [hloμ i]
  have ha := admissible_of_inv_sq_summable hp hs c d
  have haμ := admissible_of_inv_sq_summable hpμ hsμ c d
  have hprod := onsitePlusBounded_hasExactFullSpectralProduct V v₀ hV hproper B hB ev hev be hp hs c d hd
  have hprodμ := onsitePlusBounded_hasExactFullSpectralProduct V v₀ hV hproper (B + K) hBK μ hμ bm hpμ hsμ c d hd
  have hclose (i : ℕ) : |μ i - ev i| ≤ η :=
    (onsitePlusBounded_ordered_perturbation_bound V B K hB hK ev μ hev hμ be bm i).trans herror
  refine ⟨ev, μ, hev, hμ, hlo, hloμ', ha, haμ, hprod, hprodμ, hclose, ?_, ?_⟩
  · intro i
    rw [positiveSpectralPoint_sub_norm, negativeSpectralPoint_sub_norm]
    exact ⟨mul_le_mul_of_nonneg_left (hclose i) (norm_nonneg d),
      mul_le_mul_of_nonneg_left (hclose i) (norm_nonneg d)⟩
  · intro a b ha' _hab m n hcutA hcutB
    exact ⟨canonicalProduct_certified_window ev ev hev c d ha hd η a b ha' m n hcutA hcutB
        (fun i => by simpa using hη),
      canonicalProduct_certified_window ev μ hev c d haμ hd η a b ha' m n hcutA hcutB hclose⟩

end
end SpectralGeometry
