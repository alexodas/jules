module

public import SpectralGeometry.FinitePositiveEnergy

public section

/-!
# Geometric positivity from onsite energies and interactions

For a finite tiling with nonnegative individual energies and symmetric
nonnegative pair weights, we derive a sum-of-squares formula for the
unperturbed geometric quadratic energy. This proves nonnegativity directly
from the geometric data rather than assuming it.

The finite matrix discards self-interactions. We initially formulate the
identity with explicitly vanishing diagonal weights (the usual convention
for interaction weights between *different* tiles).
-/

namespace SpectralGeometry

variable {Tile : Type*} [Fintype Tile] [DecidableEq Tile]

/-- Replacing the omitted diagonal by zero turns the geometric operator
into an onsite diagonal matrix minus the interaction-weight matrix. -/
private theorem geometricMatrix_entry
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hdiag : ∀ t, w t t = 0) (t u : Tile) :
    finiteUnperturbedMatrix V w t u =
      (if t = u then V t + ∑ v : Tile, w t v else 0) - w t u := by
  have hsum :
      (∑ v : Tile, if v = t then (0 : ℝ) else w t v) =
        ∑ v : Tile, w t v := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : v = t
    · subst v
      simp [hdiag]
    · simp [h]
  by_cases htu : t = u
  · subst u
    simp only [finiteUnperturbedMatrix, ite_true]
    rw [hsum]
    simp [hdiag]
  · simp [finiteUnperturbedMatrix, htu]

/-- An algebraic expression for the unperturbed quadratic energy. -/
private theorem geometricEnergy_expansion
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hdiag : ∀ t, w t t = 0) (ψ : Tile → ℝ) :
    finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ =
      (∑ t : Tile, V t * ψ t ^ 2) +
        (∑ t : Tile, ∑ u : Tile, w t u * ψ t ^ 2) -
          (∑ t : Tile, ∑ u : Tile, w t u * ψ t * ψ u) := by
  classical
  have hterm (t u : Tile) :
      ψ t * (finiteUnperturbedMatrix V w t u * ψ u) =
        (if t = u then (V t + ∑ v : Tile, w t v) * ψ t ^ 2 else 0) -
          w t u * ψ t * ψ u := by
    rw [geometricMatrix_entry V w hdiag t u]
    by_cases htu : t = u
    · subst u
      simp [hdiag]
      ring
    · simp [htu]
      ring
  calc
    finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ =
      ∑ t : Tile, ∑ u : Tile,
        ((if t = u then (V t + ∑ v : Tile, w t v) * ψ t ^ 2 else 0) -
          w t u * ψ t * ψ u) := by
            unfold finiteQuadraticEnergy
            apply Finset.sum_congr rfl
            intro t ht
            apply Finset.sum_congr rfl
            intro u hu
            exact hterm t u
    _ = ∑ t : Tile, ((V t + ∑ v : Tile, w t v) * ψ t ^ 2 -
          ∑ u : Tile, w t u * ψ t * ψ u) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.sum_sub_distrib]
            simp
    _ = (∑ t : Tile, V t * ψ t ^ 2) +
        (∑ t : Tile, ∑ u : Tile, w t u * ψ t ^ 2) -
          (∑ t : Tile, ∑ u : Tile, w t u * ψ t * ψ u) := by
            simp only [add_mul, Finset.sum_mul,
              Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Symmetric weights make the two quadratic diagonal pair sums equal. -/
private theorem geometricEnergy_swap
    (w : Tile → Tile → ℝ) (hw : ∀ t u, w t u = w u t)
    (ψ : Tile → ℝ) :
    (∑ t : Tile, ∑ u : Tile, w t u * ψ u ^ 2) =
      ∑ t : Tile, ∑ u : Tile, w t u * ψ t ^ 2 := by
  calc
    _ = ∑ u : Tile, ∑ t : Tile, w t u * ψ u ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ u : Tile, ∑ t : Tile, w u t * ψ u ^ 2 := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro t ht
      rw [hw t u]
    _ = _ := by rfl

/-- Sum of squares identity for the geometric quadratic energy.
The factor one half accounts for counting each unordered pair twice. -/
theorem finiteGeometricEnergy_sum_squares
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hw : ∀ t u, w t u = w u t)
    (hdiag : ∀ t, w t t = 0) (ψ : Tile → ℝ) :
    finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ =
      (∑ t : Tile, V t * ψ t ^ 2) +
        (1 / 2 : ℝ) * (∑ t : Tile, ∑ u : Tile,
          w t u * (ψ t - ψ u) ^ 2) := by
  have hswap := geometricEnergy_swap w hw ψ
  have hsquare :
      (∑ t : Tile, ∑ u : Tile, w t u * (ψ t - ψ u) ^ 2) =
        2 * ((∑ t : Tile, ∑ u : Tile, w t u * ψ t ^ 2) -
          (∑ t : Tile, ∑ u : Tile, w t u * ψ t * ψ u)) := by
    calc
      _ = ∑ t : Tile, ∑ u : Tile,
        (w t u * ψ t ^ 2 - 2 * (w t u * ψ t * ψ u) +
          w t u * ψ u ^ 2) := by
            apply Finset.sum_congr rfl
            intro t ht
            apply Finset.sum_congr rfl
            intro u hu
            ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
        rw [hswap]
        ring
  rw [geometricEnergy_expansion V w hdiag ψ, hsquare]
  ring

/-- **Third geometric theorem.** Nonnegative onsite energies and
nonnegative symmetric interaction weights force nonnegative geometric
quadratic energy for every tile configuration. -/
theorem finiteGeometricEnergy_nonneg
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hV : ∀ t, 0 ≤ V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (ψ : Tile → ℝ) :
    0 ≤ finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ := by
  rw [finiteGeometricEnergy_sum_squares V w hw hdiag]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro t ht
    exact mul_nonneg (hV t) (sq_nonneg _)
  · apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply Finset.sum_nonneg
    intro t ht
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (hwpos t u) (sq_nonneg _)

/-- Geometric hypotheses plus a nonnegative perturbation yield
nonnegative quadratic energy for the complete perturbed operator. -/
theorem finiteGeometricPerturbedEnergy_nonneg
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hV : ∀ t, 0 ≤ V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (hP : ∀ ψ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P ψ)
    (hε : 0 ≤ ε) (ψ : Tile → ℝ) :
    0 ≤ finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ := by
  exact finitePerturbedMatrix_energy_nonneg V w P ε
    (fun ψ => finiteGeometricEnergy_nonneg V w hV hw hwpos hdiag ψ)
    hP hε ψ

end SpectralGeometry
