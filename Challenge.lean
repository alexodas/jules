module

public import Mathlib

public section

/-!
# Paired canonical products: convergence and prescribed-line zeros

The independent statement surface of SpectralGeometry/CanonicalProduct.lean.
Positive levels q(n) determine paired quadratic factors. Admissibility means
a summable majorant for deviations from one on every compact set.

Theorem C proves that zeros of this *constructed* infinite product lie on
the chosen affine real line; it does not concern zeros of the zeta function
or identify the levels with any spectral operator. Inverse-square summability
is a sufficient condition for admissibility. The sorry lines here are
Comparator's intentional challenge holes; proved declarations are in Solution.
-/

open Filter
open scoped BigOperators

namespace SpectralGeometry

noncomputable section

/-- The perturbation of 1 in the paired canonical factor. -/
@[expose] def perturb (q : ℕ → ℝ) (center direction : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  -(((s - center) / direction) ^ 2 / ((q n : ℂ) ^ 2))

/-- A factor corresponding to the symmetric geometric levels `±q n`. -/
@[expose] def factor (q : ℕ → ℝ) (center direction : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  1 + perturb q center direction n s

/-- The infinite paired (regularized) product. -/
@[expose] def canonicalProduct (q : ℕ → ℝ) (center direction : ℂ) (s : ℂ) : ℂ :=
  ∏' n : ℕ, factor q center direction n s

/--
An *admissible* energy family has positive energies and a summable
majorant for the deviations of the canonical factors from 1 on
every compact set. This is a checkable normal-convergence condition,
rather than an assumption that the product already converges.

The sufficient bound `∑ n, (q n)⁻² < ∞` is proved below.
-/
structure Admissible (q : ℕ → ℝ) (center direction : ℂ) : Prop where
  positive : ∀ n, 0 < q n
  compactMajorant :
    ∀ K : Set ℂ, IsCompact K →
      ∃ b : ℕ → ℝ, Summable b ∧
        ∀ n s, s ∈ K → ‖perturb q center direction n s‖ ≤ b n


theorem product_uniform_on_compact
    {q : ℕ → ℝ} {center direction : ℂ}
    (h : Admissible q center direction)
    (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun n s => factor q center direction n s)
      (canonicalProduct q center direction) K := by
  sorry

theorem factor_zero_on_line
    {q : ℕ → ℝ} {center direction s : ℂ}
    (h : Admissible q center direction)
    (hd : direction ≠ 0)
    (n : ℕ)
    (hz : factor q center direction n s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) := by
  sorry

theorem theoremC_zero_localization
    {q : ℕ → ℝ} {center direction s : ℂ}
    (h : Admissible q center direction)
    (hd : direction ≠ 0)
    (hz : canonicalProduct q center direction s = 0) :
    ∃ t : ℝ, s = center + direction * (t : ℂ) := by
  sorry

theorem admissible_of_inv_sq_summable
    {q : ℕ → ℝ} (hq : ∀ n, 0 < q n)
    (hsum : Summable (fun n => 1 / (q n) ^ 2))
    (center direction : ℂ) : Admissible q center direction := by
  sorry

theorem factor_zero_at_positive_level
    (q : ℕ → ℝ) (n : ℕ)
    (hq : q n ≠ 0)
    (center direction : ℂ) (hd : direction ≠ 0) :
    factor q center direction n
      (center + direction * (q n : ℂ)) = 0 := by
  sorry

theorem canonicalProduct_zero_at_positive_level
    (q : ℕ → ℝ) (n : ℕ) (hq : q n ≠ 0)
    (center direction : ℂ) (hd : direction ≠ 0) :
    canonicalProduct q center direction
      (center + direction * (q n : ℂ)) = 0 := by
  sorry

end
end SpectralGeometry

/-! ## Finite geometric operators -/

namespace SpectralGeometry

variable {Tile : Type*} [Fintype Tile] [DecidableEq Tile]

@[expose] noncomputable def finiteUnperturbedMatrix
    (V : Tile → ℝ) (w : Tile → Tile → ℝ) : Matrix Tile Tile ℝ :=
  fun t u =>
    if t = u then
      V t + ∑ v : Tile, if v = t then (0 : ℝ) else w t v
    else
      -w t u

@[expose] noncomputable def finitePerturbedMatrix
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ) : Matrix Tile Tile ℝ :=
  fun t u => finiteUnperturbedMatrix V w t u + ε * P t u

@[expose] noncomputable def finiteQuadraticEnergy
    (M : Matrix Tile Tile ℝ) (ψ : Tile → ℝ) : ℝ :=
  ∑ t : Tile, ∑ u : Tile, ψ t * (M t u * ψ u)

-- Independently reproduced statement signatures from SpectralGeometry/FinitePerturbation.lean
theorem finiteUnperturbedMatrix_symmetric
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hw : ∀ t u, w t u = w u t) :
    ∀ t u, finiteUnperturbedMatrix V w t u =
      finiteUnperturbedMatrix V w u t := by
  sorry

theorem finitePerturbedMatrix_symmetric
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hw : ∀ t u, w t u = w u t)
    (hP : ∀ t u, P t u = P u t) :
    ∀ t u, finitePerturbedMatrix V w P ε t u =
      finitePerturbedMatrix V w P ε u t := by
  sorry

theorem finitePerturbedMatrix_zero
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) :
    finitePerturbedMatrix V w P 0 = finiteUnperturbedMatrix V w := by
  sorry

-- Independently reproduced statement signatures from SpectralGeometry/FinitePositiveEnergy.lean
theorem finitePerturbedMatrix_energy_eq
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ) (ψ : Tile → ℝ) :
    finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ =
      finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ +
        ε * finiteQuadraticEnergy P ψ := by
  sorry

theorem finitePerturbedMatrix_energy_nonneg
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hBase : ∀ ψ : Tile → ℝ,
      0 ≤ finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ)
    (hP : ∀ ψ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P ψ)
    (hε : 0 ≤ ε) (ψ : Tile → ℝ) :
    0 ≤ finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ := by
  sorry

theorem finitePerturbedMatrix_energy_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hBase : ∀ ψ : Tile → ℝ, (∃ t, ψ t ≠ 0) →
      0 < finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ)
    (hP : ∀ ψ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P ψ)
    (hε : 0 ≤ ε) (ψ : Tile → ℝ)
    (hψ : ∃ t, ψ t ≠ 0) :
    0 < finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ := by
  sorry

-- Independently reproduced statement signatures from SpectralGeometry/FiniteGeometricEnergy.lean
theorem finiteGeometricEnergy_sum_squares
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hw : ∀ t u, w t u = w u t)
    (hdiag : ∀ t, w t t = 0) (ψ : Tile → ℝ) :
    finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ =
      (∑ t : Tile, V t * ψ t ^ 2) +
        (1 / 2 : ℝ) * (∑ t : Tile, ∑ u : Tile,
          w t u * (ψ t - ψ u) ^ 2) := by
  sorry

theorem finiteGeometricEnergy_nonneg
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hV : ∀ t, 0 ≤ V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (ψ : Tile → ℝ) :
    0 ≤ finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ := by
  sorry

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
  sorry

-- Independently reproduced statement signatures from SpectralGeometry/FiniteStrictPositivity.lean
theorem finiteGeometricEnergy_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hV : ∀ t, 0 < V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (ψ : Tile → ℝ) (hψ : ∃ t, ψ t ≠ 0) :
    0 < finiteQuadraticEnergy (finiteUnperturbedMatrix V w) ψ := by
  sorry

theorem finiteGeometricPerturbedEnergy_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hV : ∀ t, 0 < V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (hP : ∀ ψ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P ψ)
    (hε : 0 ≤ ε)
    (ψ : Tile → ℝ) (hψ : ∃ t, ψ t ≠ 0) :
    0 < finiteQuadraticEnergy (finitePerturbedMatrix V w P ε) ψ := by
  sorry

theorem finiteGeometricEigenvalue_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (hV : ∀ t, 0 < V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (ψ : Tile → ℝ) (eigenvalue : ℝ)
    (hψ : ∃ t, ψ t ≠ 0)
    (heigen : ∀ t,
      (∑ u : Tile, finiteUnperturbedMatrix V w t u * ψ u) =
        eigenvalue * ψ t) :
    0 < eigenvalue := by
  sorry

theorem finiteGeometricPerturbedEigenvalue_pos
    (V : Tile → ℝ) (w : Tile → Tile → ℝ)
    (P : Matrix Tile Tile ℝ) (ε : ℝ)
    (hV : ∀ t, 0 < V t)
    (hw : ∀ t u, w t u = w u t)
    (hwpos : ∀ t u, 0 ≤ w t u)
    (hdiag : ∀ t, w t t = 0)
    (hP : ∀ χ : Tile → ℝ, 0 ≤ finiteQuadraticEnergy P χ)
    (hε : 0 ≤ ε)
    (ψ : Tile → ℝ) (eigenvalue : ℝ)
    (hψ : ∃ t, ψ t ≠ 0)
    (heigen : ∀ t,
      (∑ u : Tile, finitePerturbedMatrix V w P ε t u * ψ u) =
        eigenvalue * ψ t) :
    0 < eigenvalue := by
  sorry

end SpectralGeometry

/-! ## Infinite diagonal operators -/

namespace SpectralGeometry

@[expose] abbrev TileHilbert (Tile : Type*) : Type _ :=
  lp (fun _ : Tile => ℝ) 2

variable {Tile : Type*}

/-- Natural domain of multiplication by a possibly unbounded potential.
Both the original state and the onsite-multiplied state must lie in ℓ². -/
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

/-- The diagonal multiplication operator with its natural ℓ² domain.
It is a linear map into ℓ², even if the potential is unbounded. -/
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

-- Independently audited signatures from SpectralGeometry/InfiniteOnsite.lean
theorem infiniteOnsiteOperator_apply
    (V : Tile → ℝ) (ψ : infiniteOnsiteDomain V) (t : Tile) :
    infiniteOnsiteOperator V ψ t = V t * ψ.1 t := by
  sorry

theorem infiniteOnsiteOperator_local_nonneg
    (V : Tile → ℝ) (hV : ∀ t, 0 ≤ V t)
    (ψ : infiniteOnsiteDomain V) (t : Tile) :
    0 ≤ ψ.1 t * infiniteOnsiteOperator V ψ t := by
  sorry

-- Independently audited signatures from SpectralGeometry/InfiniteOnsiteDensity.lean
section
variable [DecidableEq Tile]

theorem infiniteOnsiteDomain_single
    (V : Tile → ℝ) (i : Tile) (a : ℝ) :
    lp.single (2 : ENNReal) i a ∈ infiniteOnsiteDomain V := by
  sorry

theorem infiniteOnsiteDomain_finset_sum
    (V : Tile → ℝ) (ψ : TileHilbert Tile) (s : Finset Tile) :
    (∑ i ∈ s, lp.single (2 : ENNReal) i (ψ i)) ∈
      infiniteOnsiteDomain V := by
  sorry

theorem infiniteOnsiteDomain_dense
    (V : Tile → ℝ) :
    Dense (infiniteOnsiteDomain V : Set (TileHilbert Tile)) := by
  sorry

end

-- Independently audited signatures from SpectralGeometry/InfiniteOnsiteEigenvalues.lean
section
theorem infiniteOnsiteEigenvalue_eq_at_nonzero
    (V : Tile → ℝ) (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = eigenvalue • (ψ.1 : TileHilbert Tile))
    (t : Tile) (hψ : ψ.1 t ≠ 0) :
    eigenvalue = V t := by
  sorry

theorem infiniteOnsiteEigenvector_zero_of_potential_ne
    (V : Tile → ℝ) (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = eigenvalue • (ψ.1 : TileHilbert Tile))
    (t : Tile) (hV : V t ≠ eigenvalue) :
    ψ.1 t = 0 := by
  sorry

theorem infiniteOnsiteEigenvalue_lower_bound
    (V : Tile → ℝ) (c : ℝ) (hV : ∀ t, c ≤ V t)
    (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = eigenvalue • (ψ.1 : TileHilbert Tile))
    (hψ : ∃ t, ψ.1 t ≠ 0) :
    c ≤ eigenvalue := by
  sorry

theorem infiniteOnsiteEigenvalue_pos
    (V : Tile → ℝ) (hV : ∀ t, 0 < V t)
    (ψ : infiniteOnsiteDomain V) (eigenvalue : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = eigenvalue • (ψ.1 : TileHilbert Tile))
    (hψ : ∃ t, ψ.1 t ≠ 0) :
    0 < eigenvalue := by
  sorry

end

-- Independently audited signatures from SpectralGeometry/InfiniteOnsiteSummability.lean
theorem infiniteOnsiteLinearGrowth_positive
    (V : ℕ → ℝ) (hGrowth : ∀ n, ((n + 1 : ℕ) : ℝ) ≤ V n)
    (n : ℕ) : 0 < V n := by
  sorry

theorem infiniteOnsiteLinearGrowth_invSq_summable
    (V : ℕ → ℝ) (hGrowth : ∀ n, ((n + 1 : ℕ) : ℝ) ≤ V n) :
    Summable (fun n : ℕ => 1 / (V n) ^ 2) := by
  sorry

-- Independently audited signatures from SpectralGeometry/InfiniteOnsitePowerGrowth.lean
theorem infiniteOnsitePowerGrowth_invSq_summable
    (V : ℕ → ℝ) (alpha : ℝ) (halpha : (1 / 2 : ℝ) < alpha)
    (hGrowth : ∀ n, (((n + 1 : ℕ) : ℝ) ^ alpha) ≤ V n) :
    Summable (fun n : ℕ => 1 / (V n) ^ 2) := by
  sorry

theorem infiniteOnsitePowerGrowth_positive
    (V : ℕ → ℝ) (alpha : ℝ)
    (hGrowth : ∀ n, (((n + 1 : ℕ) : ℝ) ^ alpha) ≤ V n)
    (n : ℕ) : 0 < V n := by
  sorry

theorem infiniteOnsiteExactPower_not_invSq_summable
    (alpha : ℝ) (halpha : alpha ≤ (1 / 2 : ℝ)) :
    ¬ Summable (fun n : ℕ =>
      1 / (((((n + 1 : ℕ) : ℝ) ^ alpha) ^ 2))) := by
  sorry

-- Infinite onsite point-spectrum bounds and finite energy sectors.
@[expose] def infiniteOnsiteLowEnergyTiles (V : Tile → ℝ) (R : ℝ) :
    Set Tile := {t | V t ≤ R}

theorem infiniteOnsiteEigenvector_support_subset_lowEnergy
    (V : Tile → ℝ) (R eigenvalue : ℝ)
    (hbound : eigenvalue ≤ R)
    (ψ : infiniteOnsiteDomain V)
    (heigen : infiniteOnsiteOperator V ψ =
      eigenvalue • (ψ.1 : TileHilbert Tile)) :
    {t : Tile | ψ.1 t ≠ 0} ⊆ infiniteOnsiteLowEnergyTiles V R := by
  sorry

theorem infiniteOnsiteEigenvector_support_finite
    (V : Tile → ℝ) (R eigenvalue : ℝ)
    (hfinite : (infiniteOnsiteLowEnergyTiles V R).Finite)
    (hbound : eigenvalue ≤ R)
    (ψ : infiniteOnsiteDomain V)
    (heigen : infiniteOnsiteOperator V ψ =
      eigenvalue • (ψ.1 : TileHilbert Tile)) :
    {t : Tile | ψ.1 t ≠ 0}.Finite := by
  sorry

theorem infiniteOnsitePointEigenvalues_below_subset_image
    (V : Tile → ℝ) (R : ℝ) :
    {a | a ≤ R ∧
      ∃ ψ : infiniteOnsiteDomain V,
        (∃ t : Tile, ψ.1 t ≠ 0) ∧
        infiniteOnsiteOperator V ψ =
          a • (ψ.1 : TileHilbert Tile)} ⊆
      V '' infiniteOnsiteLowEnergyTiles V R := by
  sorry

theorem infiniteOnsitePointEigenvalues_below_finite
    (V : Tile → ℝ) (R : ℝ)
    (hfinite : (infiniteOnsiteLowEnergyTiles V R).Finite) :
    {a | a ≤ R ∧
      ∃ ψ : infiniteOnsiteDomain V,
        (∃ t : Tile, ψ.1 t ≠ 0) ∧
        infiniteOnsiteOperator V ψ =
          a • (ψ.1 : TileHilbert Tile)}.Finite := by
  sorry

-- Infinite Hilbert-space operators with finitely many geometric edges.
section
variable [DecidableEq Tile]

@[expose] noncomputable def infiniteEdgeVector (a b : Tile) : TileHilbert Tile :=
  lp.single (2 : ENNReal) a (1 : ℝ) -
    lp.single (2 : ENNReal) b (1 : ℝ)

@[expose] noncomputable def infiniteEdgeLaplacian (a b : Tile) (w : ℝ) :
    TileHilbert Tile →ₗ[ℝ] TileHilbert Tile where
  toFun := fun ψ => (w * (ψ a - ψ b)) • infiniteEdgeVector a b
  map_add' := by
    intro ψ φ
    change (w * ((ψ + φ) a - (ψ + φ) b)) • infiniteEdgeVector a b =
      (w * (ψ a - ψ b)) • infiniteEdgeVector a b +
        (w * (φ a - φ b)) • infiniteEdgeVector a b
    have h :
        w * ((ψ + φ) a - (ψ + φ) b) =
          w * (ψ a - ψ b) + w * (φ a - φ b) := by
      simp only [lp.coeFn_add, Pi.add_apply]
      ring
    rw [h, add_smul]
  map_smul' := by
    intro r ψ
    change (w * ((r • ψ) a - (r • ψ) b)) • infiniteEdgeVector a b =
      r • ((w * (ψ a - ψ b)) • infiniteEdgeVector a b)
    have h :
        w * ((r • ψ) a - (r • ψ) b) =
          r * (w * (ψ a - ψ b)) := by
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h, mul_smul]

@[expose] noncomputable def infiniteFiniteEdgeLaplacian
    (edges : Finset (Tile × Tile)) (w : Tile × Tile → ℝ) :
    TileHilbert Tile →ₗ[ℝ] TileHilbert Tile :=
  ∑ e ∈ edges, infiniteEdgeLaplacian e.1 e.2 (w e)

theorem infiniteEdgeLaplacian_inner
    (a b : Tile) (w : ℝ) (ψ φ : TileHilbert Tile) :
    (inner ℝ (ψ) (infiniteEdgeLaplacian a b w φ)) =
      w * (φ a - φ b) * (ψ a - ψ b) := by
  sorry

theorem infiniteEdgeLaplacian_symmetric
    (a b : Tile) (w : ℝ) (ψ φ : TileHilbert Tile) :
    (inner ℝ (ψ) (infiniteEdgeLaplacian a b w φ)) =
      (inner ℝ (infiniteEdgeLaplacian a b w ψ) (φ)) := by
  sorry

theorem infiniteEdgeLaplacian_energy_nonneg
    (a b : Tile) (w : ℝ) (hw : 0 ≤ w) (ψ : TileHilbert Tile) :
    0 ≤ (inner ℝ (ψ) (infiniteEdgeLaplacian a b w ψ)) := by
  sorry

theorem infiniteFiniteEdgeLaplacian_energy_nonneg
    (edges : Finset (Tile × Tile)) (w : Tile × Tile → ℝ)
    (hw : ∀ e ∈ edges, 0 ≤ w e) (ψ : TileHilbert Tile) :
    0 ≤ (inner ℝ (ψ) (infiniteFiniteEdgeLaplacian edges w ψ)) := by
  sorry

theorem infiniteFiniteEdgeLaplacian_symmetric
    (edges : Finset (Tile × Tile)) (w : Tile × Tile → ℝ)
    (ψ φ : TileHilbert Tile) :
    (inner ℝ (ψ) (infiniteFiniteEdgeLaplacian edges w φ)) =
      (inner ℝ (infiniteFiniteEdgeLaplacian edges w ψ) (φ)) := by
  sorry

-- Nonnegative symmetric interactions plus an independent bounded perturbation.
@[expose] noncomputable def infiniteFiniteEdgePerturbedOperator
    (V : Tile → ℝ) (edges : Finset (Tile × Tile))
    (w : Tile × Tile → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ) :
    (infiniteOnsiteDomain V) →ₗ[ℝ] TileHilbert Tile :=
  infiniteOnsiteOperator V +
    (infiniteFiniteEdgeLaplacian edges w).comp
      (infiniteOnsiteDomain V).subtype +
    ε • (P.toLinearMap.comp (infiniteOnsiteDomain V).subtype)

theorem infiniteOnsiteOperator_symmetric
    (V : Tile → ℝ) (ψ φ : infiniteOnsiteDomain V) :
    (inner ℝ ((ψ.1 : TileHilbert Tile)) (infiniteOnsiteOperator V φ)) =
      (inner ℝ (infiniteOnsiteOperator V ψ) ((φ.1 : TileHilbert Tile))) := by
  sorry

theorem infiniteOnsiteOperator_energy_nonneg
    (V : Tile → ℝ) (hV : ∀ t, 0 ≤ V t)
    (ψ : infiniteOnsiteDomain V) :
    0 ≤ (inner ℝ ((ψ.1 : TileHilbert Tile)) (infiniteOnsiteOperator V ψ)) := by
  sorry

theorem infiniteFiniteEdgePerturbedOperator_apply
    (V : Tile → ℝ) (edges : Finset (Tile × Tile))
    (w : Tile × Tile → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (ψ : infiniteOnsiteDomain V) :
    infiniteFiniteEdgePerturbedOperator V edges w P ε ψ =
      infiniteOnsiteOperator V ψ +
        infiniteFiniteEdgeLaplacian edges w (ψ.1 : TileHilbert Tile) +
        ε • P (ψ.1 : TileHilbert Tile) := by
  sorry

theorem infiniteFiniteEdgePerturbedOperator_energy_eq
    (V : Tile → ℝ) (edges : Finset (Tile × Tile))
    (w : Tile × Tile → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (ψ : infiniteOnsiteDomain V) :
    (inner ℝ ((ψ.1 : TileHilbert Tile)) (infiniteFiniteEdgePerturbedOperator V edges w P ε ψ)) =
      (inner ℝ ((ψ.1 : TileHilbert Tile)) (infiniteOnsiteOperator V ψ)) +
        (inner ℝ ((ψ.1 : TileHilbert Tile)) (infiniteFiniteEdgeLaplacian edges w ψ.1)) +
        ε * (inner ℝ ((ψ.1 : TileHilbert Tile)) (P ψ.1)) := by
  sorry

theorem infiniteFiniteEdgePerturbedOperator_energy_nonneg
    (V : Tile → ℝ) (edges : Finset (Tile × Tile))
    (w : Tile × Tile → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (hV : ∀ t, 0 ≤ V t)
    (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hP : ∀ ψ : TileHilbert Tile, 0 ≤ (inner ℝ (ψ) (P ψ)))
    (hε : 0 ≤ ε) (ψ : infiniteOnsiteDomain V) :
    0 ≤ (inner ℝ ((ψ.1 : TileHilbert Tile)) (infiniteFiniteEdgePerturbedOperator V edges w P ε ψ)) := by
  sorry

theorem infiniteFiniteEdgePerturbedOperator_symmetric
    (V : Tile → ℝ) (edges : Finset (Tile × Tile))
    (w : Tile × Tile → ℝ)
    (P : TileHilbert Tile →L[ℝ] TileHilbert Tile) (ε : ℝ)
    (hP : ∀ ψ φ : TileHilbert Tile,
      (inner ℝ (ψ) (P φ)) = (inner ℝ (P ψ) (φ)))
    (ψ φ : infiniteOnsiteDomain V) :
    (inner ℝ ((ψ.1 : TileHilbert Tile)) (infiniteFiniteEdgePerturbedOperator V edges w P ε φ)) =
      (inner ℝ (infiniteFiniteEdgePerturbedOperator V edges w P ε ψ) ((φ.1 : TileHilbert Tile))) := by
  sorry

end

end SpectralGeometry
