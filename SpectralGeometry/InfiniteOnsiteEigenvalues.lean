import SpectralGeometry.InfiniteOnsiteDensity

/-!
# Point spectrum of the infinite onsite operator

For the (possibly unbounded) multiplication operator on the natural dense
domain in real ℓ²(Tile), an eigenvector can be nonzero at a tile only if
its eigenvalue equals that tile's onsite potential.

Consequently, positive onsite energies force all *existing point
eigenvalues* to be positive. A uniform lower bound for the onsite
potential likewise bounds every point eigenvalue below.

These are point-spectrum statements. They do not imply that every
potential value is an eigenvalue, that the spectrum is discrete, or
that the multiplication operator has compact resolvent. The
interaction Laplacian and perturbation are not yet included.
-/

namespace SpectralGeometry

variable {Tile : Type*}

/-- At any tile where an onsite eigenstate is nonzero, the eigenvalue
must equal the potential at that tile. -/
theorem infiniteOnsiteEigenvalue_eq_at_nonzero
    (V : Tile → ℝ) (ψ : infiniteOnsiteDomain V) (λ : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = λ • (ψ.1 : TileHilbert Tile))
    (t : Tile) (hψ : ψ.1 t ≠ 0) :
    λ = V t := by
  have hcoord :=
    congrArg (fun φ : TileHilbert Tile => φ t) heigen
  have hmul : V t * ψ.1 t = λ * ψ.1 t := by
    simpa only [infiniteOnsiteOperator_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul] using hcoord
  have hz : (V t - λ) * ψ.1 t = 0 := by
    calc
      (V t - λ) * ψ.1 t =
          V t * ψ.1 t - λ * ψ.1 t := by ring
      _ = 0 := sub_eq_zero.mpr hmul
  rcases mul_eq_zero.mp hz with hv | hv
  · exact (sub_eq_zero.mp hv).symm
  · exact (hψ hv).elim

/-- An eigenstate vanishes at every tile where the onsite potential
does not equal its eigenvalue. -/
theorem infiniteOnsiteEigenvector_zero_of_potential_ne
    (V : Tile → ℝ) (ψ : infiniteOnsiteDomain V) (λ : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = λ • (ψ.1 : TileHilbert Tile))
    (t : Tile) (hV : V t ≠ λ) :
    ψ.1 t = 0 := by
  by_contra hψ
  exact hV (infiniteOnsiteEigenvalue_eq_at_nonzero V ψ λ heigen t hψ).symm

/-- A lower bound on the potential gives the same lower bound on
every point eigenvalue with a nonzero eigenstate. -/
theorem infiniteOnsiteEigenvalue_lower_bound
    (V : Tile → ℝ) (c : ℝ) (hV : ∀ t, c ≤ V t)
    (ψ : infiniteOnsiteDomain V) (λ : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = λ • (ψ.1 : TileHilbert Tile))
    (hψ : ∃ t, ψ.1 t ≠ 0) :
    c ≤ λ := by
  obtain ⟨t, ht⟩ := hψ
  rw [infiniteOnsiteEigenvalue_eq_at_nonzero V ψ λ heigen t ht]
  exact hV t

/-- Strictly positive onsite energies exclude zero and negative point
eigenvalues on the natural domain, even for an infinite tile set. -/
theorem infiniteOnsiteEigenvalue_pos
    (V : Tile → ℝ) (hV : ∀ t, 0 < V t)
    (ψ : infiniteOnsiteDomain V) (λ : ℝ)
    (heigen : infiniteOnsiteOperator V ψ = λ • (ψ.1 : TileHilbert Tile))
    (hψ : ∃ t, ψ.1 t ≠ 0) :
    0 < λ := by
  obtain ⟨t, ht⟩ := hψ
  rw [infiniteOnsiteEigenvalue_eq_at_nonzero V ψ λ heigen t ht]
  exact hV t

end SpectralGeometry
