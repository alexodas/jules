module

public import SpectralGeometry.InfiniteLocalFullGlobalOrderedEnumeration

public section

/-!
# Ordering proper onsite energies without a supplied site enumeration

Finite onsite sublevel sets suffice to enumerate an infinite site type in
nondecreasing energy order. A cardinal embedding breaks ties, and the
existing finite-predecessor enumeration lists every site exactly once.
No countability, injectivity of the potential or preordered site bijection
is assumed. The natural-number conclusion explicitly requires infinitely
many sites; finite and empty types are not padded by repetitions.
-/

namespace SpectralGeometry

noncomputable section

variable {Tile : Type*}

/-- Proper onsite energies on infinitely many sites admit a sorted
bijection. Equal-energy sites remain distinct and are all enumerated. -/
theorem infiniteOnsite_exists_monotone_equiv [Infinite Tile]
    (V : Tile → ℝ)
    (hproper : ∀ R : ℝ, (infiniteOnsiteLowEnergyTiles V R).Finite) :
    ∃ e : ℕ ≃ Tile, Monotone (fun n => V (e n)) := by
  classical
  let key (t : Tile) := toLex (V t, embeddingToCardinal t)
  have hkey : Function.Injective key := by
    intro x y h
    exact embeddingToCardinal.injective (congrArg (fun p => (ofLex p).2) h)
  letI : LinearOrder Tile := LinearOrder.lift' key hkey
  have hpred (x : Tile) : {y : Tile | y < x}.Finite := by
    apply (hproper (V x)).subset
    intro y hy
    change V y ≤ V x
    have hh : key y ≤ key x := le_of_lt hy
    exact Prod.Lex.monotone_fst _ _ hh
  obtain ⟨e, he, hs⟩ := exists_strictMono_surjective_of_finite_predecessors hpred
  refine ⟨Equiv.ofBijective e ⟨he.injective, hs⟩, ?_⟩
  intro i j hij
  have hh : key (e i) ≤ key (e j) := he.monotone hij
  exact Prod.Lex.monotone_fst _ _ hh

end
end SpectralGeometry
