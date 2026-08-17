import Mathlib

noncomputable section

/--
Area totale di una coppia di spicchi opposti di ampiezza π/4.
`R` è il raggio della pizza, `d` la distanza OP, `φ` la direzione OP,
e `θ` l'angolo iniziale dello spicchio.
-/
def pairArea (R d φ θ : ℝ) : ℝ :=
  R ^ 2 * (Real.pi / 4) +
    d ^ 2 / 2 *
      (Real.sin (2 * (θ + Real.pi / 4 - φ)) -
       Real.sin (2 * (θ - φ)))

/--
Quattro rette concorrenti distanziate di π/4 producono otto spicchi.
La somma delle coppie opposte 0 e 2 coincide con quella delle coppie 1 e 3.
-/
theorem pairArea_four_cuts (R d φ : ℝ) :
    pairArea R d φ 0 + pairArea R d φ (Real.pi / 2) =
      pairArea R d φ (Real.pi / 4) + pairArea R d φ (3 * Real.pi / 4) := by
  let x : ℝ := -2 * φ

  have h00 : 2 * (0 + Real.pi / 4 - φ) = x + Real.pi / 2 := by
    dsimp [x]
    ring
  have h01 : 2 * (0 - φ) = x := by
    dsimp [x]
    ring
  have h10 : 2 * (Real.pi / 4 + Real.pi / 4 - φ) = x + Real.pi := by
    dsimp [x]
    ring
  have h11 : 2 * (Real.pi / 4 - φ) = x + Real.pi / 2 := by
    dsimp [x]
    ring
  have h20 : 2 * (Real.pi / 2 + Real.pi / 4 - φ) = x + 3 * Real.pi / 2 := by
    dsimp [x]
    ring
  have h21 : 2 * (Real.pi / 2 - φ) = x + Real.pi := by
    dsimp [x]
    ring
  have h30 : 2 * (3 * Real.pi / 4 + Real.pi / 4 - φ) = x + 2 * Real.pi := by
    dsimp [x]
    ring
  have h31 : 2 * (3 * Real.pi / 4 - φ) = x + 3 * Real.pi / 2 := by
    dsimp [x]
    ring

  have hs1 : Real.sin (x + Real.pi / 2) = Real.cos x :=
    Real.sin_add_pi_div_two x
  have hs2 : Real.sin (x + Real.pi) = -Real.sin x :=
    Real.sin_add_pi x
  have hs3 : Real.sin (x + 3 * Real.pi / 2) = -Real.cos x := by
    calc
      Real.sin (x + 3 * Real.pi / 2)
          = Real.sin ((x + Real.pi) + Real.pi / 2) := by
              congr 1
              ring
      _ = Real.cos (x + Real.pi) := Real.sin_add_pi_div_two (x + Real.pi)
      _ = -Real.cos x := Real.cos_add_pi x
  have hs4 : Real.sin (x + 2 * Real.pi) = Real.sin x :=
    Real.sin_add_two_pi x

  simp only [pairArea]
  rw [h00, h01, h20, h21, h10, h11, h30, h31]
  rw [hs1, hs2, hs3, hs4]
  ring

/--
Versione sugli otto spicchi. `A i` è l'area dello spicchio i.
Le ipotesi h0..h3 identificano le quattro coppie di spicchi opposti
con la formula `pairArea`.
-/
theorem pizza_four_cuts
    (A : Fin 8 → ℝ)
    (R d φ : ℝ)
    (h0 : A 0 + A 4 = pairArea R d φ 0)
    (h1 : A 1 + A 5 = pairArea R d φ (Real.pi / 4))
    (h2 : A 2 + A 6 = pairArea R d φ (Real.pi / 2))
    (h3 : A 3 + A 7 = pairArea R d φ (3 * Real.pi / 4)) :
    A 0 + A 2 + A 4 + A 6 = A 1 + A 3 + A 5 + A 7 := by
  calc
    A 0 + A 2 + A 4 + A 6
        = (A 0 + A 4) + (A 2 + A 6) := by ring
    _ = pairArea R d φ 0 + pairArea R d φ (Real.pi / 2) := by rw [h0, h2]
    _ = pairArea R d φ (Real.pi / 4) + pairArea R d φ (3 * Real.pi / 4) :=
      pairArea_four_cuts R d φ
    _ = (A 1 + A 5) + (A 3 + A 7) := by rw [h1, h3]
    _ = A 1 + A 3 + A 5 + A 7 := by ring

end
