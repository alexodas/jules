module

public import SpectralGeometry.AmmannBeenkerCrossingGapCycle

public section

/-!
# A 17-coordinate scalar certificate for the crossing block

The two alternating ring directions are removed by imposing zero
alternating sums. The estimate combines:
* the verified eight-cycle bound on each mean-zero ring component;
* the verified three-coordinate constant-sector bound;
* algebraic orthogonality of mean and mean-zero components.

The theorem below concerns the explicit scalar formula of the finite
central block. Identifying it with the actual centralCrossingBlock and
transferring it to the full infinite operator are separate obligations.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

set_option maxHeartbeats 5000000 in
/-- A squared singular-value lower bound 1/576 for the central
seventeen-coordinate crossing expression, restricted to the complement
of the two alternating ring modes. -/
theorem crossingCentralSeventeenScalar_gap
    (delta z a b c d e f g h p q r s t u v w : ℝ)
    (hdelta : 3 ≤ delta)
    (hxa : a - b + c - d + e - f + g - h = 0)
    (hya : p - q + r - s + t - u + v - w = 0) :
    (1 / 576 : ℝ) * (z ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2 + h ^ 2 + p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 + w ^ 2) ≤
      (delta * z + (a + b + c + d + e + f + g + h) / 16) ^ 2 +
      ( (z + p + w) ^ 2 +
        (z + q + p) ^ 2 +
        (z + r + q) ^ 2 +
        (z + s + r) ^ 2 +
        (z + t + s) ^ 2 +
        (z + u + t) ^ 2 +
        (z + v + u) ^ 2 +
        (z + w + v) ^ 2 ) / 256 +
      ( (a + b) ^ 2 +
        (b + c) ^ 2 +
        (c + d) ^ 2 +
        (d + e) ^ 2 +
        (e + f) ^ 2 +
        (f + g) ^ 2 +
        (g + h) ^ 2 +
        (h + a) ^ 2 ) / 256 := by
  let mx : ℝ := (a + b + c + d + e + f + g + h) / 8
  let my : ℝ := (p + q + r + s + t + u + v + w) / 8
  have hxc := crossingEightCycle_neighbor_sum_lower
    (a - mx) (b - mx) (c - mx) (d - mx) (e - mx) (f - mx) (g - mx) (h - mx) (by linarith only [hxa])
  have hyc := crossingEightCycle_neighbor_sum_lower
    (p - my) (q - my) (r - my) (s - my) (t - my) (u - my) (v - my) (w - my) (by linarith only [hya])
  have hconstant := crossingCentralConstantMode_gap delta z mx my hdelta
  have hnorm :
      z ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2 + h ^ 2 + p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 + w ^ 2 =
        z ^ 2 + 8 * mx ^ 2 + 8 * my ^ 2 +
        ((a - mx) ^ 2 + (b - mx) ^ 2 + (c - mx) ^ 2 + (d - mx) ^ 2 + (e - mx) ^ 2 + (f - mx) ^ 2 + (g - mx) ^ 2 + (h - mx) ^ 2) +
        ((p - my) ^ 2 + (q - my) ^ 2 + (r - my) ^ 2 + (s - my) ^ 2 + (t - my) ^ 2 + (u - my) ^ 2 + (v - my) ^ 2 + (w - my) ^ 2) := by
    dsimp [mx, my]
    ring
  have henergy :
      (delta * z + (a + b + c + d + e + f + g + h) / 16) ^ 2 +
      ( (z + p + w) ^ 2 +
        (z + q + p) ^ 2 +
        (z + r + q) ^ 2 +
        (z + s + r) ^ 2 +
        (z + t + s) ^ 2 +
        (z + u + t) ^ 2 +
        (z + v + u) ^ 2 +
        (z + w + v) ^ 2 ) / 256 +
      ( (a + b) ^ 2 +
        (b + c) ^ 2 +
        (c + d) ^ 2 +
        (d + e) ^ 2 +
        (e + f) ^ 2 +
        (f + g) ^ 2 +
        (g + h) ^ 2 +
        (h + a) ^ 2 ) / 256 =
      (delta * z + mx / 2) ^ 2 + (z + 2 * my) ^ 2 / 32 + mx ^ 2 / 8 +
      (((a - mx) + (b - mx)) ^ 2 +
        ((b - mx) + (c - mx)) ^ 2 +
        ((c - mx) + (d - mx)) ^ 2 +
        ((d - mx) + (e - mx)) ^ 2 +
        ((e - mx) + (f - mx)) ^ 2 +
        ((f - mx) + (g - mx)) ^ 2 +
        ((g - mx) + (h - mx)) ^ 2 +
        ((h - mx) + (a - mx)) ^ 2) / 256 +
      (((p - my) + (q - my)) ^ 2 +
        ((q - my) + (r - my)) ^ 2 +
        ((r - my) + (s - my)) ^ 2 +
        ((s - my) + (t - my)) ^ 2 +
        ((t - my) + (u - my)) ^ 2 +
        ((u - my) + (v - my)) ^ 2 +
        ((v - my) + (w - my)) ^ 2 +
        ((w - my) + (p - my)) ^ 2) / 256 := by
    dsimp [mx, my]
    ring
  calc
    (1 / 576 : ℝ) * (z ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2 + h ^ 2 + p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 + w ^ 2) =
        (1 / 576 : ℝ) * (z ^ 2 + 8 * mx ^ 2 + 8 * my ^ 2 +
          ((a - mx) ^ 2 + (b - mx) ^ 2 + (c - mx) ^ 2 + (d - mx) ^ 2 + (e - mx) ^ 2 + (f - mx) ^ 2 + (g - mx) ^ 2 + (h - mx) ^ 2) +
          ((p - my) ^ 2 + (q - my) ^ 2 + (r - my) ^ 2 + (s - my) ^ 2 + (t - my) ^ 2 + (u - my) ^ 2 + (v - my) ^ 2 + (w - my) ^ 2)) := by rw [hnorm]
    _ ≤ (1 / 144 : ℝ) * (z ^ 2 + 8 * mx ^ 2 + 8 * my ^ 2) +
        (1 / 512 : ℝ) * (((a - mx) ^ 2 + (b - mx) ^ 2 + (c - mx) ^ 2 + (d - mx) ^ 2 + (e - mx) ^ 2 + (f - mx) ^ 2 + (g - mx) ^ 2 + (h - mx) ^ 2) + ((p - my) ^ 2 + (q - my) ^ 2 + (r - my) ^ 2 + (s - my) ^ 2 + (t - my) ^ 2 + (u - my) ^ 2 + (v - my) ^ 2 + (w - my) ^ 2)) := by
      nlinarith [sq_nonneg z, sq_nonneg mx, sq_nonneg my,
        sq_nonneg (a - mx),
        sq_nonneg (b - mx),
        sq_nonneg (c - mx),
        sq_nonneg (d - mx),
        sq_nonneg (e - mx),
        sq_nonneg (f - mx),
        sq_nonneg (g - mx),
        sq_nonneg (h - mx),
        sq_nonneg (p - my),
        sq_nonneg (q - my),
        sq_nonneg (r - my),
        sq_nonneg (s - my),
        sq_nonneg (t - my),
        sq_nonneg (u - my),
        sq_nonneg (v - my),
        sq_nonneg (w - my)]
    _ ≤ (delta * z + mx / 2) ^ 2 + (z + 2 * my) ^ 2 / 32 + mx ^ 2 / 8 +
      (((a - mx) + (b - mx)) ^ 2 +
        ((b - mx) + (c - mx)) ^ 2 +
        ((c - mx) + (d - mx)) ^ 2 +
        ((d - mx) + (e - mx)) ^ 2 +
        ((e - mx) + (f - mx)) ^ 2 +
        ((f - mx) + (g - mx)) ^ 2 +
        ((g - mx) + (h - mx)) ^ 2 +
        ((h - mx) + (a - mx)) ^ 2) / 256 +
      (((p - my) + (q - my)) ^ 2 +
        ((q - my) + (r - my)) ^ 2 +
        ((r - my) + (s - my)) ^ 2 +
        ((s - my) + (t - my)) ^ 2 +
        ((t - my) + (u - my)) ^ 2 +
        ((u - my) + (v - my)) ^ 2 +
        ((v - my) + (w - my)) ^ 2 +
        ((w - my) + (p - my)) ^ 2) / 256 := by
      nlinarith only [hconstant, hxc, hyc]
    _ = _ := henergy.symm


/-!
The scalar formula above is exactly the Euclidean squared norm of
\`centralCrossingBlock\`. The following theorem is the actual finite
17-vertex singular-value estimate, on the orthogonal complement of
the compact ring directions; its only hypotheses are the two
alternating-sum orthogonality conditions.

The remaining task is to transfer this estimate through the
central/exterior coupling to exclude additional infinite-operator
eigenvalues near E*.
-/

set_option maxHeartbeats 6000000 in
theorem crossingCentralBlock_norm_sq_lower
    (x : Fin 17 → ℝ)
    (hxa : x 1 - x 2 + x 3 - x 4 + x 5 - x 6 + x 7 - x 8 = 0)
    (hya : x 9 - x 10 + x 11 - x 12 + x 13 - x 14 + x 15 - x 16 = 0) :
    (1 / 576 : ℝ) * (∑ i : Fin 17, (x i) ^ 2) ≤
      ∑ i : Fin 17, (centralCrossingBlock x i) ^ 2 := by
  have hscalar := crossingCentralSeventeenScalar_gap
    (crossingEnergy - 3 / 2) (x 0)
    (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
    (x 9) (x 10) (x 11) (x 12) (x 13) (x 14) (x 15) (x 16)
    (le_of_lt crossingCentralConstantDiagonal_gt_three)
    hxa hya
  have hleft :
      (∑ i : Fin 17, (x i) ^ 2) =
        (x 0) ^ 2 + (x 1) ^ 2 +
        (x 2) ^ 2 +
        (x 3) ^ 2 +
        (x 4) ^ 2 +
        (x 5) ^ 2 +
        (x 6) ^ 2 +
        (x 7) ^ 2 +
        (x 8) ^ 2 +
        (x 9) ^ 2 +
        (x 10) ^ 2 +
        (x 11) ^ 2 +
        (x 12) ^ 2 +
        (x 13) ^ 2 +
        (x 14) ^ 2 +
        (x 15) ^ 2 +
        (x 16) ^ 2 := by
    norm_num [Fin.sum_univ_succ]
  have hright :
      (∑ i : Fin 17, (centralCrossingBlock x i) ^ 2) =
        ((crossingEnergy - 3 / 2) * x 0 +
          (x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8) / 16) ^ 2 +
        ((x 0 + x 9 + x 16) ^ 2 +
        (x 0 + x 10 + x 9) ^ 2 +
        (x 0 + x 11 + x 10) ^ 2 +
        (x 0 + x 12 + x 11) ^ 2 +
        (x 0 + x 13 + x 12) ^ 2 +
        (x 0 + x 14 + x 13) ^ 2 +
        (x 0 + x 15 + x 14) ^ 2 +
        (x 0 + x 16 + x 15) ^ 2) / 256 +
        ((x 1 + x 2) ^ 2 +
        (x 2 + x 3) ^ 2 +
        (x 3 + x 4) ^ 2 +
        (x 4 + x 5) ^ 2 +
        (x 5 + x 6) ^ 2 +
        (x 6 + x 7) ^ 2 +
        (x 7 + x 8) ^ 2 +
        (x 8 + x 1) ^ 2) / 256 := by
    simp only [Fin.sum_univ_succ, centralCrossingBlock_values]
    ring
  rw [hleft, hright]
  exact hscalar

end
end SpectralGeometry.AmmannBeenker
