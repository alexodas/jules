import PythagoreanIsotropyFull

namespace PythagoreanIsotropy

/-!
# Stronger foundational layer: derive J from synthetic isotropy data

This file removes the need to postulate both basis velocities of the
infinitesimal rotation.  Instead it assumes only a calibrated oriented
quarter-turn, covariance of the generator under that quarter-turn,
tangency at e1, and a positive unit parameter normalization.

No norm, distance, square root, or Pythagorean identity occurs in these
axioms.
-/

/--
Synthetic infinitesimal rotation data.

* `quarter_e1` and `quarter_e2` calibrate the positive quarter-turn.
* `isotropic` says the infinitesimal generator is equivariant under that
  quarter-turn.
* `e1_tangent` says the initial velocity at e1 has no e1 component.
* `positive_normalization` fixes the orientation and parameter scale.
-/
structure SyntheticInfinitesimalRotation where
  generator : Mat2
  quarterTurn : Mat2
  quarter_e1 : Mat2.mulVec quarterTurn e1 = e2
  quarter_e2 : Mat2.mulVec quarterTurn e2 = negE1
  isotropic :
    Mat2.mmul generator quarterTurn =
    Mat2.mmul quarterTurn generator
  e1_tangent : (Mat2.mulVec generator e1).x = 0
  positive_normalization : (Mat2.mulVec generator e1).y = 1

/-- The calibrated positive quarter-turn is forced to be J. -/
theorem synthetic_quarter_turn_eq_J
    (R : SyntheticInfinitesimalRotation) :
    R.quarterTurn = Mat2.J := by
  apply Mat2.ext_of_basis R.quarterTurn Mat2.J
  · rw [R.quarter_e1]
    apply Vec2.ext'
    · simp [Mat2.mulVec, Mat2.J, e1, e2]
    · simp [Mat2.mulVec, Mat2.J, e1, e2]
  · rw [R.quarter_e2]
    apply Vec2.ext'
    · simp [Mat2.mulVec, Mat2.J, e2, negE1]
    · simp [Mat2.mulVec, Mat2.J, e2, negE1]

/-- Tangency and normalization derive the first basis velocity. -/
theorem synthetic_e1_velocity
    (R : SyntheticInfinitesimalRotation) :
    Mat2.mulVec R.generator e1 = e2 := by
  apply Vec2.ext'
  · exact R.e1_tangent
  · exact R.positive_normalization

/--
The second basis velocity is not assumed.  It follows from isotropic
covariance with the quarter-turn.
-/
theorem synthetic_e2_velocity
    (R : SyntheticInfinitesimalRotation) :
    Mat2.mulVec R.generator e2 = negE1 := by
  have hK : R.quarterTurn = Mat2.J := synthetic_quarter_turn_eq_J R
  have hcomm :
      Mat2.mmul R.generator Mat2.J =
      Mat2.mmul Mat2.J R.generator := by
    simpa [hK] using R.isotropic
  have h11 := congrArg Mat2.a11 hcomm
  have h12 := congrArg Mat2.a12 hcomm
  have ht := R.e1_tangent
  have hn := R.positive_normalization
  simp [Mat2.mmul, Mat2.J, Mat2.mulVec, e1] at h11 h12 ht hn
  apply Vec2.ext'
  · simp [Mat2.mulVec, e2, negE1]
    linarith
  · simp [Mat2.mulVec, e2, negE1]
    linarith

/--
The normalized infinitesimal generator is therefore J, with no metric
formula used in its derivation.
-/
theorem generator_eq_J_from_synthetic_isotropy
    (R : SyntheticInfinitesimalRotation) :
    R.generator = Mat2.J := by
  exact Mat2.normalized_generator_eq_J R.generator
    (synthetic_e1_velocity R)
    (synthetic_e2_velocity R)

end PythagoreanIsotropy
