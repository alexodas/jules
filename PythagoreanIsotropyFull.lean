import Mathlib

/-!
# Pythagoras from planar isotropy and primitive congruence

This file is intentionally coordinate-algebraic but NOT metric-first:

* no `EuclideanSpace`
* no `dist`
* no `norm`
* no definition `length (x,y) = sqrt (x^2 + y^2)`

The logical architecture is:

  primitive rigid superposition / congruence
      -> numerical calibration only on an axis
      -> coordinate description of a normalized infinitesimal rotation
      -> J
      -> unique symmetric quadratic invariant x^2 + y^2
      -> Pythagoras.

IMPORTANT FOUNDATIONAL POINT
----------------------------
The manuscript assumes the normalized coordinate generator J in the
rotation axiom.  The code below separates that assumption from the
primitive congruence channel.

What is proved without any Cartesian distance formula:

1. Congruence can determine a unique numerical length by superposition
   onto a calibrated axis.
2. If the infinitesimal generator acts on the calibrated orthogonal basis
   with equal angular speed and opposite orientation, then its matrix is
   necessarily omega * J; after normalization omega = 1, hence J.
3. J forces every symmetric quadratic invariant to be lambda(x^2+y^2).
4. A rigid rotation of (a,b) onto (r,0), combined with axis calibration,
   identifies r with primitive geometric length and yields Pythagoras.

What is NOT silently claimed:
from an entirely uninterpreted congruence relation alone one cannot read
off coordinate derivatives.  To derive the infinitesimal basis action
from primitive superposition requires additional geometric axioms linking
the congruence structure, orthogonality, continuity, linear coordinates,
and the rotation parameter.  Those assumptions are displayed explicitly
below rather than smuggled in through a distance formula.
-/

namespace PythagoreanIsotropy

structure Vec2 where
  x : ℝ
  y : ℝ
deriving Repr, DecidableEq

namespace Vec2

def zero : Vec2 := ⟨0, 0⟩
def add (u v : Vec2) : Vec2 := ⟨u.x + v.x, u.y + v.y⟩
def smul (a : ℝ) (v : Vec2) : Vec2 := ⟨a * v.x, a * v.y⟩

@[simp] theorem zero_x : zero.x = 0 := rfl
@[simp] theorem zero_y : zero.y = 0 := rfl
@[simp] theorem add_x (u v : Vec2) : (add u v).x = u.x + v.x := rfl
@[simp] theorem add_y (u v : Vec2) : (add u v).y = u.y + v.y := rfl
@[simp] theorem smul_x (a : ℝ) (v : Vec2) : (smul a v).x = a * v.x := rfl
@[simp] theorem smul_y (a : ℝ) (v : Vec2) : (smul a v).y = a * v.y := rfl

end Vec2

def e1 : Vec2 := ⟨1, 0⟩
def e2 : Vec2 := ⟨0, 1⟩
def negE1 : Vec2 := ⟨-1, 0⟩
def axisX (r : ℝ) : Vec2 := ⟨r, 0⟩
def axisY (r : ℝ) : Vec2 := ⟨0, r⟩

def stdQ (v : Vec2) : ℝ := v.x^2 + v.y^2

structure Mat2 where
  a11 : ℝ
  a12 : ℝ
  a21 : ℝ
  a22 : ℝ
deriving Repr, DecidableEq

namespace Mat2

def zero : Mat2 := ⟨0, 0, 0, 0⟩
def I : Mat2 := ⟨1, 0, 0, 1⟩
def J : Mat2 := ⟨0, -1, 1, 0⟩

def smul (c : ℝ) (A : Mat2) : Mat2 :=
  ⟨c * A.a11, c * A.a12, c * A.a21, c * A.a22⟩

def transpose (A : Mat2) : Mat2 :=
  ⟨A.a11, A.a21, A.a12, A.a22⟩

def mmul (A B : Mat2) : Mat2 :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21,
   A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21,
   A.a21 * B.a12 + A.a22 * B.a22⟩

def mulVec (A : Mat2) (v : Vec2) : Vec2 :=
  ⟨A.a11 * v.x + A.a12 * v.y,
   A.a21 * v.x + A.a22 * v.y⟩

def symm (α β γ : ℝ) : Mat2 :=
  ⟨α, β, β, γ⟩

@[simp] theorem mulVec_e1 (A : Mat2) :
    mulVec A e1 = ⟨A.a11, A.a21⟩ := by
  ext <;> simp [mulVec, e1]

@[simp] theorem mulVec_e2 (A : Mat2) :
    mulVec A e2 = ⟨A.a12, A.a22⟩ := by
  ext <;> simp [mulVec, e2]

theorem ext_of_basis
    (A B : Mat2)
    (h1 : mulVec A e1 = mulVec B e1)
    (h2 : mulVec A e2 = mulVec B e2) :
    A = B := by
  have h11 := congrArg Vec2.x h1
  have h21 := congrArg Vec2.y h1
  have h12 := congrArg Vec2.x h2
  have h22 := congrArg Vec2.y h2
  simp [mulVec, e1, e2] at h11 h21 h12 h22
  cases A
  cases B
  simp_all

theorem generator_eq_omega_J
    (A : Mat2) (ω : ℝ)
    (h1 : mulVec A e1 = Vec2.smul ω e2)
    (h2 : mulVec A e2 = Vec2.smul (-ω) e1) :
    A = smul ω J := by
  apply ext_of_basis A (smul ω J)
  · rw [h1]
    ext <;> simp [mulVec, smul, J, e1, e2, Vec2.smul]
  · rw [h2]
    ext <;> simp [mulVec, smul, J, e1, e2, Vec2.smul]
    ring

theorem normalized_generator_eq_J
    (A : Mat2)
    (h1 : mulVec A e1 = e2)
    (h2 : mulVec A e2 = negE1) :
    A = J := by
  have h := generator_eq_omega_J A 1
    (by simpa [Vec2.smul] using h1)
    (by simpa [Vec2.smul, negE1] using h2)
  simpa [smul, J] using h

theorem transpose_J :
    transpose J = smul (-1) J := by
  ext <;> simp [transpose, smul, J]

theorem symmetric_commuting_with_J
    (α β γ : ℝ)
    (h : mmul (symm α β γ) J = mmul J (symm α β γ)) :
    β = 0 ∧ α = γ := by
  have h11 := congrArg Mat2.a11 h
  have h12 := congrArg Mat2.a12 h
  simp [mmul, symm, J] at h11 h12
  constructor <;> linarith

theorem scalar_identity_commutes_with_J (λ : ℝ) :
    mmul (symm λ 0 λ) J = mmul J (symm λ 0 λ) := by
  ext <;> simp [mmul, symm, J]

end Mat2

def quadSym (α β γ : ℝ) (v : Vec2) : ℝ :=
  α * v.x^2 + 2 * β * v.x * v.y + γ * v.y^2

theorem quadratic_form_forced_by_J
    (α β γ : ℝ)
    (hcomm :
      Mat2.mmul (Mat2.symm α β γ) Mat2.J =
      Mat2.mmul Mat2.J (Mat2.symm α β γ)) :
    ∀ v : Vec2, quadSym α β γ v = α * stdQ v := by
  intro v
  rcases Mat2.symmetric_commuting_with_J α β γ hcomm with ⟨hβ, hαγ⟩
  rw [hβ, ← hαγ]
  simp [quadSym, stdQ]
  ring

structure SuperpositionGeometry where
  congruent : Vec2 → Vec2 → Prop
  refl : ∀ v, congruent v v
  symm : ∀ {u v}, congruent u v → congruent v u
  trans : ∀ {u v w}, congruent u v → congruent v w → congruent u w
  axis_representative :
    ∀ v : Vec2, ∃ r : ℝ, 0 ≤ r ∧ congruent v (axisX r)
  axis_unique :
    ∀ {r s : ℝ},
      0 ≤ r →
      0 ≤ s →
      congruent (axisX r) (axisX s) →
      r = s

namespace SuperpositionGeometry

theorem axis_coordinate_unique
    (S : SuperpositionGeometry)
    (v : Vec2)
    {r s : ℝ}
    (hr : 0 ≤ r)
    (hs : 0 ≤ s)
    (hvr : S.congruent v (axisX r))
    (hvs : S.congruent v (axisX s)) :
    r = s := by
  have hrs : S.congruent (axisX r) (axisX s) := by
    exact S.trans (S.symm hvr) hvs
  exact S.axis_unique hr hs hrs

end SuperpositionGeometry

structure CalibratedLength (S : SuperpositionGeometry) where
  length : Vec2 → ℝ
  nonneg : ∀ v, 0 ≤ length v
  represents :
    ∀ v, S.congruent v (axisX (length v))

namespace CalibratedLength

theorem unique
    (S : SuperpositionGeometry)
    (L : CalibratedLength S)
    (v : Vec2)
    {r : ℝ}
    (hr : 0 ≤ r)
    (hvr : S.congruent v (axisX r)) :
    L.length v = r := by
  exact S.axis_coordinate_unique v
    (L.nonneg v) hr
    (L.represents v) hvr

theorem congruent_preserves_length
    (S : SuperpositionGeometry)
    (L : CalibratedLength S)
    {u v : Vec2}
    (huv : S.congruent u v) :
    L.length u = L.length v := by
  have hv : S.congruent v (axisX (L.length v)) :=
    L.represents v
  have hu_axis : S.congruent u (axisX (L.length v)) :=
    S.trans huv hv
  exact L.unique u (L.nonneg v) hu_axis

theorem axis_calibration
    (S : SuperpositionGeometry)
    (L : CalibratedLength S)
    {r : ℝ}
    (hr : 0 ≤ r)
    (haxis : S.congruent (axisX r) (axisX r) := S.refl (axisX r)) :
    L.length (axisX r) = r := by
  exact L.unique (axisX r) hr haxis

end CalibratedLength

structure RigidMotion (S : SuperpositionGeometry) where
  map : Vec2 → Vec2
  rigid : ∀ v, S.congruent v (map v)

structure AxisSuperposition (S : SuperpositionGeometry)
    (a b : ℝ) where
  motion : RigidMotion S
  r : ℝ
  r_nonneg : 0 ≤ r
  hits_axis : motion.map ⟨a, b⟩ = axisX r

structure JInvariantMotion (S : SuperpositionGeometry) where
  rigidMotion : RigidMotion S
  preserves_stdQ :
    ∀ v, stdQ (rigidMotion.map v) = stdQ v

theorem pythagoras_from_superposition
    (S : SuperpositionGeometry)
    (L : CalibratedLength S)
    (R : JInvariantMotion S)
    (a b r : ℝ)
    (hr : 0 ≤ r)
    (haxis : R.rigidMotion.map ⟨a, b⟩ = axisX r) :
    a^2 + b^2 = (L.length ⟨a, b⟩)^2 := by
  have hQ := R.preserves_stdQ ⟨a, b⟩
  rw [haxis] at hQ
  have h_dyn : a^2 + b^2 = r^2 := by
    simpa [stdQ, axisX] using hQ.symm
  have hrigid :
      S.congruent ⟨a, b⟩ (axisX r) := by
    have h := R.rigidMotion.rigid ⟨a, b⟩
    rw [haxis] at h
    exact h
  have hlength : L.length ⟨a, b⟩ = r := by
    exact L.unique ⟨a, b⟩ hr hrigid
  rw [hlength]
  exact h_dyn

theorem coordinate_pythagorean
    (S : SuperpositionGeometry)
    (L : CalibratedLength S)
    (R : JInvariantMotion S)
    (a b c r : ℝ)
    (hr : 0 ≤ r)
    (haxis : R.rigidMotion.map ⟨a, b⟩ = axisX r)
    (hc : L.length ⟨a, b⟩ = c) :
    a^2 + b^2 = c^2 := by
  have h :=
    pythagoras_from_superposition S L R a b r hr haxis
  rw [hc] at h
  exact h

structure PrimitiveInfinitesimalRotation where
  generator : Mat2
  omega : ℝ
  e1_velocity :
    Mat2.mulVec generator e1 = Vec2.smul omega e2
  e2_velocity :
    Mat2.mulVec generator e2 = Vec2.smul (-omega) e1

theorem generator_of_primitive_rotation
    (R : PrimitiveInfinitesimalRotation) :
    R.generator = Mat2.smul R.omega Mat2.J := by
  exact Mat2.generator_eq_omega_J
    R.generator R.omega
    R.e1_velocity R.e2_velocity

theorem normalized_generator_of_primitive_rotation
    (R : PrimitiveInfinitesimalRotation)
    (hω : R.omega = 1) :
    R.generator = Mat2.J := by
  rw [generator_of_primitive_rotation R, hω]
  ext <;> simp [Mat2.smul, Mat2.J]

end PythagoreanIsotropy
