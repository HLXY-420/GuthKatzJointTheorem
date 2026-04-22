import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import GuthKatzJointTheorem.Geometry

abbrev PolyR3 := MvPolynomial (Fin 3) ℝ

def evalP (P : PolyR3) (p : Point3) : ℝ :=
  MvPolynomial.eval p P

def evalPLine (P : PolyR3) (l : Line3) : (Polynomial ℝ) := sorry

-- Shorthand for partial derivative
noncomputable def PDeriv3 (P : PolyR3) (i : Fin 3) : PolyR3 :=
  MvPolynomial.pderiv i P

-- Lemma 1: Parameter Counting / Minimal Degree Polynomial
-- For any non-empty set of joints, there exists a polynomial of minimal degree
-- that vanishes on all joints, and its degree is bounded by 3 * |S|^(1/3).
theorem exists_min_degree_poly (S : Finset Point3) (hS : S.Nonempty) :
    ∃ P : PolyR3, P ≠ 0 ∧
    (∀ p ∈ S, evalP P p = 0) ∧
    ((MvPolynomial.totalDegree P : ℝ) ≤ 3 * (S.card : ℝ) ^ (1/3 : ℝ)) ∧
    (∀ Q : PolyR3, Q ≠ 0 → (∀ p ∈ S, evalP Q p = 0) → MvPolynomial.totalDegree P ≤ MvPolynomial.totalDegree Q) := by
  -- Use `FiniteDimensional` rank arguments to prove existence.
  -- Use `Nat.find` or `WellFounded` to select the one of minimal degree.
  sorry

-- Lemma 2: Vanishing on a line
theorem poly_vanishes_on_line (P : PolyR3) (l : Line3) (S : Finset Point3)
    (h_subset : ∀ p ∈ S, l.contains p)
    (h_roots : ∀ p ∈ S, evalP P p = 0)
    (h_deg : (MvPolynomial.totalDegree P : ℝ) < S.card) :
    ∀ p : Point3, l.contains p → evalP P p = 0 := by
  -- Parameterize the line as a univariate polynomial `Polynomial ℝ`.
  -- A univariate polynomial of degree D with > D roots is the zero polynomial.
  sorry

-- Lemma 3: Gradient vanishing at a joint
theorem gradient_zero_at_joint (P : PolyR3) (p : Point3) (L : Finset Line3)
    (h_joint : IsJoint p L)
    (h_vanish : ∀ l ∈ L, evalPLine P l = 0) :
    ∀ i : Fin 3, evalP (PDeriv3 P i) p = 0 := by
  -- Directional derivatives along 3 linearly independent vectors (h_joint) are 0.
  -- Thus the full gradient must be the zero vector.
  sorry
