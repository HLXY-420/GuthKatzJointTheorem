import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import GuthKatzJointTheorem.Geometry

abbrev PolyR3 := MvPolynomial (Fin 3) ℝ

-- Shorthand for partial derivative
noncomputable def PDeriv3 (P : PolyR3) (i : Fin 3) : PolyR3 :=
  pderiv i P

-- Lemma 1: Parameter Counting / Minimal Degree Polynomial
-- For any non-empty set of joints, there exists a polynomial of minimal degree
-- that vanishes on all joints, and its degree is bounded by 3 * |S|^(1/3).
theorem exists_min_degree_poly (S : Finset Point3) (hS : S.Nonempty) :
    ∃ P : PolyR3, P ≠ 0 ∧
    (∀ p ∈ S, eval p P = 0) ∧
    ((totalDegree P : ℝ) ≤ 3 * (S.card : ℝ) ^ (1/3 : ℝ)) ∧
    (∀ Q : PolyR3, Q ≠ 0 → (∀ p ∈ S, eval p Q = 0) → totalDegree P ≤ totalDegree Q) := by
  -- Use `FiniteDimensional` rank arguments to prove existence.
  -- Use `Nat.find` or `WellFounded` to select the one of minimal degree.
  sorry

-- Lemma 2: Vanishing on a line
theorem poly_vanishes_on_line (P : PolyR3) (l : Line3) (S : Finset Point3)
    (h_subset : ∀ p ∈ S, l.contains p)
    (h_roots : ∀ p ∈ S, eval p P = 0)
    (h_deg : (totalDegree P : ℝ) < S.card) :
    ∀ p : Point3, l.contains p → eval p P = 0 := by
  -- Parameterize the line as a univariate polynomial `Polynomial ℝ`.
  -- A univariate polynomial of degree D with > D roots is the zero polynomial.
  sorry

-- Lemma 3: Gradient vanishing at a joint
theorem gradient_zero_at_joint (P : PolyR3) (p : Point3) (L : Finset Line3)
    (h_joint : IsJoint p L)
    (h_vanish : ∀ l ∈ L, ∀ x : Point3, l.contains x → eval x P = 0) :
    ∀ i : Fin 3, eval p (PDeriv3 P i) = 0 := by
  -- Directional derivatives along 3 linearly independent vectors (h_joint) are 0.
  -- Thus the full gradient must be the zero vector.
  sorry
