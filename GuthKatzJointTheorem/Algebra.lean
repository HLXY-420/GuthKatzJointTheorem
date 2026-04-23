import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import GuthKatzJointTheorem.Geometry

abbrev PolyR3 := MvPolynomial (Fin 3) ℝ

def evalP (P : PolyR3) (p : Point3) : ℝ :=
  MvPolynomial.eval p P

noncomputable def evalPLine (P : PolyR3) (l : Line3) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C (fun i =>
    Polynomial.C (l.base i) + Polynomial.X * Polynomial.C (l.dir i)) P

-- Shorthand for partial derivative
noncomputable def PDeriv3 (P : PolyR3) (i : Fin 3) : PolyR3 :=
  MvPolynomial.pderiv i P

-- Lemmas for Lemma 1

-- Parameter counting: if the number of monomials of degree ≤ d in 3 variables
-- exceeds |S|, there exists a nonzero polynomial of degree ≤ d vanishing on S.
-- The dimension of the space of polynomials of degree ≤ d in 3 variables is C(d+3,3).
lemma poly_vanishing_exists (S : Finset Point3) (d : ℕ)
    (h_param : S.card < Nat.choose (d + 3) 3) :
    ∃ P : PolyR3, P ≠ 0 ∧ (∀ p ∈ S, evalP P p = 0)
     ∧ (MvPolynomial.totalDegree P : ℝ) ≤ (d : ℝ) := sorry

-- The parameter counting condition is satisfiable at the cube-root scale:
-- there exists d ≤ 3 * |S|^(1/3) with C(d+3,3) > |S|.
lemma param_count_at_cube_root (S : Finset Point3) (hS : S.Nonempty) :
    ∃ d : ℕ, (d : ℝ) ≤ 3 * (S.card : ℝ) ^ (1/3 : ℝ)
    ∧ S.card < Nat.choose (d + 3) 3 := sorry

lemma min_degree_poly_exists (S : Finset Point3) (P : PolyR3) (hP_neq : P ≠ 0)
    (hP_vanish : ∀ p ∈ S, evalP P p = 0) :
    ∃ P_min : PolyR3, P_min ≠ 0 ∧ (∀ p ∈ S, evalP P_min p = 0)
    ∧ (∀ Q : PolyR3, Q ≠ 0 → (∀ p ∈ S, evalP Q p = 0)
     → MvPolynomial.totalDegree P_min ≤ MvPolynomial.totalDegree Q) := sorry

-- Lemma 1: Parameter Counting / Minimal Degree Polynomial
-- For any non-empty set of joints, there exists a polynomial of minimal degree
-- that vanishes on all joints, and its degree is bounded by 3 * |S|^(1/3).
theorem exists_min_degree_poly (S : Finset Point3) (hS : S.Nonempty) :
    ∃ P : PolyR3, P ≠ 0 ∧
    (∀ p ∈ S, evalP P p = 0) ∧
    ((MvPolynomial.totalDegree P : ℝ) ≤ 3 * (S.card : ℝ) ^ (1/3 : ℝ)) ∧
    (∀ Q : PolyR3, Q ≠ 0 → (∀ p ∈ S, evalP Q p = 0) →
      MvPolynomial.totalDegree P ≤ MvPolynomial.totalDegree Q) := by
  -- Obtain d with the degree bound and parameter counting condition
  rcases param_count_at_cube_root S hS with ⟨d, hd, h_param⟩
  -- Use parameter counting to get a nonzero vanishing polynomial of degree ≤ d
  rcases poly_vanishing_exists S d h_param with ⟨P, hP_neq, hP_vanish, hP_deg⟩
  -- Extract the minimal-degree polynomial among all vanishing polynomials
  rcases min_degree_poly_exists S P hP_neq hP_vanish with ⟨P_min, hP_min_neq, hP_min_vanish, hP_min_deg⟩
  use P_min
  refine ⟨hP_min_neq, hP_min_vanish, ?_, hP_min_deg⟩
  -- The minimal polynomial has degree ≤ deg(P) ≤ d ≤ 3 * |S|^(1/3)
  have h_P_min_le_P : (MvPolynomial.totalDegree P_min : ℝ) ≤ (MvPolynomial.totalDegree P : ℝ) := by
    exact_mod_cast hP_min_deg P hP_neq hP_vanish
  linarith

-- Lemmas for Lemma 2
lemma poly_vanishes_on_line_helper (P : PolyR3) (l : Line3) (S : Finset Point3)
    (h_subset : ∀ p ∈ S, l.contains p)
    (h_roots : ∀ p ∈ S, evalP P p = 0)
    (h_deg : (MvPolynomial.totalDegree P : ℝ) < S.card) :
    evalPLine P l = 0 := sorry

lemma evalPLine_zero_implies_eval_zero (P : PolyR3) (l : Line3)
    (h_zero : evalPLine P l = 0) (p : Point3) (hp : l.contains p) :
    evalP P p = 0 := by
    rcases hp with ⟨t, rfl⟩
    sorry

-- Lemma 2: Vanishing on a line
theorem poly_vanishes_on_line (P : PolyR3) (l : Line3) (S : Finset Point3)
    (h_subset : ∀ p ∈ S, l.contains p)
    (h_roots : ∀ p ∈ S, evalP P p = 0)
    (h_deg : (MvPolynomial.totalDegree P : ℝ) < S.card) :
    ∀ p : Point3, l.contains p → evalP P p = 0 := by
  intro p hp
  have h_P_line_zero : evalPLine P l = 0 :=
    poly_vanishes_on_line_helper P l S h_subset h_roots h_deg
  exact evalPLine_zero_implies_eval_zero P l h_P_line_zero p hp

-- Lemmas for Lemma 3
lemma evalPLine_zero_implies_dir_deriv_zero (P : PolyR3) (l : Line3)
    (h_vanish : evalPLine P l = 0) (i : Fin 3) :
    evalPLine (PDeriv3 P i) l = 0 := sorry

lemma dir_deriv_zero_implies_gradient_zero (P : PolyR3) (p : Point3) (l1 l2 l3 : Line3)
    (hcont1 : l1.contains p) (hcont2 : l2.contains p) (hcont3 : l3.contains p)
    (hcop : ¬ Coplanar l1 l2 l3)
    (h_dir1 : ∀ i : Fin 3, evalPLine (PDeriv3 P i) l1 = 0)
    (h_dir2 : ∀ i : Fin 3, evalPLine (PDeriv3 P i) l2 = 0)
    (h_dir3 : ∀ i : Fin 3, evalPLine (PDeriv3 P i) l3 = 0) :
    ∀ i : Fin 3, evalP (PDeriv3 P i) p = 0 := sorry

-- Lemma 3: Gradient vanishing at a joint
theorem gradient_zero_at_joint (P : PolyR3) (p : Point3) (L : Finset Line3)
    (h_joint : IsJoint p L)
    (h_vanish : ∀ l ∈ L, evalPLine P l = 0) :
    ∀ i : Fin 3, evalP (PDeriv3 P i) p = 0 := by
  rcases h_joint with ⟨l1, l2, l3, hl1, hl2, hl3, hneq12, hneq13, hneq23,
    hcont1, hcont2, hcont3, hcop⟩
  have h_dir1 : ∀ i : Fin 3, evalPLine (PDeriv3 P i) l1 = 0 := by
    intro i; exact evalPLine_zero_implies_dir_deriv_zero P l1 (h_vanish l1 hl1) i
  have h_dir2 : ∀ i : Fin 3, evalPLine (PDeriv3 P i) l2 = 0 := by
    intro i; exact evalPLine_zero_implies_dir_deriv_zero P l2 (h_vanish l2 hl2) i
  have h_dir3 : ∀ i : Fin 3, evalPLine (PDeriv3 P i) l3 = 0 := by
    intro i; exact evalPLine_zero_implies_dir_deriv_zero P l3 (h_vanish l3 hl3) i
  intro i
  exact dir_deriv_zero_implies_gradient_zero P p l1 l2 l3 hcont1 hcont2 hcont3
    hcop h_dir1 h_dir2 h_dir3 i
