import Mathlib.Analysis.SpecialFunctions.Pow.Real

import GuthKatzJointTheorem.Geometry
import GuthKatzJointTheorem.Algebra

set_option linter.style.openClassical false

open Classical

-- Fact: the degree of a partial derivative is strictly less than the degree of the polynomial.
lemma pderiv_degree_lt (P : PolyR3) (i : Fin 3) (hP : PDeriv3 P i ≠ 0) :
    MvPolynomial.totalDegree (PDeriv3 P i) < MvPolynomial.totalDegree P := by
    sorry

-- Fact: if all partial derivatives of a polynomial are zero, then the polynomial is a constant.
lemma pderiv_zero_implies_const (P : PolyR3) (h : ∀ i : Fin 3, PDeriv3 P i = 0) :
    ∃ c : ℝ, P = MvPolynomial.C c := by
    sorry

-- The core contradiction: At least one line must have relatively few joints.
theorem exists_sparse_line (L : Finset Line3) (hL : L.Nonempty) (hJ : (Joints L).Nonempty) :
    ∃ l ∈ L, ((Joints L).filter (fun p => l.contains p)).card
    ≤ 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
  -- 1. Proceed by contradiction: assume EVERY line has > 3 * |J|^(1/3) joints.
  by_contra h
  push_neg at h
  -- 2. Let P be the minimal degree polynomial from `exists_min_degree_poly (Joints L)`.
  rcases exists_min_degree_poly (Joints L) hJ with ⟨P, P_neq_0, P_roots, P_deg, P_min⟩

  -- 3. We know deg(P) ≤ 3 * |J|^(1/3).
  -- 4. Therefore, on every line `l`, the number of joints is strictly greater than deg(P).
  have h_deg_lt : ∀ l ∈ L, (MvPolynomial.totalDegree P : ℝ)
    < ((Joints L).filter (fun p => l.contains p)).card := by
    intro l hl
    calc (MvPolynomial.totalDegree P : ℝ) ≤ 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := P_deg
      _ < ((Joints L).filter (fun p => l.contains p)).card := h l hl

  -- 5. By `poly_vanishes_on_line`, P vanishes entirely on every line `l ∈ L`.
  have P_line_zero : ∀ l ∈ L, evalPLine P l = 0 := by
    intro l hl
    let S_l := (Joints L).filter (fun p => l.contains p)
    have h_subset : ∀ p ∈ S_l, l.contains p := fun p hp => (Finset.mem_filter.mp hp).2
    have h_roots_l : ∀ p ∈ S_l, evalP P p = 0 := fun p hp => P_roots p (Finset.mem_filter.mp hp).1
    have h_deg_l : (MvPolynomial.totalDegree P : ℝ) < S_l.card := h_deg_lt l hl
    exact poly_vanishes_on_line_helper P l S_l h_subset h_roots_l h_deg_l

  -- 6. By `gradient_zero_at_joint`, the gradient ∇P vanishes on every joint `p ∈ Joints L`.
  have grad_zero : ∀ p ∈ Joints L, ∀ i : Fin 3, evalP (PDeriv3 P i) p = 0 := by
    intro p hp i
    have h_joint : IsJoint p L := (Finset.mem_filter.mp hp).2
    exact gradient_zero_at_joint P p L h_joint (fun l hl => P_line_zero l hl) i

  -- 7. The partial derivatives ∂P/∂x_i have degree strictly less than deg(P).
  -- 8. Since ∇P vanishes on `Joints L`, by the minimality of P, ∇P must be identically 0.
  have grad_identically_zero : ∀ i : Fin 3, PDeriv3 P i = 0 := by
    intro i
    by_contra h_not_zero
    have h_roots_deriv : ∀ p ∈ Joints L, evalP (PDeriv3 P i) p = 0 := fun p hp => grad_zero p hp i
    have h_min_deg := P_min (PDeriv3 P i) h_not_zero h_roots_deriv
    have h_lt_deg : MvPolynomial.totalDegree (PDeriv3 P i) < MvPolynomial.totalDegree P :=
      pderiv_degree_lt P i h_not_zero
    linarith

  -- 9. If all partial derivatives are 0, P is a constant.
  have P_is_const : ∃ c : ℝ, P = MvPolynomial.C c :=
    pderiv_zero_implies_const P grad_identically_zero
  rcases P_is_const with ⟨c, hc⟩

  -- 10. Since P vanishes on the joints, that constant is 0, so P = 0.
  have c_zero : MvPolynomial.C c = (0 : PolyR3) := by
    rcases hJ with ⟨p, hp⟩
    have h_eval : evalP P p = 0 := P_roots p hp
    rw [hc] at h_eval
    have h_eval_C : evalP (MvPolynomial.C c) p = c := by
      unfold evalP
      exact MvPolynomial.eval_C c
    rw [h_eval_C] at h_eval
    rw [h_eval]
    exact MvPolynomial.C_0

  have P_zero : P = 0 := by
    rw [hc]
    exact c_zero

  -- 11. This contradicts the fact that P ≠ 0.
  exact P_neq_0 P_zero
