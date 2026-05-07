import Mathlib.Analysis.SpecialFunctions.Pow.Real

import GuthKatzJointTheorem.Geometry
import GuthKatzJointTheorem.Algebra

set_option linter.style.openClassical false

open Classical
open MvPolynomial
lemma coeff_pderiv (P : PolyR3) (i : Fin 3) (m : Fin 3 →₀ ℕ) :
    coeff m (pderiv i P) = coeff (m + Finsupp.single i 1) P * (m i + 1) := by
  induction P using MvPolynomial.induction_on'
  case add P Q hP hQ =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hP, hQ]
    ring
  case monomial m' c =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h_eq : m + Finsupp.single i 1 = m'
    · subst h_eq
      have h1 : m + Finsupp.single i 1 - Finsupp.single i 1 = m := by
        ext j
        by_cases h : j = i
        · subst h
          simp
        · simp
      simp [h1]
    · have h_eq' : m' ≠ m + Finsupp.single i 1 := Ne.symm h_eq
      by_cases h1 : m' - Finsupp.single i 1 = m
      · subst h1
        have h_zero : m' i = 0 := by
          by_contra hc
          have hc' : 0 < m' i := Nat.pos_of_ne_zero hc
          have h2 : m' - Finsupp.single i 1 + Finsupp.single i 1 = m' := by
            ext j
            by_cases h : j = i
            · subst h
              simp only [Finsupp.coe_add, Finsupp.coe_tsub]
              simp only [Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
              exact Nat.sub_add_cancel hc'
            · simp [h]
          exact h_eq h2
        simp [h_zero, h_eq']
      · simp [h1, h_eq']

-- Fact: the degree of a partial derivative is strictly less than the degree of the polynomial.
lemma pderiv_degree_lt (P : PolyR3) (i : Fin 3) (hP : PDeriv3 P i ≠ 0) :
    MvPolynomial.totalDegree (PDeriv3 P i) < MvPolynomial.totalDegree P := by
  have h_exists : ∃ m ∈ (PDeriv3 P i).support, m.sum (fun _ e => e) =
      (PDeriv3 P i).totalDegree := by
    have h_nonempty : (PDeriv3 P i).support.Nonempty := by
      exact Finsupp.support_nonempty_iff.mpr hP
    have h_ex := Finset.exists_mem_eq_sup _ h_nonempty (fun m : Fin 3 →₀ ℕ => m.sum (fun _ e => e))
    rcases h_ex with ⟨m, hm, h_eq⟩
    use m
    exact ⟨hm, h_eq.symm⟩
  rcases h_exists with ⟨m, hm_supp, hm_deg⟩
  have h_coeff : coeff m (PDeriv3 P i) ≠ 0 := Finsupp.mem_support_iff.mp hm_supp
  have h_coeff_pderiv := coeff_pderiv P i m
  change coeff m (pderiv i P) = _ at h_coeff_pderiv
  change coeff m (pderiv i P) ≠ 0 at h_coeff
  rw [h_coeff_pderiv] at h_coeff
  have h_coeff_P : coeff (m + Finsupp.single i 1) P ≠ 0 := by
    intro hc
    rw [hc] at h_coeff
    simp at h_coeff
  have h_supp_P : m + Finsupp.single i 1 ∈ P.support := Finsupp.mem_support_iff.mpr h_coeff_P
  have h_deg_P : (m + Finsupp.single i 1).sum (fun _ e => e) ≤ P.totalDegree := by
    exact Finset.le_sup (f := fun (m : Fin 3 →₀ ℕ) => m.sum (fun _ e => e)) h_supp_P
  have h_sum_add : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index]
    · simp
    · intro _ _
      rfl
    · intro _ _ _ _
      rfl
  rw [h_sum_add, hm_deg] at h_deg_P
  exact Nat.lt_of_succ_le h_deg_P

-- Fact: if all partial derivatives of a polynomial are zero, then the polynomial is a constant.
lemma pderiv_zero_implies_const (P : PolyR3) (h : ∀ i : Fin 3, PDeriv3 P i = 0) :
    ∃ c : ℝ, P = MvPolynomial.C c := by
  use coeff 0 P
  ext m
  by_cases h0 : m = 0
  · subst h0
    simp
  · have h_exists : ∃ i : Fin 3, 0 < m i := by
      by_contra hc
      push_neg at hc
      have h_zero : m = 0 := by
        ext i
        exact Nat.eq_zero_of_le_zero (hc i)
      exact h0 h_zero
    rcases h_exists with ⟨i, hi⟩
    have h_eval := coeff_pderiv P i (m - Finsupp.single i 1)
    have h_zero := h i
    change pderiv i P = 0 at h_zero
    rw [h_zero] at h_eval
    rw [coeff_zero] at h_eval
    have h_rebuild : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
      ext j
      by_cases h_eq : j = i
      · subst h_eq
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
        simp only [Finsupp.single_eq_same]
        exact Nat.sub_add_cancel hi
      · simp [h_eq]
    rw [h_rebuild] at h_eval
    have h_eq_zero : coeff m P * (m i) = 0 := by
      revert h_eval
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      intro h_eval
      have h_sub : ((m i - 1 : ℕ) : ℝ) + 1 = m i := by
        rw [Nat.cast_sub hi]
        have : m i - 1 + 1 = m i := Nat.sub_add_cancel hi
        simp
      rw [h_sub] at h_eval
      exact h_eval.symm
    have hm_i_pos : (m i : ℝ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (ne_of_gt hi)
    cases mul_eq_zero.mp h_eq_zero with
    | inl hP =>
      rw [coeff_C]
      rw [if_neg (Ne.symm h0)]
      exact hP
    | inr hm =>
      exfalso
      exact hm_i_pos hm

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
