import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic
import GuthKatzJointTheorem.Geometry

set_option linter.style.openClassical false

open scoped Classical

abbrev PolyR3 := MvPolynomial (Fin 3) ℝ

def evalP (P : PolyR3) (p : Point3) : ℝ :=
  MvPolynomial.eval p P

noncomputable def evalPLine (P : PolyR3) (l : Line3) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C (fun i =>
    Polynomial.C (l.base i) + Polynomial.X * Polynomial.C (l.dir i)) P

-- Shorthand for partial derivative
noncomputable def PDeriv3 (P : PolyR3) (i : Fin 3) : PolyR3 :=
  MvPolynomial.pderiv i P

-- ============================================================================
-- Lemmas for Lemma 1
-- ============================================================================

-- Parameter counting: if the number of monomials of degree ≤ d in 3 variables
-- exceeds |S|, there exists a nonzero polynomial of degree ≤ d vanishing on S.
-- The dimension of the space of polynomials of degree ≤ d in 3 variables is C(d+3,3).
-- here I give a proof for arbitrary dim n and degree D:
-- Fix D and n. We encode a monomial x_i_1 ...x_i_D by using the stars and bars method.
-- We have D stars and n-1 bars. We put the stars in a row,
-- and we put the bars in the spaces between the stars.
-- This gives us a bijection between all the monomials in Poly^D(F_n)
-- and all the strings of D '*'s and n-1 '|'s.
-- Therefore, the number of monomials is (D+n-1 choose n-1).
lemma finrank_restrictTotalDegree_fin_3 (d : ℕ) :
    Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ d) = Nat.choose (d + 3) 3 := by
  -- Convert Finsupp to Fun
  have e1 : {s : Fin 3 →₀ ℕ // s.sum (fun _ e => e) ≤ d} ≃ {f : Fin 3 → ℕ // ∑ i, f i ≤ d} := by
    refine Finsupp.equivFunOnFinite.subtypeEquiv (fun s => ?_)
    rw [Finsupp.sum_fintype]
    · rfl
    · intro
      rfl
  -- Convert ≤ d to = d
  have e2 : {f : Fin 3 → ℕ // ∑ i, f i ≤ d} ≃ {f : Fin 4 → ℕ // ∑ i, f i = d} :=
    { toFun := fun f => ⟨Fin.cons (d - ∑ i, f.1 i) f.1, by
        have hsum :
            ∑ i : Fin 4, Fin.cons (d - ∑ i : Fin 3, f.1 i) f.1 i =
              (d - ∑ i : Fin 3, f.1 i) + ∑ i : Fin 3, f.1 i := by
          simp [Fin.sum_univ_succ]
        rw [hsum]
        have h_le : ∑ i : Fin 3, f.1 i ≤ d := f.2
        omega⟩
      invFun := fun f => ⟨fun i => f.1 i.succ, by
        have h : f.1 0 + ∑ i : Fin 3, f.1 i.succ = d := by
          simpa [Fin.sum_univ_succ] using f.2
        have hle : ∑ i : Fin 3, f.1 i.succ ≤ f.1 0 + ∑ i : Fin 3, f.1 i.succ :=
          Nat.le_add_left _ _
        exact hle.trans (by simp [h])⟩
      left_inv := by
        intro f
        ext i
        simp
      right_inv := by
        intro f
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have h : f.1 0 + ∑ i : Fin 3, f.1 i.succ = d := by
            simpa [Fin.sum_univ_succ] using f.2
          have h0 : d - ∑ i : Fin 3, f.1 i.succ = f.1 0 := by
            omega
          simp [h0]
        · simp }
  -- Convert to Sym
  have e3 : {f : Fin 4 → ℕ // ∑ i, f i = d} ≃ Sym (Fin 4) d :=
    (Sym.equivNatSumOfFintype (Fin 4) d).symm
  haveI : Finite ({n : Fin 3 →₀ ℕ // n.sum (fun _ e => e) ≤ d}) :=
    Finite.of_equiv (Sym (Fin 4) d) (e1.trans (e2.trans e3)).symm
  letI : Fintype ({n : Fin 3 →₀ ℕ // n.sum (fun _ e => e) ≤ d}) := Fintype.ofFinite _
  letI : Fintype (↑({n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ d} : Set (Fin 3 →₀ ℕ))) := by
    change Fintype ({n : Fin 3 →₀ ℕ // n.sum (fun _ e => e) ≤ d})
    infer_instance
  haveI : Finite ({f : Fin 3 → ℕ // ∑ i, f i ≤ d}) :=
    Finite.of_equiv ({n : Fin 3 →₀ ℕ // n.sum (fun _ e => e) ≤ d}) e1
  letI : Fintype ({f : Fin 3 → ℕ // ∑ i, f i ≤ d}) := Fintype.ofFinite _
  haveI : Finite ({f : Fin 4 → ℕ // ∑ i, f i = d}) :=
    Finite.of_equiv (Sym (Fin 4) d) e3.symm
  letI : Fintype ({f : Fin 4 → ℕ // ∑ i, f i = d}) := Fintype.ofFinite _
  have h_basis := MvPolynomial.basisRestrictSupport ℝ {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ d}
  change Module.finrank ℝ
    ↥(MvPolynomial.restrictSupport ℝ {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ d}) =
    Nat.choose (d + 3) 3
  rw [Module.finrank_eq_card_basis h_basis]
  change Fintype.card ({n : Fin 3 →₀ ℕ // n.sum (fun _ e => e) ≤ d}) = Nat.choose (d + 3) 3
  -- Card of Sym
  rw [Fintype.card_congr e1, Fintype.card_congr e2, Fintype.card_congr e3]
  have h_card := Sym.card_sym_eq_choose (α := Fin 4) d
  have h_eq : Fintype.card (Fin 4) + d - 1 = d + 3 := by
    have : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
    omega
  rw [h_eq] at h_card
  rw [h_card]
  have h_symm : Nat.choose (d + 3) d = Nat.choose (d + 3) 3 := by
    have := Nat.choose_symm (show d ≤ d + 3 by omega)
    have hd3 : d + 3 - d = 3 := by omega
    rw [hd3] at this
    exact this.symm
  rw [h_symm]

-- Sub-lemma: The evaluation map from polynomials of degree ≤ d to ℝ^|S|
-- has a non-trivial kernel when C(d+3,3) > |S|.
-- This is a standard linear algebra fact: if dim(V) > dim(W) for a linear
-- map V → W, the kernel is non-trivial.
lemma exists_nonzero_in_ker_of_eval (S : Finset Point3) (d : ℕ)
    (h_param : S.card < Nat.choose (d + 3) 3) :
    ∃ P : PolyR3, P ≠ 0 ∧ (∀ p ∈ S, evalP P p = 0)
     ∧ MvPolynomial.totalDegree P ≤ d := by
  let V := MvPolynomial.restrictTotalDegree (Fin 3) ℝ d
  let W := S → ℝ
  let f : V →ₗ[ℝ] W :=
    { toFun := fun P p => evalP P.1 p.1
      map_add' := fun P Q => by ext p; simp [evalP]; rfl
      map_smul' := fun c P => by ext p; simp [evalP]; rfl }
  have h_dim_W : Module.finrank ℝ W = S.card := by
    rw [Module.finrank_pi_fintype]
    rw [← Fintype.card_coe]
    simp
  have h_dim_V : Module.finrank ℝ V = Nat.choose (d + 3) 3 := finrank_restrictTotalDegree_fin_3 d
  have h_lt : Module.finrank ℝ W < Module.finrank ℝ V := by
    rw [h_dim_W, h_dim_V]
    exact h_param
  have h_ker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt h_lt
  obtain ⟨P, hP_ker, hP_neq⟩ := (Submodule.ne_bot_iff f.ker).mp h_ker
  use P.1
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hP_neq
    ext
    rw [h]
    norm_cast
  · intro p hp
    have h_eval := LinearMap.mem_ker.mp hP_ker
    have h_eval_p : f P ⟨p, hp⟩ = 0 := by
      rw [h_eval, Pi.zero_apply]
    exact h_eval_p
  · exact MvPolynomial.mem_restrictTotalDegree _ _ _ |>.mp P.2

lemma poly_vanishing_exists (S : Finset Point3) (d : ℕ)
    (h_param : S.card < Nat.choose (d + 3) 3) :
    ∃ P : PolyR3, P ≠ 0 ∧ (∀ p ∈ S, evalP P p = 0)
     ∧ (MvPolynomial.totalDegree P : ℝ) ≤ (d : ℝ) := by
     -- Follows directly from the linear algebra kernel argument
     rcases exists_nonzero_in_ker_of_eval S d h_param with ⟨P, hP_neq, hP_vanish, hP_deg⟩
     exact ⟨P, hP_neq, hP_vanish, Nat.cast_le.mpr hP_deg⟩

-- The parameter counting condition is satisfiable at the cube-root scale:
-- there exists d ≤ 3 * |S|^(1/3) with C(d+3,3) > |S|.

-- Sub-lemma: for d = ⌈3 * |S|^(1/3)⌉, we have C(d+3,3) > |S|
-- This is an elementary combinatorial bound: C(d+3,3) = (d+3)(d+2)(d+1)/6 ≥ (d/3)^3
-- and when d ≥ 3|S|^(1/3), we get (d/3)^3 ≥ |S|.
lemma choose_gt_of_cube_root_bound (n : ℕ) (d : ℕ) (hn : 0 < n)
    (hd : (n : ℝ) ^ (1 / 3 : ℝ) * 3 ≤ (d : ℝ)) :
    n < Nat.choose (d + 3) 3 := by
  have hd_pos : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hn_pos : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (n : ℝ) ^ (1 / 3 : ℝ) ≤ (d : ℝ) / 3 := by linarith
  have h1_pos : 0 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have h2 : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 ≤ ((d : ℝ) / 3) ^ 3 := pow_le_pow_left₀ h1_pos h1 3
  have h_cube_nat : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (n : ℝ) := by
    rw [← Real.rpow_natCast]
    push_cast
    rw [← Real.rpow_mul hn_pos]
    norm_num
  rw [h_cube_nat] at h2
  have h_choose : (d + 3) * (d + 2) * (d + 1) = 6 * Nat.choose (d + 3) 3 := by
    have h_desc : (d + 3).descFactorial 3 = (d + 3) * (d + 2) * (d + 1) := by
      simp only [Nat.descFactorial_succ, Nat.reduceSubDiff, Nat.add_one_sub_one,
        tsub_zero, Nat.descFactorial_zero, mul_one]
      rw [Nat.mul_comm (d + 1), Nat.mul_comm (d + 3)]
    have h_fact : Nat.factorial 3 = 6 := by rfl
    have h3 := Nat.descFactorial_eq_factorial_mul_choose (d + 3) 3
    rw [h_desc, h_fact] at h3
    rw [h3.symm]
  have h_choose_R : ((d : ℝ) + 3) * ((d : ℝ) + 2) * ((d : ℝ) + 1) =
    6 * (Nat.choose (d + 3) 3 : ℝ) := by
    have h_cast : ((d + 3) * (d + 2) * (d + 1) : ℝ) =
      (6 * Nat.choose (d + 3) 3 : ℝ) := by norm_cast
    push_cast at h_cast
    exact h_cast
  have h4 : 27 * (n : ℝ) ≤ (d : ℝ) ^ 3 := by linarith
  have h5 : 6 * (n : ℝ) < 27 * (n : ℝ) := by
    have hn_pos_strict : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    linarith
  have h6 : (d : ℝ) ^ 3 < ((d : ℝ) + 3) * ((d : ℝ) + 2) * ((d : ℝ) + 1) := by nlinarith
  have h7 : 6 * (n : ℝ) < 6 * (Nat.choose (d + 3) 3 : ℝ) := by
    calc 6 * (n : ℝ) < 27 * (n : ℝ) := h5
      _ ≤ (d : ℝ) ^ 3 := h4
      _ < ((d : ℝ) + 3) * ((d : ℝ) + 2) * ((d : ℝ) + 1) := h6
      _ = 6 * (Nat.choose (d + 3) 3 : ℝ) := h_choose_R
  have h8 : (n : ℝ) < (Nat.choose (d + 3) 3 : ℝ) := by linarith
  exact Nat.cast_lt.mp h8

lemma param_count_at_cube_root (S : Finset Point3) (hS : S.Nonempty) :
    ∃ d : ℕ, (d : ℝ) ≤ 3 * (S.card : ℝ) ^ (1/3 : ℝ)
    ∧ S.card < Nat.choose (d + 3) 3 := by
  set d := Nat.floor (3 * (S.card : ℝ) ^ (1 / 3 : ℝ))
  use d
  have h1 : (d : ℝ) ≤ 3 * (S.card : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
  constructor
  · exact h1
  · have h2 : 3 * (S.card : ℝ) ^ (1 / 3 : ℝ) < (d : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2_pos : 0 ≤ 3 * (S.card : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have h3 : (3 * (S.card : ℝ) ^ (1 / 3 : ℝ)) ^ 3 < ((d : ℝ) + 1) ^ 3 :=
      pow_lt_pow_left₀ h2 h2_pos (by norm_num)
    have h3_eq : (3 * (S.card : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 27 * (S.card : ℝ) := by
      calc (3 * (S.card : ℝ) ^ (1 / 3 : ℝ)) ^ 3 =
          27 * ((S.card : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by ring
        _ = 27 * (S.card : ℝ) := by
          rw [← Real.rpow_natCast]
          push_cast
          rw [← Real.rpow_mul (Nat.cast_nonneg S.card)]
          norm_num
    rw [h3_eq] at h3
    have h_choose : (d + 3) * (d + 2) * (d + 1) = 6 * Nat.choose (d + 3) 3 := by
      have h_desc : (d + 3).descFactorial 3 = (d + 3) * (d + 2) * (d + 1) := by
        simp only [Nat.descFactorial_succ, Nat.reduceSubDiff, Nat.add_one_sub_one,
          tsub_zero, Nat.descFactorial_zero, mul_one]
        rw [Nat.mul_comm (d + 1), Nat.mul_comm (d + 3)]
      have h_fact : Nat.factorial 3 = 6 := by rfl
      have hc := Nat.descFactorial_eq_factorial_mul_choose (d + 3) 3
      rw [h_desc, h_fact] at hc
      rw [hc.symm]
    have h_choose_R : ((d : ℝ) + 3) * ((d : ℝ) + 2) * ((d : ℝ) + 1) =
      6 * (Nat.choose (d + 3) 3 : ℝ) := by
      have h_cast : ((d + 3) * (d + 2) * (d + 1) : ℝ) =
        (6 * Nat.choose (d + 3) 3 : ℝ) := by norm_cast
      push_cast at h_cast
      exact h_cast
    have h4 : ((d : ℝ) + 1) ^ 3 ≤ ((d : ℝ) + 3) * ((d : ℝ) + 2) * ((d : ℝ) + 1) := by
      have hd_pos_strict : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      nlinarith
    have h5 : 27 * (S.card : ℝ) < 6 * (Nat.choose (d + 3) 3 : ℝ) := by
      calc 27 * (S.card : ℝ) < ((d : ℝ) + 1) ^ 3 := h3
        _ ≤ ((d : ℝ) + 3) * ((d : ℝ) + 2) * ((d : ℝ) + 1) := h4
        _ = 6 * (Nat.choose (d + 3) 3 : ℝ) := h_choose_R
    have h6 : (S.card : ℝ) < (Nat.choose (d + 3) 3 : ℝ) := by
      have hS_pos : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
      linarith
    exact Nat.cast_lt.mp h6

lemma min_degree_poly_exists (S : Finset Point3) (P : PolyR3) (hP_neq : P ≠ 0)
    (hP_vanish : ∀ p ∈ S, evalP P p = 0) :
    ∃ P_min : PolyR3, P_min ≠ 0 ∧ (∀ p ∈ S, evalP P_min p = 0)
    ∧ (∀ Q : PolyR3, Q ≠ 0 → (∀ p ∈ S, evalP Q p = 0)
     → MvPolynomial.totalDegree P_min ≤ MvPolynomial.totalDegree Q) := by
     -- By well-ordering of ℕ: the set of degrees achieved by nonzero
     -- vanishing polynomials is nonempty, so has a minimum.
     have h_exists_deg : ∃ n : ℕ, ∃ Q : PolyR3, Q ≠ 0
         ∧ (∀ p ∈ S, evalP Q p = 0) ∧ MvPolynomial.totalDegree Q = n :=
       ⟨_, P, hP_neq, hP_vanish, rfl⟩
     -- Find the minimum such degree using Nat.find
     set d_min := Nat.find h_exists_deg with hd_min_def
     obtain ⟨P_min, hP_min_neq, hP_min_vanish, hP_min_deg⟩ := Nat.find_spec h_exists_deg
     exact ⟨P_min, hP_min_neq, hP_min_vanish, fun Q hQ_neq hQ_vanish => by
       rw [hP_min_deg]
       exact Nat.find_min' h_exists_deg ⟨Q, hQ_neq, hQ_vanish, rfl⟩⟩

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
  rcases min_degree_poly_exists S P hP_neq hP_vanish
      with ⟨P_min, hP_min_neq, hP_min_vanish, hP_min_deg⟩
  use P_min
  refine ⟨hP_min_neq, hP_min_vanish, ?_, hP_min_deg⟩
  -- The minimal polynomial has degree ≤ deg(P) ≤ d ≤ 3 * |S|^(1/3)
  have h_P_min_le_P : (MvPolynomial.totalDegree P_min : ℝ) ≤ (MvPolynomial.totalDegree P : ℝ) := by
    exact_mod_cast hP_min_deg P hP_neq hP_vanish
  linarith

-- ============================================================================
-- Lemmas for Lemma 2
-- ============================================================================

-- Compatibility of evalPLine and evalP: evaluating the univariate restriction
-- at the parameter t gives the same result as evaluating the multivariate
-- polynomial at the point on the line.
lemma evalPLine_eval_eq (P : PolyR3) (l : Line3) (t : ℝ) :
    Polynomial.eval t (evalPLine P l) = evalP P (l.base + t • l.dir) := by
  unfold evalPLine evalP
  induction P using MvPolynomial.induction_on
  case C r =>
    simp [MvPolynomial.eval₂_C, MvPolynomial.eval_C, Polynomial.eval_C]
  case add P Q hP hQ =>
    rw [MvPolynomial.eval₂_add, Polynomial.eval_add, hP, hQ, MvPolynomial.eval_add]
  case mul_X P i hP =>
    rw [MvPolynomial.eval₂_mul, Polynomial.eval_mul, hP, MvPolynomial.eval₂_X,
        MvPolynomial.eval_mul, MvPolynomial.eval_X]
    congr 1
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring

-- The degree of evalPLine P l is at most the total degree of P.
lemma evalPLine_degree_le (P : PolyR3) (l : Line3) :
    (evalPLine P l).degree ≤ MvPolynomial.totalDegree P := by
  unfold evalPLine
  rw [MvPolynomial.eval₂_eq]
  refine (Polynomial.degree_sum_le _ _).trans ?_
  simp only [Finset.sup_le_iff]
  intro m hm
  -- degree of monomial part
  have hX : ∀ i, (Polynomial.C (l.base i) + Polynomial.X * Polynomial.C (l.dir i)).degree ≤ 1 :=
    fun i => by
      refine (Polynomial.degree_add_le _ _).trans (max_le (Polynomial.degree_C_le.trans ?_) ?_)
      · exact_mod_cast Nat.zero_le 1
      · refine (Polynomial.degree_mul_le _ _).trans ?_
        rw [Polynomial.degree_X]
        exact (add_le_add_right (Polynomial.degree_C_le (a := l.dir i)) 1).trans
          (by exact_mod_cast le_refl _)
  refine (Polynomial.degree_mul_le _ _).trans ?_
  have h_deg_C : (Polynomial.C (MvPolynomial.coeff m P)).degree ≤ 0 := Polynomial.degree_C_le
  refine (add_le_add h_deg_C le_rfl).trans ?_
  rw [zero_add]
  refine (Polynomial.degree_prod_le _ _).trans ?_
  have h1 : ∑ i ∈ m.support,
      ((Polynomial.C (l.base i) + Polynomial.X * Polynomial.C (l.dir i)) ^ m i).degree ≤
      ∑ i ∈ m.support, (m i : WithBot ℕ) :=
    Finset.sum_le_sum fun i _ => (Polynomial.degree_pow_le _ _).trans (by
      have h : (Polynomial.C (l.base i) + Polynomial.X * Polynomial.C (l.dir i)).degree ≤
        (1 : WithBot ℕ) := hX i
      exact (nsmul_le_nsmul_right h (m i)).trans (by simp))
  have h2 : ∑ i ∈ m.support, (m i : WithBot ℕ) ≤ ↑(MvPolynomial.totalDegree P) := by
    rw [← Nat.cast_sum]
    exact Nat.cast_le.mpr (MvPolynomial.le_totalDegree hm)
  exact h1.trans h2

lemma poly_vanishes_on_line_helper (P : PolyR3) (l : Line3) (S : Finset Point3)
    (h_subset : ∀ p ∈ S, l.contains p)
    (h_roots : ∀ p ∈ S, evalP P p = 0)
    (h_deg : (MvPolynomial.totalDegree P : ℝ) < S.card) :
    evalPLine P l = 0 := by
  -- Step 1: For each p ∈ S, choose a parameter t_p such that p = l.base + t_p • l.dir
  have h_exists_t : ∀ p ∈ S, ∃ t : ℝ, p = l.base + t • l.dir := h_subset
  let t (p : Point3) (hp : p ∈ S) : ℝ := Classical.choose (h_exists_t p hp)
  have ht (p : Point3) (hp : p ∈ S) : p = l.base + (t p hp) • l.dir :=
    Classical.choose_spec (h_exists_t p hp)
  -- The set of parameters
  let T : Finset ℝ := S.attach.image (fun p => t p.1 p.2)
  -- Step 2: evalPLine P l is a univariate polynomial of degree ≤ totalDegree P
  have h_deg_poly : (evalPLine P l).degree ≤ (MvPolynomial.totalDegree P : ℕ) :=
    evalPLine_degree_le P l
  -- Step 3: It has |S| roots (at the t_p values), and |S| > degree
  have h_roots_T : ∀ t_val ∈ T, (evalPLine P l).eval t_val = 0 := by
    intro t_val ht_val
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, T] at ht_val
    rcases ht_val with ⟨p, hp_mem, rfl⟩
    rw [evalPLine_eval_eq, ← ht p hp_mem]
    exact h_roots p hp_mem
  have h_card_T : T.card = S.card := by
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_attach]
    · intro p1 _ p2 _ h_eq
      simp only at h_eq
      ext
      rw [ht p1.1 p1.2, ht p2.1 p2.2, h_eq]
  -- |S| > degree
  have h_deg_lt : (evalPLine P l).degree < (T.card : ℕ) := by
    rw [h_card_T]
    have h_deg_N : MvPolynomial.totalDegree P < S.card := by
      exact_mod_cast h_deg
    exact h_deg_poly.trans_lt (Nat.cast_lt.mpr h_deg_N)
  -- Step 4: By Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero, it must be 0
  exact Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero T h_deg_lt h_roots_T

lemma evalPLine_zero_implies_eval_zero (P : PolyR3) (l : Line3)
    (h_zero : evalPLine P l = 0) (p : Point3) (hp : l.contains p) :
    evalP P p = 0 := by
    rcases hp with ⟨t, rfl⟩
    -- Use the compatibility lemma: Polynomial.eval t (evalPLine P l) = evalP P (l.base + t • l.dir)
    have h := evalPLine_eval_eq P l t
    rw [h_zero] at h
    simp [Polynomial.eval_zero] at h
    exact h.symm

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

-- ============================================================================
-- Lemmas for Lemma 3
-- ============================================================================
-- The following lemma is another version of a Lemma:
-- If x is a joint of L, and if a smooth function F : R^3 → R vanishes
-- on the lines of L, then ∇F vanishes at x.
-- I'll put the sketch of the proof in the comments, it is a single argument:
-- Proof:
-- By hypothesis, x lies in three non-coplanar lines of L. Let v_i be
-- tangent vectors for these three lines. The directional derivative of F in the direction
-- v_i must vanish at x. So we have ∇F(x) · v_i = 0 for each i. Since the v_i are a basis
-- of R^3, we have ∇F(x) = 0.
--
-- NOTE: The original decomposition into `evalPLine_zero_implies_dir_deriv_zero` was
-- incorrect (it's false that individual partial derivatives vanish on a line where P
-- vanishes; only the directional derivative along the line vanishes). The correct
-- decomposition uses directional derivatives and linear independence.

lemma evalPLine_derivative (P : PolyR3) (l : Line3) :
    Polynomial.derivative (evalPLine P l) =
    ∑ i : Fin 3, Polynomial.C (l.dir i) * evalPLine (PDeriv3 P i) l := by
  unfold evalPLine PDeriv3
  induction P using MvPolynomial.induction_on
  case C r =>
    simp only [MvPolynomial.eval₂_C, Polynomial.derivative_C, MvPolynomial.pderiv_C,
      MvPolynomial.eval₂_zero, mul_zero, Finset.sum_const_zero]
  case add P Q hP hQ =>
    simp only [MvPolynomial.eval₂_add, map_add, hP, hQ, Finset.sum_add_distrib, mul_add]
  case mul_X P i hP =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X, MvPolynomial.eval₂_add]
    rw [Polynomial.derivative_mul, hP]
    simp only [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.derivative_mul, mul_add, Finset.sum_mul, mul_assoc, zero_add, add_zero,
      mul_zero]
    simp only [Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Finset.sum_eq_single i]
      · simp
        ring_nf
        sorry
      · intro j _ hne
        simp
        ring_nf
        sorry
      · intro hi; simp at hi
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring_nf
      sorry


lemma dir_deriv_vanishes_on_line (P : PolyR3) (l : Line3) (p : Point3)
    (h_vanish : evalPLine P l = 0) (hp : l.contains p) :
    ∑ i : Fin 3, l.dir i * evalP (PDeriv3 P i) p = 0 := by
  have h_deriv_zero : Polynomial.derivative (evalPLine P l) = 0 := by
    rw [h_vanish, Polynomial.derivative_zero]
  rw [evalPLine_derivative P l] at h_deriv_zero
  rcases hp with ⟨t0, rfl⟩
  have h_eval := congr_arg (Polynomial.eval t0) h_deriv_zero
  simp only [Polynomial.eval_zero] at h_eval
  have h_compat : ∀ i, (evalPLine (PDeriv3 P i) l).eval t0 =
      evalP (PDeriv3 P i) (l.base + t0 • l.dir) := by
    intro i
    exact evalPLine_eval_eq (PDeriv3 P i) l t0
  simp_rw [← h_compat]
  sorry



-- If the dot product of the gradient with 3 linearly independent direction
-- vectors is zero at a point, then the gradient is zero at that point.
-- This is a standard linear algebra fact: if M * v = 0 and M is invertible, then v = 0.
lemma gradient_zero_of_indep_dot_zero (w : Fin 3 → ℝ)
    (v1 v2 v3 : Point3)
    (h_indep : LinearIndependent ℝ ![v1, v2, v3])
    (h_dot1 : ∑ i : Fin 3, v1 i * w i = 0)
    (h_dot2 : ∑ i : Fin 3, v2 i * w i = 0)
    (h_dot3 : ∑ i : Fin 3, v3 i * w i = 0) :
    ∀ i : Fin 3, w i = 0 := by
  let v : Fin 3 → Point3 := ![v1, v2, v3]
  let b := basisOfLinearIndependentOfCardEqFinrank h_indep (by simp)
  have hb : ∀ i, b i = v i := by
    intro i; simp [b]; rfl
  let f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun x ↦ ∑ j, x j * w j
    map_add' := by intro x y; simp [Finset.sum_add_distrib, add_mul]
    map_smul' := by intro r x; simp [Finset.mul_sum, mul_assoc]
  }
  have hf_zero : ∀ i, f (b i) = 0 := by
    intro i
    rw [hb]
    fin_cases i
    · exact h_dot1
    · exact h_dot2
    · exact h_dot3
  have hf : f = 0 := b.ext hf_zero
  intro i
  have hi : f (Pi.single i 1) = 0 := by rw [hf]; rfl
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, f] at hi
  exact hi


-- Lemma 3: Gradient vanishing at a joint
theorem gradient_zero_at_joint (P : PolyR3) (p : Point3) (L : Finset Line3)
    (h_joint : IsJoint p L)
    (h_vanish : ∀ l ∈ L, evalPLine P l = 0) :
    ∀ i : Fin 3, evalP (PDeriv3 P i) p = 0 := by
  rcases h_joint with ⟨l1, l2, l3, hl1, hl2, hl3, hneq12, hneq13, hneq23,
    hcont1, hcont2, hcont3, hcop⟩
  -- The directional derivative along each line vanishes at p
  have h_dir1 : ∑ i : Fin 3, l1.dir i * evalP (PDeriv3 P i) p = 0 :=
    dir_deriv_vanishes_on_line P l1 p (h_vanish l1 hl1) hcont1
  have h_dir2 : ∑ i : Fin 3, l2.dir i * evalP (PDeriv3 P i) p = 0 :=
    dir_deriv_vanishes_on_line P l2 p (h_vanish l2 hl2) hcont2
  have h_dir3 : ∑ i : Fin 3, l3.dir i * evalP (PDeriv3 P i) p = 0 :=
    dir_deriv_vanishes_on_line P l3 p (h_vanish l3 hl3) hcont3
  -- Since the lines are non-coplanar, their direction vectors are linearly independent
  -- (¬ Coplanar means ¬ ¬ LinearIndependent, so LinearIndependent)
  have h_li : LinearIndependent ℝ ![l1.dir, l2.dir, l3.dir] := by
    unfold Coplanar at hcop
    push_neg at hcop
    exact hcop
  -- Apply the linear algebra fact
  intro i
  exact gradient_zero_of_indep_dot_zero
    (fun i => evalP (PDeriv3 P i) p)
    l1.dir l2.dir l3.dir h_li h_dir1 h_dir2 h_dir3 i
