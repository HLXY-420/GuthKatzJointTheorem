import Mathlib.Analysis.SpecialFunctions.Pow.Real

import GuthKatzJointTheorem.Geometry
import GuthKatzJointTheorem.Algebra
import GuthKatzJointTheorem.MainLemma

open Classical

/-!
## Helper lemmas for the main theorem

We extract several combinatorial / analytic facts as `sorry`-ed lemmas
so that the **structure** of the two main proofs is fully explicit.
-/

-- Joints is monotone: removing lines can only lose joints
lemma joints_mono_erase (L : Finset Line3) (l₀ : Line3) :
    Joints (L.erase l₀) ⊆ Joints L := sorry

-- The number of joints on a single line is bounded by the sparse-line certificate
-- (this is the "telescoping" step:  |Joints L \ Joints (L \ {l₀})| ≤ sparse bound)
lemma joints_diff_le_sparse (L : Finset Line3) (l₀ : Line3) (hl₀ : l₀ ∈ L)
    (h_sparse : ((Joints L).filter (fun p => l₀.contains p)).card
        ≤ 3 * ((Joints L).card : ℝ) ^ (1 / 3 : ℝ)) :
    ((Joints L).card : ℝ) ≤
      ((Joints (L.erase l₀)).card : ℝ) + 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := sorry

-- Card of erase: |L.erase l₀| = |L| - 1  when l₀ ∈ L  (cast to ℝ)
lemma card_erase_cast (L : Finset Line3) (l₀ : Line3) (hl₀ : l₀ ∈ L) :
    (L.erase l₀).card = L.card - 1 := Finset.card_erase_of_mem hl₀

-- rpow monotonicity helper for the substitution step
-- If a ≤ b and 0 ≤ a then a ^ r ≤ b ^ r for 0 ≤ r
lemma rpow_le_rpow_of_nonneg (a b : ℝ) (r : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hr : 0 ≤ r) :
    a ^ r ≤ b ^ r := Real.rpow_le_rpow ha hab hr

-- If J = 0, then 0 ≤ anything (trivial)
lemma joints_empty_bound (L : Finset Line3) (hJ : (Joints L).card = 0) :
    ((Joints L).card : ℝ) ≤ (L.card : ℝ) * 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
  rw [hJ]
  simp

-- L.card = 0 implies Joints L = ∅
lemma joints_of_card_zero (L : Finset Line3) (h : L.card = 0) :
    (Joints L).card = 0 := by
  have hL : L = ∅ := Finset.card_eq_zero.mp h
  subst hL
  -- Joints ∅ has no elements since IsJoint requires lines in L
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_empty


-- L.Nonempty when L.card = n + 1
lemma finset_nonempty_of_card_succ {α : Type*} (S : Finset α) (n : ℕ) (h : S.card = n + 1) :
    S.Nonempty := Finset.card_pos.mp (by omega)

-- Joints L nonempty implies L nonempty
lemma joints_nonempty_imp_lines_nonempty (L : Finset Line3) (hJ : (Joints L).Nonempty) :
    L.Nonempty := by
  rcases hJ with ⟨p, hp⟩
  have h_joint : IsJoint p L := (Finset.mem_filter.mp hp).2
  rcases h_joint with ⟨l₁, _, _, hl₁, _⟩
  exact ⟨l₁, hl₁⟩

/-!
## The main inductive lemma

Telescoping removal bound: J ≤ |L| * 3 * J^(1/3)
-/

-- Telescoping removal bound: J ≤ |L| * 3 * J^(1/3)
lemma joints_removal_bound : ∀ (L : Finset Line3),
    ((Joints L).card : ℝ) ≤ (L.card : ℝ) * 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
  -- Proof by strong induction on `L.card`.
  intro L
  induction hn : L.card using Nat.strongRecOn generalizing L with
  | _ n ih =>
  -- Base case: L.card = 0. Joints L must be empty, so 0 ≤ 0.
  rcases n with _ | n
  · rw [Nat.cast_zero]
    simp [joints_of_card_zero L hn]
  · -- Inductive step: L.card = n + 1
    --   If (Joints L) is empty, 0 ≤ 0.
    by_cases hJ : (Joints L).card = 0
    · have : (Joints L).card = 0 := hJ
      rw [this]
      simp
    · -- (Joints L) is non-empty
      have hJ_nonempty : (Joints L).Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hJ)
      have hL_nonempty : L.Nonempty := joints_nonempty_imp_lines_nonempty L hJ_nonempty
      -- Use `exists_sparse_line` to extract line `l₀` with few joints.
      rcases exists_sparse_line L hL_nonempty hJ_nonempty with ⟨l₀, hl₀_mem, hl₀_sparse⟩
      -- Let L' = L.erase l₀
      set L' := L.erase l₀ with hL'_def
      -- |L'| = n
      have hL'_card : L'.card = n := by
        have h_erase := Finset.card_erase_of_mem hl₀_mem
        rw [← hL'_def] at h_erase
        omega
      -- |L'.card| < |L.card|, so we can apply the IH
      have hL'_lt : L'.card < n + 1 := by omega
      have ih_L' : ((Joints L').card : ℝ) ≤
          (L'.card : ℝ) * 3 * ((Joints L').card : ℝ) ^ (1/3 : ℝ) :=
        ih L'.card (by exact hL'_lt) L' rfl
      -- |Joints L| ≤ |Joints L'| + 3 * |Joints L|^(1/3)
      have h_split := joints_diff_le_sparse L l₀ hl₀_mem hl₀_sparse
      -- |Joints L'| ≤ |Joints L|  by monotonicity
      have h_mono : (Joints L').card ≤ (Joints L).card :=
        Finset.card_le_card (joints_mono_erase L l₀)
      -- |Joints L'|^(1/3) ≤ |Joints L|^(1/3) by rpow monotonicity
      have h_rpow_mono : ((Joints L').card : ℝ) ^ (1/3 : ℝ)
          ≤ ((Joints L).card : ℝ) ^ (1/3 : ℝ) :=
        rpow_le_rpow_of_nonneg _ _ (1/3 : ℝ)
          (Nat.cast_nonneg _) (Nat.cast_le.mpr h_mono) (by norm_num)
      -- From IH:  |Joints L'| ≤ n * 3 * |Joints L'|^(1/3)
      --                       ≤ n * 3 * |Joints L|^(1/3)
      have ih_upgraded : ((Joints L').card : ℝ) ≤
          (n : ℝ) * 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
        calc ((Joints L').card : ℝ)
            ≤ (L'.card : ℝ) * 3 * ((Joints L').card : ℝ) ^ (1/3 : ℝ) := ih_L'
          _ = (n : ℝ) * 3 * ((Joints L').card : ℝ) ^ (1/3 : ℝ) := by
              rw [hL'_card]
          _ ≤ (n : ℝ) * 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
              apply mul_le_mul_of_nonneg_left h_rpow_mono
              apply mul_nonneg (Nat.cast_nonneg _) (by norm_num)
      -- Combine:  J ≤ |Joints L'| + 3 * J^(1/3)
      --            ≤ n * 3 * J^(1/3) + 3 * J^(1/3)
      --            = (n + 1) * 3 * J^(1/3)
      --            = |L| * 3 * J^(1/3)
      calc ((Joints L).card : ℝ)
          ≤ ((Joints L').card : ℝ) + 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := h_split
        _ ≤ (n : ℝ) * 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ)
            + 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by linarith
        _ = ((n : ℝ) + 1) * 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by ring
        _ = (L.card : ℝ) * 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
            rw [hn]; push_cast; ring
      rw [hn]

/-!
## Helper lemmas for the final algebraic manipulation

We need to go from  J ≤ 3|L| · J^(1/3)  to  J ≤ 3^(3/2) · |L|^(3/2).
The key algebraic steps are:
  1. Divide both sides by J^(1/3) to get J^(2/3) ≤ 3|L|
  2. Raise both sides to the 3/2 power to get J ≤ (3|L|)^(3/2) = 3^(3/2)|L|^(3/2)
-/

-- Division by J^(1/3):  J ≤ a * J^(1/3) implies J^(2/3) ≤ a  when J > 0
lemma rpow_div_bound {J a : ℝ} (hJ_pos : 0 < J)
    (h : J ≤ a * J ^ (1 / 3 : ℝ)) :
    J ^ (2 / 3 : ℝ) ≤ a := sorry

-- Raising to the 3/2 power:  J^(2/3) ≤ a  implies J ≤ a^(3/2)  when J > 0 and a ≥ 0
lemma rpow_raise_bound {J a : ℝ} (hJ_pos : 0 < J) (ha : 0 ≤ a)
    (h : J ^ (2 / 3 : ℝ) ≤ a) :
    J ≤ a ^ (3 / 2 : ℝ) := sorry

-- mul_rpow for the final step: (3 * |L|)^(3/2) = 3^(3/2) * |L|^(3/2)
lemma mul_rpow_split (a b : ℝ) (r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b) ^ r = a ^ r * b ^ r := Real.mul_rpow ha hb

/-!
## The Joints Conjecture
-/

-- The Joints Conjecture
theorem joints_conjecture (L : Finset Line3) :
    ((Joints L).card : ℝ) ≤ 3 ^ (3/2 : ℝ) * (L.card : ℝ) ^ (3/2 : ℝ) := by
  -- 1. Apply `joints_removal_bound` to get:
  --    J ≤ |L| * 3 * J^(1/3)
  have h_bound := joints_removal_bound L
  -- 2. If J = 0, the theorem holds trivially (0 ≤ 0).
  by_cases hJ : (Joints L).card = 0
  · rw [hJ]
    simp only [CharP.cast_eq_zero, ge_iff_le]
    apply mul_nonneg
    · apply Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3)
    · apply Real.rpow_nonneg (Nat.cast_nonneg _)
  · -- 3. If J > 0, divide both sides by J^(1/3):
    have hJ_pos : (0 : ℝ) < (Joints L).card := by
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hJ)
    -- Rewrite bound as J ≤ (3 * |L|) * J^(1/3)
    have h_bound' : ((Joints L).card : ℝ) ≤
        (3 * (L.card : ℝ)) * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
      have : (L.card : ℝ) * 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ)
           = 3 * (L.card : ℝ) * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by ring
      linarith
    --    J^(2/3) ≤ 3 * |L|
    have h_div := rpow_div_bound hJ_pos h_bound'
    -- 4. Raise both sides to the (3/2) power:
    --    J ≤ (3 * |L|)^(3/2)
    have h_raise := rpow_raise_bound hJ_pos
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (Nat.cast_nonneg _)) h_div
    --    (3 * |L|)^(3/2) = 3^(3/2) * |L|^(3/2)
    rw [mul_rpow_split 3 (L.card : ℝ) (3/2 : ℝ) (by norm_num) (Nat.cast_nonneg _)] at h_raise
    exact h_raise
