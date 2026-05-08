/-
Copyright (c) 2026 Yuchen Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuchen Liu
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

import GuthKatzJointTheorem.Geometry
import GuthKatzJointTheorem.Algebra
import GuthKatzJointTheorem.MainLemma
import Mathlib.Data.Num.Lemmas

set_option linter.style.openClassical false

open Classical

/-!
## Helper lemmas for the main theorem

We extract several combinatorial / analytic facts as `sorry`-ed lemmas
so that the **structure** of the two main proofs is fully explicit.
-/

-- Joints is monotone: removing lines can only lose joints
-- I think this can be proven by just a few lines of calculation.
lemma joints_mono_erase (L : Finset Line3) (l₀ : Line3) :
    Joints (L.erase l₀) ⊆ Joints L := by
  intro p hp
  rw [Joints, Finset.mem_filter] at hp ⊢
  rcases hp with ⟨h_mem, h_joint⟩
  constructor
  · -- Prove p is in the biUnion for L
    simp only [Finset.mem_biUnion, Finset.mem_product, Prod.exists] at h_mem ⊢
    rcases h_mem with ⟨l₁, l₂, ⟨hl₁, hl₂⟩, h_pt⟩
    use l₁, l₂
    constructor
    · constructor
      · exact Finset.mem_of_mem_erase hl₁
      · exact Finset.mem_of_mem_erase hl₂
    · exact h_pt
  · -- Prove IsJoint p L
    rcases h_joint with ⟨l₁, l₂, l₃, hl₁, hl₂, hl₃, h_distinct₁, h_distinct₂, h_distinct₃,
      h_p₁, h_p₂, h_p₃, h_coplanar⟩
    use l₁, l₂, l₃
    refine ⟨?_, ?_, ?_, h_distinct₁, h_distinct₂, h_distinct₃, h_p₁, h_p₂, h_p₃, h_coplanar⟩
    · exact Finset.mem_of_mem_erase hl₁
    · exact Finset.mem_of_mem_erase hl₂
    · exact Finset.mem_of_mem_erase hl₃


-- The number of joints on a single line is bounded by the sparse-line certificate
-- (this is the "telescoping" step:  |Joints L \ Joints (L \ {l₀})| ≤ sparse bound)
-- I think this can be proven by just a few lines of calculation.
lemma joints_diff_le_sparse (L : Finset Line3) (l₀ : Line3) (hl₀ : l₀ ∈ L)
    (h_sparse : ((Joints L).filter (fun p => l₀.contains p)).card
        ≤ 3 * ((Joints L).card : ℝ) ^ (1 / 3 : ℝ)) :
    ((Joints L).card : ℝ) ≤
      ((Joints (L.erase l₀)).card : ℝ) + 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
  have h_mono := joints_mono_erase L l₀
  have h_subset : Joints L \ Joints (L.erase l₀) ⊆ (Joints L).filter (fun p => l₀.contains p) := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    rcases hp with ⟨hp_L, hp_not_L_erase⟩
    rw [Finset.mem_filter]
    constructor
    · exact hp_L
    · -- Contradiction: if l₀ does not contain p, then p must be a joint of L.erase l₀
      by_contra h_not_contains
      apply hp_not_L_erase
      rw [Joints, Finset.mem_filter] at hp_L ⊢
      constructor
      · -- p in biUnion of L.erase l₀
        have hp_bi := hp_L.1
        rw [Finset.mem_biUnion] at hp_bi
        rcases hp_bi with ⟨⟨l₁, l₂⟩, h_l12, h_pt⟩
        rw [Finset.mem_product] at h_l12
        rcases h_l12 with ⟨hl₁, hl₂⟩
        dsimp at h_pt
        -- Since l₁.contains p and l₂.contains p (implicit in h_pt), and ¬ l₀.contains p:
        -- we must have l₁ ≠ l₀ and l₂ ≠ l₀.
        -- First, extract l₁.contains p and l₂.contains p from h_pt.
        have h_exists : ∃ p', l₁.contains p' ∧ l₂.contains p' ∧ l₁ ≠ l₂ := by
          split_ifs at h_pt
          · assumption
          · contradiction
        have hp_eq : p = Classical.choose h_exists := by
          split_ifs at h_pt
          · exact Finset.mem_singleton.mp h_pt
          · contradiction
        have h_p_in_l₁ : l₁.contains p := by
          rw [hp_eq]; exact (Classical.choose_spec h_exists).1
        have h_p_in_l₂ : l₂.contains p := by
          rw [hp_eq]; exact (Classical.choose_spec h_exists).2.1
        -- Now we can say l₁ ≠ l₀ and l₂ ≠ l₀
        have hl₁_erase : l₁ ∈ L.erase l₀ := Finset.mem_erase.mpr
          ⟨fun h => h_not_contains (h ▸ h_p_in_l₁), hl₁⟩
        have hl₂_erase : l₂ ∈ L.erase l₀ := Finset.mem_erase.mpr
          ⟨fun h => h_not_contains (h ▸ h_p_in_l₂), hl₂⟩
        apply Finset.mem_biUnion.mpr
        use ⟨l₁, l₂⟩
        constructor
        · rw [Finset.mem_product]; exact ⟨hl₁_erase, hl₂_erase⟩
        · dsimp
          rw [hp_eq]
          split_ifs with h'
          · exact Finset.mem_singleton.mpr rfl
          · -- h' is the same as h_exists, but for L.erase l₀.
            -- But the condition only depends on l₁, l₂, which are in L.erase l₀.
            exfalso; apply h'; exact h_exists
      · -- IsJoint p (L.erase l₀)
        rcases hp_L.2 with ⟨l₁, l₂, l₃, hl₁, hl₂, hl₃, h_dist₁, h_dist₂, h_dist₃,
          h_p₁, h_p₂, h_p₃, h_coplanar⟩
        use l₁, l₂, l₃
        have h_l₁ : l₁ ≠ l₀ := fun h => h_not_contains (h ▸ h_p₁)
        have h_l₂ : l₂ ≠ l₀ := fun h => h_not_contains (h ▸ h_p₂)
        have h_l₃ : l₃ ≠ l₀ := fun h => h_not_contains (h ▸ h_p₃)
        refine ⟨?_, ?_, ?_, h_dist₁, h_dist₂, h_dist₃, h_p₁, h_p₂, h_p₃, h_coplanar⟩
        · rw [Finset.mem_erase]; exact ⟨h_l₁, hl₁⟩
        · rw [Finset.mem_erase]; exact ⟨h_l₂, hl₂⟩
        · rw [Finset.mem_erase]; exact ⟨h_l₃, hl₃⟩

  -- Now finish the cardinality inequality
  have h_card := Finset.card_le_card h_subset
  have h_card_real : (Joints L).card = (Joints (L.erase l₀)).card
    + (Joints L \ Joints (L.erase l₀)).card := by
    rw [← Finset.card_sdiff_add_card_inter (Joints L) (Joints (L.erase l₀)),
      Finset.inter_eq_right.mpr h_mono, add_comm]
  push_cast at h_card ⊢
  calc ((Joints L).card : ℝ)
    _ = ((Joints (L.erase l₀)).card : ℝ) + ((Joints L \ Joints (L.erase l₀)).card : ℝ) := by
        rw [← Nat.cast_add, ← h_card_real]
    _ ≤ ((Joints (L.erase l₀)).card : ℝ) + (((Joints L).filter
      (fun p => l₀.contains p)).card : ℝ) := by
        gcongr
    _ ≤ ((Joints (L.erase l₀)).card : ℝ) + 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
        gcongr




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
-- I think this can be proven by just a few lines of calculation.
lemma rpow_div_bound {J a : ℝ} (hJ_pos : 0 < J)
    (h : J ≤ a * J ^ (1 / 3 : ℝ)) :
    J ^ (2 / 3 : ℝ) ≤ a := by
  have hJ_rpow_pos : 0 < J ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hJ_pos (1 / 3)
  have h_div := (div_le_iff₀ hJ_rpow_pos).mpr h
  nth_rw 1 [← Real.rpow_one J] at h_div
  rw [← Real.rpow_sub hJ_pos] at h_div
  norm_num at h_div
  exact h_div


-- Raising to the 3/2 power:  J^(2/3) ≤ a  implies J ≤ a^(3/2)  when J > 0 and a ≥ 0
-- I think this can be proven by just a few lines of calculation.
lemma rpow_raise_bound {J a : ℝ} (hJ_pos : 0 < J) (_ha : 0 ≤ a)
    (h : J ^ (2 / 3 : ℝ) ≤ a) :
    J ≤ a ^ (3 / 2 : ℝ) := by
  have h_base_nonneg : 0 ≤ J ^ (2 / 3 : ℝ) := Real.rpow_nonneg (le_of_lt hJ_pos) (2/3)
  have h_exp_nonneg : 0 ≤ (3 / 2 : ℝ) := by norm_num
  have h_raise := Real.rpow_le_rpow h_base_nonneg h h_exp_nonneg
  rw [← Real.rpow_mul (le_of_lt hJ_pos)] at h_raise
  norm_num at h_raise
  on_goal 1 => exact h_raise


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
