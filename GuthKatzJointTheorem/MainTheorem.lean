import Mathlib.Analysis.SpecialFunctions.Pow.Real

import GuthKatzJointTheorem.Geometry
import GuthKatzJointTheorem.Algebra
import GuthKatzJointTheorem.MainLemma

-- Telescoping removal bound: J ≤ |L| * 3 * J^(1/3)
lemma joints_removal_bound (L : Finset Line3) :
    ((Joints L).card : ℝ) ≤ (L.card : ℝ) * 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
  -- Proof by induction / well-founded recursion on `L.card`.
  -- Base case: L = ∅. (Joints ∅) = ∅, so 0 ≤ 0.
  -- Inductive step:
  --   If (Joints L) is empty, 0 ≤ 0.
  --   If (Joints L) is non-empty, use `exists_sparse_line` to extract line `l₀`.
  --   (Joints L) ⊆ (Joints (L \ {l₀})) ∪ (Joints on l₀)
  --   |Joints L| ≤ |Joints (L \ {l₀})| + 3 * |Joints L|^(1/3)
  --   Apply inductive hypothesis to (L \ {l₀}):
  --   |Joints (L \ {l₀})| ≤ (|L| - 1) * 3 * |Joints (L \ {l₀})|^(1/3)
  --   Since |Joints (L \ {l₀})| ≤ |Joints L|, we can substitute the upper bound:
  --   |Joints L| ≤ (|L| - 1) * 3 * |Joints L|^(1/3) + 3 * |Joints L|^(1/3)
  --   |Joints L| ≤ |L| * 3 * |Joints L|^(1/3)
  sorry

-- The Joints Conjecture
theorem joints_conjecture (L : Finset Line3) :
    ((Joints L).card : ℝ) ≤ 3 ^ (3/2 : ℝ) * (L.card : ℝ) ^ (3/2 : ℝ) := by
  -- 1. Apply `joints_removal_bound` to get:
  --    J ≤ |L| * 3 * J^(1/3)
  -- 2. If J = 0, the theorem holds trivially (0 ≤ 0).
  -- 3. If J > 0, divide both sides by J^(1/3):
  --    J^(2/3) ≤ 3 * |L|
  -- 4. Raise both sides to the (3/2) power:
  --    (J^(2/3))^(3/2) ≤ (3 * |L|)^(3/2)
  --    J ≤ 3^(3/2) * |L|^(3/2)
  -- Use Lean's `Real.rpow` rules to finish the inequality.
  sorry
