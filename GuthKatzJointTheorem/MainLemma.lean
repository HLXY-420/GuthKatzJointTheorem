import Mathlib.Analysis.SpecialFunctions.Pow.Real

import GuthKatzJointTheorem.Geometry
import GuthKatzJointTheorem.Algebra

open Classical
-- The core contradiction: At least one line must have relatively few joints.
theorem exists_sparse_line (L : Finset Line3) (hL : L.Nonempty) (hJ : (Joints L).Nonempty) :
    ∃ l ∈ L, ((Joints L).filter (fun p => l.contains p)).card ≤ 3 * ((Joints L).card : ℝ) ^ (1/3 : ℝ) := by
  -- 1. Proceed by contradiction: assume EVERY line has > 3 * |J|^(1/3) joints.
  -- 2. Let P be the minimal degree polynomial from `exists_min_degree_poly (Joints L)`.
  -- 3. We know deg(P) ≤ 3 * |J|^(1/3).
  -- 4. Therefore, on every line `l`, the number of joints is strictly greater than deg(P).
  -- 5. By `poly_vanishes_on_line`, P vanishes entirely on every line `l ∈ L`.
  -- 6. By `gradient_zero_at_joint`, the gradient ∇P vanishes on every joint `p ∈ Joints L`.
  -- 7. The partial derivatives ∂P/∂x_i have degree strictly less than deg(P).
  -- 8. Since ∇P vanishes on `Joints L`, by the minimality of P, ∇P must be identically 0.
  -- 9. If all partial derivatives are 0, P is a constant.
  -- 10. Since P vanishes on the joints, that constant is 0, so P = 0.
  -- 11. This contradicts the fact that P ≠ 0.
  sorry
