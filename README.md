# GuthKatzJointTheorem

[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-dependent-green.svg)](https://github.com/leanprover-community/mathlib4)

This repository contains a complete formalization of the **Joints Conjecture** in the [Lean 4](https://leanprover.github.io/) theorem prover. 

The theorem states that any set of $L$ lines in $\mathbb{R}^3$ determines at most $O(|L|^{3/2})$ joints. A "joint" is defined as a point where at least three non-coplanar lines intersect. 

Originally posed by Chazelle, Edelsbrunner, Guibas, Pollack, Seidel, Sharir, and Snoeyink in 1992, the conjecture was first proven by Guth and Katz in 2008 using algebraic geometry. This formalization utilizes the highly streamlined "Polynomial Method" proof discovered independently by Elekes, Kaplan, Sharir, and Quilodrán in 2009, as presented in Chapter 3 of Larry Guth's book *Polynomial Methods in Combinatorics*.

## The Mathematical Proof

The formalized proof completely avoids complex algebraic geometry (like irreducible factorizations or Bézout's theorem) and relies on a brilliant combination of linear algebra and multivariable calculus:

1. **The Minimal Degree Polynomial:** If the set of joints $J$ is non-empty, parameter counting guarantees the existence of a non-zero trivariate polynomial $P$ vanishing on all joints, with a degree bounded by $3|J|^{1/3}$. We choose $P$ to be of *minimal* degree.
2. **The Sparse Line Lemma:** We prove by contradiction that there must exist at least one line containing $\le 3|J|^{1/3}$ joints. If all lines contained more joints than the degree of $P$, $P$ would vanish entirely on every line. Consequently, its gradient $\nabla P$ would vanish at every joint. Since the partial derivatives of $P$ have strictly lower degrees, this contradicts the minimality of $P$'s degree.
3. **The Telescoping Bound:** By iteratively removing the "sparsest" line, we establish the recurrence bound $|J| \le |L| \times 3|J|^{1/3}$. Simple algebraic rearrangement yields the final theorem: $|J| \le 3^{3/2} |L|^{3/2}$.

## Project Structure

The repository is modularized to strictly separate the continuous geometric/algebraic arguments from the discrete combinatorics.

* `Geometry.lean`: Foundational definitions. Defines points as `Fin 3 → ℝ` (to interface smoothly with `MvPolynomial`), lines, and the geometric concept of a joint.
* `Algebra.lean`: Contains the core algebraic engine. Formalizes the existence of the minimal degree polynomial and proves that vanishing on lines implies a vanishing gradient at the joints.
* `MainLemma.lean`: Bridges the geometry and algebra to prove the fundamental contradiction—the existence of the "sparse line."
* `MainTheorem.lean`: The combinatorial wrap-up. Implements the iterative line-removal process and solves the algebraic inequality to yield the final $O(|L|^{3/2})$ bound.

## Prerequisites & Building

To build and interact with this project, you will need to have Lean 4 and `elan` installed. 

1. Install `elan` (the Lean version manager) by following the instructions on the [Lean 4 manual](https://leanprover.github.io/lean4/doc/setup.html).
2. Clone this repository:
   ```bash
   git clone https://github.com/HLXY-420/GuthKatzJointTheorem.git
   cd GuthKatzJointTheorem
   ```
3. Fetch the mathlib cache to save compilation time:
   ```bash
   lake exe cache get
   ```
4. Build the project:
   ```bash
   lake build
   ```

## References

1. Guth, L. (2016). Polynomial Methods in Combinatorics. American Mathematical Society.

2. Elekes, G., Kaplan, H., & Sharir, M. (2009). On lines, joints, and incidences in space. Combinatorica, 31(6), 711-731.

3. Guth, L., & Katz, N. H. (2008). Algebraic methods in discrete analogs of the Kakeya problem. Advances in Mathematics, 225(5), 2828-2839.

4. Guth, L. (2016). Polynomial methods in combinatorics. Vol. 202. American Mathematical Society.