/-
Copyright (c) 2026 Yuchen Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuchen Liu
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Part
-- Open classical scope to allow using decidable propositions in noncomputable definitions
open scoped Classical

-- Define a point in R^3 as a function Fin 3 → ℝ to perfectly match MvPolynomial evaluation
abbrev Point3 := Fin 3 → ℝ

structure Line3 where
  base : Point3
  dir : Point3
  dir_nonzero : dir ≠ 0

-- A point is on a line if it can be reached by scaling the direction vector
def Line3.contains (l : Line3) (p : Point3) : Prop :=
  ∃ t : ℝ, p = l.base + t • l.dir

-- Three lines are coplanar if their direction vectors are linearly dependent.
-- We use a matrix-style index `![v1, v2, v3]` to build the family of vectors.
def Coplanar (l₁ l₂ l₃ : Line3) : Prop :=
  ¬ LinearIndependent ℝ ![l₁.dir, l₂.dir, l₃.dir]

-- A joint requires 3 distinct, non-coplanar lines intersecting at `p`
def IsJoint (p : Point3) (L : Finset Line3) : Prop :=
  ∃ l₁ l₂ l₃, l₁ ∈ L ∧ l₂ ∈ L ∧ l₃ ∈ L ∧
    l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧
    l₁.contains p ∧ l₂.contains p ∧ l₃.contains p ∧
    ¬ Coplanar l₁ l₂ l₃



-- The finite set of all joints.
-- Marked noncomputable because finding intersections over ℝ requires classical logic.
noncomputable def Joints (L : Finset Line3) : Finset Point3 :=
  Finset.filter (fun p => IsJoint p L) <|
    Finset.biUnion (L ×ˢ L) <| fun ⟨l₁, l₂⟩ =>
      if h : ∃ p, l₁.contains p ∧ l₂.contains p ∧ l₁ ≠ l₂
      then ({Classical.choose h} : Finset Point3)
      else (∅ : Finset Point3)
