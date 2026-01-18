/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Block.While

/-! # Minimization Combinator for URMBlock

This file defines the minimization (μ-recursion) combinator for URMBlock,
implementing h(x) = μy[f(x,y) = 0] (least y such that f(x,y) = 0).

This implementation uses the while loop combinator from `Urm.Block.While`,
which factors out the common loop iteration pattern. The minimization
combinator is a special case where the result register is the counter.

## Main Definitions

- `URMBlock.min`: Minimization combinator
- `minFunction`: The μ-recursion function semantics

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

namespace URMBlock

open Program

/-! ## Helper Definitions -/

/-- Compute the base offset for minimization (needed to set up resultReg). -/
def minBase' (n : ℕ) (f : URMBlock) : ℕ :=
  max n f.maxReg

/-- The counter register for minimization (the result of μ-recursion).
    Updated to match whileCounterReg which is now at base + maxReg + 1. -/
def minCounterReg' (n : ℕ) (f : URMBlock) : ℕ :=
  minBase' n f + f.maxReg + 1

/-! ## The Min Combinator via While -/

/-- Create a WhileSpec for minimization.
The body is f, and the result register is the counter. -/
def minSpec (n : ℕ) (f : URMBlock) : WhileSpec where
  body := f
  n := n
  resultReg := minCounterReg' n f

/-- Verify that minSpec has the expected base. -/
theorem minSpec_base (n : ℕ) (f : URMBlock) :
    whileBase (minSpec n f) = minBase' n f := rfl

/-- Verify that resultReg equals whileCounterReg. -/
theorem minSpec_resultReg (n : ℕ) (f : URMBlock) :
    (minSpec n f).resultReg = whileCounterReg (minSpec n f) := by
  simp only [minSpec, minCounterReg', whileCounterReg, whileBase, minBase']

/-- Verify that resultReg is bounded by whileMaxReg. -/
theorem minSpec_resultReg_bounded (n : ℕ) (f : URMBlock) :
    (minSpec n f).resultReg ≤ whileMaxReg (minSpec n f) := by
  simp only [minSpec, minCounterReg', whileMaxReg, whileBase, minBase']
  omega

/-- Minimization combinator: h(x) = μy[f(x,y) = 0].

Given f : URMBlock with arity n+1 (takes x and y),
produces a block with arity n that finds the least y where f(x,y) = 0. -/
def min (n : ℕ) (f : URMBlock)
    (hf_arity : f.arity = n + 1) : URMBlock :=
  while' (minSpec n f) hf_arity (minSpec_resultReg_bounded n f)

/-! ## Convenience Accessors -/

/-- The program for minimization. -/
theorem min_program (n : ℕ) (f : URMBlock) (hf_arity : f.arity = n + 1) :
    (min n f hf_arity).program = whileProgram (minSpec n f) := rfl

/-- The arity of the minimization block. -/
theorem min_arity (n : ℕ) (f : URMBlock) (hf_arity : f.arity = n + 1) :
    (min n f hf_arity).arity = n := rfl

/-! ## Correctness -/

/-- The minimized function.
μy[f(x,y) = 0] = least y such that f(x,0), ..., f(x,y) are all defined and f(x,y) = 0. -/
def minFunction (n : ℕ) (fFunc : (Fin (n + 1) → ℕ) → Part ℕ) : (Fin n → ℕ) → Part ℕ :=
  fun inputs => Nat.rfind fun y => (fFunc (Fin.snoc inputs y)).map (· == 0)

/-- minFunction equals whileFunctionMin for any WhileSpec with matching n. -/
theorem minFunction_eq_whileFunctionMin (n : ℕ) (f : URMBlock)
    (fFunc : (Fin (n + 1) → ℕ) → Part ℕ) :
    minFunction n fFunc = whileFunctionMin (minSpec n f) fFunc := rfl

/-- Minimization correctness theorem.

If f computes fFunc, then min n f computes minFunction n fFunc.
This follows from the while loop correctness theorem. -/
theorem min_correct (n : ℕ) (f : URMBlock)
    (fFunc : (Fin (n + 1) → ℕ) → Part ℕ)
    (hf_arity : f.arity = n + 1)
    (hf_sf : f.program.IsStandardForm)
    (hf_computes : f.ComputesN (n + 1) fFunc) :
    (min n f hf_arity).ComputesN n (minFunction n fFunc) := by
  -- Rewrite to use whileFunctionMin
  rw [minFunction_eq_whileFunctionMin n f fFunc]
  -- This follows from while_correct_min
  exact while_correct_min (minSpec n f) hf_arity (minSpec_resultReg n f)
    (minSpec_resultReg_bounded n f) hf_sf fFunc hf_computes

end URMBlock

end Urm
