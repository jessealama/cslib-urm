/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Block.Basic
import Urm.Block.Compile
import Urm.Block.Glue
import Urm.StraightLine
import Urm.PrimitiveRecursion.Core

/-! # Primitive Recursion Combinator for URMBlock

This file defines the primitive recursion combinator for URMBlock, implementing
h(x, 0) = f(x) and h(x, y+1) = g(x, y, h(x, y)).

## Register Layout

For primitive recursion with:
- f : URMBlock with arity n (base case)
- g : URMBlock with arity n+2 (recursive step: takes x, counter, accumulator)

Register layout:
- R[0..n-1]           : working inputs for f and g (restored each iteration)
- R[n]                : for g: counter k
- R[n+1]              : for g: accumulator value
- R[base+1..base+n]   : saved inputs x (preserved throughout)
- R[base+n+1]         : savedY (original recursion depth)
- R[base+n+2]         : counter (current iteration 0..y)
- R[base+n+3]         : accumulator (result from previous iteration)
- R[base+n+4]         : zero register (always 0, for J comparisons)

## Program Structure

1. Setup: save inputs, initialize counter=0, zero register
2. Base case: copy saved x to working, run f.compile(base), save to accumulator
3. Loop check: if counter = savedY, jump to output
4. Loop body: setup g inputs (x, counter, acc), run g.compile(base), save result, increment counter, jump back
5. Output: copy accumulator to R[0]

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

namespace URMBlock

open Program

/-! ## Base Computation -/

/-- The base offset for primitive recursion.
Must be large enough to accommodate g's input space (0..n+1) and both f and g's maxReg. -/
def precBase (n : ℕ) (f g : URMBlock) : ℕ :=
  max (n + 1) (max f.maxReg g.maxReg)

/-! ## Register Indices -/

/-- Start of saved inputs R[base+1..base+n]. -/
def precSavedInputsStart (n : ℕ) (f g : URMBlock) : ℕ :=
  precBase n f g + 1

/-- Register storing the original y value. -/
def precSavedYReg (n : ℕ) (f g : URMBlock) : ℕ :=
  precBase n f g + n + 1

/-- Counter register (tracks current iteration 0..y). -/
def precCounterReg (n : ℕ) (f g : URMBlock) : ℕ :=
  precBase n f g + n + 2

/-- Accumulator register (holds result from previous iteration). -/
def precAccumulatorReg (n : ℕ) (f g : URMBlock) : ℕ :=
  precBase n f g + n + 3

/-- Zero register (always 0, for J comparisons). -/
def precZeroReg (n : ℕ) (f g : URMBlock) : ℕ :=
  precBase n f g + n + 4

/-! ## Base Bound Lemmas -/

theorem precBase_ge_n_succ (n : ℕ) (f g : URMBlock) :
    n + 1 ≤ precBase n f g := le_max_left _ _

theorem precBase_ge_n (n : ℕ) (f g : URMBlock) :
    n ≤ precBase n f g := by
  have h := precBase_ge_n_succ n f g; omega

theorem precBase_ge_f (n : ℕ) (f g : URMBlock) :
    f.maxReg ≤ precBase n f g := by
  simp only [precBase]; exact le_max_of_le_right (le_max_left _ _)

theorem precBase_ge_g (n : ℕ) (f g : URMBlock) :
    g.maxReg ≤ precBase n f g := by
  simp only [precBase]; exact le_max_of_le_right (le_max_right _ _)

/-! ## Length Calculations -/

/-- Length of setup phase. -/
def precSetupLength (n : ℕ) : ℕ := (n + 1) + 2

/-- Length of base case prologue (clear + copy). -/
def precBasePrologueLength (n : ℕ) (f g : URMBlock) : ℕ :=
  (precBase n f g + 1) + n

/-- Length of base case phase. -/
def precBaseCaseLength (n : ℕ) (f g : URMBlock) : ℕ :=
  precBasePrologueLength n f g + f.program.length + 1

/-- Length of loop prologue (clear + copy + 2 transfers). -/
def precLoopPrologueLength (n : ℕ) (f g : URMBlock) : ℕ :=
  (precBase n f g + 1) + n + 2

/-- Length of loop epilogue (save + increment + jump). -/
def precLoopEpilogueLength : ℕ := 3

/-- Length of loop body. -/
def precLoopBodyLength (n : ℕ) (f g : URMBlock) : ℕ :=
  precLoopPrologueLength n f g + g.program.length + precLoopEpilogueLength

/-! ## PC Positions -/

/-- PC where base case starts. -/
def precBaseCasePC (n : ℕ) : ℕ := precSetupLength n

/-- PC where loop check happens. -/
def precLoopCheckPC (n : ℕ) (f g : URMBlock) : ℕ :=
  precSetupLength n + precBaseCaseLength n f g

/-- PC where loop body starts. -/
def precLoopBodyPC (n : ℕ) (f g : URMBlock) : ℕ :=
  precLoopCheckPC n f g + 1

/-- PC of output phase. -/
def precOutputPC (n : ℕ) (f g : URMBlock) : ℕ :=
  precLoopBodyPC n f g + precLoopBodyLength n f g

/-! ## Program Phases -/

/-- Setup phase: save inputs (including y), zero counter and zero register. -/
def precSetupPhase (n : ℕ) (f g : URMBlock) : Program :=
  (copyRegisterRange 0 (precSavedInputsStart n f g) (n + 1)).concat
    [Instr.Z (precCounterReg n f g), Instr.Z (precZeroReg n f g)]

/-- Base case prologue: clear workspace, restore x. -/
def precBasePrologue (n : ℕ) (f g : URMBlock) : Program :=
  (clearRegisters (precBase n f g)).concat
    (copyRegisterRange (precSavedInputsStart n f g) 0 n)

/-- Base case phase: prologue + f.compile(base) + save to accumulator. -/
def precBaseCasePhase (n : ℕ) (f g : URMBlock) : Program :=
  (precBasePrologue n f g).concat (
    (f.compile (precBase n f g)).concat
      [Instr.T (precBase n f g) (precAccumulatorReg n f g)])

/-- Loop check: jump to output if counter = savedY. -/
def precLoopCheck (n : ℕ) (f g : URMBlock) : Program :=
  [Instr.J (precCounterReg n f g) (precSavedYReg n f g) (precOutputPC n f g)]

/-- Loop prologue: clear workspace, restore x, setup g's inputs (counter, accumulator). -/
def precLoopPrologue (n : ℕ) (f g : URMBlock) : Program :=
  (clearRegisters (precBase n f g)).concat (
    (copyRegisterRange (precSavedInputsStart n f g) 0 n).concat
      [Instr.T (precCounterReg n f g) n,
       Instr.T (precAccumulatorReg n f g) (n + 1)])

/-- Loop epilogue: save result, increment counter, jump back. -/
def precLoopEpilogue (n : ℕ) (f g : URMBlock) : Program :=
  [Instr.T (precBase n f g) (precAccumulatorReg n f g),
   Instr.S (precCounterReg n f g),
   Instr.J (precZeroReg n f g) (precZeroReg n f g) (precLoopCheckPC n f g)]

/-- Loop body: prologue + g.compile(base) + epilogue. -/
def precLoopBody (n : ℕ) (f g : URMBlock) : Program :=
  (precLoopPrologue n f g).concat (
    (g.compile (precBase n f g)).concat
      (precLoopEpilogue n f g))

/-- Output phase: copy accumulator to R[0]. -/
def precOutputPhase (n : ℕ) (f g : URMBlock) : Program :=
  [Instr.T (precAccumulatorReg n f g) 0]

/-- The complete primitive recursion program. -/
def precProgram (n : ℕ) (f g : URMBlock) : Program :=
  (precSetupPhase n f g).concat (
    (precBaseCasePhase n f g).concat (
      (precLoopCheck n f g).concat (
        (precLoopBody n f g).concat
          (precOutputPhase n f g))))

/-! ## The Prec Combinator -/

/-- Maximum register used by the primitive recursion program. -/
def precMaxReg (n : ℕ) (f g : URMBlock) : ℕ :=
  -- Highest is zeroReg = base + n + 4
  precBase n f g + n + 4

/-- Primitive recursion combinator: h(x,0) = f(x), h(x,y+1) = g(x,y,h(x,y)).

Given:
- f : URMBlock with arity n (base case)
- g : URMBlock with arity n+2 (recursive step)

Produces a block with arity n+1 that computes the primitive recursion. -/
def prec (n : ℕ) (f g : URMBlock)
    (hf_arity : f.arity = n) (hg_arity : g.arity = n + 2) : URMBlock where
  program := precProgram n f g
  arity := n + 1
  h_sf := by
    -- TODO: Prove that precProgram is in standard form
    sorry

/-! ## Correctness -/

/-- The primitive recursive function. -/
def precFunction (n : ℕ) (fFunc : (Fin n → ℕ) → Part ℕ)
    (gFunc : (Fin (n + 2) → ℕ) → Part ℕ) : (Fin (n + 1) → ℕ) → Part ℕ :=
  fun inputs =>
    let x := fun i : Fin n => inputs i.castSucc
    let y := inputs (Fin.last n)
    -- Iterate: acc₀ = f(x), acc_{k+1} = g(x, k, acc_k)
    Nat.recOn y
      (fFunc x)
      (fun k ih => ih.bind (fun accK =>
        gFunc (Fin.snoc (Fin.snoc x k) accK)))

/-- Primitive recursion correctness theorem.

If f computes fFunc and g computes gFunc, then
prec n f g computes precFunction n fFunc gFunc. -/
theorem prec_correct (n : ℕ) (f g : URMBlock)
    (fFunc : (Fin n → ℕ) → Part ℕ)
    (gFunc : (Fin (n + 2) → ℕ) → Part ℕ)
    (hf_arity : f.arity = n)
    (hg_arity : g.arity = n + 2)
    (hf_computes : f.ComputesN n fFunc)
    (hg_computes : g.ComputesN (n + 2) gFunc) :
    (prec n f g hf_arity hg_arity).ComputesN (n + 1) (precFunction n fFunc gFunc) := by
  intro inputs
  simp only [precFunction]
  constructor
  · -- Halting equivalence
    constructor
    · -- Forward: program halts → function defined
      intro hHalts
      sorry
    · -- Backward: function defined → program halts
      intro hDom
      sorry
  · -- Result correctness
    intro hHalts hDom
    sorry

end URMBlock

end Urm
