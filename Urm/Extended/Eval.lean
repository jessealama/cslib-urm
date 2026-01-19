/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Extended.Basic
import Urm.Execution
import Mathlib.Data.Part
import Mathlib.Computability.Partrec

/-! # Extended URM: Semantics

This module defines the evaluation semantics for ExtendedURM programs.
The semantics is compositional: each extended instruction transforms state
to state (possibly partially, for non-terminating computations).

## Main Definitions

- `evalInstr`: Evaluate a single extended instruction
- `evalProgram`: Evaluate an extended program (sequential composition)
- `runBlock`: Execute a BLOCK construct
- `runMu`: Execute a MU construct (μ-recursion)

## Semantics Overview

### Basic Instructions (Z, S, T, J)
Evaluated as in base URM, updating state directly.
Note: J instructions in an ExtendedProgram context are problematic since
the program is a list of potentially complex instructions. We handle J
only for flat programs or compile to base URM for full execution.

### BLOCK [r₀, r₁, ...] { body }
1. Create sub-state: body's R[i] ← host's R[rᵢ]
2. Run body (as base URM) until halt
3. Write back: host's R[r₀] ← body's R[0]

### MU [r₀, r₁, ...] { body } resultReg
1. Setup: body's R[i] ← host's R[rᵢ], body's R[n] ← 0
2. Loop: run body, check R[0], if ≠ 0 increment counter and repeat
3. Write back: host's R[r₀] ← body's R[resultReg]

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

namespace Extended

open Urm (State Config Program Instr Halts Result eval Steps Step)

/-! ## Sub-state Construction -/

/-- Create a sub-state for body execution from host state using register mapping.
Body's R[i] gets the value from host's R[regs[i]].
Registers beyond regs.length are initialized to 0. -/
def mkSubState (hostState : State) (regs : List ℕ) : State :=
  fun i => if h : i < regs.length then hostState (regs[i]'h) else 0

/-- Update host state by writing body's result (R[0]) back to the first mapped register.
If regs is empty, state is unchanged. -/
def writeBackResult (hostState : State) (regs : List ℕ) (result : ℕ) : State :=
  match regs with
  | [] => hostState
  | r :: _ => hostState.write r result

/-- Write a specific register value back to host. -/
def writeBackReg (hostState : State) (regs : List ℕ) (bodyState : State) (resultReg : ℕ) : State :=
  match regs with
  | [] => hostState
  | r :: _ => hostState.write r (bodyState resultReg)

/-! ## Basic Instruction Evaluation -/

/-- Evaluate a basic (non-structured) extended instruction on state.
Returns the new state. J instructions are not directly evaluable in this context
since they require a program counter. -/
def evalBasicInstr (i : ExtendedInstr) (s : State) : Option State :=
  match i with
  | ExtendedInstr.Z n => some (s.write n 0)
  | ExtendedInstr.S n => some (s.write n (s n + 1))
  | ExtendedInstr.T m n => some (s.write n (s m))
  | ExtendedInstr.J _ _ _ => none  -- J requires program context
  | ExtendedInstr.Block _ _ => none  -- Not a basic instruction
  | ExtendedInstr.Mu _ _ _ => none  -- Not a basic instruction

/-! ## Block Evaluation -/

/-- Run a BLOCK construct: execute body with mapped registers, write result back.
Returns the updated host state if body halts, otherwise diverges. -/
noncomputable def runBlock (hostState : State) (regs : List ℕ) (body : FlatProgram) : Part State :=
  -- Create sub-state with inputs from mapped registers
  let subState := mkSubState hostState regs
  let inputs := List.ofFn (fun i : Fin regs.length => hostState (regs[i]))
  -- Run body and extract result
  (Urm.eval body inputs).map fun result =>
    -- Write result back to first mapped register
    writeBackResult hostState regs result

/-- Alternative formulation: run body to completion and write back R[0]. -/
noncomputable def runBlock' (hostState : State) (regs : List ℕ) (body : FlatProgram) : Part State :=
  ⟨Halts body (List.ofFn (fun i : Fin regs.length => hostState (regs[i]))),
   fun hHalts =>
     let result := Result body (List.ofFn (fun i : Fin regs.length => hostState (regs[i]))) hHalts
     writeBackResult hostState regs result⟩

theorem runBlock_eq_runBlock' (hostState : State) (regs : List ℕ) (body : FlatProgram) :
    runBlock hostState regs body = runBlock' hostState regs body := by
  simp only [runBlock, runBlock', Urm.eval]
  rfl

/-! ## Mu Evaluation (μ-recursion) -/

/-- Create sub-state for Mu body: inputs from mapped registers + counter at position n.
Body's R[i] for i < n gets host's R[regs[i]].
Body's R[n] gets the counter value.
Body's R[i] for i > n is initialized to 0. -/
def mkMuSubState (hostState : State) (regs : List ℕ) (counter : ℕ) : State :=
  fun i =>
    if h : i < regs.length then hostState (regs[i]'h)
    else if i = regs.length then counter
    else 0

/-- Run one iteration of the Mu loop body.
Returns (result in R[0], final body state) if body halts. -/
noncomputable def runMuIteration (hostState : State) (regs : List ℕ) (body : FlatProgram)
    (counter : ℕ) : Part (ℕ × State) :=
  let subState := mkMuSubState hostState regs counter
  let inputs := (List.ofFn (fun i : Fin regs.length => hostState (regs[i]))) ++ [counter]
  ⟨Halts body inputs,
   fun hHalts =>
     let finalConfig := Classical.choose hHalts
     (finalConfig.state 0, finalConfig.state)⟩

/-- Check if Mu body halts with result 0 at a given counter value. -/
noncomputable def muExitCondition (hostState : State) (regs : List ℕ) (body : FlatProgram)
    (counter : ℕ) : Part Bool :=
  let inputs := (List.ofFn (fun i : Fin regs.length => hostState (regs[i]))) ++ [counter]
  (Urm.eval body inputs).map (· == 0)

/-- Find the least counter value k such that body(inputs, k) halts with R[0] = 0.
This is the core of μ-recursion. -/
noncomputable def findMuExit (hostState : State) (regs : List ℕ) (body : FlatProgram) : Part ℕ :=
  Nat.rfind fun k => muExitCondition hostState regs body k

/-- Run a MU construct: find least k where body returns 0, then return resultReg value.
This implements μ-recursion: μk[f(x,k) = 0]. -/
noncomputable def runMu (hostState : State) (regs : List ℕ) (body : FlatProgram)
    (resultReg : ℕ) : Part State :=
  (findMuExit hostState regs body).bind fun exitCounter =>
    -- Run body one more time at exitCounter to get final state
    (runMuIteration hostState regs body exitCounter).map fun ⟨_, finalBodyState⟩ =>
      writeBackReg hostState regs finalBodyState resultReg

/-- Simplified Mu for minimization: resultReg = regs.length (the counter position).
Returns the counter value when body first returns 0. -/
noncomputable def runMuMin (hostState : State) (regs : List ℕ) (body : FlatProgram) : Part State :=
  (findMuExit hostState regs body).map fun exitCounter =>
    writeBackResult hostState regs exitCounter

/-! ## Single Instruction Evaluation -/

/-- Evaluate a single extended instruction.
- Basic instructions (Z, S, T): update state directly
- J: Not directly evaluable (requires program context), returns none/diverges
- Block: Run body with register mapping
- Mu: Find exit counter via μ-recursion -/
noncomputable def evalInstr (i : ExtendedInstr) (s : State) : Part State :=
  match i with
  | ExtendedInstr.Z n => Part.some (s.write n 0)
  | ExtendedInstr.S n => Part.some (s.write n (s n + 1))
  | ExtendedInstr.T m n => Part.some (s.write n (s m))
  | ExtendedInstr.J _ _ _ => Part.none  -- J requires full program context
  | ExtendedInstr.Block regs body => runBlock s regs body
  | ExtendedInstr.Mu regs body resultReg => runMu s regs body resultReg

/-! ## Program Evaluation -/

/-- Evaluate an extended program by sequentially evaluating each instruction.
Note: This only works correctly for J-free programs. Programs with J instructions
should be compiled to base URM and evaluated there.

For J-free programs, evaluation is a simple fold:
  eval [i₁, i₂, ..., iₙ] s = evalInstr iₙ (... (evalInstr i₂ (evalInstr i₁ s))...) -/
noncomputable def evalProgram (p : ExtendedProgram) (s : State) : Part State :=
  p.foldl (fun acc instr => acc.bind (evalInstr instr)) (Part.some s)

/-- Evaluate an extended program starting from inputs in R[0], R[1], ... -/
noncomputable def evalFromInputs (p : ExtendedProgram) (inputs : List ℕ) : Part ℕ :=
  (evalProgram p (State.fromInputs inputs)).map State.output

/-! ## Properties -/

/-- evalInstr for Z returns immediately. -/
theorem evalInstr_Z (n : ℕ) (s : State) :
    evalInstr (ExtendedInstr.Z n) s = Part.some (s.write n 0) := rfl

/-- evalInstr for S returns immediately. -/
theorem evalInstr_S (n : ℕ) (s : State) :
    evalInstr (ExtendedInstr.S n) s = Part.some (s.write n (s n + 1)) := rfl

/-- evalInstr for T returns immediately. -/
theorem evalInstr_T (m n : ℕ) (s : State) :
    evalInstr (ExtendedInstr.T m n) s = Part.some (s.write n (s m)) := rfl

/-- evalInstr for J diverges (not evaluable in this context). -/
theorem evalInstr_J (m n q : ℕ) (s : State) :
    evalInstr (ExtendedInstr.J m n q) s = Part.none := rfl

/-- evalProgram of empty program is identity. -/
theorem evalProgram_nil (s : State) : evalProgram [] s = Part.some s := rfl

/-- evalProgram of singleton. -/
theorem evalProgram_singleton (i : ExtendedInstr) (s : State) :
    evalProgram [i] s = evalInstr i s := by
  simp only [evalProgram, List.foldl_cons, List.foldl_nil, Part.bind_some]

/-- evalProgram of cons: evaluate head, then evaluate tail on result.
The proof uses the fact that foldl with bind distributes properly. -/
theorem evalProgram_cons (i : ExtendedInstr) (is : ExtendedProgram) (s : State) :
    evalProgram (i :: is) s = (evalInstr i s).bind (evalProgram is) := by
  simp only [evalProgram, List.foldl_cons, Part.bind_some]
  induction is generalizing s with
  | nil =>
    simp only [List.foldl_nil]
    -- evalInstr i s = (evalInstr i s).bind (fun x => Part.some x)
    ext x
    constructor
    · intro hx
      refine Part.mem_bind_iff.mpr ⟨x, hx, ?_⟩
      exact Part.mem_some _
    · intro hx
      have ⟨s', hs', hx'⟩ := Part.mem_bind_iff.mp hx
      -- hx' : x ∈ evalProgram [] s' = Part.some s'
      have heq : x = s' := Part.mem_unique hx' (Part.mem_some _)
      exact heq ▸ hs'
  | cons h t ih =>
    simp only [List.foldl_cons]
    -- This case requires showing (a.bind f).bind g = a.bind (fun x => (f x).bind g)
    -- which is Part.bind_assoc, but we need to manipulate the foldl
    sorry

/-- If evalInstr returns some, it's defined. -/
theorem evalInstr_dom_of_some {i : ExtendedInstr} {s s' : State}
    (h : evalInstr i s = Part.some s') : (evalInstr i s).Dom := by
  rw [h]; trivial

/-! ## Block Properties -/

/-- mkSubState at index i < regs.length returns host value at regs[i]. -/
theorem mkSubState_lt (hostState : State) (regs : List ℕ) (i : ℕ) (hi : i < regs.length) :
    mkSubState hostState regs i = hostState (regs[i]'hi) := by
  simp [mkSubState, hi]

/-- mkSubState at index i ≥ regs.length returns 0. -/
theorem mkSubState_ge (hostState : State) (regs : List ℕ) (i : ℕ) (hi : i ≥ regs.length) :
    mkSubState hostState regs i = 0 := by
  simp [mkSubState]; intro h; exact absurd h (Nat.not_lt.mpr hi)

/-- writeBackResult with empty regs is identity. -/
theorem writeBackResult_nil (hostState : State) (result : ℕ) :
    writeBackResult hostState [] result = hostState := rfl

/-- writeBackResult writes to the first register. -/
theorem writeBackResult_cons (hostState : State) (r : ℕ) (rs : List ℕ) (result : ℕ) :
    writeBackResult hostState (r :: rs) result = hostState.write r result := rfl

/-! ## Mu Properties -/

/-- mkMuSubState at index i < regs.length returns host value at regs[i]. -/
theorem mkMuSubState_lt (hostState : State) (regs : List ℕ) (counter : ℕ)
    (i : ℕ) (hi : i < regs.length) :
    mkMuSubState hostState regs counter i = hostState (regs[i]'hi) := by
  simp [mkMuSubState, hi]

/-- mkMuSubState at index regs.length returns the counter. -/
theorem mkMuSubState_counter (hostState : State) (regs : List ℕ) (counter : ℕ) :
    mkMuSubState hostState regs counter regs.length = counter := by
  simp [mkMuSubState]

/-- mkMuSubState at index > regs.length returns 0. -/
theorem mkMuSubState_gt (hostState : State) (regs : List ℕ) (counter : ℕ)
    (i : ℕ) (hi : i > regs.length) :
    mkMuSubState hostState regs counter i = 0 := by
  simp only [mkMuSubState]
  have hlt : ¬(i < regs.length) := Nat.not_lt.mpr (Nat.le_of_lt hi)
  have hne : i ≠ regs.length := Nat.ne_of_gt hi
  simp [hlt, hne]

/-- runMuMin domain characterization: defined iff there exists k with body(inputs, k) = 0. -/
theorem runMuMin_dom_iff (hostState : State) (regs : List ℕ) (body : FlatProgram) :
    (runMuMin hostState regs body).Dom ↔ (findMuExit hostState regs body).Dom := by
  -- runMuMin uses Part.map, and map preserves domain
  simp only [runMuMin, Part.map_Dom]

end Extended

end Urm
