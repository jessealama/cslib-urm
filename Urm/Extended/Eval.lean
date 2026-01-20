/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Extended.Basic
import Urm.Execution
import Mathlib.Data.Part
import Mathlib.Computability.Partrec
import Mathlib.Control.Fix
import Mathlib.Control.LawfulFix

/-! # Extended URM: Semantics

This module defines the evaluation semantics for ExtendedURM programs.
The semantics is compositional: each extended instruction transforms state
to state (possibly partially, for non-terminating computations).

## Main Definitions

- `evalInstr`: Evaluate a single extended instruction
- `evalProgram`: Evaluate an extended program (sequential composition)
- `runBlock`: Execute a BLOCK construct
- `runWhile`: Execute a WHILE construct

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

### WHILE condReg { body }
1. Check R[condReg]: if = 0, exit
2. Run body (as base URM) until halt
3. Go to step 1

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

/-- writeBackResult preserves registers other than regs[0]. -/
theorem writeBackResult_preserves (hostState : State) (regs : List ℕ) (result : ℕ)
    (r : ℕ) (hr : regs.head? ≠ some r) :
    writeBackResult hostState regs result r = hostState r := by
  cases regs with
  | nil => rfl
  | cons h t =>
    simp only [writeBackResult, State.write, List.head?] at hr ⊢
    have hne : r ≠ h := fun heq => hr (congrArg some heq.symm)
    exact Function.update_of_ne hne result hostState

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
  | ExtendedInstr.While _ _ => none  -- Not a basic instruction

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

/-- runBlock preserves registers other than regs[0]. -/
theorem runBlock_preserves_outside (hostState : State) (regs : List ℕ) (body : FlatProgram)
    (hdom : (runBlock hostState regs body).Dom)
    (r : ℕ) (hr : regs.head? ≠ some r) :
    (runBlock hostState regs body).get hdom r = hostState r := by
  simp only [runBlock, Part.map_get] at hdom ⊢
  exact writeBackResult_preserves hostState regs _ r hr

/-! ## While Evaluation -/

/-- Evaluate a flat program starting from a given state.
Returns the final state if the program halts.

This differs from `Urm.eval` which loads inputs into R[0], R[1], etc.
Here, the program runs directly on the given state. -/
noncomputable def evalFlat (body : FlatProgram) (s : State) : Part State :=
  ⟨∃ c, Steps body ⟨0, s⟩ c ∧ c.isHalted body,
   fun hHalts =>
     (Classical.choose hHalts).state⟩

/-- The step function for a while loop.
Returns `Sum.inl s` to stop (when condition is 0) or `Sum.inr s'` to continue. -/
noncomputable def whileStep (condReg : ℕ) (body : FlatProgram) (s : State) : Part (State ⊕ State) :=
  if s condReg = 0 then Part.some (Sum.inl s)
  else (evalFlat body s).map Sum.inr

/-- Run a while loop: iterate body while R[condReg] ≠ 0.
Returns the final state when R[condReg] becomes 0, or diverges if loop never exits.

Semantics:
1. Check R[condReg]: if = 0, return current state
2. Run body from current state until it halts
3. Recurse with the new state -/
noncomputable def runWhile (s : State) (condReg : ℕ) (body : FlatProgram) : Part State :=
  PFun.fix (whileStep condReg body) s

/-! ## Single Instruction Evaluation -/

/-- Evaluate a single extended instruction.
- Basic instructions (Z, S, T): update state directly
- J: Not directly evaluable (requires program context), returns none/diverges
- Block: Run body with register mapping
- While: Run body while condition register is non-zero -/
noncomputable def evalInstr (i : ExtendedInstr) (s : State) : Part State :=
  match i with
  | ExtendedInstr.Z n => Part.some (s.write n 0)
  | ExtendedInstr.S n => Part.some (s.write n (s n + 1))
  | ExtendedInstr.T m n => Part.some (s.write n (s m))
  | ExtendedInstr.J _ _ _ => Part.none  -- J requires full program context
  | ExtendedInstr.Block regs body => runBlock s regs body
  | ExtendedInstr.While condReg body => runWhile s condReg body

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

/-- Helper: foldl with bind distributes the initial Part through the fold. -/
private theorem foldl_bind_distrib (init : Part State) (p : ExtendedProgram) :
    p.foldl (fun acc i => acc.bind (evalInstr i)) init =
    init.bind (fun s => p.foldl (fun acc i => acc.bind (evalInstr i)) (Part.some s)) := by
  induction p generalizing init with
  | nil =>
    simp only [List.foldl_nil]
    -- Need: init = init.bind (fun s => Part.some s)
    exact Part.bind_some_right init |>.symm
  | cons h t ih =>
    simp only [List.foldl_cons]
    -- LHS: t.foldl ... (init.bind (evalInstr h))
    -- Apply ih to get: (init.bind (evalInstr h)).bind (fun s1 => t.foldl ... (Part.some s1))
    rw [ih (init.bind (evalInstr h))]
    -- RHS: init.bind (fun s0 => t.foldl ... ((Part.some s0).bind (evalInstr h)))
    --     = init.bind (fun s0 => t.foldl ... (evalInstr h s0))
    simp only [Part.bind_some]
    -- Now LHS and RHS match up to associativity of bind
    -- LHS: (init.bind (evalInstr h)).bind (fun s1 => t.foldl ... (Part.some s1))
    -- RHS: init.bind (fun s0 => (evalInstr h s0).bind (fun s1 => t.foldl ... (Part.some s1)))
    -- Use bind associativity
    conv_lhs => rw [Part.bind_assoc]
    -- Now both sides are: init.bind (fun s0 => ...)
    -- LHS: init.bind (fun x => (evalInstr h x).bind (fun s => t.foldl ... (Part.some s)))
    -- RHS: init.bind (fun s => t.foldl ... (evalInstr h s))
    -- These are equal because ih (evalInstr h s0) says:
    --   t.foldl ... (evalInstr h s0) = (evalInstr h s0).bind (fun s => t.foldl ... (Part.some s))
    congr 1
    funext s0
    exact (ih (evalInstr h s0)).symm

/-- evalProgram of cons: evaluate head, then evaluate tail on result. -/
theorem evalProgram_cons (i : ExtendedInstr) (is : ExtendedProgram) (s : State) :
    evalProgram (i :: is) s = (evalInstr i s).bind (evalProgram is) := by
  simp only [evalProgram, List.foldl_cons, Part.bind_some]
  rw [foldl_bind_distrib]
  rfl

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

/-! ## While Properties -/

/-- evalFlat terminates when the body program halts from the initial state. -/
theorem evalFlat_dom_iff (body : FlatProgram) (s : State) :
    (evalFlat body s).Dom ↔ ∃ c, Steps body ⟨0, s⟩ c ∧ c.isHalted body := by
  rfl

/-- whileStep at 0 returns Sum.inl s. -/
theorem whileStep_zero (condReg : ℕ) (body : FlatProgram) (s : State) (hs : s condReg = 0) :
    whileStep condReg body s = Part.some (Sum.inl s) := by
  simp only [whileStep, hs, ↓reduceIte]

/-- whileStep at non-zero returns Sum.inr of body result. -/
theorem whileStep_nonzero (condReg : ℕ) (body : FlatProgram) (s : State) (hs : s condReg ≠ 0) :
    whileStep condReg body s = (evalFlat body s).map Sum.inr := by
  simp only [whileStep, hs, ↓reduceIte]

/-- runWhile at 0 returns immediately. -/
theorem runWhile_zero (condReg : ℕ) (body : FlatProgram) (s : State) (hs : s condReg = 0) :
    runWhile s condReg body = Part.some s := by
  simp only [runWhile]
  have h : Sum.inl s ∈ whileStep condReg body s := by
    simp only [whileStep_zero condReg body s hs, Part.mem_some_iff]
  exact Part.eq_some_iff.mpr (PFun.fix_stop h)

/-- runWhile unfolds: if condition is non-zero, run body then recurse. -/
theorem runWhile_unfold (condReg : ℕ) (body : FlatProgram) (s : State) (hs : s condReg ≠ 0) :
    runWhile s condReg body = (evalFlat body s).bind (fun s' => runWhile s' condReg body) := by
  simp only [runWhile]
  ext x
  rw [PFun.mem_fix_iff]
  constructor
  · intro hx
    cases hx with
    | inl hstop =>
      -- whileStep returns Sum.inl at stop, but condition is non-zero
      simp only [whileStep_nonzero condReg body s hs, Part.mem_map_iff] at hstop
      obtain ⟨_, _, h⟩ := hstop
      exact absurd h (by simp)
    | inr hcont =>
      obtain ⟨s', hs', hfix⟩ := hcont
      simp only [whileStep_nonzero condReg body s hs, Part.mem_map_iff] at hs'
      obtain ⟨s'', hs'', hinj⟩ := hs'
      cases hinj
      exact Part.mem_bind_iff.mpr ⟨s', hs'', hfix⟩
  · intro hx
    obtain ⟨s', hs', hfix⟩ := Part.mem_bind_iff.mp hx
    right
    use s'
    constructor
    · simp only [whileStep_nonzero condReg body s hs, Part.mem_map_iff]
      exact ⟨s', hs', rfl⟩
    · exact hfix

end Extended

end Urm
