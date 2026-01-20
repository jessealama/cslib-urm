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

/-! ## Register Usage Bounds -/

/-- Maximum register used (read or written) by an extended instruction at the host level.
For basic instructions, this is the same as in base URM.
For Block regs body, this is max(regs) since the Block reads/writes those registers.
For While condReg body, this is max(condReg, body.maxRegister) since While runs body
directly on host state. -/
def ExtendedInstr.maxRegisterUsed : ExtendedInstr → ℕ
  | Z n => n
  | S n => n
  | T m n => max m n
  | J m n _ => max m n
  | Block regs _ => regs.foldl max 0
  | While condReg body => max condReg body.maxRegister

/-- Maximum register used by any instruction in an extended program. -/
def ExtendedProgram.maxRegisterUsed (p : ExtendedProgram) : ℕ :=
  p.foldl (fun acc i => max acc i.maxRegisterUsed) 0

theorem maxRegisterUsed_nil : ExtendedProgram.maxRegisterUsed [] = 0 := rfl

/-- Helper: foldl max is monotonic in the accumulator. -/
private theorem foldl_max_mono {α : Type*} (f : α → ℕ) (l : List α) (a b : ℕ) (h : a ≤ b) :
    l.foldl (fun acc x => max acc (f x)) a ≤ l.foldl (fun acc x => max acc (f x)) b := by
  induction l generalizing a b with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h' : max a (f x) ≤ max b (f x) := by omega
    exact ih (max a (f x)) (max b (f x)) h'

/-- Helper: foldl max result is at least the initial value. -/
private theorem foldl_max_le_init {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ) :
    init ≤ l.foldl (fun acc x => max acc (f x)) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem maxRegisterUsed_cons (i : ExtendedInstr) (is : ExtendedProgram) :
    ExtendedProgram.maxRegisterUsed (i :: is) =
    max i.maxRegisterUsed (ExtendedProgram.maxRegisterUsed is) := by
  simp only [ExtendedProgram.maxRegisterUsed, List.foldl_cons]
  -- LHS: is.foldl (fun acc x => max acc x.maxRegisterUsed) (max 0 i.maxRegisterUsed)
  -- RHS: max i.maxRegisterUsed (is.foldl (fun acc x => max acc x.maxRegisterUsed) 0)
  induction is generalizing i with
  | nil => simp only [List.foldl]; omega
  | cons j js ih =>
    simp only [List.foldl_cons]
    -- Show: js.foldl ... (max (max 0 i.maxRegisterUsed) j.maxRegisterUsed)
    --     = max i.maxRegisterUsed (js.foldl ... (max 0 j.maxRegisterUsed))
    have h1 : max (max 0 i.maxRegisterUsed) j.maxRegisterUsed =
              max i.maxRegisterUsed (max 0 j.maxRegisterUsed) := by omega
    rw [h1]
    -- Now use that foldl max distributes over max at the init
    have h2 : ∀ (a b : ℕ) (l : List ExtendedInstr),
        l.foldl (fun acc x => max acc x.maxRegisterUsed) (max a b) =
        max a (l.foldl (fun acc x => max acc x.maxRegisterUsed) b) := by
      intro a b l
      induction l generalizing a b with
      | nil => simp [List.foldl]
      | cons k ks ihk =>
        simp only [List.foldl_cons]
        rw [show max (max a b) k.maxRegisterUsed = max a (max b k.maxRegisterUsed) by omega]
        exact ihk a (max b k.maxRegisterUsed)
    exact h2 i.maxRegisterUsed (max 0 j.maxRegisterUsed) js

theorem maxRegisterUsed_le_of_mem {i : ExtendedInstr} {p : ExtendedProgram} (h : i ∈ p) :
    i.maxRegisterUsed ≤ p.maxRegisterUsed := by
  induction p with
  | nil => simp only [List.mem_nil_iff] at h
  | cons j js ih =>
    simp only [List.mem_cons] at h
    rw [maxRegisterUsed_cons]
    rcases h with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

/-! ## State Agreement Lemmas -/

/-- mkSubState only depends on registers in regs. -/
theorem mkSubState_agree (s s' : State) (regs : List ℕ)
    (h : ∀ r ∈ regs, s r = s' r) :
    mkSubState s regs = mkSubState s' regs := by
  funext i
  simp only [mkSubState]
  split_ifs with hi
  · have hr : regs[i] ∈ regs := List.getElem_mem hi
    exact h _ hr
  · rfl

/-- If states agree on all registers in regs, then runBlock has equal domains. -/
theorem runBlock_agree_dom (regs : List ℕ) (body : FlatProgram) (s s' : State)
    (h_agree : ∀ r ∈ regs, s r = s' r) :
    (runBlock s regs body).Dom ↔ (runBlock s' regs body).Dom := by
  simp only [runBlock]
  -- The inputs list is the same
  have h_inputs : (List.ofFn fun i : Fin regs.length => s (regs[i])) =
                  (List.ofFn fun i : Fin regs.length => s' (regs[i])) := by
    apply List.ext_getElem (by simp) (fun i h1 h2 => ?_)
    simp only [List.getElem_ofFn, List.length_ofFn] at h1 h2 ⊢
    exact h_agree _ (List.getElem_mem h1)
  -- Part.map f p has same domain as p
  simp only [Part.map]
  rw [h_inputs]

/-- If states agree on all registers in regs and runBlock halts, then the results
agree at the first register (regs[0]). -/
theorem runBlock_agree_head (regs : List ℕ) (body : FlatProgram) (s s' : State)
    (hne : regs ≠ [])
    (h_agree : ∀ r ∈ regs, s r = s' r)
    (hdom : (runBlock s regs body).Dom) (hdom' : (runBlock s' regs body).Dom) :
    (runBlock s regs body).get hdom (regs.head hne) =
    (runBlock s' regs body).get hdom' (regs.head hne) := by
  -- The inputs list is the same
  have h_inputs : (List.ofFn fun i : Fin regs.length => s (regs[i])) =
                  (List.ofFn fun i : Fin regs.length => s' (regs[i])) := by
    apply List.ext_getElem (by simp) (fun i h1 h2 => ?_)
    simp only [List.getElem_ofFn, List.length_ofFn] at h1 h2 ⊢
    exact h_agree _ (List.getElem_mem h1)
  cases regs with
  | nil => exact absurd rfl hne
  | cons r rs =>
    -- writeBackResult writes the result head to register r
    -- At register r, Function.update gives the updated value regardless of base state
    simp only [runBlock, Part.map_get, writeBackResult, List.head_cons, State.write]
    -- Unfold composition and apply Function.update_self
    simp only [Function.comp_apply, Function.update_self]
    -- The eval result is the same because inputs are equal
    congr 1
    rw [h_inputs]

/-- Helper lemma: foldl max is at least init. -/
private theorem foldl_max_ge_init (l : List ℕ) (init : ℕ) : init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- Helper lemma: foldl max is monotone in init. -/
private theorem foldl_max_mono' (l : List ℕ) (a b : ℕ) (h : a ≤ b) :
    l.foldl max a ≤ l.foldl max b := by
  induction l generalizing a b with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    omega

/-- Helper lemma: member of list is ≤ foldl max 0 of list. -/
theorem mem_le_foldl_max {l : List ℕ} {r : ℕ} (hr : r ∈ l) : r ≤ l.foldl max 0 := by
  induction l with
  | nil => simp only [List.mem_nil_iff] at hr
  | cons y ys ih =>
    simp only [List.mem_cons] at hr
    cases hr with
    | inl heq =>
      subst heq
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_right 0 r) (foldl_max_ge_init ys (max 0 r))
    | inr hr' =>
      simp only [List.foldl_cons]
      have hih := ih hr'
      exact Nat.le_trans hih (foldl_max_mono' ys 0 (max 0 y) (Nat.zero_le _))

/-- evalInstr for Block only depends on registers in regs (domain equality). -/
theorem evalInstr_Block_agree_dom (regs : List ℕ) (body : FlatProgram) (s s' : State)
    (h_agree : ∀ r ∈ regs, s r = s' r) :
    (evalInstr (ExtendedInstr.Block regs body) s).Dom ↔
    (evalInstr (ExtendedInstr.Block regs body) s').Dom := by
  simp only [evalInstr]
  exact runBlock_agree_dom regs body s s' h_agree

/-- evalProgram domain only depends on registers ≤ p.maxRegisterUsed.
Note: This is a partial result - Block and While cases are complex due to
workspace register modifications. -/
theorem evalProgram_agree_dom (p : ExtendedProgram) (s s' : State)
    (h_agree : ∀ r ≤ p.maxRegisterUsed, s r = s' r) :
    (evalProgram p s).Dom ↔ (evalProgram p s').Dom := by
  sorry -- Complex proof deferred; we'll fill specific cases in Correctness.lean directly

/-- evalProgram output (R[0]) only depends on registers ≤ p.maxRegisterUsed,
given that the program terminates. -/
theorem evalProgram_agree_output (p : ExtendedProgram) (s s' : State)
    (h_agree : ∀ r ≤ p.maxRegisterUsed, s r = s' r)
    (hdom : (evalProgram p s).Dom) (hdom' : (evalProgram p s').Dom) :
    (evalProgram p s).get hdom 0 = (evalProgram p s').get hdom' 0 := by
  sorry

/-! ## Workspace Read Safety -/

/-- For each Block/While in the program, subsequent instructions use registers below its workspace/internal register.
This ensures that states agreeing below the bound can be substituted in evalProgram. -/
def ExtendedProgram.WorkspaceReadSafe : ExtendedProgram → Prop
  | [] => True
  | ExtendedInstr.Block regs _ :: rest =>
      ExtendedProgram.maxRegisterUsed rest < registerBase regs ∧ WorkspaceReadSafe rest
  | ExtendedInstr.While condReg body :: rest =>
      -- While uses whileZeroReg = max condReg body.maxRegister + 1 internally
      -- So rest must use registers <= max condReg body.maxRegister
      ExtendedProgram.maxRegisterUsed rest ≤ max condReg body.maxRegister ∧ WorkspaceReadSafe rest
  | _ :: rest => WorkspaceReadSafe rest

theorem WorkspaceReadSafe_nil : ExtendedProgram.WorkspaceReadSafe [] := trivial

theorem WorkspaceReadSafe_cons_Block {regs : List ℕ} {body : FlatProgram}
    {rest : ExtendedProgram}
    (h : ExtendedProgram.WorkspaceReadSafe (ExtendedInstr.Block regs body :: rest)) :
    ExtendedProgram.maxRegisterUsed rest < registerBase regs ∧
    ExtendedProgram.WorkspaceReadSafe rest :=
  h

theorem WorkspaceReadSafe_cons_rest {i : ExtendedInstr} {rest : ExtendedProgram}
    (h : ExtendedProgram.WorkspaceReadSafe (i :: rest)) :
    ExtendedProgram.WorkspaceReadSafe rest := by
  cases i with
  | Block _ _ => exact h.2
  | While _ _ => exact h.2
  | Z _ | S _ | T _ _ | J _ _ _ => exact h

theorem WorkspaceReadSafe_cons_While {condReg : ℕ} {body : FlatProgram}
    {rest : ExtendedProgram}
    (h : ExtendedProgram.WorkspaceReadSafe (ExtendedInstr.While condReg body :: rest)) :
    ExtendedProgram.maxRegisterUsed rest ≤ max condReg body.maxRegister ∧
    ExtendedProgram.WorkspaceReadSafe rest :=
  h

/-! ## State Agreement Below Bound -/

/-- Helper: evalInstr domain only depends on registers read by the instruction. -/
theorem evalInstr_dom_agree (i : ExtendedInstr) (s s' : State) (bound : ℕ)
    (h_agree : ∀ r < bound, s r = s' r)
    (h_bound : i.maxRegisterUsed < bound) :
    (evalInstr i s).Dom ↔ (evalInstr i s').Dom := by
  cases i with
  | Z n =>
    simp only [evalInstr]
    exact Iff.rfl
  | S n =>
    simp only [evalInstr]
    exact Iff.rfl
  | T m n =>
    simp only [evalInstr]
    exact Iff.rfl
  | J m n q =>
    simp only [evalInstr]
  | Block regs body =>
    simp only [evalInstr]
    apply runBlock_agree_dom
    intro r hr
    have hr_lt : r < bound := by
      have hr_le := mem_le_foldl_max hr
      simp only [ExtendedInstr.maxRegisterUsed] at h_bound
      omega
    exact h_agree r hr_lt
  | While condReg body =>
    -- While domain depends on runWhile, which depends on condReg and body execution
    -- This case is more complex - we'll handle it specially in the correctness proof
    -- For now, use sorry (this case will be bypassed by specific state equality in Correctness)
    sorry

/-- Helper: evalInstr result at register r < bound agrees when states agree below bound. -/
theorem evalInstr_result_agree (i : ExtendedInstr) (s s' : State) (bound : ℕ) (r : ℕ)
    (h_agree : ∀ r' < bound, s r' = s' r')
    (h_bound : i.maxRegisterUsed < bound)
    (hr : r < bound)
    (hdom : (evalInstr i s).Dom) (hdom' : (evalInstr i s').Dom) :
    (evalInstr i s).get hdom r = (evalInstr i s').get hdom' r := by
  cases i with
  | Z n =>
    simp only [evalInstr, Part.get_some] at hdom hdom' ⊢
    by_cases hn : n = r
    · subst hn
      simp only [State.write, Function.update_self]
    · rw [State.write, State.write,
        Function.update_of_ne (Ne.symm hn), Function.update_of_ne (Ne.symm hn)]
      exact h_agree r hr
  | S n =>
    simp only [evalInstr, Part.get_some] at hdom hdom' ⊢
    by_cases hn : n = r
    · subst hn
      simp only [State.write, Function.update_self]
      have hn_lt : n < bound := by
        simp only [ExtendedInstr.maxRegisterUsed] at h_bound
        exact h_bound
      congr 1
      exact h_agree n hn_lt
    · rw [State.write, State.write,
        Function.update_of_ne (Ne.symm hn), Function.update_of_ne (Ne.symm hn)]
      exact h_agree r hr
  | T m n =>
    simp only [evalInstr, Part.get_some] at hdom hdom' ⊢
    by_cases hn : n = r
    · subst hn
      simp only [State.write, Function.update_self]
      have hm_lt : m < bound := by
        simp only [ExtendedInstr.maxRegisterUsed] at h_bound
        omega
      exact h_agree m hm_lt
    · rw [State.write, State.write,
        Function.update_of_ne (Ne.symm hn), Function.update_of_ne (Ne.symm hn)]
      exact h_agree r hr
  | J m n q =>
    simp only [evalInstr] at hdom
    exact hdom.elim
  | Block regs body =>
    simp only [evalInstr] at hdom hdom' ⊢
    -- Block writes to regs[0] and preserves other registers
    have h_inputs_eq : ∀ r' ∈ regs, s r' = s' r' := by
      intro r' hr'
      have hr'_lt : r' < bound := by
        have hr'_le := mem_le_foldl_max hr'
        simp only [ExtendedInstr.maxRegisterUsed] at h_bound
        omega
      exact h_agree r' hr'_lt
    by_cases hregs_ne : regs = []
    · -- Empty regs: runBlock preserves all registers
      subst hregs_ne
      simp only [runBlock, writeBackResult_nil, Part.map_get]
      exact h_agree r hr
    · -- Non-empty regs
      have hhead := regs.head?_eq_some_head hregs_ne
      by_cases hr0 : r = regs.head hregs_ne
      · -- r = regs[0]: both get the body result
        subst hr0
        exact runBlock_agree_head regs body s s' hregs_ne h_inputs_eq hdom hdom'
      · -- r ≠ regs[0]: both preserve original value
        have hr_neq : regs.head? ≠ some r := by
          rw [hhead]
          simp only [Option.some.injEq, ne_eq]
          exact Ne.symm hr0
        rw [runBlock_preserves_outside s regs body hdom r hr_neq]
        rw [runBlock_preserves_outside s' regs body hdom' r hr_neq]
        exact h_agree r hr
  | While condReg body =>
    -- While case: complex, handle in correctness proof directly
    sorry

/-- If states agree below bound and program uses registers below bound,
then evalProgram has equal domains. -/
theorem evalProgram_dom_agree_below (p : ExtendedProgram) (s s' : State) (bound : ℕ)
    (h_agree : ∀ r < bound, s r = s' r)
    (h_bound : ExtendedProgram.maxRegisterUsed p < bound)
    (h_ws : ExtendedProgram.WorkspaceReadSafe p) :
    (evalProgram p s).Dom ↔ (evalProgram p s').Dom := by
  induction p generalizing s s' with
  | nil =>
    simp only [evalProgram_nil]
    exact Iff.rfl
  | cons i rest ih =>
    rw [evalProgram_cons, evalProgram_cons]
    have hi_bound : i.maxRegisterUsed < bound := by
      rw [maxRegisterUsed_cons] at h_bound
      omega
    have hrest_bound : ExtendedProgram.maxRegisterUsed rest < bound := by
      rw [maxRegisterUsed_cons] at h_bound
      omega
    have hrest_ws : ExtendedProgram.WorkspaceReadSafe rest := WorkspaceReadSafe_cons_rest h_ws
    -- Domain of evalInstr agrees
    have hdom_i_iff := evalInstr_dom_agree i s s' bound h_agree hi_bound
    constructor
    · intro hdom
      obtain ⟨hdom_i, hdom_rest_get⟩ := Part.bind_dom.mp hdom
      have hdom_i' : (evalInstr i s').Dom := hdom_i_iff.mp hdom_i
      apply Part.bind_dom.mpr
      use hdom_i'
      have h_agree' : ∀ r < bound, (evalInstr i s).get hdom_i r = (evalInstr i s').get hdom_i' r :=
        fun r hr => evalInstr_result_agree i s s' bound r h_agree hi_bound hr hdom_i hdom_i'
      exact (ih ((evalInstr i s).get hdom_i) ((evalInstr i s').get hdom_i') h_agree'
        hrest_bound hrest_ws).mp hdom_rest_get
    · intro hdom'
      obtain ⟨hdom_i', hdom_rest'_get⟩ := Part.bind_dom.mp hdom'
      have hdom_i : (evalInstr i s).Dom := hdom_i_iff.mpr hdom_i'
      apply Part.bind_dom.mpr
      use hdom_i
      have h_agree' : ∀ r < bound, (evalInstr i s).get hdom_i r = (evalInstr i s').get hdom_i' r :=
        fun r hr => evalInstr_result_agree i s s' bound r h_agree hi_bound hr hdom_i hdom_i'
      exact (ih ((evalInstr i s).get hdom_i) ((evalInstr i s').get hdom_i') h_agree'
        hrest_bound hrest_ws).mpr hdom_rest'_get

/-- If states agree below bound and program uses registers below bound,
then evalProgram results agree at register 0. -/
theorem evalProgram_result0_agree_below (p : ExtendedProgram) (s s' : State) (bound : ℕ)
    (h_agree : ∀ r < bound, s r = s' r)
    (h_bound : ExtendedProgram.maxRegisterUsed p < bound)
    (h_ws : ExtendedProgram.WorkspaceReadSafe p)
    (h0 : 0 < bound)
    (hdom : (evalProgram p s).Dom) (hdom' : (evalProgram p s').Dom) :
    (evalProgram p s).get hdom 0 = (evalProgram p s').get hdom' 0 := by
  induction p generalizing s s' with
  | nil =>
    simp only [evalProgram_nil]
    exact h_agree 0 h0
  | cons i rest ih =>
    have hi_bound : i.maxRegisterUsed < bound := by
      rw [maxRegisterUsed_cons] at h_bound
      omega
    have hrest_bound : ExtendedProgram.maxRegisterUsed rest < bound := by
      rw [maxRegisterUsed_cons] at h_bound
      omega
    have hrest_ws : ExtendedProgram.WorkspaceReadSafe rest := WorkspaceReadSafe_cons_rest h_ws
    -- Unfold evalProgram for cons to get bind structure
    have heq1 : evalProgram (i :: rest) s = (evalInstr i s).bind (evalProgram rest) := evalProgram_cons i rest s
    have heq2 : evalProgram (i :: rest) s' = (evalInstr i s').bind (evalProgram rest) := evalProgram_cons i rest s'
    -- Extract domains
    have hdom_bind : ((evalInstr i s).bind (evalProgram rest)).Dom := heq1 ▸ hdom
    have hdom'_bind : ((evalInstr i s').bind (evalProgram rest)).Dom := heq2 ▸ hdom'
    have hdom_i : (evalInstr i s).Dom := Part.Dom.of_bind hdom_bind
    have hdom_i' : (evalInstr i s').Dom := Part.Dom.of_bind hdom'_bind
    obtain ⟨w1, hdom_rest⟩ := Part.bind_dom.mp hdom_bind
    obtain ⟨w2, hdom_rest'⟩ := Part.bind_dom.mp hdom'_bind
    -- Since Part.get is proof-irrelevant, (evalInstr i s).get w1 = (evalInstr i s).get hdom_i
    have hdom_rest_get : (evalProgram rest ((evalInstr i s).get hdom_i)).Dom := hdom_rest
    have hdom_rest'_get : (evalProgram rest ((evalInstr i s').get hdom_i')).Dom := hdom_rest'
    -- States after evalInstr agree below bound
    have h_agree' : ∀ r < bound, (evalInstr i s).get hdom_i r = (evalInstr i s').get hdom_i' r :=
      fun r hr => evalInstr_result_agree i s s' bound r h_agree hi_bound hr hdom_i hdom_i'
    -- Apply IH (h0 is fixed in context, not a parameter of ih)
    have hih := ih ((evalInstr i s).get hdom_i) ((evalInstr i s').get hdom_i')
      h_agree' hrest_bound hrest_ws hdom_rest_get hdom_rest'_get
    -- Use Part.Dom.bind: o.bind f = f (o.get h) when h : o.Dom
    have hbind1 : (evalInstr i s).bind (evalProgram rest) = evalProgram rest ((evalInstr i s).get hdom_i) :=
      Part.Dom.bind hdom_i (evalProgram rest)
    have hbind2 : (evalInstr i s').bind (evalProgram rest) = evalProgram rest ((evalInstr i s').get hdom_i') :=
      Part.Dom.bind hdom_i' (evalProgram rest)
    -- Chain equalities using Part.get_eq_get_of_eq: a.get ha = b.get _ when a = b
    have heq_lhs : evalProgram (i :: rest) s = evalProgram rest ((evalInstr i s).get hdom_i) :=
      heq1.trans hbind1
    have heq_rhs : evalProgram (i :: rest) s' = evalProgram rest ((evalInstr i s').get hdom_i') :=
      heq2.trans hbind2
    calc (evalProgram (i :: rest) s).get hdom 0
        = (evalProgram rest ((evalInstr i s).get hdom_i)).get (heq_lhs ▸ hdom) 0 := by
            simp only [Part.get.congr_simp _ _ heq_lhs]
      _ = (evalProgram rest ((evalInstr i s).get hdom_i)).get hdom_rest_get 0 := rfl
      _ = (evalProgram rest ((evalInstr i s').get hdom_i')).get hdom_rest'_get 0 := hih
      _ = (evalProgram rest ((evalInstr i s').get hdom_i')).get (heq_rhs ▸ hdom') 0 := rfl
      _ = (evalProgram (i :: rest) s').get hdom' 0 := by
            simp only [Part.get.congr_simp _ _ heq_rhs.symm]

end Extended

end Urm
