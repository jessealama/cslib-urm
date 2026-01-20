/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Extended.Basic
import Urm.Execution
import Urm.Shift
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

/-! ## State Agreement and Preservation Lemmas -/

/-- Single step preserves registers above maxRegister. -/
private theorem step_preserves_above_maxRegister {body : FlatProgram} {c c' : Config}
    (hstep : Step body c c') (r : ℕ) (hr : body.maxRegister < r) : c'.state r = c.state r := by
  cases hstep with
  | zero hinstr =>
    simp only [State.write]
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hn_lt : _ < r := Nat.lt_of_le_of_lt hmax hr
    exact Function.update_of_ne (Ne.symm (Nat.ne_of_lt hn_lt)) _ _
  | succ hinstr =>
    simp only [State.write]
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hn_lt : _ < r := Nat.lt_of_le_of_lt hmax hr
    exact Function.update_of_ne (Ne.symm (Nat.ne_of_lt hn_lt)) _ _
  | trans hinstr =>
    simp only [State.write, State.read]
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hn_le : _ ≤ body.maxRegister := Nat.le_trans (Nat.le_max_right _ _) hmax
    have hn_lt : _ < r := Nat.lt_of_le_of_lt hn_le hr
    exact Function.update_of_ne (Ne.symm (Nat.ne_of_lt hn_lt)) _ _
  | jump_eq _ _ | jump_ne _ _ =>
    rfl

/-- evalFlat preserves registers above maxRegister. -/
theorem evalFlat_preserves_above_maxRegister {body : FlatProgram} {s : State}
    (hdom : (evalFlat body s).Dom) (r : ℕ) (hr : body.maxRegister < r) :
    (evalFlat body s).get hdom r = s r := by
  simp only [evalFlat] at hdom ⊢
  let c := Classical.choose hdom
  have hspec := Classical.choose_spec hdom
  obtain ⟨hsteps, _⟩ := hspec
  suffices h : ∀ (c₁ c₂ : Config), Steps body c₁ c₂ → c₂.state r = c₁.state r by
    exact h ⟨0, s⟩ c hsteps
  intro c₁ c₂ hsteps'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih => rw [ih]; exact step_preserves_above_maxRegister hstep r hr

/-- If two states agree on registers ≤ maxRegister, a step from one state implies
    the same step is possible from the other, with agreeing result states. -/
private theorem step_synchronized {body : FlatProgram} {pc pc' : ℕ} {s s' σ : State}
    (hagree : ∀ r, r ≤ body.maxRegister → s r = s' r)
    (hstep : Step body ⟨pc, s⟩ ⟨pc', σ⟩) :
    ∃ σ', Step body ⟨pc, s'⟩ ⟨pc', σ'⟩ ∧ (∀ r, r ≤ body.maxRegister → σ r = σ' r) := by
  cases hstep with
  | zero hinstr =>
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    refine ⟨s'.write _ 0, Step.zero hinstr, ?_⟩
    intro r hr
    simp only [State.write, Function.update]
    split_ifs with heq
    · rfl
    · exact hagree r hr
  | succ hinstr =>
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hn_le : _ ≤ body.maxRegister := hmax
    refine ⟨s'.write _ (s'.read _ + 1), Step.succ hinstr, ?_⟩
    intro r hr
    simp only [State.write, State.read, Function.update]
    split_ifs with heq
    · subst heq; rw [hagree _ hn_le]
    · exact hagree r hr
  | trans hinstr =>
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hm_le : _ ≤ body.maxRegister := Nat.le_trans (Nat.le_max_left _ _) hmax
    refine ⟨s'.write _ (s'.read _), Step.trans hinstr, ?_⟩
    intro r hr
    simp only [State.write, State.read, Function.update]
    split_ifs with heq
    · subst heq; rw [hagree _ hm_le]
    · exact hagree r hr
  | jump_eq hinstr hcmp =>
    rename_i m n
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hm_le : m ≤ body.maxRegister := Nat.le_trans (Nat.le_max_left m n) hmax
    have hn_le : n ≤ body.maxRegister := Nat.le_trans (Nat.le_max_right m n) hmax
    have hcmp' : s'.read m = s'.read n := by
      simp only [State.read] at hcmp ⊢
      rw [← hagree m hm_le, ← hagree n hn_le, hcmp]
    exact ⟨s', Step.jump_eq hinstr hcmp', hagree⟩
  | jump_ne hinstr hcmp =>
    rename_i m n _
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hm_le : m ≤ body.maxRegister := Nat.le_trans (Nat.le_max_left m n) hmax
    have hn_le : n ≤ body.maxRegister := Nat.le_trans (Nat.le_max_right m n) hmax
    have hcmp' : s'.read m ≠ s'.read n := by
      simp only [State.read] at hcmp ⊢
      rw [← hagree m hm_le, ← hagree n hn_le]
      exact hcmp
    exact ⟨s', Step.jump_ne hinstr hcmp', hagree⟩

/-- If two states agree on ≤ maxRegister and we have steps from one,
    we can build parallel steps from the other with agreeing final states. -/
private theorem steps_synchronized' {body : FlatProgram} {c c_end : Config}
    (hsteps : Steps body c c_end) :
    ∀ s', (∀ r, r ≤ body.maxRegister → c.state r = s' r) →
      ∃ c'_end : Config, Steps body ⟨c.pc, s'⟩ c'_end ∧
        c'_end.pc = c_end.pc ∧
        (∀ r, r ≤ body.maxRegister → c_end.state r = c'_end.state r) := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s' hagree
    exact ⟨⟨c_end.pc, s'⟩, Steps.refl _, rfl, hagree⟩
  | head hstep hrest ih =>
    intro s' hagree
    obtain ⟨σ', hstep', hagree'⟩ := step_synchronized hagree hstep
    obtain ⟨c'_end, hsteps', hpc_eq, hagree_end⟩ := ih σ' hagree'
    exact ⟨c'_end, Relation.ReflTransGen.head hstep' hsteps', hpc_eq, hagree_end⟩

/-- If states agree on ≤ maxRegister, evalFlat has the same domain for both. -/
theorem evalFlat_dom_agree {body : FlatProgram} {s s' : State}
    (hagree : ∀ r, r ≤ body.maxRegister → s r = s' r) :
    (evalFlat body s).Dom ↔ (evalFlat body s').Dom := by
  simp only [evalFlat]
  constructor
  · intro ⟨c, hsteps, hhalted⟩
    obtain ⟨c', hsteps', hpc_eq, _⟩ := steps_synchronized' hsteps s' hagree
    have hhalted' : c'.isHalted body := by
      simp only [Config.isHalted] at hhalted ⊢
      rw [hpc_eq]; exact hhalted
    exact ⟨c', hsteps', hhalted'⟩
  · intro ⟨c', hsteps', hhalted'⟩
    have hagree_sym : ∀ r, r ≤ body.maxRegister → s' r = s r := fun r hr => (hagree r hr).symm
    obtain ⟨c, hsteps, hpc_eq, _⟩ := steps_synchronized' hsteps' s hagree_sym
    have hhalted : c.isHalted body := by
      simp only [Config.isHalted] at hhalted' ⊢
      rw [hpc_eq]; exact hhalted'
    exact ⟨c, hsteps, hhalted⟩

/-- If states agree on ≤ maxRegister and both evalFlat calls are defined,
    the results agree on registers ≤ maxRegister. -/
theorem evalFlat_result_agree {body : FlatProgram} {s s' : State}
    (hagree : ∀ r, r ≤ body.maxRegister → s r = s' r)
    (hdom : (evalFlat body s).Dom) (hdom' : (evalFlat body s').Dom)
    (r : ℕ) (hr : r ≤ body.maxRegister) :
    (evalFlat body s).get hdom r = (evalFlat body s').get hdom' r := by
  have hdom_unfold : ∃ c, Steps body ⟨0, s⟩ c ∧ c.isHalted body := by simp only [evalFlat] at hdom; exact hdom
  have hdom'_unfold : ∃ c', Steps body ⟨0, s'⟩ c' ∧ c'.isHalted body := by simp only [evalFlat] at hdom'; exact hdom'
  obtain ⟨c, hsteps, hhalted⟩ := hdom_unfold
  obtain ⟨c', hsteps', hhalted'⟩ := hdom'_unfold
  obtain ⟨c'_sync, hsteps'_sync, hpc_eq, hagree_end⟩ := steps_synchronized' hsteps s' hagree
  have hhalted'_sync : c'_sync.isHalted body := by
    simp only [Config.isHalted] at hhalted ⊢
    rw [hpc_eq]; exact hhalted
  have hc'_eq : c' = c'_sync := Steps.halts_unique hsteps' hhalted' hsteps'_sync hhalted'_sync
  simp only [evalFlat]
  have hchoose_c : (Classical.choose hdom) = c := by
    have hspec := Classical.choose_spec hdom
    exact Steps.halts_unique hspec.1 hspec.2 hsteps hhalted
  have hchoose_c' : (Classical.choose hdom') = c' := by
    have hspec' := Classical.choose_spec hdom'
    exact Steps.halts_unique hspec'.1 hspec'.2 hsteps' hhalted'
  rw [hchoose_c, hchoose_c', hc'_eq]
  exact hagree_end r hr

/-- If `x ∈ runWhile s condReg body` and s' agrees with s on relevant registers,
    then `runWhile s' condReg body` is defined. -/
private theorem runWhile_dom_of_mem_agree {condReg : ℕ} {body : FlatProgram}
    {s s' : State} {x : State}
    (hmem : x ∈ runWhile s condReg body)
    (hagree : ∀ r, r ≤ max condReg body.maxRegister → s r = s' r) :
    (runWhile s' condReg body).Dom := by
  simp only [runWhile] at hmem ⊢
  refine PFun.fixInduction' hmem
    (fun a_final hstop a' hagree' => ?_)
    (fun a₀ a₁ hmem_a₁ hcont ih a' hagree' => ?_)
    s' hagree
  · simp only [whileStep] at hstop
    split_ifs at hstop with hcond
    · have ha'_cond : a' condReg = 0 := by
        rw [← hagree' condReg (Nat.le_max_left _ _), hcond]
      have hstop' : Sum.inl a' ∈ whileStep condReg body a' := by
        simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_some_iff]
      exact Part.dom_iff_mem.mpr ⟨a', PFun.fix_stop hstop'⟩
    · simp only [Part.mem_map_iff] at hstop
      obtain ⟨_, _, h⟩ := hstop
      exact absurd h (by simp)
  · simp only [whileStep] at hcont
    split_ifs at hcont with hcond
    · simp only [Part.mem_some_iff] at hcont
      exact absurd hcont (by simp)
    · simp only [Part.mem_map_iff] at hcont
      obtain ⟨σ, hσ_mem, hσ_eq⟩ := hcont
      cases hσ_eq
      have ha'_cond : a' condReg ≠ 0 := by
        rw [← hagree' condReg (Nat.le_max_left _ _)]; exact hcond
      have hagree_body : ∀ r, r ≤ body.maxRegister → a₀ r = a' r := fun r hr =>
        hagree' r (Nat.le_trans hr (Nat.le_max_right _ _))
      have hdom_a₀ : (evalFlat body a₀).Dom := Part.dom_iff_mem.mpr ⟨a₁, hσ_mem⟩
      have hdom_a' : (evalFlat body a').Dom := (evalFlat_dom_agree hagree_body).mp hdom_a₀
      let a'₁ := (evalFlat body a').get hdom_a'
      have hagree_result : ∀ r, r ≤ max condReg body.maxRegister → a₁ r = a'₁ r := by
        intro r hr
        have ha₁_eq : a₁ = (evalFlat body a₀).get hdom_a₀ :=
          (Part.get_eq_of_mem hσ_mem hdom_a₀).symm
        by_cases hr_body : r ≤ body.maxRegister
        · rw [ha₁_eq]
          exact evalFlat_result_agree hagree_body hdom_a₀ hdom_a' r hr_body
        · have hr_gt : body.maxRegister < r := Nat.lt_of_not_le hr_body
          rw [ha₁_eq]
          rw [evalFlat_preserves_above_maxRegister hdom_a₀ r hr_gt]
          have ha'₁_eq : a'₁ = (evalFlat body a').get hdom_a' := rfl
          rw [ha'₁_eq, evalFlat_preserves_above_maxRegister hdom_a' r hr_gt]
          exact hagree' r hr
      have hdom_recurse : (PFun.fix (whileStep condReg body) a'₁).Dom := ih a'₁ hagree_result
      have hcont' : Sum.inr a'₁ ∈ whileStep condReg body a' := by
        simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_map_iff]
        exact ⟨a'₁, Part.get_mem hdom_a', rfl⟩
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hdom_recurse
      exact Part.dom_iff_mem.mpr ⟨y, PFun.mem_fix_iff.mpr (Or.inr ⟨a'₁, hcont', hy⟩)⟩

/-- Domain equivalence: runWhile terminates iff runWhile from agreeing state terminates. -/
theorem runWhile_dom_agree' {condReg : ℕ} {body : FlatProgram} {s s' : State}
    (hagree : ∀ r, r ≤ max condReg body.maxRegister → s r = s' r) :
    (runWhile s condReg body).Dom ↔ (runWhile s' condReg body).Dom := by
  constructor
  · intro hdom
    obtain ⟨x, hmem⟩ := Part.dom_iff_mem.mp hdom
    exact runWhile_dom_of_mem_agree hmem hagree
  · intro hdom'
    obtain ⟨x', hmem'⟩ := Part.dom_iff_mem.mp hdom'
    have hagree_sym : ∀ r, r ≤ max condReg body.maxRegister → s' r = s r :=
      fun r hr => (hagree r hr).symm
    exact runWhile_dom_of_mem_agree hmem' hagree_sym

/-- If `x ∈ runWhile s condReg body` and `x' ∈ runWhile s' condReg body` where s and s'
    agree on relevant registers, then x and x' agree on relevant registers. -/
theorem runWhile_result_of_mem_agree {condReg : ℕ} {body : FlatProgram}
    {s s' x x' : State}
    (hmem : x ∈ runWhile s condReg body)
    (hmem' : x' ∈ runWhile s' condReg body)
    (hagree : ∀ r, r ≤ max condReg body.maxRegister → s r = s' r) :
    ∀ r, r ≤ max condReg body.maxRegister → x r = x' r := by
  simp only [runWhile] at hmem hmem'
  refine PFun.fixInduction' hmem
    (fun a_final hstop a' hagree' x' hmem'_inner r hr => ?_)
    (fun a₀ a₁ hmem_a₁ hcont ih a' hagree' x' hmem'_inner r hr => ?_)
    s' hagree x' hmem'
  · simp only [whileStep] at hstop
    split_ifs at hstop with hcond
    · have ha'_cond : a' condReg = 0 := by
        rw [← hagree' condReg (Nat.le_max_left _ _), hcond]
      have hx_eq : x = a_final := by
        have hinj := Part.mem_some_iff.mp hstop
        exact Sum.inl.inj hinj
      have hstop' : Sum.inl a' ∈ whileStep condReg body a' := by
        simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_some_iff]
      have hx'_eq : x' = a' := by
        rw [PFun.mem_fix_iff] at hmem'_inner
        cases hmem'_inner with
        | inl h =>
          simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_some_iff] at h
          exact Sum.inl.inj h
        | inr h =>
          obtain ⟨a'', hcont', _⟩ := h
          simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_some_iff] at hcont'
          exact absurd hcont' (by simp)
      rw [hx_eq, hx'_eq]
      exact hagree' r hr
    · simp only [Part.mem_map_iff] at hstop
      obtain ⟨_, _, h⟩ := hstop
      exact absurd h (by simp)
  · simp only [whileStep] at hcont
    split_ifs at hcont with hcond
    · simp only [Part.mem_some_iff] at hcont
      exact absurd hcont (by simp)
    · simp only [Part.mem_map_iff] at hcont
      obtain ⟨σ, hσ_mem, hσ_eq⟩ := hcont
      cases hσ_eq
      have ha'_cond : a' condReg ≠ 0 := by
        rw [← hagree' condReg (Nat.le_max_left _ _)]; exact hcond
      have hagree_body : ∀ r, r ≤ body.maxRegister → a₀ r = a' r := fun r hr' =>
        hagree' r (Nat.le_trans hr' (Nat.le_max_right _ _))
      have hdom_a₀ : (evalFlat body a₀).Dom := Part.dom_iff_mem.mpr ⟨a₁, hσ_mem⟩
      have hdom_a' : (evalFlat body a').Dom := (evalFlat_dom_agree hagree_body).mp hdom_a₀
      let a'₁ := (evalFlat body a').get hdom_a'
      have hagree_result : ∀ r, r ≤ max condReg body.maxRegister → a₁ r = a'₁ r := by
        intro r' hr'
        have ha₁_eq : a₁ = (evalFlat body a₀).get hdom_a₀ :=
          (Part.get_eq_of_mem hσ_mem hdom_a₀).symm
        by_cases hr_body : r' ≤ body.maxRegister
        · rw [ha₁_eq]
          exact evalFlat_result_agree hagree_body hdom_a₀ hdom_a' r' hr_body
        · have hr_gt : body.maxRegister < r' := Nat.lt_of_not_le hr_body
          rw [ha₁_eq]
          rw [evalFlat_preserves_above_maxRegister hdom_a₀ r' hr_gt]
          have ha'₁_eq : a'₁ = (evalFlat body a').get hdom_a' := rfl
          rw [ha'₁_eq, evalFlat_preserves_above_maxRegister hdom_a' r' hr_gt]
          exact hagree' r' hr'
      rw [PFun.mem_fix_iff] at hmem'_inner
      cases hmem'_inner with
      | inl h =>
        simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_map_iff] at h
        obtain ⟨_, _, h'⟩ := h
        exact absurd h' (by simp)
      | inr h =>
        obtain ⟨a'', hcont', hmem''⟩ := h
        simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_map_iff] at hcont'
        obtain ⟨σ', hσ'_mem, hσ'_eq⟩ := hcont'
        have hσ'_eq_a'' : σ' = a'' := Sum.inr.inj hσ'_eq
        have ha''_eq : a'' = a'₁ := by
          rw [← hσ'_eq_a'']
          exact (Part.get_eq_of_mem hσ'_mem hdom_a').symm
        subst ha''_eq
        exact ih a'₁ hagree_result x' hmem'' r hr

/-- Helper: For any x ∈ runWhile s condReg body, x r = s r when r > max condReg maxRegister. -/
private theorem runWhile_preserves_above_aux {condReg : ℕ} {body : FlatProgram}
    {s x : State} (hmem : x ∈ runWhile s condReg body)
    (r : ℕ) (hr : max condReg body.maxRegister < r) : x r = s r := by
  simp only [runWhile] at hmem
  refine PFun.fixInduction' hmem
    (fun s_final hstop => ?_)
    (fun s₀ s₁ _ hcont ih => ?_)
  · simp only [whileStep] at hstop
    split_ifs at hstop with hcond
    · have hx_eq := Sum.inl.inj (Part.mem_some_iff.mp hstop)
      rw [hx_eq]
    · simp only [Part.mem_map_iff] at hstop
      obtain ⟨_, _, h⟩ := hstop
      exact absurd h (by simp)
  · simp only [whileStep] at hcont
    split_ifs at hcont with hcond
    · simp only [Part.mem_some_iff] at hcont
      exact absurd hcont (by simp)
    · simp only [Part.mem_map_iff] at hcont
      obtain ⟨σ, hσ_mem, hσ_eq⟩ := hcont
      cases hσ_eq
      have hdom_body : (evalFlat body s₀).Dom := Part.dom_iff_mem.mpr ⟨s₁, hσ_mem⟩
      have hs₁_eq : s₁ = (evalFlat body s₀).get hdom_body :=
        (Part.get_eq_of_mem hσ_mem hdom_body).symm
      have hpres : s₁ r = s₀ r := by
        rw [hs₁_eq]
        exact evalFlat_preserves_above_maxRegister hdom_body r (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hr)
      rw [ih, hpres]

/-- runWhile preserves registers above max condReg body.maxRegister. -/
theorem runWhile_preserves_above (condReg : ℕ) (body : FlatProgram) (s : State)
    (hdom : (runWhile s condReg body).Dom) (r : ℕ) (hr : max condReg body.maxRegister < r) :
    (runWhile s condReg body).get hdom r = s r :=
  runWhile_preserves_above_aux (Part.get_mem hdom) r hr

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
    simp only [evalInstr]
    apply runWhile_dom_agree'
    intro r hr
    apply h_agree
    simp only [ExtendedInstr.maxRegisterUsed] at h_bound
    omega

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
    simp only [evalInstr] at hdom hdom' ⊢
    by_cases hr_le : r ≤ max condReg body.maxRegister
    · -- r ≤ max condReg body.maxRegister: use runWhile_result_of_mem_agree
      have hmem := Part.get_mem hdom
      have hmem' := Part.get_mem hdom'
      have hagree : ∀ r', r' ≤ max condReg body.maxRegister → s r' = s' r' := by
        intro r' hr'
        apply h_agree
        simp only [ExtendedInstr.maxRegisterUsed] at h_bound
        omega
      exact runWhile_result_of_mem_agree hmem hmem' hagree r hr_le
    · -- r > max condReg body.maxRegister: both preserve original value
      have hr_gt : max condReg body.maxRegister < r := Nat.lt_of_not_le hr_le
      rw [runWhile_preserves_above condReg body s hdom r hr_gt]
      rw [runWhile_preserves_above condReg body s' hdom' r hr_gt]
      exact h_agree r hr

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
