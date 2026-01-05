/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable
import Urm.Execution

/-! # Arithmetic Operations for URMs

This file proves that basic arithmetic operations are URM-computable,
starting with addition.

## Main results

- `Urm.add_computable`: Addition is URM-computable

## The Addition Program

The program computes `x + y` where `x` is in R0 and `y` is in R1:

```
[Z 2,           -- 0: Clear counter R2
 J 2 1 5,       -- 1: If R2 = R1, exit
 S 0,           -- 2: Increment result R0
 S 2,           -- 3: Increment counter R2
 J 0 0 1]       -- 4: Unconditional jump back
```

The loop invariant at instruction 1 is: R0 = x + R2 ∧ R2 ≤ y

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-- URM program that computes addition: R0 := R0 + R1

Uses R2 as a counter that increments from 0 to R1,
incrementing R0 each iteration. -/
def addProgram : Program := [
  Instr.Z 2,      -- 0: Clear counter R2
  Instr.J 2 1 5,  -- 1: If R2 = R1, jump to exit (instruction 5)
  Instr.S 0,      -- 2: Increment result R0
  Instr.S 2,      -- 3: Increment counter R2
  Instr.J 0 0 1   -- 4: Unconditional jump back to check
]

namespace addProgram

-- Helper lemmas about getInstr
@[simp] theorem getInstr_0 : addProgram.getInstr 0 = some (Instr.Z 2) := rfl
@[simp] theorem getInstr_1 : addProgram.getInstr 1 = some (Instr.J 2 1 5) := rfl
@[simp] theorem getInstr_2 : addProgram.getInstr 2 = some (Instr.S 0) := rfl
@[simp] theorem getInstr_3 : addProgram.getInstr 3 = some (Instr.S 2) := rfl
@[simp] theorem getInstr_4 : addProgram.getInstr 4 = some (Instr.J 0 0 1) := rfl
@[simp] theorem length_eq : addProgram.length = 5 := rfl

/-- The initial instruction (Z 2) takes us from pc=0 to pc=1 with R2=0. -/
theorem step_init (s : State) :
    Step addProgram ⟨0, s⟩ ⟨1, s.write 2 0⟩ :=
  Step.zero getInstr_0

/-- When counter equals y (R2 = R1), we exit the loop by jumping to pc=5. -/
theorem step_exit (s : State) (heq : s.read 2 = s.read 1) :
    Step addProgram ⟨1, s⟩ ⟨5, s⟩ :=
  Step.jump_eq getInstr_1 heq

/-- When counter < y (R2 ≠ R1), we continue to the increment instructions. -/
theorem step_continue (s : State) (hne : s.read 2 ≠ s.read 1) :
    Step addProgram ⟨1, s⟩ ⟨2, s⟩ :=
  Step.jump_ne getInstr_1 hne

/-- Increment R0 at instruction 2. -/
theorem step_inc_r0 (s : State) :
    Step addProgram ⟨2, s⟩ ⟨3, s.write 0 (s.read 0 + 1)⟩ :=
  Step.succ getInstr_2

/-- Increment R2 at instruction 3. -/
theorem step_inc_r2 (s : State) :
    Step addProgram ⟨3, s⟩ ⟨4, s.write 2 (s.read 2 + 1)⟩ :=
  Step.succ getInstr_3

/-- Unconditional jump back at instruction 4 (J 0 0 1 always jumps since R0 = R0). -/
theorem step_jump_back (s : State) :
    Step addProgram ⟨4, s⟩ ⟨1, s⟩ :=
  Step.jump_eq getInstr_4 rfl

/-- One complete loop iteration: from pc=1 with k < y, to pc=1 with k+1.
    Precondition: s.read 2 = k, s.read 1 = y, k < y
    Postcondition: s'.read 2 = k+1, s'.read 0 = s.read 0 + 1, s'.read 1 = y -/
theorem loop_iteration (s : State) (k y : ℕ)
    (hk : s.read 2 = k) (hy : s.read 1 = y) (hlt : k < y) :
    ∃ s', Steps addProgram ⟨1, s⟩ ⟨1, s'⟩ ∧
          s'.read 0 = s.read 0 + 1 ∧
          s'.read 1 = y ∧
          s'.read 2 = k + 1 := by
  -- k < y implies k ≠ y
  have hne : s.read 2 ≠ s.read 1 := by omega
  -- Step 1→2: continue (since R2 ≠ R1)
  have h1 : Step addProgram ⟨1, s⟩ ⟨2, s⟩ := step_continue s hne
  -- Step 2→3: increment R0
  let s1 := s.write 0 (s.read 0 + 1)
  have h2 : Step addProgram ⟨2, s⟩ ⟨3, s1⟩ := step_inc_r0 s
  -- Step 3→4: increment R2
  let s2 := s1.write 2 (s1.read 2 + 1)
  have h3 : Step addProgram ⟨3, s1⟩ ⟨4, s2⟩ := step_inc_r2 s1
  -- Step 4→1: jump back
  have h4 : Step addProgram ⟨4, s2⟩ ⟨1, s2⟩ := step_jump_back s2
  -- Compose all steps
  use s2
  constructor
  · exact Steps.trans (Steps.trans (Steps.trans (Steps.single h1) (Steps.single h2))
                      (Steps.single h3)) (Steps.single h4)
  · constructor
    · -- s2.read 0 = s.read 0 + 1
      simp only [s2, s1, State.write, State.read, Function.update_of_ne (by decide : (0 : ℕ) ≠ 2),
                 Function.update_self]
    constructor
    · -- s2.read 1 = y
      simp only [s2, s1, State.write, State.read,
                 Function.update_of_ne (by decide : (1 : ℕ) ≠ 2),
                 Function.update_of_ne (by decide : (1 : ℕ) ≠ 0)]
      exact hy
    · -- s2.read 2 = k + 1
      -- s2.read 2 = s1.read 2 + 1 by definition of s2
      -- s1.read 2 = s.read 2 since s1 only wrote to register 0
      -- s.read 2 = k by hk
      simp only [s2, State.read, State.write, Function.update_self]
      simp only [s1, State.read, State.write, Function.update_of_ne (by decide : (2 : ℕ) ≠ 0)]
      -- Now goal is s 2 + 1 = k + 1, and hk : s.read 2 = k means s 2 = k
      simp only [State.read] at hk
      omega

/-- After k iterations starting from the loop entry, we have the loop invariant.
    Starting state: pc=1, R0=x, R1=y, R2=0
    After k iterations: pc=1, R0=x+k, R1=y, R2=k -/
theorem loop_invariant (x y k : ℕ) (hk : k ≤ y) :
    ∃ s, Steps addProgram ⟨1, (State.fromInputs [x, y]).write 2 0⟩ ⟨1, s⟩ ∧
         s.read 0 = x + k ∧
         s.read 1 = y ∧
         s.read 2 = k := by
  induction k with
  | zero =>
    -- Base case: 0 iterations, state unchanged
    use (State.fromInputs [x, y]).write 2 0
    refine ⟨Steps.refl _, ?_, ?_, ?_⟩
    · simp [State.write, State.read, State.fromInputs, Function.update_of_ne]
    · simp [State.write, State.read, State.fromInputs, Function.update_of_ne]
    · simp [State.write, State.read, Function.update_self]
  | succ k' ih =>
    -- Inductive case: use k' iterations, then one more
    have hk' : k' ≤ y := Nat.le_of_succ_le hk
    obtain ⟨s', hsteps', hr0', hr1', hr2'⟩ := ih hk'
    -- If k' < y, we can do one more iteration
    have hlt : k' < y := Nat.lt_of_succ_le hk
    obtain ⟨s'', hiter, hr0'', hr1'', hr2''⟩ := loop_iteration s' k' y hr2' hr1' hlt
    use s''
    refine ⟨Steps.trans hsteps' hiter, ?_, hr1'', hr2''⟩
    omega

/-- The program halts after completing y iterations.
    Starting from pc=1 with R2=y and R1=y, we exit to pc=5. -/
theorem exits_when_done (s : State) (h : s.read 2 = s.read 1) :
    Steps addProgram ⟨1, s⟩ ⟨5, s⟩ :=
  Steps.single (step_exit s h)

/-- Configuration at pc=5 is halted. -/
theorem halted_at_5 (s : State) : (⟨5, s⟩ : Config).isHalted addProgram := by
  simp [Config.isHalted, length_eq]

/-- The full execution from initial state to halted state. -/
theorem full_execution (x y : ℕ) :
    ∃ s, Steps addProgram (Config.init [x, y]) ⟨5, s⟩ ∧
         s.read 0 = x + y ∧
         (⟨5, s⟩ : Config).isHalted addProgram := by
  -- Step 0: Initialize (pc=0 → pc=1, R2 := 0)
  let s0 := State.fromInputs [x, y]
  have h_init : Step addProgram ⟨0, s0⟩ ⟨1, s0.write 2 0⟩ := step_init s0
  -- Get state after y iterations
  obtain ⟨s_final, hsteps_loop, hr0, hr1, hr2⟩ := loop_invariant x y y (Nat.le_refl y)
  -- Exit condition: R2 = R1 = y
  have heq : s_final.read 2 = s_final.read 1 := by omega
  have h_exit := exits_when_done s_final heq
  -- Compose: init step + loop steps + exit step
  use s_final
  refine ⟨?_, ?_, halted_at_5 s_final⟩
  · exact Steps.trans (Steps.single h_init) (Steps.trans hsteps_loop h_exit)
  · exact hr0

end addProgram

/-- Addition is URM-computable.

The program uses a counter to increment R0 (initially x) by 1 for each
of y iterations, resulting in x + y in R0. -/
theorem add_computable : URMComputable 2 (fun xy => Part.some (xy 0 + xy 1)) := by
  use addProgram
  intro inputs
  -- Convert Fin 2 → ℕ to concrete values
  let x := inputs 0
  let y := inputs 1
  have h_ofFn : List.ofFn inputs = [x, y] := by
    simp only [List.ofFn]; rfl
  constructor
  · -- Halting equivalence: always halts ↔ Part.some is defined (always true)
    simp only [Part.some_dom, iff_true]
    rw [h_ofFn]
    obtain ⟨s, hsteps, _, hhalted⟩ := addProgram.full_execution x y
    exact ⟨⟨5, s⟩, hsteps, hhalted⟩
  · -- Result equality: Result = x + y
    intro hHalts hDom
    -- Get the halted config and its properties
    obtain ⟨s, hsteps, hr0, hhalted⟩ := addProgram.full_execution x y
    -- Convert steps to use List.ofFn
    have hsteps' : Steps addProgram (Config.init (List.ofFn inputs)) ⟨5, s⟩ := by
      simp only [h_ofFn]; exact hsteps
    -- The chosen halted config must equal our computed one (by uniqueness)
    obtain ⟨hsteps_chosen, hhalted_chosen⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps_chosen hhalted_chosen hsteps' hhalted
    simp only [Result, heq, State.output, Part.get_some]
    -- hr0 : s.read 0 = x + y, and x = inputs 0, y = inputs 1
    exact hr0

end Urm
