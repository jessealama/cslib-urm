/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable
import Urm.Execution
import Urm.PrimitiveRecursion.Basic
import Urm.Composition.Basic
import Mathlib.Tactic.FinCases

/-! # Arithmetic Operations for URMs

This file proves that basic arithmetic operations are URM-computable,
starting with addition.

## Main results

- `Urm.add_computable`: Addition is URM-computable
- `Urm.pred_computable`: Predecessor is URM-computable

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

/-! ## The Predecessor Program

The program computes `pred(n)` where `n` is in R0:

```
[Z 1,       -- 0: Clear R1 (for zero check)
 J 0 1 9,   -- 1: If R0 = 0, jump to halt (result is already 0)
 Z 2,       -- 2: Clear R2 (result counter)
 S 1,       -- 3: R1 := 1 (upper counter)
 J 0 1 8,   -- 4: If R0 = R1, jump to copy result
 S 2,       -- 5: Increment R2
 S 1,       -- 6: Increment R1
 J 0 0 4,   -- 7: Unconditional jump back to check
 T 2 0]     -- 8: Copy R2 to R0
```

The loop invariant at instruction 4 is: R0 = n ∧ R1 = k + 1 ∧ R2 = k for k ∈ [0, n)
-/

/-- URM program that computes predecessor: R0 := pred(R0)

For n = 0: exits immediately (R0 already contains 0 = pred(0))
For n > 0: counts R1 from 1 until R1 = n, with R2 = R1 - 1, then copies R2 to R0. -/
def predProgram : Program := [
  Instr.Z 1,      -- 0: Clear R1 (for zero check)
  Instr.J 0 1 9,  -- 1: If R0 = 0, jump to halt (result is already 0)
  Instr.Z 2,      -- 2: Clear R2 (result counter)
  Instr.S 1,      -- 3: R1 := 1 (upper counter)
  Instr.J 0 1 8,  -- 4: If R0 = R1, jump to copy result
  Instr.S 2,      -- 5: Increment R2
  Instr.S 1,      -- 6: Increment R1
  Instr.J 0 0 4,  -- 7: Unconditional jump back to check
  Instr.T 2 0     -- 8: Copy R2 to R0
]

namespace predProgram

-- Helper lemmas about getInstr
@[simp] theorem getInstr_0 : predProgram.getInstr 0 = some (Instr.Z 1) := rfl
@[simp] theorem getInstr_1 : predProgram.getInstr 1 = some (Instr.J 0 1 9) := rfl
@[simp] theorem getInstr_2 : predProgram.getInstr 2 = some (Instr.Z 2) := rfl
@[simp] theorem getInstr_3 : predProgram.getInstr 3 = some (Instr.S 1) := rfl
@[simp] theorem getInstr_4 : predProgram.getInstr 4 = some (Instr.J 0 1 8) := rfl
@[simp] theorem getInstr_5 : predProgram.getInstr 5 = some (Instr.S 2) := rfl
@[simp] theorem getInstr_6 : predProgram.getInstr 6 = some (Instr.S 1) := rfl
@[simp] theorem getInstr_7 : predProgram.getInstr 7 = some (Instr.J 0 0 4) := rfl
@[simp] theorem getInstr_8 : predProgram.getInstr 8 = some (Instr.T 2 0) := rfl
@[simp] theorem length_eq : predProgram.length = 9 := rfl

/-- Clear R1 for zero check (pc 0 → 1). -/
theorem step_clear_r1 (s : State) :
    Step predProgram ⟨0, s⟩ ⟨1, s.write 1 0⟩ :=
  Step.zero getInstr_0

/-- When R0 = 0 (= R1 after clear), jump to halt (pc 1 → 9). -/
theorem step_zero_exit (s : State) (heq : s.read 0 = s.read 1) :
    Step predProgram ⟨1, s⟩ ⟨9, s⟩ :=
  Step.jump_eq getInstr_1 heq

/-- When R0 ≠ 0, continue to main loop setup (pc 1 → 2). -/
theorem step_nonzero_continue (s : State) (hne : s.read 0 ≠ s.read 1) :
    Step predProgram ⟨1, s⟩ ⟨2, s⟩ :=
  Step.jump_ne getInstr_1 hne

/-- Clear R2 for result tracking (pc 2 → 3). -/
theorem step_clear_r2 (s : State) :
    Step predProgram ⟨2, s⟩ ⟨3, s.write 2 0⟩ :=
  Step.zero getInstr_2

/-- Initialize R1 to 1 (pc 3 → 4). -/
theorem step_init_r1 (s : State) :
    Step predProgram ⟨3, s⟩ ⟨4, s.write 1 (s.read 1 + 1)⟩ :=
  Step.succ getInstr_3

/-- When R0 = R1, jump to copy result (pc 4 → 8). -/
theorem step_found_pred (s : State) (heq : s.read 0 = s.read 1) :
    Step predProgram ⟨4, s⟩ ⟨8, s⟩ :=
  Step.jump_eq getInstr_4 heq

/-- When R0 ≠ R1, continue loop (pc 4 → 5). -/
theorem step_continue_loop (s : State) (hne : s.read 0 ≠ s.read 1) :
    Step predProgram ⟨4, s⟩ ⟨5, s⟩ :=
  Step.jump_ne getInstr_4 hne

/-- Increment R2 (pc 5 → 6). -/
theorem step_inc_r2 (s : State) :
    Step predProgram ⟨5, s⟩ ⟨6, s.write 2 (s.read 2 + 1)⟩ :=
  Step.succ getInstr_5

/-- Increment R1 (pc 6 → 7). -/
theorem step_inc_r1 (s : State) :
    Step predProgram ⟨6, s⟩ ⟨7, s.write 1 (s.read 1 + 1)⟩ :=
  Step.succ getInstr_6

/-- Unconditional jump back to loop check (pc 7 → 4). -/
theorem step_jump_back (s : State) :
    Step predProgram ⟨7, s⟩ ⟨4, s⟩ :=
  Step.jump_eq getInstr_7 rfl

/-- Copy R2 to R0 (pc 8 → 9). -/
theorem step_copy_result (s : State) :
    Step predProgram ⟨8, s⟩ ⟨9, s.write 0 (s.read 2)⟩ :=
  Step.trans getInstr_8

/-- Configuration at pc=9 is halted. -/
theorem halted_at_9 (s : State) : (⟨9, s⟩ : Config).isHalted predProgram := by
  simp [Config.isHalted, length_eq]

/-- Full execution for n = 0: immediately exits with R0 = 0. -/
theorem zero_execution :
    ∃ s, Steps predProgram (Config.init [0]) ⟨9, s⟩ ∧
         s.read 0 = 0 ∧
         (⟨9, s⟩ : Config).isHalted predProgram := by
  -- Initial state: R0 = 0, R1 = 0 (fromInputs gives 0 for out-of-range)
  let s0 := State.fromInputs [0]
  have hs0_r0 : s0 0 = 0 := rfl
  have hs0_r1 : s0 1 = 0 := rfl
  -- pc=0: Z 1 -> pc=1, R1=0
  let s1 := s0.write 1 0
  have h1 : Step predProgram ⟨0, s0⟩ ⟨1, s1⟩ := step_clear_r1 s0
  -- pc=1: J 0 1 9 -> R0=0, R1=0, equal! Jump to pc=9
  have hs1_r0 : s1.read 0 = 0 := by
    simp only [s1, State.read, State.write, Function.update_of_ne (by decide : (0 : ℕ) ≠ 1)]
    exact hs0_r0
  have hs1_r1 : s1.read 1 = 0 := by
    simp only [s1, State.read, State.write, Function.update_self]
  have heq : s1.read 0 = s1.read 1 := by rw [hs1_r0, hs1_r1]
  have h2 : Step predProgram ⟨1, s1⟩ ⟨9, s1⟩ := step_zero_exit s1 heq
  -- Compose steps
  use s1
  refine ⟨Steps.trans (Steps.single h1) (Steps.single h2), hs1_r0, halted_at_9 s1⟩

/-- One loop iteration: from pc=4 with R1 = k + 1 < n, to pc=4 with R1 = k + 2.
    Invariant: R0 = n, R1 = k + 1, R2 = k -/
theorem loop_iteration (s : State) (n k : ℕ)
    (hn : s.read 0 = n) (hr1 : s.read 1 = k + 1) (hr2 : s.read 2 = k)
    (hlt : k + 1 < n) :
    ∃ s', Steps predProgram ⟨4, s⟩ ⟨4, s'⟩ ∧
          s'.read 0 = n ∧
          s'.read 1 = k + 2 ∧
          s'.read 2 = k + 1 := by
  -- k + 1 < n implies R0 ≠ R1
  have hne : s.read 0 ≠ s.read 1 := by omega
  -- pc=4 → pc=5: continue loop (R0 ≠ R1)
  have h1 : Step predProgram ⟨4, s⟩ ⟨5, s⟩ := step_continue_loop s hne
  -- pc=5 → pc=6: increment R2
  let s1 := s.write 2 (s.read 2 + 1)
  have h2 : Step predProgram ⟨5, s⟩ ⟨6, s1⟩ := step_inc_r2 s
  -- pc=6 → pc=7: increment R1
  let s2 := s1.write 1 (s1.read 1 + 1)
  have h3 : Step predProgram ⟨6, s1⟩ ⟨7, s2⟩ := step_inc_r1 s1
  -- pc=7 → pc=4: jump back
  have h4 : Step predProgram ⟨7, s2⟩ ⟨4, s2⟩ := step_jump_back s2
  -- Compose all steps
  use s2
  constructor
  · exact Steps.trans (Steps.trans (Steps.trans (Steps.single h1) (Steps.single h2))
                      (Steps.single h3)) (Steps.single h4)
  constructor
  · -- s2.read 0 = n (unchanged)
    simp only [s2, s1, State.read, State.write,
               Function.update_of_ne (by decide : (0 : ℕ) ≠ 1),
               Function.update_of_ne (by decide : (0 : ℕ) ≠ 2)]
    exact hn
  constructor
  · -- s2.read 1 = k + 2
    simp only [s2, State.read, State.write, Function.update_self]
    simp only [s1, State.read, State.write, Function.update_of_ne (by decide : (1 : ℕ) ≠ 2)]
    simp only [State.read] at hr1
    omega
  · -- s2.read 2 = k + 1
    simp only [s2, State.read, State.write, Function.update_of_ne (by decide : (2 : ℕ) ≠ 1)]
    simp only [s1, State.read, State.write, Function.update_self]
    simp only [State.read] at hr2
    omega

/-- After k iterations, R1 = k + 1 and R2 = k.
    Starting state: pc=4, R0=n (n > 0), R1=1, R2=0 -/
theorem loop_invariant (n k : ℕ) (hk : k < n) :
    ∃ s, Steps predProgram ⟨4, (State.fromInputs [n]).write 1 0 |>.write 2 0 |>.write 1 1⟩ ⟨4, s⟩ ∧
         s.read 0 = n ∧
         s.read 1 = k + 1 ∧
         s.read 2 = k := by
  induction k with
  | zero =>
    -- Base: 0 iterations, just use initial state
    let s_init := (State.fromInputs [n]).write 1 0 |>.write 2 0 |>.write 1 1
    use s_init
    refine ⟨Steps.refl _, ?_, ?_, ?_⟩
    · -- s_init.read 0 = n
      simp only [s_init, State.read, State.write, State.fromInputs,
                 Function.update_of_ne (by decide : (0 : ℕ) ≠ 1),
                 Function.update_of_ne (by decide : (0 : ℕ) ≠ 2),
                 List.getD_cons_zero]
    · -- s_init.read 1 = 1
      simp only [s_init, State.read, State.write, Function.update_self]
    · -- s_init.read 2 = 0
      simp only [s_init, State.read, State.write,
                 Function.update_of_ne (by decide : (2 : ℕ) ≠ 1),
                 Function.update_self]
  | succ k' ih =>
    -- Inductive case: use k' iterations, then one more
    have hk' : k' < n := Nat.lt_of_succ_lt hk
    obtain ⟨s', hsteps', hr0', hr1', hr2'⟩ := ih (hk')
    -- k' + 1 < n (since k' + 1 = succ k' ≤ k < n by hk)
    have hlt : k' + 1 < n := hk
    obtain ⟨s'', hiter, hr0'', hr1'', hr2''⟩ := loop_iteration s' n k' hr0' hr1' hr2' hlt
    use s''
    refine ⟨Steps.trans hsteps' hiter, hr0'', hr1'', hr2''⟩

/-- When R0 = R1 at pc=4, we exit to pc=8 and copy R2 to R0, then halt at pc=9. -/
theorem loop_exit (s : State) (n : ℕ)
    (hr0 : s.read 0 = n) (hr1 : s.read 1 = n) (hr2 : s.read 2 = n - 1) :
    ∃ s', Steps predProgram ⟨4, s⟩ ⟨9, s'⟩ ∧
          s'.read 0 = n - 1 ∧
          (⟨9, s'⟩ : Config).isHalted predProgram := by
  -- pc=4: J 0 1 8 -> R0 = R1 = n, jump to pc=8
  have heq : s.read 0 = s.read 1 := by rw [hr0, hr1]
  have h1 : Step predProgram ⟨4, s⟩ ⟨8, s⟩ := step_found_pred s heq
  -- pc=8: T 2 0 -> R0 := R2 = n - 1, pc=9 (halted)
  let s' := s.write 0 (s.read 2)
  have h2 : Step predProgram ⟨8, s⟩ ⟨9, s'⟩ := step_copy_result s
  -- Compose steps
  use s'
  refine ⟨Steps.trans (Steps.single h1) (Steps.single h2), ?_, halted_at_9 s'⟩
  -- s'.read 0 = n - 1
  simp only [s', State.read, State.write, Function.update_self]
  simp only [State.read] at hr2
  exact hr2

/-- Full execution for n > 0. -/
theorem nonzero_execution (n : ℕ) (hn : 0 < n) :
    ∃ s, Steps predProgram (Config.init [n]) ⟨9, s⟩ ∧
         s.read 0 = n - 1 ∧
         (⟨9, s⟩ : Config).isHalted predProgram := by
  -- Phase 1: Setup (pc 0-3)
  let s0 := State.fromInputs [n]
  have hs0_r0 : s0 0 = n := rfl
  have hs0_r1 : s0 1 = 0 := rfl

  -- pc=0: Z 1 -> R1 := 0, pc=1
  let s1 := s0.write 1 0
  have h_step0 : Step predProgram ⟨0, s0⟩ ⟨1, s1⟩ := step_clear_r1 s0

  -- pc=1: J 0 1 9 -> R0 = n ≠ 0 = R1, continue to pc=2
  have hs1_r0 : s1.read 0 = n := by
    simp only [s1, State.read, State.write, Function.update_of_ne (by decide : (0 : ℕ) ≠ 1)]
    exact hs0_r0
  have hs1_r1 : s1.read 1 = 0 := by
    simp only [s1, State.read, State.write, Function.update_self]
  have hne1 : s1.read 0 ≠ s1.read 1 := by rw [hs1_r0, hs1_r1]; omega
  have h_step1 : Step predProgram ⟨1, s1⟩ ⟨2, s1⟩ := step_nonzero_continue s1 hne1

  -- pc=2: Z 2 -> R2 := 0, pc=3
  let s2 := s1.write 2 0
  have h_step2 : Step predProgram ⟨2, s1⟩ ⟨3, s2⟩ := step_clear_r2 s1

  -- pc=3: S 1 -> R1 := 1, pc=4
  let s3 := s2.write 1 (s2.read 1 + 1)
  have h_step3 : Step predProgram ⟨3, s2⟩ ⟨4, s3⟩ := step_init_r1 s2

  -- Verify s3 = the state expected by loop_invariant
  have hs3_eq : s3 = ((((State.fromInputs [n]).write 1 0).write 2 0).write 1 1) := by
    simp only [s3, s2, s1, State.write, State.read]
    ext i
    simp only [Function.update]
    split_ifs <;> first | rfl | omega

  -- Compose setup steps: pc 0 -> 1 -> 2 -> 3 -> 4
  have h_setup : Steps predProgram ⟨0, s0⟩ ⟨4, s3⟩ :=
    Steps.trans (Steps.single h_step0)
      (Steps.trans (Steps.single h_step1)
        (Steps.trans (Steps.single h_step2) (Steps.single h_step3)))

  -- Phase 2: Loop iterations
  -- We need n - 1 iterations to get R1 = n, R2 = n - 1
  have hk : n - 1 < n := Nat.sub_lt hn Nat.one_pos
  obtain ⟨s_loop, h_loop_steps, hr0_loop, hr1_loop, hr2_loop⟩ := loop_invariant n (n - 1) hk

  -- Convert loop steps to use s3
  have h_loop_steps' : Steps predProgram ⟨4, s3⟩ ⟨4, s_loop⟩ := by
    rw [hs3_eq]; exact h_loop_steps

  -- Phase 3: Exit
  -- At this point: R0 = n, R1 = (n-1) + 1 = n, R2 = n - 1
  have hr1_eq_n : s_loop.read 1 = n := by omega
  obtain ⟨s_final, h_exit_steps, hr0_final, h_halted_final⟩ :=
    loop_exit s_loop n hr0_loop hr1_eq_n hr2_loop

  -- Compose all phases: setup + loop + exit
  use s_final
  refine ⟨?_, hr0_final, h_halted_final⟩
  exact Steps.trans h_setup (Steps.trans h_loop_steps' h_exit_steps)

end predProgram

/-- Predecessor is URM-computable.
    pred(0) = 0, pred(n+1) = n (using truncated subtraction). -/
theorem pred_computable : URMComputable 1 (fun x => Part.some (x 0 - 1)) := by
  use predProgram
  intro inputs
  let n := inputs 0
  have h_ofFn : List.ofFn inputs = [n] := by simp only [List.ofFn]; rfl
  constructor
  · -- Halting equivalence: always halts
    simp only [Part.some_dom, iff_true]
    cases Nat.eq_zero_or_pos n with
    | inl hz =>
      -- n = 0: use zero_execution
      rw [h_ofFn, hz]
      obtain ⟨s, hsteps, _, hhalted⟩ := predProgram.zero_execution
      exact ⟨⟨9, s⟩, hsteps, hhalted⟩
    | inr hpos =>
      -- n > 0: use nonzero_execution
      rw [h_ofFn]
      obtain ⟨s, hsteps, _, hhalted⟩ := predProgram.nonzero_execution n hpos
      exact ⟨⟨9, s⟩, hsteps, hhalted⟩
  · -- Result equality
    intro hHalts hDom
    obtain ⟨hsteps_chosen, hhalted_chosen⟩ := Classical.choose_spec hHalts
    cases Nat.eq_zero_or_pos n with
    | inl hz =>
      -- n = 0: result is 0 = 0 - 1 = 0
      obtain ⟨s, hsteps, hr0, hhalted⟩ := predProgram.zero_execution
      have hsteps' : Steps predProgram (Config.init (List.ofFn inputs)) ⟨9, s⟩ := by
        simp only [h_ofFn, hz]; exact hsteps
      have heq := Steps.halts_unique hsteps_chosen hhalted_chosen hsteps' hhalted
      simp only [Result, heq, State.output, Part.get_some, State.read] at hr0 ⊢
      omega
    | inr hpos =>
      -- n > 0: result is n - 1
      obtain ⟨s, hsteps, hr0, hhalted⟩ := predProgram.nonzero_execution n hpos
      have hsteps' : Steps predProgram (Config.init (List.ofFn inputs)) ⟨9, s⟩ := by
        simp only [h_ofFn]; exact hsteps
      have heq := Steps.halts_unique hsteps_chosen hhalted_chosen hsteps' hhalted
      simp only [Result, heq, State.output, Part.get_some]
      exact hr0

/-! ## Monus (Truncated Subtraction)

Monus (truncated subtraction) is computed via primitive recursion:
- `m ∸ 0 = m` (base case: identity)
- `m ∸ (k+1) = pred(m ∸ k)` (recursive case: apply predecessor)
-/

/-- Helper: The PR step function for monus computes pred of accumulator. -/
private theorem monus_pr_step_eq (inputs : Fin 3 → ℕ) :
    compFunction 1 3 (fun x => Part.some (x 0 - 1)) (fun _ => fun y => Part.some (y 2)) inputs =
    Part.some (inputs 2 - 1) := by
  simp only [compFunction, Part.sequence, Part.bind_some, Fin.isValue]
  simp only [Part.map, Part.bind, Part.some]
  simp only [Part.assert_pos (by trivial : True)]
  rfl

/-- Helper: Pr with identity base and pred-of-accumulator step computes monus. -/
private theorem monus_pr_eq (m n : ℕ) :
    Pr (fun x => Part.some (x 0)) (fun inputs => Part.some (inputs 2 - 1))
      (Fin.snoc (fun _ : Fin 1 => m) n) = Part.some (m - n) := by
  induction n with
  | zero => simp only [Pr_snoc_zero, Nat.sub_zero]
  | succ k ih =>
    simp only [Pr_snoc_succ]
    rw [ih]
    simp only [Part.bind_some]
    -- extendInputsForG (fun _ => m) k (m - k) 2 = m - k (the accumulator)
    -- Note: 2 in Fin 3 is Fin.last 2
    have h2_eq : (2 : Fin 3) = Fin.last 2 := rfl
    have h : extendInputsForG (fun _ : Fin 1 => m) k (m - k) 2 = m - k := by
      simp only [extendInputsForG, h2_eq, Fin.snoc_last]
    -- Goal: Part.some (extendInputsForG ... 2 - 1) = Part.some (m - (k + 1))
    -- Using h: Part.some ((m - k) - 1) = Part.some (m - (k + 1))
    rw [h]
    -- Now: Part.some ((m - k) - 1) = Part.some (m - (k + 1))
    -- Use Nat.sub_succ: m - (k + 1) = (m - k) - 1
    rw [Nat.sub_succ]
    -- Now need: Part.some ((m - k) - 1) = Part.some ((m - k).pred)
    -- But (n - 1) = n.pred for natural numbers
    rfl

open URMComputable in
/-- Monus (truncated subtraction) is URM-computable.

    monus(m, n) = m - n with natural truncation (0 when n > m).

    Proof uses primitive recursion with:
    - Base: f(m) = m (identity)
    - Step: g(m, k, acc) = pred(acc) -/
theorem monus_computable : URMComputable 2 (fun mn => Part.some (mn 0 - mn 1)) := by
  -- The step function g(m, k, acc) = pred(acc) is composition of pred with projection
  have hStepSF : URMComputableSF 3 (fun inputs => Part.some (inputs 2 - 1)) := by
    have h := URMComputable.comp_general (m := 1) (n := 3)
      pred_computable
      (fun _ => proj_computable 3 2)
    convert h using 1
    funext inputs
    exact (monus_pr_step_eq inputs).symm
  have hStep : URMComputable 3 (fun inputs => Part.some (inputs 2 - 1)) :=
    hStepSF.toComputable
  -- Apply primitive recursion closure
  have hPR := URMComputable.primRec (n := 1) id_computable hStep
  -- Convert to show PrFunction computes monus
  convert hPR using 1
  funext inputs
  simp only [PrFunction]
  -- Express inputs as Fin.snoc
  have hinputs : inputs = Fin.snoc (fun _ : Fin 1 => inputs 0) (inputs 1) := by
    ext i
    fin_cases i
    · simp [Fin.snoc]
    · simp [Fin.snoc]
  rw [hinputs]
  -- Need the symmetric form
  symm
  exact monus_pr_eq (inputs 0) (inputs 1)

end Urm
