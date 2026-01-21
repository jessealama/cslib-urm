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
import Aesop



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

-- Helper lemmas about instruction lookup
@[simp] theorem instr_0 : addProgram[0]? = some (Instr.Z 2) := rfl
@[simp] theorem instr_1 : addProgram[1]? = some (Instr.J 2 1 5) := rfl
@[simp] theorem instr_2 : addProgram[2]? = some (Instr.S 0) := rfl
@[simp] theorem instr_3 : addProgram[3]? = some (Instr.S 2) := rfl
@[simp] theorem instr_4 : addProgram[4]? = some (Instr.J 0 0 1) := rfl
@[simp] theorem length_eq : addProgram.length = 5 := rfl

/-- The initial instruction (Z 2) takes us from pc=0 to pc=1 with R2=0. -/
theorem step_init (s : State) :
    Step addProgram ⟨0, s⟩ ⟨1, s.write 2 0⟩ :=
  Step.zero instr_0

/-- When counter equals y (R2 = R1), we exit the loop by jumping to pc=5. -/
theorem step_exit (s : State) (heq : s.read 2 = s.read 1) :
    Step addProgram ⟨1, s⟩ ⟨5, s⟩ :=
  Step.jump_eq instr_1 heq

/-- When counter < y (R2 ≠ R1), we continue to the increment instructions. -/
theorem step_continue (s : State) (hne : s.read 2 ≠ s.read 1) :
    Step addProgram ⟨1, s⟩ ⟨2, s⟩ :=
  Step.jump_ne instr_1 hne

/-- Increment R0 at instruction 2. -/
theorem step_inc_r0 (s : State) :
    Step addProgram ⟨2, s⟩ ⟨3, s.write 0 (s.read 0 + 1)⟩ :=
  Step.succ instr_2

/-- Increment R2 at instruction 3. -/
theorem step_inc_r2 (s : State) :
    Step addProgram ⟨3, s⟩ ⟨4, s.write 2 (s.read 2 + 1)⟩ :=
  Step.succ instr_3

/-- Unconditional jump back at instruction 4 (J 0 0 1 always jumps since R0 = R0). -/
theorem step_jump_back (s : State) :
    Step addProgram ⟨4, s⟩ ⟨1, s⟩ :=
  Step.jump_eq instr_4 rfl

/-- One complete loop iteration: from pc=1 with k < y, to pc=1 with k+1.
    Precondition: s.read 2 = k, s.read 1 = y, k < y
    Postcondition: s'.read 2 = k+1, s'.read 0 = s.read 0 + 1, s'.read 1 = y -/
theorem loop_iteration (s : State) (k y : ℕ)
    (hk : s.read 2 = k) (hy : s.read 1 = y) (hlt : k < y) :
    ∃ s', Steps addProgram ⟨1, s⟩ ⟨1, s'⟩ ∧
          s'.read 0 = s.read 0 + 1 ∧
          s'.read 1 = y ∧
          s'.read 2 = k + 1 := by
  have hne : s.read 2 ≠ s.read 1 := by omega
  have h1 : Step addProgram ⟨1, s⟩ ⟨2, s⟩ := step_continue s hne
  let s1 := s.write 0 (s.read 0 + 1)
  have h2 : Step addProgram ⟨2, s⟩ ⟨3, s1⟩ := step_inc_r0 s
  let s2 := s1.write 2 (s1.read 2 + 1)
  have h3 : Step addProgram ⟨3, s1⟩ ⟨4, s2⟩ := step_inc_r2 s1
  have h4 : Step addProgram ⟨4, s2⟩ ⟨1, s2⟩ := step_jump_back s2
  refine ⟨s2, by aesop_steps, ?_, ?_, ?_⟩
  · simp only [s2, s1, State.write, State.read, Function.update_of_ne (by decide : (0 : ℕ) ≠ 2),
               Function.update_self]
  · simp only [s2, s1, State.write, State.read, Function.update_of_ne (by decide : (1 : ℕ) ≠ 2),
               Function.update_of_ne (by decide : (1 : ℕ) ≠ 0)]
    exact hy
  · simp only [s2, s1, State.read, State.write, Function.update_self,
               Function.update_of_ne (by decide : (2 : ℕ) ≠ 0)]
    simp only [State.read] at hk; omega

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
    refine ⟨_, Steps.refl _, ?_, ?_, ?_⟩ <;>
      simp [State.write, State.read, State.fromInputs, Function.update_of_ne, Function.update_self]
  | succ k' ih =>
    obtain ⟨s', hsteps', hr0', hr1', hr2'⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨s'', hiter, hr0'', hr1'', hr2''⟩ := loop_iteration s' k' y hr2' hr1' (Nat.lt_of_succ_le hk)
    exact ⟨s'', Steps.trans hsteps' hiter, by omega, hr1'', hr2''⟩

/-- The program halts after completing y iterations.
    Starting from pc=1 with R2=y and R1=y, we exit to pc=5. -/
theorem exits_when_done (s : State) (h : s.read 2 = s.read 1) :
    Steps addProgram ⟨1, s⟩ ⟨5, s⟩ := by
  have hstep := step_exit s h
  aesop_steps

/-- Configuration at pc=5 is halted. -/
theorem halted_at_5 (s : State) : (⟨5, s⟩ : Config).isHalted addProgram := by
  simp [Config.isHalted, length_eq]

/-- The full execution from initial state to halted state. -/
theorem full_execution (x y : ℕ) :
    ∃ s, Steps addProgram (Config.init [x, y]) ⟨5, s⟩ ∧
         s.read 0 = x + y ∧
         (⟨5, s⟩ : Config).isHalted addProgram := by
  let s0 := State.fromInputs [x, y]
  have h_init : Step addProgram ⟨0, s0⟩ ⟨1, s0.write 2 0⟩ := step_init s0
  obtain ⟨s_final, hsteps_loop, hr0, hr1, hr2⟩ := loop_invariant x y y (Nat.le_refl y)
  have heq : s_final.read 2 = s_final.read 1 := by omega
  have h_exit := exits_when_done s_final heq
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
  let x := inputs 0
  let y := inputs 1
  have h_ofFn : List.ofFn inputs = [x, y] := by simp only [List.ofFn]; rfl
  constructor
  · simp only [Part.some_dom, iff_true]
    rw [h_ofFn]
    obtain ⟨s, hsteps, _, hhalted⟩ := addProgram.full_execution x y
    exact ⟨⟨5, s⟩, hsteps, hhalted⟩
  · intro hHalts hDom
    obtain ⟨s, hsteps, hr0, hhalted⟩ := addProgram.full_execution x y
    have hsteps' : Steps addProgram (Config.init (List.ofFn inputs)) ⟨5, s⟩ := by
      simp only [h_ofFn]; exact hsteps
    obtain ⟨hsteps_chosen, hhalted_chosen⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps_chosen hhalted_chosen hsteps' hhalted
    simp only [Result, heq, State.output, Part.get_some]
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

-- Helper lemmas about instruction lookup
@[simp] theorem instr_0 : predProgram[0]? = some (Instr.Z 1) := rfl
@[simp] theorem instr_1 : predProgram[1]? = some (Instr.J 0 1 9) := rfl
@[simp] theorem instr_2 : predProgram[2]? = some (Instr.Z 2) := rfl
@[simp] theorem instr_3 : predProgram[3]? = some (Instr.S 1) := rfl
@[simp] theorem instr_4 : predProgram[4]? = some (Instr.J 0 1 8) := rfl
@[simp] theorem instr_5 : predProgram[5]? = some (Instr.S 2) := rfl
@[simp] theorem instr_6 : predProgram[6]? = some (Instr.S 1) := rfl
@[simp] theorem instr_7 : predProgram[7]? = some (Instr.J 0 0 4) := rfl
@[simp] theorem instr_8 : predProgram[8]? = some (Instr.T 2 0) := rfl
@[simp] theorem length_eq : predProgram.length = 9 := rfl

/-- Clear R1 for zero check (pc 0 → 1). -/
theorem step_clear_r1 (s : State) :
    Step predProgram ⟨0, s⟩ ⟨1, s.write 1 0⟩ :=
  Step.zero instr_0

/-- When R0 = 0 (= R1 after clear), jump to halt (pc 1 → 9). -/
theorem step_zero_exit (s : State) (heq : s.read 0 = s.read 1) :
    Step predProgram ⟨1, s⟩ ⟨9, s⟩ :=
  Step.jump_eq instr_1 heq

/-- When R0 ≠ 0, continue to main loop setup (pc 1 → 2). -/
theorem step_nonzero_continue (s : State) (hne : s.read 0 ≠ s.read 1) :
    Step predProgram ⟨1, s⟩ ⟨2, s⟩ :=
  Step.jump_ne instr_1 hne

/-- Clear R2 for result tracking (pc 2 → 3). -/
theorem step_clear_r2 (s : State) :
    Step predProgram ⟨2, s⟩ ⟨3, s.write 2 0⟩ :=
  Step.zero instr_2

/-- Initialize R1 to 1 (pc 3 → 4). -/
theorem step_init_r1 (s : State) :
    Step predProgram ⟨3, s⟩ ⟨4, s.write 1 (s.read 1 + 1)⟩ :=
  Step.succ instr_3

/-- When R0 = R1, jump to copy result (pc 4 → 8). -/
theorem step_found_pred (s : State) (heq : s.read 0 = s.read 1) :
    Step predProgram ⟨4, s⟩ ⟨8, s⟩ :=
  Step.jump_eq instr_4 heq

/-- When R0 ≠ R1, continue loop (pc 4 → 5). -/
theorem step_continue_loop (s : State) (hne : s.read 0 ≠ s.read 1) :
    Step predProgram ⟨4, s⟩ ⟨5, s⟩ :=
  Step.jump_ne instr_4 hne

/-- Increment R2 (pc 5 → 6). -/
theorem step_inc_r2 (s : State) :
    Step predProgram ⟨5, s⟩ ⟨6, s.write 2 (s.read 2 + 1)⟩ :=
  Step.succ instr_5

/-- Increment R1 (pc 6 → 7). -/
theorem step_inc_r1 (s : State) :
    Step predProgram ⟨6, s⟩ ⟨7, s.write 1 (s.read 1 + 1)⟩ :=
  Step.succ instr_6

/-- Unconditional jump back to loop check (pc 7 → 4). -/
theorem step_jump_back (s : State) :
    Step predProgram ⟨7, s⟩ ⟨4, s⟩ :=
  Step.jump_eq instr_7 rfl

/-- Copy R2 to R0 (pc 8 → 9). -/
theorem step_copy_result (s : State) :
    Step predProgram ⟨8, s⟩ ⟨9, s.write 0 (s.read 2)⟩ :=
  Step.trans instr_8

/-- Configuration at pc=9 is halted. -/
theorem halted_at_9 (s : State) : (⟨9, s⟩ : Config).isHalted predProgram := by
  simp [Config.isHalted, length_eq]

/-- Full execution for n = 0: immediately exits with R0 = 0. -/
theorem zero_execution :
    ∃ s, Steps predProgram (Config.init [0]) ⟨9, s⟩ ∧
         s.read 0 = 0 ∧
         (⟨9, s⟩ : Config).isHalted predProgram := by
  let s0 := State.fromInputs [0]
  have hs0_r0 : s0 0 = 0 := rfl
  have hs0_r1 : s0 1 = 0 := rfl
  let s1 := s0.write 1 0
  have h1 : Step predProgram ⟨0, s0⟩ ⟨1, s1⟩ := step_clear_r1 s0
  have hs1_r0 : s1.read 0 = 0 := by
    simp only [s1, State.read, State.write, Function.update_of_ne (by decide : (0 : ℕ) ≠ 1)]
    exact hs0_r0
  have hs1_r1 : s1.read 1 = 0 := by
    simp only [s1, State.read, State.write, Function.update_self]
  have heq : s1.read 0 = s1.read 1 := by rw [hs1_r0, hs1_r1]
  have h2 : Step predProgram ⟨1, s1⟩ ⟨9, s1⟩ := step_zero_exit s1 heq
  use s1
  refine ⟨by aesop_steps, hs1_r0, halted_at_9 s1⟩

/-- One loop iteration: from pc=4 with R1 = k + 1 < n, to pc=4 with R1 = k + 2.
    Invariant: R0 = n, R1 = k + 1, R2 = k -/
theorem loop_iteration (s : State) (n k : ℕ)
    (hn : s.read 0 = n) (hr1 : s.read 1 = k + 1) (hr2 : s.read 2 = k)
    (hlt : k + 1 < n) :
    ∃ s', Steps predProgram ⟨4, s⟩ ⟨4, s'⟩ ∧
          s'.read 0 = n ∧
          s'.read 1 = k + 2 ∧
          s'.read 2 = k + 1 := by
  have hne : s.read 0 ≠ s.read 1 := by omega
  have h1 : Step predProgram ⟨4, s⟩ ⟨5, s⟩ := step_continue_loop s hne
  let s1 := s.write 2 (s.read 2 + 1)
  have h2 : Step predProgram ⟨5, s⟩ ⟨6, s1⟩ := step_inc_r2 s
  let s2 := s1.write 1 (s1.read 1 + 1)
  have h3 : Step predProgram ⟨6, s1⟩ ⟨7, s2⟩ := step_inc_r1 s1
  have h4 : Step predProgram ⟨7, s2⟩ ⟨4, s2⟩ := step_jump_back s2
  refine ⟨s2, by aesop_steps, ?_, ?_, ?_⟩
  · simp only [s2, s1, State.read, State.write, Function.update_of_ne (by decide : (0 : ℕ) ≠ 1),
               Function.update_of_ne (by decide : (0 : ℕ) ≠ 2)]
    exact hn
  · simp only [s2, s1, State.read, State.write, Function.update_self,
               Function.update_of_ne (by decide : (1 : ℕ) ≠ 2)]
    simp only [State.read] at hr1; omega
  · simp only [s2, s1, State.read, State.write, Function.update_of_ne (by decide : (2 : ℕ) ≠ 1),
               Function.update_self]
    simp only [State.read] at hr2; omega

/-- After k iterations, R1 = k + 1 and R2 = k.
    Starting state: pc=4, R0=n (n > 0), R1=1, R2=0 -/
theorem loop_invariant (n k : ℕ) (hk : k < n) :
    ∃ s, Steps predProgram ⟨4, (State.fromInputs [n]).write 1 0 |>.write 2 0 |>.write 1 1⟩ ⟨4, s⟩ ∧
         s.read 0 = n ∧
         s.read 1 = k + 1 ∧
         s.read 2 = k := by
  induction k with
  | zero =>
    let s_init := (State.fromInputs [n]).write 1 0 |>.write 2 0 |>.write 1 1
    refine ⟨s_init, Steps.refl _, ?_, ?_, ?_⟩
    · simp [s_init, State.read, State.write, State.fromInputs]
    · simp [s_init, State.read, State.write, Function.update_self]
    · simp [s_init, State.read, State.write, Function.update_of_ne, Function.update_self]
  | succ k' ih =>
    obtain ⟨s', hsteps', hr0', hr1', hr2'⟩ := ih (Nat.lt_of_succ_lt hk)
    obtain ⟨s'', hiter, hr0'', hr1'', hr2''⟩ := loop_iteration s' n k' hr0' hr1' hr2' hk
    exact ⟨s'', Steps.trans hsteps' hiter, hr0'', hr1'', hr2''⟩

/-- When R0 = R1 at pc=4, we exit to pc=8 and copy R2 to R0, then halt at pc=9. -/
theorem loop_exit (s : State) (n : ℕ)
    (hr0 : s.read 0 = n) (hr1 : s.read 1 = n) (hr2 : s.read 2 = n - 1) :
    ∃ s', Steps predProgram ⟨4, s⟩ ⟨9, s'⟩ ∧
          s'.read 0 = n - 1 ∧
          (⟨9, s'⟩ : Config).isHalted predProgram := by
  have heq : s.read 0 = s.read 1 := by rw [hr0, hr1]
  have h1 : Step predProgram ⟨4, s⟩ ⟨8, s⟩ := step_found_pred s heq
  let s' := s.write 0 (s.read 2)
  have h2 : Step predProgram ⟨8, s⟩ ⟨9, s'⟩ := step_copy_result s
  use s'
  refine ⟨by aesop_steps, ?_, halted_at_9 s'⟩
  simp only [s', State.read, State.write, Function.update_self]
  simp only [State.read] at hr2
  exact hr2

/-- Full execution for n > 0. -/
theorem nonzero_execution (n : ℕ) (hn : 0 < n) :
    ∃ s, Steps predProgram (Config.init [n]) ⟨9, s⟩ ∧
         s.read 0 = n - 1 ∧
         (⟨9, s⟩ : Config).isHalted predProgram := by
  let s0 := State.fromInputs [n]
  have hs0_r0 : s0 0 = n := rfl
  have hs0_r1 : s0 1 = 0 := rfl
  let s1 := s0.write 1 0
  have h_step0 : Step predProgram ⟨0, s0⟩ ⟨1, s1⟩ := step_clear_r1 s0
  have hs1_r0 : s1.read 0 = n := by
    simp only [s1, State.read, State.write, Function.update_of_ne (by decide : (0 : ℕ) ≠ 1)]
    exact hs0_r0
  have hs1_r1 : s1.read 1 = 0 := by
    simp only [s1, State.read, State.write, Function.update_self]
  have hne1 : s1.read 0 ≠ s1.read 1 := by rw [hs1_r0, hs1_r1]; omega
  have h_step1 : Step predProgram ⟨1, s1⟩ ⟨2, s1⟩ := step_nonzero_continue s1 hne1
  let s2 := s1.write 2 0
  have h_step2 : Step predProgram ⟨2, s1⟩ ⟨3, s2⟩ := step_clear_r2 s1
  let s3 := s2.write 1 (s2.read 1 + 1)
  have h_step3 : Step predProgram ⟨3, s2⟩ ⟨4, s3⟩ := step_init_r1 s2
  have hs3_eq : s3 = ((((State.fromInputs [n]).write 1 0).write 2 0).write 1 1) := by
    simp only [s3, s2, s1, State.write, State.read]
    ext i
    simp only [Function.update]
    split_ifs <;> first | rfl | omega
  have h_setup : Steps predProgram ⟨0, s0⟩ ⟨4, s3⟩ := by aesop_steps
  have hk : n - 1 < n := Nat.sub_lt hn Nat.one_pos
  obtain ⟨s_loop, h_loop_steps, hr0_loop, hr1_loop, hr2_loop⟩ := loop_invariant n (n - 1) hk
  have h_loop_steps' : Steps predProgram ⟨4, s3⟩ ⟨4, s_loop⟩ := by
    rw [hs3_eq]; exact h_loop_steps
  have hr1_eq_n : s_loop.read 1 = n := by omega
  obtain ⟨s_final, h_exit_steps, hr0_final, h_halted_final⟩ :=
    loop_exit s_loop n hr0_loop hr1_eq_n hr2_loop
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
  · simp only [Part.some_dom, iff_true]
    cases Nat.eq_zero_or_pos n with
    | inl hz =>
      rw [h_ofFn, hz]
      obtain ⟨s, hsteps, _, hhalted⟩ := predProgram.zero_execution
      exact ⟨⟨9, s⟩, hsteps, hhalted⟩
    | inr hpos =>
      rw [h_ofFn]
      obtain ⟨s, hsteps, _, hhalted⟩ := predProgram.nonzero_execution n hpos
      exact ⟨⟨9, s⟩, hsteps, hhalted⟩
  · intro hHalts hDom
    obtain ⟨hsteps_chosen, hhalted_chosen⟩ := Classical.choose_spec hHalts
    cases Nat.eq_zero_or_pos n with
    | inl hz =>
      obtain ⟨s, hsteps, hr0, hhalted⟩ := predProgram.zero_execution
      have hsteps' : Steps predProgram (Config.init (List.ofFn inputs)) ⟨9, s⟩ := by
        simp only [h_ofFn, hz]; exact hsteps
      have heq := Steps.halts_unique hsteps_chosen hhalted_chosen hsteps' hhalted
      simp only [Result, heq, State.output, Part.get_some, State.read] at hr0 ⊢
      omega
    | inr hpos =>
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

/-- Helper: The PR step function for sub computes pred of accumulator. -/
private theorem sub_pr_step_eq (inputs : Fin 3 → ℕ) :
    compFunction 1 3 (fun x => Part.some (x 0 - 1)) (fun _ => fun y => Part.some (y 2)) inputs =
    Part.some (inputs 2 - 1) := by
  simp only [compFunction, Part.sequence, Part.bind_some, Fin.isValue]
  simp only [Part.map, Part.bind, Part.some]
  simp only [Part.assert_pos (by trivial : True)]
  rfl

/-- Helper: Pr with identity base and pred-of-accumulator step computes sub. -/
private theorem sub_pr_eq (m n : ℕ) :
    Pr (fun x => Part.some (x 0)) (fun inputs => Part.some (inputs 2 - 1))
      (Fin.snoc (fun _ : Fin 1 => m) n) = Part.some (m - n) := by
  induction n with
  | zero => simp only [Pr_snoc_zero, Nat.sub_zero]
  | succ k ih =>
    simp only [Pr_snoc_succ]
    rw [ih]
    simp only [Part.bind_some]
    have h2_eq : (2 : Fin 3) = Fin.last 2 := rfl
    have h : extendInputsForG (fun _ : Fin 1 => m) k (m - k) 2 = m - k := by
      simp only [extendInputsForG, h2_eq, Fin.snoc_last]
    rw [h, Nat.sub_succ]; rfl

open URMComputable in
/-- Truncated subtraction (monus) is URM-computable.

    sub(m, n) = m - n with natural truncation (0 when n > m).

    Proof uses primitive recursion with:
    - Base: f(m) = m (identity)
    - Step: g(m, k, acc) = pred(acc) -/
theorem sub_computable : URMComputable 2 (fun mn => Part.some (mn 0 - mn 1)) := by
  have h_sub_step := URMComputable.comp_general (m := 1) (n := 3)
    pred_computable (fun _ => proj_computable 3 2)
  have hStepSF : URMComputableSF 3 (fun inputs => Part.some (inputs 2 - 1)) := by
    convert h_sub_step using 1
    funext inputs
    exact (sub_pr_step_eq inputs).symm
  have hStep : URMComputable 3 (fun inputs => Part.some (inputs 2 - 1)) :=
    hStepSF.toComputable
  have hPR := URMComputable.primRec (n := 1) id_computable hStep
  convert hPR using 1
  funext inputs
  simp only [PrFunction]
  have hinputs : inputs = Fin.snoc (fun _ : Fin 1 => inputs 0) (inputs 1) := by
    ext i
    fin_cases i
    · simp [Fin.snoc]
    · simp [Fin.snoc]
  rw [hinputs]
  symm
  exact sub_pr_eq (inputs 0) (inputs 1)

/-! ## Multiplication

Multiplication is computed via primitive recursion:
- `x * 0 = 0` (base case: constant zero)
- `x * (k+1) = x + (x * k)` (recursive case: add x to accumulator)
-/

/-- The constant zero function (unary) is URM-computable.
    Program: [Z 0] - zero register 0 and halt. -/
private theorem const_zero_computable : URMComputable 1 (fun _ => Part.some 0) := by
  use [Instr.Z 0]
  intro inputs
  let finalState := (Config.init (List.ofFn inputs)).state.write 0 0
  have hstep : Step [Instr.Z 0] (Config.init (List.ofFn inputs)) ⟨1, finalState⟩ :=
    Step.zero rfl
  have hhalted : (⟨1, finalState⟩ : Config).isHalted [Instr.Z 0] := by simp
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨⟨1, finalState⟩, Steps.single hstep, hhalted⟩
  · intro hHalts _
    obtain ⟨hsteps, hhalted'⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps hhalted' (Steps.single hstep) hhalted
    simp only [Result, heq, State.output]
    rfl

/-- The inner functions for mul step: project to x (index 0) and acc (index 2). -/
private def mulStepGs : Fin 2 → (Fin 3 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun y => Part.some (y 0)) else (fun y => Part.some (y 2))

@[simp] private theorem mulStepGs_zero : mulStepGs 0 = (Part.some <| · 0) := rfl
@[simp] private theorem mulStepGs_one : mulStepGs 1 = (Part.some <| · 2) := rfl

/-- Helper: The PR step function for mul computes x + acc. -/
private theorem mul_pr_step_eq (inputs : Fin 3 → ℕ) :
    compFunction 2 3 (fun xy => Part.some (xy 0 + xy 1)) mulStepGs inputs =
    Part.some (inputs 0 + inputs 2) := by
  have h0 : mulStepGs 0 inputs = Part.some (inputs 0) := rfl
  have h1 : mulStepGs (Fin.succ 0) inputs = Part.some (inputs 2) := rfl
  simp only [compFunction, Part.sequence, h0, h1, Part.bind_some, Part.map_some]; rfl

/-- Helper: Pr with zero base and add-x-to-acc step computes multiplication. -/
private theorem mul_pr_eq (x y : ℕ) :
    Pr (fun _ => Part.some 0) (fun inputs => Part.some (inputs 0 + inputs 2))
      (Fin.snoc (fun _ : Fin 1 => x) y) = Part.some (x * y) := by
  induction y with
  | zero => simp only [Pr_snoc_zero, Nat.mul_zero]
  | succ k ih =>
    simp only [Pr_snoc_succ]
    rw [ih]
    simp only [Part.bind_some]
    have h0 : extendInputsForG (fun _ : Fin 1 => x) k (x * k) 0 = x := by
      simp only [extendInputsForG, Fin.snoc]; rfl
    have h2_eq : (2 : Fin 3) = Fin.last 2 := rfl
    have h2 : extendInputsForG (fun _ : Fin 1 => x) k (x * k) 2 = x * k := by
      simp only [extendInputsForG, h2_eq, Fin.snoc_last]
    rw [h0, h2, Nat.mul_succ, Nat.add_comm]

open URMComputable in
/-- Multiplication is URM-computable.

    mul(x, y) = x * y

    Proof uses primitive recursion with:
    - Base: f(x) = 0 (constant zero)
    - Step: g(x, k, acc) = x + acc (add x to accumulator) -/
theorem mul_computable : URMComputable 2 (fun xy => Part.some (xy 0 * xy 1)) := by
  have hgs : ∀ i, URMComputable 3 (mulStepGs i) := by
    intro i; fin_cases i <;> simp only [mulStepGs] <;> exact proj_computable 3 _
  have h_mul_step := URMComputable.comp_general (m := 2) (n := 3) add_computable hgs
  have hStepSF : URMComputableSF 3 (fun inputs => Part.some (inputs 0 + inputs 2)) := by
    convert h_mul_step using 1
    funext inputs
    exact (mul_pr_step_eq inputs).symm
  have hStep : URMComputable 3 (fun inputs => Part.some (inputs 0 + inputs 2)) :=
    hStepSF.toComputable
  have hBase : URMComputable 1 (fun _ => Part.some 0) := const_zero_computable
  have hPR := URMComputable.primRec (n := 1) hBase hStep
  convert hPR using 1
  funext inputs
  simp only [PrFunction]
  have hinputs : inputs = Fin.snoc (fun _ : Fin 1 => inputs 0) (inputs 1) := by
    ext i
    fin_cases i
    · simp [Fin.snoc]
    · simp [Fin.snoc]
  rw [hinputs]
  symm
  exact mul_pr_eq (inputs 0) (inputs 1)

end Urm
