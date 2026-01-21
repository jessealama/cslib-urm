/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.PrimitiveRecursion.Base
import Urm.Concat

/-! # Program Construction for Primitive Recursion

This file constructs the witness program for primitive recursion.

## Program Structure

```
[Setup Phase]
  copy_register_range 0 savedStart (n+1)    -- save inputs including y
  Z counter                               -- counter := 0
  Z zero                                  -- zero register := 0

[Base Case Phase]
  clear_registers base                     -- clear working space
  copy_register_range savedStart 0 n        -- restore x₁,...,xₙ
  pF (shifted)                            -- execute base case
  T 0 accumulator                         -- save result

[Loop Check] (PC = loopCheckPC)
  J counter savedY outputPC               -- if counter = y, exit loop

[Loop Body]
  clear_registers base                     -- clear working space
  copy_register_range savedStart 0 n        -- restore x₁,...,xₙ
  T counter R[n]                          -- R[n] := counter
  T accumulator R[n+1]                    -- R[n+1] := current accumulator
  pG (shifted)                            -- execute recursive step
  T 0 accumulator                         -- update accumulator
  S counter                               -- counter++
  J zero zero loopCheckPC                 -- unconditional jump back

[Output Phase] (PC = outputPC)
  T accumulator 0                         -- copy final result to R[0]
```
-/

namespace Urm

open Program

/-! ## Length calculations -/

/-- Length of setup phase: copy (n+1) registers + zero counter + zero register. -/
def pr_setup_phase_length (n : ℕ) : ℕ := (n + 1) + 2

/-- Length of base case prologue: clear (base+1) registers + copy n registers. -/
def pr_base_case_prologue_length (n : ℕ) (pF pG : Program) : ℕ :=
  (primitive_recursion_base n pF pG + 1) + n

/-- Length of base case phase: prologue + pF + transfer to accumulator. -/
def pr_base_case_phase_length (n : ℕ) (pF pG : Program) : ℕ :=
  pr_base_case_prologue_length n pF pG + pF.length + 1

/-- Length of loop prologue: clear (base+1) + copy n + 2 transfers. -/
def pr_loop_prologue_length (n : ℕ) (pF pG : Program) : ℕ :=
  (primitive_recursion_base n pF pG + 1) + n + 2

/-- Length of loop epilogue: transfer + increment + unconditional jump. -/
def pr_loop_epilogue_length : ℕ := 3

/-- Length of loop body: prologue + pG + epilogue. -/
def pr_loop_body_length (n : ℕ) (pF pG : Program) : ℕ :=
  pr_loop_prologue_length n pF pG + pG.length + pr_loop_epilogue_length

/-! ## PC positions -/

/-- PC where base case phase starts (after setup). -/
def pr_base_case_pc (n : ℕ) : ℕ := pr_setup_phase_length n

/-- PC where loop check happens (after base case). -/
def pr_loop_check_pc (n : ℕ) (pF pG : Program) : ℕ :=
  pr_setup_phase_length n + pr_base_case_phase_length n pF pG

/-- PC where loop body starts (after loop check). -/
def pr_loop_body_pc (n : ℕ) (pF pG : Program) : ℕ :=
  pr_loop_check_pc n pF pG + 1

/-- Offset for shifting pF's jumps. -/
def pr_pf_offset (n : ℕ) (pF pG : Program) : ℕ :=
  pr_setup_phase_length n + pr_base_case_prologue_length n pF pG

/-- Offset for shifting pG's jumps. -/
def pr_pg_offset (n : ℕ) (pF pG : Program) : ℕ :=
  pr_loop_body_pc n pF pG + pr_loop_prologue_length n pF pG

/-- PC of output phase (after loop body). -/
def pr_output_pc (n : ℕ) (pF pG : Program) : ℕ :=
  pr_loop_body_pc n pF pG + pr_loop_body_length n pF pG

/-! ## Program phases -/

/-- Setup phase: save inputs (including y), initialize counter and zero register. -/
def pr_setup_phase (n : ℕ) (pF pG : Program) : Program :=
  copy_register_range 0 (pr_saved_inputs_start n pF pG) (n + 1) ++
  [Instr.Z (pr_counter_reg n pF pG), Instr.Z (pr_zero_reg n pF pG)]

/-- Base case prologue: clear working space, restore x₁,...,xₙ. -/
def pr_base_case_prologue (n : ℕ) (pF pG : Program) : Program :=
  clear_registers (primitive_recursion_base n pF pG) ++
  copy_register_range (pr_saved_inputs_start n pF pG) 0 n

/-- Base case phase: prologue + pF + save result to accumulator. -/
def pr_base_case_phase (n : ℕ) (pF pG : Program) : Program :=
  pr_base_case_prologue n pF pG ++
  pF.shift_jumps (pr_pf_offset n pF pG) ++
  [Instr.T 0 (pr_accumulator_reg n pF pG)]

/-- Loop check: jump to output if counter = savedY. -/
def pr_loop_check (n : ℕ) (pF pG : Program) : Program :=
  [Instr.J (pr_counter_reg n pF pG) (pr_saved_y_reg n pF pG) (pr_output_pc n pF pG)]

/-- Loop prologue: clear working space, restore inputs, set up pG inputs. -/
def pr_loop_prologue (n : ℕ) (pF pG : Program) : Program :=
  clear_registers (primitive_recursion_base n pF pG) ++
  copy_register_range (pr_saved_inputs_start n pF pG) 0 n ++
  [Instr.T (pr_counter_reg n pF pG) n,
   Instr.T (pr_accumulator_reg n pF pG) (n + 1)]

/-- Loop epilogue: save result, increment counter, jump back. -/
def pr_loop_epilogue (n : ℕ) (pF pG : Program) : Program :=
  [Instr.T 0 (pr_accumulator_reg n pF pG),
   Instr.S (pr_counter_reg n pF pG),
   Instr.J (pr_zero_reg n pF pG) (pr_zero_reg n pF pG) (pr_loop_check_pc n pF pG)]

/-- Loop body: prologue + pG + epilogue. -/
def pr_loop_body (n : ℕ) (pF pG : Program) : Program :=
  pr_loop_prologue n pF pG ++
  pG.shift_jumps (pr_pg_offset n pF pG) ++
  pr_loop_epilogue n pF pG

/-- Output phase: copy accumulator to R[0]. -/
def pr_output_phase (n : ℕ) (pF pG : Program) : Program :=
  [Instr.T (pr_accumulator_reg n pF pG) 0]

/-- The complete primitive recursion witness program. -/
def primitive_recursion_program (n : ℕ) (pF pG : Program) : Program :=
  pr_setup_phase n pF pG ++
  pr_base_case_phase n pF pG ++
  pr_loop_check n pF pG ++
  pr_loop_body n pF pG ++
  pr_output_phase n pF pG

/-! ## Length lemmas -/

@[simp] theorem pr_setup_phase_length_eq (n : ℕ) (pF pG : Program) :
    (pr_setup_phase n pF pG).length = pr_setup_phase_length n := by
  simp only [pr_setup_phase, pr_setup_phase_length, List.length_append,
    copy_register_range_length, List.length]

@[simp] theorem pr_base_case_prologue_length_eq (n : ℕ) (pF pG : Program) :
    (pr_base_case_prologue n pF pG).length = pr_base_case_prologue_length n pF pG := by
  simp only [pr_base_case_prologue, pr_base_case_prologue_length, List.length_append,
    clear_registers_length, copy_register_range_length]

@[simp] theorem pr_base_case_phase_length_eq (n : ℕ) (pF pG : Program) :
    (pr_base_case_phase n pF pG).length = pr_base_case_phase_length n pF pG := by
  simp only [pr_base_case_phase, pr_base_case_phase_length, List.length_append,
    pr_base_case_prologue_length_eq, shift_jumps_length, List.length]

@[simp] theorem pr_loop_check_length (n : ℕ) (pF pG : Program) :
    (pr_loop_check n pF pG).length = 1 := by
  simp only [pr_loop_check, List.length]

@[simp] theorem pr_loop_prologue_length_eq (n : ℕ) (pF pG : Program) :
    (pr_loop_prologue n pF pG).length = pr_loop_prologue_length n pF pG := by
  simp only [pr_loop_prologue, pr_loop_prologue_length, List.length_append,
    clear_registers_length, copy_register_range_length, List.length]

@[simp] theorem pr_loop_epilogue_length_eq (n : ℕ) (pF pG : Program) :
    (pr_loop_epilogue n pF pG).length = pr_loop_epilogue_length := by
  simp only [pr_loop_epilogue, pr_loop_epilogue_length, List.length]

@[simp] theorem pr_loop_body_length_eq (n : ℕ) (pF pG : Program) :
    (pr_loop_body n pF pG).length = pr_loop_body_length n pF pG := by
  simp only [pr_loop_body, pr_loop_body_length, List.length_append,
    pr_loop_prologue_length_eq, shift_jumps_length, pr_loop_epilogue_length_eq]

@[simp] theorem pr_output_phase_length (n : ℕ) (pF pG : Program) :
    (pr_output_phase n pF pG).length = 1 := by
  simp only [pr_output_phase, List.length]

@[simp] theorem primitive_recursion_program_length (n : ℕ) (pF pG : Program) :
    (primitive_recursion_program n pF pG).length = pr_output_pc n pF pG + 1 := by
  simp only [primitive_recursion_program, pr_output_pc, pr_loop_body_pc, pr_loop_check_pc,
    pr_setup_phase_length_eq, pr_base_case_phase_length_eq, pr_loop_body_length_eq,
    List.length_append, pr_setup_phase_length, pr_base_case_phase_length,
    pr_loop_check_length, pr_loop_body_length, pr_output_phase_length]

/-! ## PC position lemmas -/

theorem pr_loop_body_pc_eq (n : ℕ) (pF pG : Program) :
    pr_loop_body_pc n pF pG = (pr_setup_phase n pF pG).length +
      (pr_base_case_phase n pF pG).length + (pr_loop_check n pF pG).length := by
  simp only [pr_loop_body_pc, pr_loop_check_pc, pr_setup_phase_length_eq,
    pr_base_case_phase_length_eq, pr_loop_check_length]

/-! ## Key instruction access lemmas -/

/-- The loop check instruction is a J comparing counter to savedY. -/
theorem instr_at_loopCheck (n : ℕ) (pF pG : Program) :
    (primitive_recursion_program n pF pG)[pr_loop_check_pc n pF pG]? =
      some (Instr.J (pr_counter_reg n pF pG) (pr_saved_y_reg n pF pG) (pr_output_pc n pF pG)) := by
  simp only [primitive_recursion_program, pr_loop_check_pc, pr_loop_check,
    List.getElem?_append, List.length_append, pr_setup_phase_length_eq, pr_base_case_phase_length_eq]
  simp only [pr_setup_phase_length, pr_base_case_phase_length, pr_base_case_prologue_length]
  simp only [List.length] at *
  split_ifs with h1 h2 h3 h4
  · omega
  · omega
  · simp only [Nat.sub_self, List.getElem?_cons_zero]
  · omega
  · omega

/-- The output instruction is a T copying accumulator to R[0]. -/
theorem instr_at_output (n : ℕ) (pF pG : Program) :
    (primitive_recursion_program n pF pG)[pr_output_pc n pF pG]? =
      some (Instr.T (pr_accumulator_reg n pF pG) 0) := by
  simp only [primitive_recursion_program, pr_output_pc, pr_loop_body_pc, pr_loop_check_pc,
    pr_output_phase, List.getElem?_append, List.length_append, pr_setup_phase_length_eq,
    pr_base_case_phase_length_eq, pr_loop_check_length, pr_loop_body_length_eq]
  simp only [pr_setup_phase_length, pr_base_case_phase_length, pr_base_case_prologue_length,
    pr_loop_body_length, pr_loop_prologue_length, pr_loop_epilogue_length]
  split_ifs with h1 h2 h3 h4
  · omega
  · omega
  · omega
  · omega
  · simp only [Nat.sub_self, List.getElem?_cons_zero]

end Urm
