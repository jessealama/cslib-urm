/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.Base
import Urm.Concat

/-! # Program Construction for Minimization

This file constructs the witness program for minimization.

## Program Structure

```
[Setup Phase]
  copy_register_range 0 (savedStart) n    -- save inputs
  Z counter                             -- counter := 0
  Z zero                                -- zero register := 0

[Loop Start] (PC = setupLen)
  clear_registers base                   -- clear working space
  copy_register_range savedStart 0 n      -- restore inputs
  T counter n                           -- copy counter to R[n]
  pF (shifted)                          -- execute subprogram
  J 0 zero outputPC                     -- if R[0] = 0, exit loop
  S counter                             -- counter++
  J zero zero loopStart                 -- unconditional jump back

[Output] (PC = outputPC)
  T counter 0                           -- copy counter to R[0]
```
-/

namespace Urm

open Program

/-! ## Length calculations -/

/-- Length of setup phase: copy n registers + zero counter + zero register. -/
@[simp] def setup_phase_length (n : ℕ) : ℕ := n + 2

/-- Length of loop prologue: clear (base+1) registers + copy n registers + transfer. -/
@[simp] def loop_prologueLength (n : ℕ) (pF : Program) : ℕ :=
  (minimization_base n pF + 1) + n + 1

/-- PC where loop starts (after setup). -/
def loop_start_pc (n : ℕ) : ℕ := setup_phase_length n

/-- Offset for shifting pF's jumps. -/
def pFOffset (n : ℕ) (pF : Program) : ℕ :=
  setup_phase_length n + loop_prologueLength n pF

/-- PC of output phase (after loop body). -/
def outputPC (n : ℕ) (pF : Program) : ℕ :=
  pFOffset n pF + pF.length + 3

/-! ## Program phases -/

/-- Setup phase: save inputs, initialize counter and zero register. -/
def setup_phase (n : ℕ) (pF : Program) : Program :=
  copy_register_range 0 (savedInputsStart n pF) n ++
  [Instr.Z (counter_reg n pF), Instr.Z (zero_reg n pF)]

/-- Loop prologue: clear working space, restore inputs, set R[n] to counter. -/
def loop_prologue (n : ℕ) (pF : Program) : Program :=
  clear_registers (minimization_base n pF) ++
  copy_register_range (savedInputsStart n pF) 0 n ++
  [Instr.T (counter_reg n pF) n]

/-- Loop epilogue: check result, increment counter, jump back. -/
def loopEpilogue (n : ℕ) (pF : Program) : Program :=
  [Instr.J 0 (zero_reg n pF) (outputPC n pF),
   Instr.S (counter_reg n pF),
   Instr.J (zero_reg n pF) (zero_reg n pF) (loop_start_pc n)]

/-- Output phase: copy counter to R[0]. -/
def output_phase (n : ℕ) (pF : Program) : Program :=
  [Instr.T (counter_reg n pF) 0]

/-- The complete minimization witness program. -/
def minimize_program (n : ℕ) (pF : Program) : Program :=
  setup_phase n pF ++
  loop_prologue n pF ++
  pF.shift_jumps (pFOffset n pF) ++
  loopEpilogue n pF ++
  output_phase n pF

/-! ## Length lemmas -/

@[simp] theorem setup_phase_len (n : ℕ) (pF : Program) :
    (setup_phase n pF).length = setup_phase_length n := by
  simp only [setup_phase, setup_phase_length, List.length_append, copy_register_range_length, List.length]

@[simp] theorem loop_prologue_length (n : ℕ) (pF : Program) :
    (loop_prologue n pF).length = loop_prologueLength n pF := by
  simp only [loop_prologue, loop_prologueLength, List.length_append,
    clear_registers_length, copy_register_range_length, List.length]

@[simp] theorem loopEpilogue_length (n : ℕ) (pF : Program) :
    (loopEpilogue n pF).length = 3 := by
  simp only [loopEpilogue, List.length]

@[simp] theorem output_phase_length (n : ℕ) (pF : Program) :
    (output_phase n pF).length = 1 := by
  simp only [output_phase, List.length]

@[simp] theorem minimize_program_length (n : ℕ) (pF : Program) :
    (minimize_program n pF).length = outputPC n pF + 1 := by
  simp only [minimize_program, outputPC, pFOffset, List.length_append,
    setup_phase_len, loop_prologue_length, shift_jumps_length,
    loopEpilogue_length, output_phase_length, setup_phase_length, loop_prologueLength]

/-! ## Epilogue instruction lemmas

These lemmas provide direct access to epilogue instructions at specific PCs.
They eliminate repeated simp chains in Halting.lean. -/

/-- PC at start of loop epilogue. -/
def epilogueStartPC (n : ℕ) (pF : Program) : ℕ := pFOffset n pF + pF.length

/-- Helper for epilogue instruction proofs: the common setup. -/
private theorem epilogue_instr_setup (n : ℕ) (pF : Program) (k : ℕ) (hk : k < 3) :
    (minimize_program n pF)[epilogueStartPC n pF + k]? =
      (loopEpilogue n pF)[k]? := by
  simp only [minimize_program, epilogueStartPC, pFOffset, setup_phase_length, loop_prologueLength,
    List.getElem?_append, List.length_append, setup_phase_len, loop_prologue_length,
    shift_jumps_length, loopEpilogue_length]
  simp only [show ¬ (n + 2 + (minimization_base n pF + 1 + n + 1) + pF.length + k < n + 2) by omega,
    show ¬ (n + 2 + (minimization_base n pF + 1 + n + 1) + pF.length + k <
      n + 2 + (minimization_base n pF + 1 + n + 1)) by omega,
    show ¬ (n + 2 + (minimization_base n pF + 1 + n + 1) + pF.length + k <
      n + 2 + (minimization_base n pF + 1 + n + 1) + pF.length) by omega,
    show n + 2 + (minimization_base n pF + 1 + n + 1) + pF.length + k <
      n + 2 + (minimization_base n pF + 1 + n + 1) + pF.length + 3 by omega,
    show n + 2 + (minimization_base n pF + 1 + n + 1) + pF.length + k -
      (n + 2 + (minimization_base n pF + 1 + n + 1) + pF.length) = k by omega,
    ite_true, ite_false]

theorem instr_at_epilogue_J0 (n : ℕ) (pF : Program) :
    (minimize_program n pF)[epilogueStartPC n pF]? =
      some (Instr.J 0 (zero_reg n pF) (outputPC n pF)) := by
  rw [show epilogueStartPC n pF = epilogueStartPC n pF + 0 from rfl,
      epilogue_instr_setup n pF 0 (by omega), loopEpilogue]; rfl

theorem instr_at_epilogue_S (n : ℕ) (pF : Program) :
    (minimize_program n pF)[epilogueStartPC n pF + 1]? =
      some (Instr.S (counter_reg n pF)) := by
  rw [epilogue_instr_setup n pF 1 (by omega), loopEpilogue]; rfl

theorem instr_at_epilogue_J1 (n : ℕ) (pF : Program) :
    (minimize_program n pF)[epilogueStartPC n pF + 2]? =
      some (Instr.J (zero_reg n pF) (zero_reg n pF) (loop_start_pc n)) := by
  rw [epilogue_instr_setup n pF 2 (by omega), loopEpilogue]; rfl

end Urm
