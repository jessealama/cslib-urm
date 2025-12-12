/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.PartialComp

/-! # Lemmas about Shifted Programs

This file contains lemmas about shifting jump targets and registers in programs.

## Main statements

- `Urm.Instr.shiftJumps_zero`: Shifting by 0 is the identity for instructions
- `Urm.Program.shiftJumps_zero`: Shifting by 0 is the identity for programs
- `Urm.Step.shiftJumps_getInstr`: Instruction lookup in shifted programs
- `Urm.Step.shiftRegisters_getInstr`: Instruction lookup in register-shifted programs
-/

namespace Urm

namespace Instr

/-- Shifting jump targets by 0 is the identity. -/
@[simp]
theorem shiftJumps_zero (i : Instr) : i.shiftJumps 0 = i := by
  cases i <;> simp [shiftJumps]

end Instr

namespace Program

/-- Shifting all jump targets in a program by 0 is the identity. -/
@[simp]
theorem shiftJumps_zero (p : Program) : p.shiftJumps 0 = p := by
  simp only [shiftJumps]
  induction p with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, Instr.shiftJumps_zero, ih]

end Program

namespace Step

variable {p : Program}

/-- If `i < p.length`, the instruction at `i` in the shifted program is the shifted instruction. -/
theorem shiftJumps_getInstr (offset : ℕ) (i : ℕ) (_hi : i < p.length) :
    (p.shiftJumps offset).getInstr i = (p.getInstr i).map (Instr.shiftJumps offset) := by
  simp only [Program.shiftJumps, Program.getInstr, List.getElem?_map]

theorem shiftRegisters_getInstr (offset : ℕ) (i : ℕ) (_hi : i < p.length) :
    (p.shiftRegisters offset).getInstr i = (p.getInstr i).map (Instr.shiftRegisters offset) := by
  simp only [Program.shiftRegisters, Program.getInstr, List.getElem?_map]

end Step

end Urm
