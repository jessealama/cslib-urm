/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable

/-! # Sequential Composition of URM Programs

This file defines sequential composition of URM programs.

## Main definitions

- `Urm.Program.seq`: Sequential composition of URM programs
-/

namespace Urm

namespace Program

/-- Sequential composition of programs: run `p1`, then run `p2`.
Jump targets in `p2` are shifted by `p1.length` so they remain valid. -/
def seq (p1 p2 : Program) : Program :=
  p1 ++ p2.shiftJumps p1.length

@[simp]
theorem seq_length (p1 p2 : Program) : (p1.seq p2).length = p1.length + p2.length := by
  simp [seq, shiftJumps]

theorem seq_getInstr_first (p1 p2 : Program) (i : ℕ) (hi : i < p1.length) :
    (p1.seq p2).getInstr i = p1.getInstr i := by
  simp only [seq, getInstr, List.getElem?_append_left hi]

theorem seq_getInstr_second (p1 p2 : Program) (i : ℕ) (hi : p1.length ≤ i)
    (_hi' : i < p1.length + p2.length) :
    (p1.seq p2).getInstr i = (p2.shiftJumps p1.length).getInstr (i - p1.length) := by
  simp only [seq, getInstr, List.getElem?_append_right hi, shiftJumps, List.getElem?_map]

end Program

end Urm
