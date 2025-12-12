/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Seq

/-! # Register Operations for URM Programs

This file defines basic register operations: copy and zero.

## Main definitions

- `Urm.copyReg`: Copy a single register value
- `Urm.copyRegs`: Copy consecutive registers
- `Urm.zeroReg`: Zero out a register
-/

namespace Urm

/-- Copy a single register value from `src` to `dst`. -/
def copyReg (src dst : ℕ) : Program := [Instr.T src dst]

/-- Copy `n` consecutive registers starting from `srcBase` to `dstBase`.
Copies srcBase → dstBase, srcBase+1 → dstBase+1, ..., srcBase+(n-1) → dstBase+(n-1). -/
def copyRegs (n : ℕ) (srcBase dstBase : ℕ) : Program :=
  (List.finRange n).map fun i => Instr.T (srcBase + i.val) (dstBase + i.val)

@[simp]
theorem copyRegs_length (n srcBase dstBase : ℕ) : (copyRegs n srcBase dstBase).length = n := by
  simp [copyRegs]

/-- The instruction at position i in copyRegs is T (srcBase + i) (dstBase + i). -/
theorem copyRegs_getInstr (n srcBase dstBase : ℕ) (i : ℕ) (hi : i < n) :
    (copyRegs n srcBase dstBase).getInstr i = some (Instr.T (srcBase + i) (dstBase + i)) := by
  simp only [copyRegs, Program.getInstr, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp; exact hi)]
  simp [List.getElem_finRange]

/-- Zero out a single register. -/
def zeroReg (n : ℕ) : Program := [Instr.Z n]

end Urm
