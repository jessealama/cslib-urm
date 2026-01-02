/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.Base
import Urm.Composition.Core

/-! # Program Construction for Minimization

This file constructs the witness program for minimization.

## Program Structure

```
[Setup Phase]
  copyRegisterRange 0 (savedStart) n    -- save inputs
  Z counter                             -- counter := 0
  Z zero                                -- zero register := 0

[Loop Start] (PC = setupLen)
  clearRegisters base                   -- clear working space
  copyRegisterRange savedStart 0 n      -- restore inputs
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
def setupPhaseLength (n : ℕ) : ℕ := n + 2

/-- Length of loop prologue: clear (base+1) registers + copy n registers + transfer. -/
def loopPrologueLength (n : ℕ) (pF : Program) : ℕ :=
  (minimizationBase n pF + 1) + n + 1

/-- PC where loop starts (after setup). -/
def loopStartPC (n : ℕ) : ℕ := setupPhaseLength n

/-- Offset for shifting pF's jumps. -/
def pFOffset (n : ℕ) (pF : Program) : ℕ :=
  setupPhaseLength n + loopPrologueLength n pF

/-- PC of output phase (after loop body). -/
def outputPC (n : ℕ) (pF : Program) : ℕ :=
  pFOffset n pF + pF.length + 3

/-! ## Program phases -/

/-- Setup phase: save inputs, initialize counter and zero register. -/
def setupPhase (n : ℕ) (pF : Program) : Program :=
  copyRegisterRange 0 (savedInputsStart n pF) n ++
  [Instr.Z (counterReg n pF), Instr.Z (zeroReg n pF)]

/-- Loop prologue: clear working space, restore inputs, set R[n] to counter. -/
def loopPrologue (n : ℕ) (pF : Program) : Program :=
  clearRegisters (minimizationBase n pF) ++
  copyRegisterRange (savedInputsStart n pF) 0 n ++
  [Instr.T (counterReg n pF) n]

/-- Loop epilogue: check result, increment counter, jump back. -/
def loopEpilogue (n : ℕ) (pF : Program) : Program :=
  [Instr.J 0 (zeroReg n pF) (outputPC n pF),
   Instr.S (counterReg n pF),
   Instr.J (zeroReg n pF) (zeroReg n pF) (loopStartPC n)]

/-- Output phase: copy counter to R[0]. -/
def outputPhase (n : ℕ) (pF : Program) : Program :=
  [Instr.T (counterReg n pF) 0]

/-- The complete minimization witness program. -/
def minimizeProgram (n : ℕ) (pF : Program) : Program :=
  setupPhase n pF ++
  loopPrologue n pF ++
  pF.shiftJumps (pFOffset n pF) ++
  loopEpilogue n pF ++
  outputPhase n pF

/-! ## Length lemmas -/

theorem setupPhase_length (n : ℕ) (pF : Program) :
    (setupPhase n pF).length = setupPhaseLength n := by
  simp only [setupPhase, setupPhaseLength, List.length_append, copyRegisterRange_length, List.length]

theorem loopPrologue_length (n : ℕ) (pF : Program) :
    (loopPrologue n pF).length = loopPrologueLength n pF := by
  simp only [loopPrologue, loopPrologueLength, List.length_append,
    clearRegisters_length, copyRegisterRange_length, List.length]

theorem loopEpilogue_length (n : ℕ) (pF : Program) :
    (loopEpilogue n pF).length = 3 := by
  simp only [loopEpilogue, List.length]

theorem outputPhase_length (n : ℕ) (pF : Program) :
    (outputPhase n pF).length = 1 := by
  simp only [outputPhase, List.length]

theorem minimizeProgram_length (n : ℕ) (pF : Program) :
    (minimizeProgram n pF).length = outputPC n pF + 1 := by
  simp only [minimizeProgram, outputPC, pFOffset, List.length_append,
    setupPhase_length, loopPrologue_length, shiftJumps_length,
    loopEpilogue_length, outputPhase_length, setupPhaseLength, loopPrologueLength]

/-! ## PC position lemmas -/

theorem loopStartPC_eq (n : ℕ) (pF : Program) :
    loopStartPC n = (setupPhase n pF).length := by
  simp only [loopStartPC, setupPhase_length]

theorem pFOffset_eq (n : ℕ) (pF : Program) :
    pFOffset n pF = (setupPhase n pF).length + (loopPrologue n pF).length := by
  simp only [pFOffset, setupPhase_length, loopPrologue_length]

theorem outputPC_eq (n : ℕ) (pF : Program) :
    outputPC n pF = (setupPhase n pF).length + (loopPrologue n pF).length +
                    pF.length + (loopEpilogue n pF).length := by
  simp only [outputPC, pFOffset, setupPhase_length, loopPrologue_length, loopEpilogue_length,
    setupPhaseLength, loopPrologueLength]

/-! ## Program structure helpers -/

/-- The loop body (prologue + pF + epilogue). -/
def loopBody (n : ℕ) (pF : Program) : Program :=
  loopPrologue n pF ++ pF.shiftJumps (pFOffset n pF) ++ loopEpilogue n pF

theorem loopBody_length (n : ℕ) (pF : Program) :
    (loopBody n pF).length = loopPrologueLength n pF + pF.length + 3 := by
  simp only [loopBody, List.length_append, loopPrologue_length,
    shiftJumps_length, loopEpilogue_length]

theorem minimizeProgram_eq_setup_loop_output (n : ℕ) (pF : Program) :
    minimizeProgram n pF = setupPhase n pF ++ loopBody n pF ++ outputPhase n pF := by
  simp only [minimizeProgram, loopBody, List.append_assoc]

end Urm
