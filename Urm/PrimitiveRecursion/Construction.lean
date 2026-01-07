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
  copyRegisterRange 0 savedStart (n+1)    -- save inputs including y
  Z counter                               -- counter := 0
  Z zero                                  -- zero register := 0

[Base Case Phase]
  clearRegisters base                     -- clear working space
  copyRegisterRange savedStart 0 n        -- restore x₁,...,xₙ
  pF (shifted)                            -- execute base case
  T 0 accumulator                         -- save result

[Loop Check] (PC = loopCheckPC)
  J counter savedY outputPC               -- if counter = y, exit loop

[Loop Body]
  clearRegisters base                     -- clear working space
  copyRegisterRange savedStart 0 n        -- restore x₁,...,xₙ
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
def prSetupPhaseLength (n : ℕ) : ℕ := (n + 1) + 2

/-- Length of base case prologue: clear (base+1) registers + copy n registers. -/
def prBaseCasePrologueLength (n : ℕ) (pF pG : Program) : ℕ :=
  (primitiveRecursionBase n pF pG + 1) + n

/-- Length of base case phase: prologue + pF + transfer to accumulator. -/
def prBaseCasePhaseLength (n : ℕ) (pF pG : Program) : ℕ :=
  prBaseCasePrologueLength n pF pG + pF.length + 1

/-- Length of loop prologue: clear (base+1) + copy n + 2 transfers. -/
def prLoopPrologueLength (n : ℕ) (pF pG : Program) : ℕ :=
  (primitiveRecursionBase n pF pG + 1) + n + 2

/-- Length of loop epilogue: transfer + increment + unconditional jump. -/
def prLoopEpilogueLength : ℕ := 3

/-- Length of loop body: prologue + pG + epilogue. -/
def prLoopBodyLength (n : ℕ) (pF pG : Program) : ℕ :=
  prLoopPrologueLength n pF pG + pG.length + prLoopEpilogueLength

/-! ## PC positions -/

/-- PC where base case phase starts (after setup). -/
def prBaseCasePC (n : ℕ) : ℕ := prSetupPhaseLength n

/-- PC where loop check happens (after base case). -/
def prLoopCheckPC (n : ℕ) (pF pG : Program) : ℕ :=
  prSetupPhaseLength n + prBaseCasePhaseLength n pF pG

/-- PC where loop body starts (after loop check). -/
def prLoopBodyPC (n : ℕ) (pF pG : Program) : ℕ :=
  prLoopCheckPC n pF pG + 1

/-- Offset for shifting pF's jumps. -/
def prPFOffset (n : ℕ) (pF pG : Program) : ℕ :=
  prSetupPhaseLength n + prBaseCasePrologueLength n pF pG

/-- Offset for shifting pG's jumps. -/
def prPGOffset (n : ℕ) (pF pG : Program) : ℕ :=
  prLoopBodyPC n pF pG + prLoopPrologueLength n pF pG

/-- PC of output phase (after loop body). -/
def prOutputPC (n : ℕ) (pF pG : Program) : ℕ :=
  prLoopBodyPC n pF pG + prLoopBodyLength n pF pG

/-! ## Program phases -/

/-- Setup phase: save inputs (including y), initialize counter and zero register. -/
def prSetupPhase (n : ℕ) (pF pG : Program) : Program :=
  copyRegisterRange 0 (prSavedInputsStart n pF pG) (n + 1) ++
  [Instr.Z (prCounterReg n pF pG), Instr.Z (prZeroReg n pF pG)]

/-- Base case prologue: clear working space, restore x₁,...,xₙ. -/
def prBaseCasePrologue (n : ℕ) (pF pG : Program) : Program :=
  clearRegisters (primitiveRecursionBase n pF pG) ++
  copyRegisterRange (prSavedInputsStart n pF pG) 0 n

/-- Base case phase: prologue + pF + save result to accumulator. -/
def prBaseCasePhase (n : ℕ) (pF pG : Program) : Program :=
  prBaseCasePrologue n pF pG ++
  pF.shiftJumps (prPFOffset n pF pG) ++
  [Instr.T 0 (prAccumulatorReg n pF pG)]

/-- Loop check: jump to output if counter = savedY. -/
def prLoopCheck (n : ℕ) (pF pG : Program) : Program :=
  [Instr.J (prCounterReg n pF pG) (prSavedYReg n pF pG) (prOutputPC n pF pG)]

/-- Loop prologue: clear working space, restore inputs, set up pG inputs. -/
def prLoopPrologue (n : ℕ) (pF pG : Program) : Program :=
  clearRegisters (primitiveRecursionBase n pF pG) ++
  copyRegisterRange (prSavedInputsStart n pF pG) 0 n ++
  [Instr.T (prCounterReg n pF pG) n,
   Instr.T (prAccumulatorReg n pF pG) (n + 1)]

/-- Loop epilogue: save result, increment counter, jump back. -/
def prLoopEpilogue (n : ℕ) (pF pG : Program) : Program :=
  [Instr.T 0 (prAccumulatorReg n pF pG),
   Instr.S (prCounterReg n pF pG),
   Instr.J (prZeroReg n pF pG) (prZeroReg n pF pG) (prLoopCheckPC n pF pG)]

/-- Loop body: prologue + pG + epilogue. -/
def prLoopBody (n : ℕ) (pF pG : Program) : Program :=
  prLoopPrologue n pF pG ++
  pG.shiftJumps (prPGOffset n pF pG) ++
  prLoopEpilogue n pF pG

/-- Output phase: copy accumulator to R[0]. -/
def prOutputPhase (n : ℕ) (pF pG : Program) : Program :=
  [Instr.T (prAccumulatorReg n pF pG) 0]

/-- The complete primitive recursion witness program. -/
def primitiveRecursionProgram (n : ℕ) (pF pG : Program) : Program :=
  prSetupPhase n pF pG ++
  prBaseCasePhase n pF pG ++
  prLoopCheck n pF pG ++
  prLoopBody n pF pG ++
  prOutputPhase n pF pG

/-! ## Length lemmas -/

@[simp] theorem prSetupPhase_length (n : ℕ) (pF pG : Program) :
    (prSetupPhase n pF pG).length = prSetupPhaseLength n := by
  simp only [prSetupPhase, prSetupPhaseLength, List.length_append,
    copyRegisterRange_length, List.length]

@[simp] theorem prBaseCasePrologue_length (n : ℕ) (pF pG : Program) :
    (prBaseCasePrologue n pF pG).length = prBaseCasePrologueLength n pF pG := by
  simp only [prBaseCasePrologue, prBaseCasePrologueLength, List.length_append,
    clearRegisters_length, copyRegisterRange_length]

@[simp] theorem prBaseCasePhase_length (n : ℕ) (pF pG : Program) :
    (prBaseCasePhase n pF pG).length = prBaseCasePhaseLength n pF pG := by
  simp only [prBaseCasePhase, prBaseCasePhaseLength, List.length_append,
    prBaseCasePrologue_length, shiftJumps_length, List.length]

@[simp] theorem prLoopCheck_length (n : ℕ) (pF pG : Program) :
    (prLoopCheck n pF pG).length = 1 := by
  simp only [prLoopCheck, List.length]

@[simp] theorem prLoopPrologue_length (n : ℕ) (pF pG : Program) :
    (prLoopPrologue n pF pG).length = prLoopPrologueLength n pF pG := by
  simp only [prLoopPrologue, prLoopPrologueLength, List.length_append,
    clearRegisters_length, copyRegisterRange_length, List.length]

@[simp] theorem prLoopEpilogue_length (n : ℕ) (pF pG : Program) :
    (prLoopEpilogue n pF pG).length = prLoopEpilogueLength := by
  simp only [prLoopEpilogue, prLoopEpilogueLength, List.length]

@[simp] theorem prLoopBody_length (n : ℕ) (pF pG : Program) :
    (prLoopBody n pF pG).length = prLoopBodyLength n pF pG := by
  simp only [prLoopBody, prLoopBodyLength, List.length_append,
    prLoopPrologue_length, shiftJumps_length, prLoopEpilogue_length]

@[simp] theorem prOutputPhase_length (n : ℕ) (pF pG : Program) :
    (prOutputPhase n pF pG).length = 1 := by
  simp only [prOutputPhase, List.length]

@[simp] theorem primitiveRecursionProgram_length (n : ℕ) (pF pG : Program) :
    (primitiveRecursionProgram n pF pG).length = prOutputPC n pF pG + 1 := by
  simp only [primitiveRecursionProgram, prOutputPC, prLoopBodyPC, prLoopCheckPC,
    prSetupPhaseLength, prBaseCasePhaseLength, prLoopBodyLength,
    List.length_append, prSetupPhase_length, prBaseCasePhase_length,
    prLoopCheck_length, prLoopBody_length, prOutputPhase_length]

/-! ## PC position lemmas -/

theorem prLoopBodyPC_eq (n : ℕ) (pF pG : Program) :
    prLoopBodyPC n pF pG = (prSetupPhase n pF pG).length +
      (prBaseCasePhase n pF pG).length + (prLoopCheck n pF pG).length := by
  simp only [prLoopBodyPC, prLoopCheckPC, prSetupPhase_length,
    prBaseCasePhase_length, prLoopCheck_length]

/-! ## Key instruction access lemmas -/

/-- The loop check instruction is a J comparing counter to savedY. -/
theorem instr_at_loopCheck (n : ℕ) (pF pG : Program) :
    (primitiveRecursionProgram n pF pG).getInstr (prLoopCheckPC n pF pG) =
      some (Instr.J (prCounterReg n pF pG) (prSavedYReg n pF pG) (prOutputPC n pF pG)) := by
  simp only [primitiveRecursionProgram, getInstr, prLoopCheckPC, prLoopCheck,
    List.getElem?_append, List.length_append, prSetupPhase_length, prBaseCasePhase_length]
  simp only [prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength]
  simp only [List.length] at *
  split_ifs with h1 h2 h3 h4
  · omega
  · omega
  · simp only [Nat.sub_self, List.getElem?_cons_zero]
  · omega
  · omega

/-- The output instruction is a T copying accumulator to R[0]. -/
theorem instr_at_output (n : ℕ) (pF pG : Program) :
    (primitiveRecursionProgram n pF pG).getInstr (prOutputPC n pF pG) =
      some (Instr.T (prAccumulatorReg n pF pG) 0) := by
  simp only [primitiveRecursionProgram, getInstr, prOutputPC, prLoopBodyPC, prLoopCheckPC,
    prOutputPhase, List.getElem?_append, List.length_append, prSetupPhase_length,
    prBaseCasePhase_length, prLoopCheck_length, prLoopBody_length]
  simp only [prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength,
    prLoopBodyLength, prLoopPrologueLength, prLoopEpilogueLength]
  split_ifs with h1 h2 h3 h4
  · omega
  · omega
  · omega
  · omega
  · simp only [Nat.sub_self, List.getElem?_cons_zero]

end Urm
