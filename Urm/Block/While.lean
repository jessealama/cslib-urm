/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Block.Basic
import Urm.Block.Compile
import Urm.Block.Glue
import Urm.StraightLine
import Urm.Halting.PhaseExecution
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Computability.Partrec

/-! # While Loop Combinator for URMBlock

This file defines a `while` loop combinator that repeatedly executes a body block
until its output (R[0]) equals 0. This abstracts the common loop pattern used in
both minimization and primitive recursion.

## Semantics

Starting from inputs `x = (x₀, ..., x_{n-1})`:
1. Save inputs to preserved registers
2. Initialize counter to 0
3. Loop:
   a. Clear workspace
   b. Restore saved inputs to R[0..n-1]
   c. Copy counter to R[n]
   d. Execute body (which reads inputs and counter, writes result to R[0])
   e. If R[0] = 0, exit loop; otherwise increment counter and repeat
4. Copy the result register value to R[0]

## Register Layout

```
[0..n-1]                           : original inputs (only used in setup phase)
[base..base+n-1]                   : body's input registers (restored each iteration)
[base+n]                           : body's counter input (set from loop counter)
[base..base+maxReg]                : body block's full workspace (includes inputs)
[base+maxReg+1]                    : loop counter (incremented each iteration)
[base+maxReg+2]                    : zero register (always 0, for J comparisons)
[base+maxReg+3..base+maxReg+n+2]   : saved original inputs (preserved across iterations)
```

Note: The body is compiled with shiftRegisters(base), so the body's R[i] maps to
host's R[base+i]. The body expects inputs at its R[0..n-1] and counter at R[n],
which means host's R[base..base+n-1] and R[base+n].

CRITICAL: Counter, zero, and saved inputs are placed AFTER base+maxReg to ensure
they are not clobbered by body execution (which may use registers up to base+maxReg).

## Main Definitions

- `WhileSpec`: Specification of a while loop (body, arity, result register)
- `whileProgram`: The URM program implementing the while loop
- `URMBlock.while`: The while combinator producing a URMBlock

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

namespace URMBlock

open Program

/-! ## While Loop Specification -/

/-- Specification of a while loop.
- `body`: the block executed each iteration (takes n+1 inputs: x and counter)
- `n`: number of preserved inputs
- `resultReg`: which register to read result from when loop exits (typically the counter) -/
structure WhileSpec where
  /-- The block executed each iteration. Takes n+1 inputs where input n is the counter. -/
  body : URMBlock
  /-- Number of preserved inputs (not including the counter). -/
  n : ℕ
  /-- Register to read final result from on loop exit.
      For minimization, this is the counter register.
      For primitive recursion, this is the accumulator register. -/
  resultReg : ℕ

/-! ## Base Computation -/

/-- The base offset for a while loop.
Must be large enough to accommodate body's input space and maxReg. -/
def whileBase (spec : WhileSpec) : ℕ :=
  max spec.n spec.body.maxReg

/-! ## Register Indices -/

/-- Counter register (tracks current iteration).
    Placed after body's full workspace to avoid overlap with body execution. -/
def whileCounterReg (spec : WhileSpec) : ℕ :=
  whileBase spec + spec.body.maxReg + 1

/-- Zero register (always 0, for J comparisons).
    Placed after counter, outside body's workspace. -/
def whileZeroReg (spec : WhileSpec) : ℕ :=
  whileBase spec + spec.body.maxReg + 2

/-- Start of saved inputs R[base+maxReg+3..base+maxReg+n+2].
    Placed after counter and zero to avoid overlap with body's workspace. -/
def whileSavedInputsStart (spec : WhileSpec) : ℕ :=
  whileBase spec + spec.body.maxReg + 3

/-! ## Base Bound Lemmas -/

theorem whileBase_ge_n (spec : WhileSpec) :
    spec.n ≤ whileBase spec := le_max_left _ _

theorem whileBase_ge_body (spec : WhileSpec) :
    spec.body.maxReg ≤ whileBase spec := le_max_right _ _

-- Note: body_maxReg_ge_n theorem removed; spec.n ≤ spec.body.maxReg
-- must now be provided as an explicit hypothesis where needed.

/-! ## Length Calculations -/

/-- Length of setup phase: copy n registers + zero counter + zero zeroReg. -/
def whileSetupLength (spec : WhileSpec) : ℕ := spec.n + 2

/-- Length of loop prologue: clear (maxReg+1) registers + copy n + transfer counter. -/
def whileLoopPrologueLength (spec : WhileSpec) : ℕ :=
  (spec.body.maxReg + 1) + spec.n + 1

/-- Length of loop epilogue: check exit + increment + unconditional jump. -/
def whileLoopEpilogueLength : ℕ := 3

/-! ## PC Positions -/

/-- PC where loop starts (after setup). -/
def whileLoopStartPC (spec : WhileSpec) : ℕ := whileSetupLength spec

/-- Offset for body.compile within the loop. -/
def whileBodyOffset (spec : WhileSpec) : ℕ :=
  whileSetupLength spec + whileLoopPrologueLength spec

/-- PC of output phase. -/
def whileOutputPC (spec : WhileSpec) : ℕ :=
  whileBodyOffset spec + spec.body.program.length + whileLoopEpilogueLength

/-! ## Program Phases -/

/-- Setup phase: save inputs, initialize counter and zero register.
Copies inputs from R[0..n-1] to saved area, zeros counter and zeroReg. -/
def whileSetupPhase (spec : WhileSpec) : Program :=
  (copyRegisterRange 0 (whileSavedInputsStart spec) spec.n).concat
    [Instr.Z (whileCounterReg spec), Instr.Z (whileZeroReg spec)]

/-- Loop prologue: clear body workspace, restore inputs to body's register range, set body's R[n] to counter.
Prepares state for body execution. Since body is compiled with shiftRegisters(base),
inputs must be at R[base..base+n-1] and counter at R[base+n].
The workspace R[base..base+maxReg] is cleared first, then inputs and counter are set. -/
def whileLoopPrologue (spec : WhileSpec) : Program :=
  (clearRegistersFrom (whileBase spec) (spec.body.maxReg + 1)).concat (
    (copyRegisterRange (whileSavedInputsStart spec) (whileBase spec) spec.n).concat
      [Instr.T (whileCounterReg spec) (whileBase spec + spec.n)])

/-- Loop epilogue: check result, increment counter, jump back.
If R[base] = 0, exit to output; otherwise increment counter and loop. -/
def whileLoopEpilogue (spec : WhileSpec) : Program :=
  [Instr.J (whileBase spec) (whileZeroReg spec) (whileOutputPC spec),
   Instr.S (whileCounterReg spec),
   Instr.J (whileZeroReg spec) (whileZeroReg spec) (whileLoopStartPC spec)]

/-- Output phase: copy result register to R[0]. -/
def whileOutputPhase (spec : WhileSpec) : Program :=
  [Instr.T spec.resultReg 0]

/-- The complete while loop program. -/
def whileProgram (spec : WhileSpec) : Program :=
  (whileSetupPhase spec).concat (
    (whileLoopPrologue spec).concat (
      (spec.body.compile (whileBase spec)).concat (
        (whileLoopEpilogue spec).concat
          (whileOutputPhase spec))))

/-! ## Length Lemmas -/

@[simp] theorem whileSetupPhase_length (spec : WhileSpec) :
    (whileSetupPhase spec).length = whileSetupLength spec := by
  simp only [whileSetupPhase, whileSetupLength, concat_length, copyRegisterRange_length,
    List.length_cons, List.length_nil]

@[simp] theorem whileLoopPrologue_length (spec : WhileSpec) :
    (whileLoopPrologue spec).length = whileLoopPrologueLength spec := by
  simp only [whileLoopPrologue, whileLoopPrologueLength, concat_length, clearRegistersFrom_length,
    copyRegisterRange_length, List.length_singleton]
  omega

@[simp] theorem whileLoopEpilogue_length :
    (whileLoopEpilogue spec).length = whileLoopEpilogueLength := by
  simp [whileLoopEpilogue, whileLoopEpilogueLength]

@[simp] theorem whileOutputPhase_length (spec : WhileSpec) :
    (whileOutputPhase spec).length = 1 := rfl

@[simp] theorem whileProgram_length (spec : WhileSpec) :
    (whileProgram spec).length = whileOutputPC spec + 1 := by
  simp only [whileProgram, whileOutputPC, whileBodyOffset, concat_length,
    whileSetupPhase_length, whileLoopPrologue_length, compile_length,
    whileLoopEpilogue_length, whileOutputPhase_length]
  omega

/-! ## Straight-Line Properties -/

/-- shiftJumps preserves isNonJumping status for each instruction. -/
private theorem shiftJumps_preserves_isStraightLine (p : Program) (offset : ℕ) :
    p.isStraightLine = true → (p.shiftJumps offset).isStraightLine = true := by
  simp only [Program.isStraightLine, shiftJumps]
  intro h
  rw [List.all_map]
  simp only [List.all_eq_true] at h ⊢
  intro x hx
  have hx' := h x hx
  cases x with
  | Z n => rfl
  | S n => rfl
  | T m n => rfl
  | J m n q => simp [Instr.isNonJumping] at hx'

/-- Concatenation of straight-line programs is straight-line. -/
private theorem concat_isStraightLine (p1 p2 : Program)
    (h1 : p1.isStraightLine = true) (h2 : p2.isStraightLine = true) :
    (p1.concat p2).isStraightLine = true := by
  simp only [concat, Program.isStraightLine, List.all_append, Bool.and_eq_true]
  exact ⟨h1, shiftJumps_preserves_isStraightLine p2 p1.length h2⟩

theorem whileSetupPhase_isStraightLine (spec : WhileSpec) :
    (whileSetupPhase spec).isStraightLine = true := by
  simp only [whileSetupPhase]
  apply concat_isStraightLine
  · exact copyRegisterRange_isStraightLine 0 (whileSavedInputsStart spec) spec.n
  · rfl

theorem whileLoopPrologue_isStraightLine (spec : WhileSpec) :
    (whileLoopPrologue spec).isStraightLine = true := by
  simp only [whileLoopPrologue]
  apply concat_isStraightLine
  · exact clearRegistersFrom_isStraightLine (whileBase spec) (spec.body.maxReg + 1)
  · apply concat_isStraightLine
    · exact copyRegisterRange_isStraightLine (whileSavedInputsStart spec) (whileBase spec) spec.n
    · rfl

/-! ## Embedding Lemmas

These lemmas show how each phase of the while program is embedded within the
concatenated whileProgram structure. They are essential for using the phase
execution infrastructure from `Urm.Halting.PhaseExecution`. -/

/-- whileLoopPrologue is embedded in whileProgram at offset whileLoopStartPC.
    This is the key embedding lemma needed for using execPhaseInHost. -/
theorem whileLoopPrologue_embed (spec : WhileSpec) :
    ∀ i, i < (whileLoopPrologue spec).length →
    (whileProgram spec).getInstr (whileLoopStartPC spec + i) = (whileLoopPrologue spec).getInstr i := by
  intro i hi
  simp only [whileProgram, whileLoopStartPC, whileSetupLength, Program.getInstr, concat]
  rw [List.getElem?_append_right (by simp [whileSetupPhase_length, whileSetupLength])]
  simp only [whileSetupPhase_length, whileSetupLength, Nat.add_sub_cancel_left]
  rw [shiftJumps, List.getElem?_map]
  have hi' : i < (whileLoopPrologue spec).length := hi
  rw [List.getElem?_append_left hi']
  simp only [List.getElem?_eq_getElem hi']
  have hsl := whileLoopPrologue_isStraightLine spec
  simp only [Program.isStraightLine, List.all_eq_true] at hsl
  simp only [Option.map_some, Instr.shiftJumps_of_isNonJumping (hsl _ (List.getElem_mem hi'))]

/-- body.compile is embedded in whileProgram at offset whileBodyOffset.
    Note: The embedded body has shiftJumps applied from concat nesting.
    compile uses shiftRegisters which shifts registers; concat adds shiftJumps for jump targets. -/
theorem whileBody_embed (spec : WhileSpec) :
    ∀ i, i < spec.body.program.length →
    (whileProgram spec).getInstr (whileBodyOffset spec + i) =
      ((spec.body.compile (whileBase spec)).shiftJumps (whileBodyOffset spec)).getInstr i := by
  intro i hi
  have hSetup : (whileSetupPhase spec).length = whileSetupLength spec := whileSetupPhase_length spec
  have hPrologue : (whileLoopPrologue spec).length = whileLoopPrologueLength spec :=
    whileLoopPrologue_length spec
  have hCompile : (spec.body.compile (whileBase spec)).length = spec.body.program.length :=
    compile_length spec.body (whileBase spec)
  simp only [whileProgram, whileBodyOffset, Program.getInstr, concat]
  -- Skip past whileSetupPhase (first concat)
  rw [List.getElem?_append_right (by simp only [hSetup, whileSetupLength]; omega)]
  simp only [hSetup]
  -- The remaining program is (loopPrologue.concat rest).shiftJumps setupLen
  simp only [shiftJumps, List.getElem?_map]
  -- Skip past loopPrologue in the shifted program
  rw [List.getElem?_append_right (by simp only [hPrologue, whileSetupLength]; omega)]
  simp only [List.getElem?_map, hPrologue]
  -- Now in body.compile.concat rest
  have hi' : whileSetupLength spec + whileLoopPrologueLength spec + i - whileSetupLength spec -
      whileLoopPrologueLength spec = i := by simp only [whileSetupLength]; omega
  rw [hi']
  -- Access body.compile at index i (concat is already expanded to ++ with shiftJumps)
  have hi'' : i < (spec.body.compile (whileBase spec)).length := by rw [hCompile]; exact hi
  rw [List.getElem?_append_left hi'']
  simp only [List.getElem?_eq_getElem hi'', Option.map_some, Option.map_some]
  -- Now show the two sides match
  -- LHS: instr.shiftJumps prologueLen |>.shiftJumps setupLen
  -- RHS: instr.shiftJumps (setupLen + prologueLen)
  congr 1
  -- shiftJumps is additive: (i.shiftJumps a).shiftJumps b = i.shiftJumps (a + b)
  -- Prove by case analysis on the instruction
  cases hinstr : (spec.body.compile (whileBase spec))[i] with
  | Z n => rfl
  | S n => rfl
  | T m n => rfl
  | J m n q =>
    simp only [Instr.shiftJumps, whileSetupLength, whileLoopPrologueLength]
    congr 1
    omega

/-! ## Maximum Register Bounds -/

/-- Maximum register used by the while program. -/
def whileMaxReg (spec : WhileSpec) : ℕ :=
  -- Highest register is the last saved input at base + maxReg + 3 + (n - 1) = base + maxReg + n + 2
  -- When n = 0, there are no saved inputs, so highest is zeroReg = base + maxReg + 2
  -- When n > 0, highest is base + maxReg + n + 2
  whileBase spec + spec.body.maxReg + spec.n + 2

theorem whileProgram_maxRegister (spec : WhileSpec)
    (hresult : spec.resultReg ≤ whileMaxReg spec) :
    (whileProgram spec).maxRegister ≤ max (whileMaxReg spec) (2 * whileBase spec) := by
  -- Unfold whileProgram and apply concat_maxRegister repeatedly
  simp only [whileProgram, concat_maxRegister]
  -- Now we have max of maxRegisters of each phase
  -- Need to show each phase's maxRegister is bounded
  apply Nat.max_le.mpr
  constructor
  · -- whileSetupPhase
    simp only [whileSetupPhase, concat_maxRegister]
    apply Nat.max_le.mpr
    constructor
    · -- copyRegisterRange 0 savedInputsStart n
      have h := copyRegisterRange_maxRegister 0 (whileSavedInputsStart spec) spec.n
      by_cases hn : spec.n = 0
      · simp only [hn, ↓reduceIte] at h ⊢
        calc (copyRegisterRange 0 (whileSavedInputsStart spec) 0).maxRegister
            ≤ 0 := h
          _ ≤ max (whileMaxReg spec) (2 * whileBase spec) := by omega
      · simp only [hn, ↓reduceIte] at h
        calc (copyRegisterRange 0 (whileSavedInputsStart spec) spec.n).maxRegister
            ≤ max (0 + spec.n - 1) (whileSavedInputsStart spec + spec.n - 1) := h
          _ ≤ max (whileMaxReg spec) (2 * whileBase spec) := by
            simp only [whileSavedInputsStart, whileMaxReg, whileBase]
            omega
    · -- [Z counterReg, Z zeroReg]
      simp only [Program.maxRegister, List.foldl_cons, List.foldl_nil, Instr.maxRegister]
      simp only [whileCounterReg, whileZeroReg, whileMaxReg, whileBase]
      omega
  · -- Rest of program: loopPrologue.concat (body.compile.concat (loopEpilogue.concat outputPhase))
    apply Nat.max_le.mpr
    constructor
    · -- whileLoopPrologue
      simp only [whileLoopPrologue, concat_maxRegister]
      apply Nat.max_le.mpr
      constructor
      · -- clearRegistersFrom base (maxReg + 1)
        rw [clearRegistersFrom_maxRegister]
        -- count = spec.body.maxReg + 1 ≥ 1, so result = base + (maxReg + 1) - 1 = base + maxReg
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        simp only [whileMaxReg, whileBase]
        omega
      · -- copyRegisterRange savedInputsStart 0 n then [T counterReg n]
        apply Nat.max_le.mpr
        constructor
        · have h := copyRegisterRange_maxRegister (whileSavedInputsStart spec) (whileBase spec) spec.n
          by_cases hn : spec.n = 0
          · simp only [hn, ↓reduceIte] at h ⊢
            calc (copyRegisterRange (whileSavedInputsStart spec) (whileBase spec) 0).maxRegister
                ≤ 0 := h
              _ ≤ max (whileMaxReg spec) (2 * whileBase spec) := by omega
          · simp only [hn, ↓reduceIte] at h
            calc (copyRegisterRange (whileSavedInputsStart spec) (whileBase spec) spec.n).maxRegister
                ≤ max (whileSavedInputsStart spec + spec.n - 1) (whileBase spec + spec.n - 1) := h
              _ ≤ max (whileMaxReg spec) (2 * whileBase spec) := by
                simp only [whileSavedInputsStart, whileMaxReg, whileBase]
                omega
        · -- [T counterReg (base + n)]
          simp only [Program.maxRegister, List.foldl_cons, List.foldl_nil, Instr.maxRegister]
          simp only [whileCounterReg, whileMaxReg, whileBase]
          omega
    · -- body.compile base then epilogue then output
      apply Nat.max_le.mpr
      constructor
      · -- body.compile base
        by_cases hemp : spec.body.program = []
        · simp only [compile, hemp, Program.shiftRegisters, Program.maxRegister, List.map_nil,
            List.foldl_nil]
          omega
        · rw [compile_maxRegister spec.body (whileBase spec) hemp]
          -- Note: maxReg = program.maxRegister, so whileBase ≥ program.maxRegister
          have hprog_le_base : spec.body.program.maxRegister ≤ whileBase spec := by
            simp only [whileBase, maxReg]
            exact le_max_right _ _
          calc spec.body.program.maxRegister + whileBase spec
              ≤ whileBase spec + whileBase spec := by omega
            _ = 2 * whileBase spec := by omega
            _ ≤ max (whileMaxReg spec) (2 * whileBase spec) := le_max_right _ _
      · -- epilogue then output
        apply Nat.max_le.mpr
        constructor
        · -- whileLoopEpilogue
          simp only [whileLoopEpilogue, Program.maxRegister, List.foldl_cons, List.foldl_nil,
            Instr.maxRegister]
          simp only [whileZeroReg, whileCounterReg, whileMaxReg, whileBase,
            whileSetupLength, whileBodyOffset, whileLoopPrologueLength]
          omega
        · -- whileOutputPhase
          simp only [whileOutputPhase, Program.maxRegister, List.foldl_cons, List.foldl_nil,
            Instr.maxRegister]
          simp only [whileMaxReg] at hresult ⊢
          omega

/-! ## The While Combinator -/

/-- While loop combinator: repeatedly execute body until R[0] = 0.

Given a body : URMBlock with arity n+1 (takes x and counter), produces a block
with arity n that finds the least k where body(x, k) = 0 and returns
the value from resultReg at that point.

For minimization (μ-recursion): resultReg = whileCounterReg spec
For primitive recursion with bounded iteration: similar pattern -/
def while' (spec : WhileSpec)
    (hbody_arity : spec.body.arity = spec.n + 1)
    (hresult_bounded : spec.resultReg ≤ whileMaxReg spec) : URMBlock where
  program := whileProgram spec
  arity := spec.n
  h_sf := by
    -- The while program is standard form if the body is
    -- All jumps are either within the program or to the virtual halt position
    -- TODO: Prove this properly using body's h_sf and the structure of the while program
    sorry

/-! ## Loop Iteration Result Types -/

/-- Result of a single while loop iteration.
Either we exit (body returned 0) or continue (body returned non-zero). -/
inductive WhileIterationOutcome (spec : WhileSpec) where
  | exit (counter : ℕ)   -- Loop exits with counter value
  | continue (counter : ℕ) -- Loop continues with incremented counter

/-- Complete result of a single iteration. -/
structure WhileIterationResult (spec : WhileSpec) (inputs : Fin spec.n → ℕ) (s : State) (k : ℕ)
    (bodyFunc : (Fin (spec.n + 1) → ℕ) → Part ℕ) where
  /-- Final configuration after one iteration -/
  config : Config
  /-- Steps taken during this iteration -/
  steps : Steps (whileProgram spec) ⟨whileLoopStartPC spec, s⟩ config
  /-- The value body wrote to R[0] (result of body(inputs, k)) -/
  bodyResult : ℕ
  /-- Either we exited to output, or we're back at loop start with incremented counter -/
  outcome : (config.pc = whileOutputPC spec ∧ bodyResult = 0) ∨
            (config.pc = whileLoopStartPC spec ∧ config.state.read (whileCounterReg spec) = k + 1 ∧ bodyResult ≠ 0)
  /-- In continue case, zeroReg is preserved -/
  zeroPreserved : bodyResult ≠ 0 → config.state.read (whileZeroReg spec) = s.read (whileZeroReg spec)
  /-- In continue case, savedInputs are preserved -/
  savedPreserved : bodyResult ≠ 0 → ∀ i : Fin spec.n,
    config.state.read (whileSavedInputsStart spec + i) = s.read (whileSavedInputsStart spec + i)
  /-- In exit case, counter is preserved equal to k -/
  counterPreservedExit : bodyResult = 0 → config.state.read (whileCounterReg spec) = k
  /-- The halting hypothesis for body on extended inputs -/
  hBodyHalts : Halts spec.body.program (List.ofFn (Fin.snoc inputs k))
  /-- bodyResult equals the Result from body execution -/
  bodyResultEq : bodyResult = Result spec.body.program (List.ofFn (Fin.snoc inputs k)) hBodyHalts

/-- Result of k iterations of the while loop. -/
structure WhileKIterationsResult (spec : WhileSpec) (inputs : Fin spec.n → ℕ)
    (s : State) (iterations : ℕ) (finalCounter : ℕ)
    (bodyFunc : (Fin (spec.n + 1) → ℕ) → Part ℕ) where
  /-- Final configuration after k iterations -/
  config : Config
  /-- Steps taken during all iterations -/
  steps : Steps (whileProgram spec) ⟨whileLoopStartPC spec, s⟩ config
  /-- Invariant: counter equals finalCounter -/
  counterEq : config.state.read (whileCounterReg spec) = finalCounter
  /-- Invariant: zeroReg is 0 -/
  zeroEq : config.state.read (whileZeroReg spec) = 0
  /-- Invariant: savedInputs are preserved -/
  savedEq : ∀ i : Fin spec.n, config.state.read (whileSavedInputsStart spec + i) = inputs i
  /-- The PC is either at loop start (more iterations needed) or output (exit found) -/
  pcLocation : config.pc = whileLoopStartPC spec ∨ config.pc = whileOutputPC spec

/-! ## Prologue Helper Lemmas -/

/-- Counter register is above the prologue write range.
    Requires maxReg >= n for register disjointness. -/
theorem whileCounterReg_gt_prologue_writes (spec : WhileSpec)
    (hn_maxReg : spec.n ≤ spec.body.maxReg) :
    whileCounterReg spec > whileBase spec + spec.n := by
  simp only [whileCounterReg, whileBase]
  omega

/-- Zero register is above the prologue write range.
    Requires maxReg >= n for register disjointness. -/
theorem whileZeroReg_gt_prologue_writes (spec : WhileSpec)
    (hn_maxReg : spec.n ≤ spec.body.maxReg) :
    whileZeroReg spec > whileBase spec + spec.n := by
  simp only [whileZeroReg, whileBase]
  omega

/-- After executing whileLoopPrologue, high registers (counter, zero, saved) are preserved.
    These registers are above the write range of the prologue.
    Requires maxReg >= n for register disjointness. -/
theorem whileLoopPrologue_preserves_high (spec : WhileSpec) (s : State)
    (hn_maxReg : spec.n ≤ spec.body.maxReg) :
    let s' := straightLineFinalState (whileLoopPrologue_isStraightLine spec) s
    -- Counter preserved
    s'.read (whileCounterReg spec) = s.read (whileCounterReg spec) ∧
    -- Zero register preserved
    s'.read (whileZeroReg spec) = s.read (whileZeroReg spec) ∧
    -- Saved inputs preserved
    (∀ i : Fin spec.n, s'.read (whileSavedInputsStart spec + i) = s.read (whileSavedInputsStart spec + i)) := by
  intro s'
  have hsl := whileLoopPrologue_isStraightLine spec
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  -- Need maxReg >= n to prove register disjointness
  have hmaxReg := hn_maxReg
  -- Counter = base + maxReg + 1, Zero = base + maxReg + 2
  -- SavedInputs = base + maxReg + 3 .. base + maxReg + n + 2
  -- Prologue writes: clearRegisters (0..base), copyRegisterRange (base..base+n-1), T (base+n)
  -- All target registers are > base + n (since maxReg >= n), so they're preserved
  refine ⟨?_, ?_, ?_⟩
  · -- Counter preserved (at base + maxReg + 1, prologue writes up to base + n)
    apply Steps.straightLine_preserves hsl hsteps
    intro instr hinstr
    simp only [whileLoopPrologue, concat, List.mem_append, shiftJumps, List.mem_map] at hinstr
    rcases hinstr with hclear | ⟨instr', hrest, heq⟩
    · simp only [Program.clearRegistersFrom, List.mem_map, List.mem_range] at hclear
      obtain ⟨j, hj, rfl⟩ := hclear
      simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileCounterReg, whileBase] at hj ⊢
      -- writes to base + j where j < maxReg + 1, counter = base + maxReg + 1
      omega
    · -- hrest is already a disjunction, no simp needed
      rcases hrest with hcopy | ⟨a, ha, heq'⟩
      · simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
        obtain ⟨j, hj, rfl⟩ := hcopy
        -- instr' is now T (savedInputsStart + j) (base + j)
        -- shiftJumps doesn't change T instructions
        simp only [Instr.shiftJumps] at heq; subst heq
        simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileCounterReg, whileBase] at hj ⊢
        -- writes to base + j where j < n, counter = base + maxReg + 1 > base + n > base + j
        omega
      · simp only [List.mem_singleton] at ha; subst ha
        simp only [Instr.shiftJumps] at heq'
        subst heq'
        simp only [Instr.shiftJumps] at heq; subst heq
        simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileCounterReg, whileBase]
        -- writes to base + n, counter = base + maxReg + 1 > base + n (since maxReg >= n)
        omega
  · -- Zero register preserved (at base + maxReg + 2, prologue writes up to base + maxReg)
    apply Steps.straightLine_preserves hsl hsteps
    intro instr hinstr
    simp only [whileLoopPrologue, concat, List.mem_append, shiftJumps, List.mem_map] at hinstr
    rcases hinstr with hclear | ⟨instr', hrest, heq⟩
    · simp only [Program.clearRegistersFrom, List.mem_map, List.mem_range] at hclear
      obtain ⟨j, hj, rfl⟩ := hclear
      simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileZeroReg, whileBase] at hj ⊢
      -- writes to base + j where j < maxReg + 1, zero = base + maxReg + 2
      omega
    · -- hrest is already a disjunction, no simp needed
      rcases hrest with hcopy | ⟨a, ha, heq'⟩
      · simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
        obtain ⟨j, hj, rfl⟩ := hcopy
        -- instr' is now T (savedInputsStart + j) (base + j)
        simp only [Instr.shiftJumps] at heq; subst heq
        simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileZeroReg, whileBase] at hj ⊢
        omega
      · simp only [List.mem_singleton] at ha; subst ha
        simp only [Instr.shiftJumps] at heq'
        subst heq'
        simp only [Instr.shiftJumps] at heq; subst heq
        simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileZeroReg, whileBase]
        omega
  · -- Saved inputs preserved (at base + maxReg + 3 + i, prologue writes up to base + n)
    intro i
    apply Steps.straightLine_preserves hsl hsteps
    intro instr hinstr
    simp only [whileLoopPrologue, concat, List.mem_append, shiftJumps, List.mem_map] at hinstr
    rcases hinstr with hclear | ⟨instr', hrest, heq⟩
    · simp only [Program.clearRegistersFrom, List.mem_map, List.mem_range] at hclear
      obtain ⟨j, hj, rfl⟩ := hclear
      simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileSavedInputsStart, whileBase] at hj ⊢
      -- clearRegistersFrom writes to base + j where j < maxReg + 1
      -- savedInputs start at base + maxReg + 3 > base + maxReg > base + j
      omega
    · -- hrest is already a disjunction, no simp needed
      rcases hrest with hcopy | ⟨a, ha, heq'⟩
      · simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
        obtain ⟨j, hj, rfl⟩ := hcopy
        -- instr' is now T (savedInputsStart + j) (base + j)
        simp only [Instr.shiftJumps] at heq; subst heq
        simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileSavedInputsStart, whileBase] at hj ⊢
        -- copyRegisterRange writes to base + j where j < n
        -- savedInputs at base + maxReg + 3 + i > base + n > base + j
        omega
      · simp only [List.mem_singleton] at ha; subst ha
        simp only [Instr.shiftJumps] at heq'
        subst heq'
        simp only [Instr.shiftJumps] at heq; subst heq
        simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileSavedInputsStart, whileBase]
        -- T writes to base + n
        -- savedInputs start at base + maxReg + 3 > base + n (since maxReg >= n)
        omega

/-! ## Body Input Setup -/

/-- After executing whileLoopPrologue, the body's input registers are set up correctly:
    - Body inputs (base..base+n-1) contain the saved inputs
    - Body counter input (base+n) contains the loop counter -/
theorem whileLoopPrologue_sets_body_inputs (spec : WhileSpec) (s : State) (k : ℕ)
    (inputs : Fin spec.n → ℕ)
    (hn_maxReg : spec.n ≤ spec.body.maxReg)
    (hs_counter : s.read (whileCounterReg spec) = k)
    (hs_saved : ∀ i : Fin spec.n, s.read (whileSavedInputsStart spec + i) = inputs i) :
    let s' := straightLineFinalState (whileLoopPrologue_isStraightLine spec) s
    -- Body inputs set from saved
    (∀ i : Fin spec.n, s'.read (whileBase spec + i) = inputs i) ∧
    -- Body counter input set from loop counter
    s'.read (whileBase spec + spec.n) = k := by
  intro s'
  have hsl := whileLoopPrologue_isStraightLine spec
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  have hmaxReg := hn_maxReg
  -- Calculate lengths for position reasoning
  have hclear_len : (clearRegistersFrom (whileBase spec) (spec.body.maxReg + 1)).length = spec.body.maxReg + 1 :=
    clearRegistersFrom_length _ _
  have hcopy_len : (copyRegisterRange (whileSavedInputsStart spec) (whileBase spec) spec.n).length = spec.n :=
    copyRegisterRange_length _ _ _
  have hprologue_len : (whileLoopPrologue spec).length = spec.body.maxReg + 1 + spec.n + 1 := by
    simp only [whileLoopPrologue_length, whileLoopPrologueLength]
  constructor
  · -- Body inputs set from saved (via copyRegisterRange)
    intro i
    -- The T instruction at position (maxReg+1) + i copies savedInputsStart+i to base+i
    let instrPos := spec.body.maxReg + 1 + i.val
    have hpos_lt : instrPos < (whileLoopPrologue spec).length := by
      simp only [instrPos, hprologue_len]; omega
    -- Get the instruction at that position
    have hinstr : (whileLoopPrologue spec)[instrPos] =
        Instr.T (whileSavedInputsStart spec + i.val) (whileBase spec + i.val) := by
      simp only [whileLoopPrologue, concat, List.getElem_append, hclear_len, instrPos]
      have h1 : ¬(spec.body.maxReg + 1 + i.val < spec.body.maxReg + 1) := by omega
      simp only [h1, ↓reduceDIte, shiftJumps, List.getElem_map, List.getElem_append, hcopy_len]
      have h2 : spec.body.maxReg + 1 + i.val - (spec.body.maxReg + 1) < spec.n := by omega
      simp only [h2, ↓reduceDIte, Program.copyRegisterRange, List.getElem_map, List.getElem_range,
        Instr.shiftJumps]
      have hi_eq : spec.body.maxReg + 1 + i.val - (spec.body.maxReg + 1) = i.val := by omega
      simp only [hi_eq]
    -- No later instruction writes to base + i
    have hnowrite : ∀ j (hj : j < (whileLoopPrologue spec).length), instrPos < j →
        ((whileLoopPrologue spec)[j]'hj).writesTo ≠ some (whileBase spec + i.val) := by
      intro j hj hinstr_lt
      simp only [whileLoopPrologue, concat, List.getElem_append, hclear_len, hprologue_len] at hj ⊢
      have hj_not_clear : ¬(j < spec.body.maxReg + 1) := by simp only [instrPos] at hinstr_lt; omega
      simp only [hj_not_clear, ↓reduceDIte, shiftJumps, List.getElem_map, List.getElem_append, hcopy_len]
      by_cases hj_copy : j - (spec.body.maxReg + 1) < spec.n
      · simp only [hj_copy, ↓reduceDIte, Program.copyRegisterRange, List.getElem_map,
          List.getElem_range, Instr.shiftJumps, Instr.writesTo, ne_eq, Option.some.injEq]
        simp only [instrPos] at hinstr_lt
        omega
      · simp only [hj_copy, ↓reduceDIte, List.getElem_singleton, Instr.shiftJumps, Instr.writesTo,
          ne_eq, Option.some.injEq]
        omega
    -- Use straightLine_transfer_result
    obtain ⟨s_before, ⟨c, hsteps_c, _, hs_before_eq⟩, hread_eq⟩ :=
      straightLine_transfer_result hsl s instrPos (whileSavedInputsStart spec + i.val)
        (whileBase spec + i.val) hpos_lt hinstr hnowrite
    rw [hread_eq, ← hs_before_eq]
    -- Show that savedInputsStart + i has the original value at time of execution
    have hsrc_preserved : c.state.read (whileSavedInputsStart spec + i.val) =
        s.read (whileSavedInputsStart spec + i.val) := by
      apply Steps.straightLine_preserves hsl hsteps_c
      intro instr hmem
      simp only [whileLoopPrologue, concat, List.mem_append, shiftJumps, List.mem_map] at hmem
      rcases hmem with hclear | ⟨instr', hrest, heq⟩
      · -- instr is from clearRegistersFrom: zeros registers base..base+maxReg
        simp only [Program.clearRegistersFrom, List.mem_map, List.mem_range] at hclear
        obtain ⟨r, hr, rfl⟩ := hclear
        simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileSavedInputsStart, whileBase,
          Nat.max_eq_right hmaxReg]
        -- writes to base + r where r < maxReg + 1
        -- savedInputs start at base + maxReg + 3
        omega
      · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hrest
        rcases hrest with hcopy | ⟨a, ha_eq, ha_shift⟩
        · -- instr' is from copyRegisterRange: writes to base..base+n-1
          simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
          obtain ⟨r, hr, rfl⟩ := hcopy
          simp only [Instr.shiftJumps] at heq; subst heq
          simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileSavedInputsStart, whileBase,
            Nat.max_eq_right hmaxReg]
          omega
        · -- a is the final T
          subst ha_eq; simp only [Instr.shiftJumps] at ha_shift; subst ha_shift
          simp only [Instr.shiftJumps] at heq; subst heq
          simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileSavedInputsStart,
            whileBase, whileCounterReg, Nat.max_eq_right hmaxReg]
          omega
    rw [hsrc_preserved, hs_saved i]
  · -- Body counter input set from counter (via T counterReg (base + n))
    let instrPos := spec.body.maxReg + 1 + spec.n
    have hpos_lt : instrPos < (whileLoopPrologue spec).length := by
      simp only [instrPos, hprologue_len]; omega
    -- Get the instruction at that position (the last one)
    have hinstr : (whileLoopPrologue spec)[instrPos] =
        Instr.T (whileCounterReg spec) (whileBase spec + spec.n) := by
      simp only [whileLoopPrologue, concat, List.getElem_append, hclear_len, instrPos]
      have h1 : ¬(spec.body.maxReg + 1 + spec.n < spec.body.maxReg + 1) := by omega
      simp only [h1, ↓reduceDIte, shiftJumps, List.getElem_map, List.getElem_append, hcopy_len]
      have h2 : ¬(spec.body.maxReg + 1 + spec.n - (spec.body.maxReg + 1) < spec.n) := by omega
      simp only [h2, ↓reduceDIte, List.getElem_singleton, Instr.shiftJumps]
    -- No later instruction (this is the last one)
    have hnowrite : ∀ j (hj : j < (whileLoopPrologue spec).length), instrPos < j →
        ((whileLoopPrologue spec)[j]'hj).writesTo ≠ some (whileBase spec + spec.n) := by
      intro j hj hinstr_lt
      simp only [instrPos, hprologue_len] at hj hinstr_lt
      omega
    -- Use straightLine_transfer_result
    obtain ⟨s_before, ⟨c, hsteps_c, _, hs_before_eq⟩, hread_eq⟩ :=
      straightLine_transfer_result hsl s instrPos (whileCounterReg spec)
        (whileBase spec + spec.n) hpos_lt hinstr hnowrite
    rw [hread_eq, ← hs_before_eq]
    -- Show that counterReg has the original value at time of execution
    have hsrc_preserved : c.state.read (whileCounterReg spec) = s.read (whileCounterReg spec) := by
      apply Steps.straightLine_preserves hsl hsteps_c
      intro instr hmem
      simp only [whileLoopPrologue, concat, List.mem_append, shiftJumps, List.mem_map] at hmem
      rcases hmem with hclear | ⟨instr', hrest, heq⟩
      · simp only [Program.clearRegistersFrom, List.mem_map, List.mem_range] at hclear
        obtain ⟨r, hr, rfl⟩ := hclear
        simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileCounterReg, whileBase,
          Nat.max_eq_right hmaxReg]
        -- writes to base + r where r < maxReg + 1, counter = base + maxReg + 1
        omega
      · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hrest
        rcases hrest with hcopy | ⟨a, ha_eq, ha_shift⟩
        · simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
          obtain ⟨r, hr, rfl⟩ := hcopy
          simp only [Instr.shiftJumps] at heq; subst heq
          simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileCounterReg, whileBase,
            Nat.max_eq_right hmaxReg]
          omega
        · subst ha_eq; simp only [Instr.shiftJumps] at ha_shift; subst ha_shift
          simp only [Instr.shiftJumps] at heq; subst heq
          simp only [Instr.writesTo, ne_eq, Option.some.injEq, whileCounterReg, whileBase,
            Nat.max_eq_right hmaxReg]
          omega
    rw [hsrc_preserved, hs_counter]

/-! ## Body Execution Helper -/

/-- Standard form is preserved under shiftRegisters.
    shiftRegisters only changes register numbers, not jump targets, so hasBoundedJump is preserved. -/
theorem Program.IsStandardForm.shiftRegisters {p : Program} (hsf : p.IsStandardForm) (offset : ℕ) :
    (p.shiftRegisters offset).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm at hsf ⊢
  simp only [Program.shiftRegisters, List.all_map]
  rw [List.all_eq_true] at hsf ⊢
  intro instr hinstr
  have horiginal := hsf instr hinstr
  -- shiftRegisters preserves length
  simp only [Program.shiftRegisters, List.length_map]
  -- hasBoundedJump only depends on jump targets, not register numbers
  cases instr with
  | Z n => simp [Instr.shiftRegisters, Instr.hasBoundedJump]
  | S n => simp [Instr.shiftRegisters, Instr.hasBoundedJump]
  | T m n => simp [Instr.shiftRegisters, Instr.hasBoundedJump]
  | J m n q =>
    simp only [Instr.shiftRegisters, Instr.hasBoundedJump] at horiginal ⊢
    exact horiginal

/-- Execute the prologue phase within the while program.
    Starting from loopStartPC with state s, reaches bodyOffset with body inputs set up. -/
noncomputable def execWhilePrologue (spec : WhileSpec) (s : State) :
    PhaseExecutionResult (whileProgram spec) (whileLoopPrologue spec) (whileLoopStartPC spec) s :=
  execPhaseInHost (whileLoopPrologue_isStraightLine spec) (whileLoopStartPC spec)
    (whileLoopPrologue_embed spec) s

/-- After executing the prologue, we're at the body offset. -/
theorem execWhilePrologue_pc (spec : WhileSpec) (s : State) :
    whileLoopStartPC spec + (whileLoopPrologue spec).length = whileBodyOffset spec := by
  simp only [whileLoopStartPC, whileBodyOffset, whileSetupLength, whileLoopPrologue_length,
    whileLoopPrologueLength]

/-! ## Body Input Agreement -/

/-- After executing the prologue, the state agrees with body's expected inputs.
    This is the key lemma for using Halts.shift_from_state to execute the body. -/
theorem whileLoopPrologue_body_agreement (spec : WhileSpec) (s : State) (k : ℕ)
    (inputs : Fin spec.n → ℕ)
    (hn_maxReg : spec.n ≤ spec.body.maxReg)
    (hs_counter : s.read (whileCounterReg spec) = k)
    (hs_saved : ∀ i : Fin spec.n, s.read (whileSavedInputsStart spec + i) = inputs i) :
    let s' := straightLineFinalState (whileLoopPrologue_isStraightLine spec) s
    ∀ r, r ≤ spec.body.program.maxRegister →
        s'.read (r + whileBase spec) = (List.ofFn (Fin.snoc inputs k)).getD r 0 := by
  intro s' r hr
  -- Note: maxReg = program.maxRegister by definition
  have hr_maxReg : r ≤ spec.body.maxReg := hr
  have hmaxReg_ge_n := hn_maxReg
  have hprologue_inputs := whileLoopPrologue_sets_body_inputs spec s k inputs hn_maxReg hs_counter hs_saved
  -- Case split: r < n (input), r = n (counter), r > n (workspace, cleared to 0)
  by_cases hr_input : r < spec.n
  · -- r is an input register: body expects inputs[r]
    have hr_lt_len : r < spec.n + 1 := Nat.lt_succ_of_lt hr_input
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hr_lt_len, Option.getD_some]
    -- Fin.snoc at position r < n gives inputs r
    simp only [Fin.snoc, dif_pos hr_input, Fin.castLT]
    have h := hprologue_inputs.1 ⟨r, hr_input⟩
    simp only [Fin.val_mk] at h
    rw [Nat.add_comm] at h
    convert h using 2
  · push_neg at hr_input
    by_cases hr_n : r = spec.n
    · -- r = n: body expects k (the counter)
      subst hr_n
      have hn_lt : spec.n < spec.n + 1 := Nat.lt_succ_self _
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hn_lt, Option.getD_some]
      -- ⟨spec.n, hn_lt⟩ is the last element, Fin.snoc gives k
      have hnn : ¬ (spec.n < spec.n) := Nat.lt_irrefl _
      simp only [Fin.snoc, Fin.val_mk, dif_neg hnn]
      have h := hprologue_inputs.2
      rw [Nat.add_comm] at h
      exact h
    · -- r > n: workspace register, cleared to 0
      have hr_gt_n : r > spec.n := Nat.lt_of_le_of_ne hr_input (Ne.symm hr_n)
      have hr_ge_len : r ≥ spec.n + 1 := hr_gt_n
      have hr_out : ¬(r < spec.n + 1) := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg hr_out, Option.getD_none]
      -- The prologue clears R[base..base+maxReg], so R[base + r] = 0 for r > n
      have hr_in_clear : r < spec.body.maxReg + 1 := Nat.lt_succ_of_le hr_maxReg
      have hsl := whileLoopPrologue_isStraightLine spec
      -- Position r in the prologue is the Z instruction that clears base + r
      have hk_lt : r < (whileLoopPrologue spec).length := by
        simp only [whileLoopPrologue_length, whileLoopPrologueLength]; omega
      have hwrite : (whileLoopPrologue spec)[r] = Instr.Z (whileBase spec + r) := by
        simp only [whileLoopPrologue, concat, List.getElem_append]
        have hclear_len : (clearRegistersFrom (whileBase spec) (spec.body.maxReg + 1)).length =
            spec.body.maxReg + 1 := clearRegistersFrom_length _ _
        simp only [hclear_len]
        have h : r < spec.body.maxReg + 1 := hr_in_clear
        simp only [h, ↓reduceDIte, clearRegistersFrom, List.getElem_map, List.getElem_range]
      have hnowrite : ∀ j (hj : j < (whileLoopPrologue spec).length), r < j →
          ((whileLoopPrologue spec)[j]'hj).writesTo ≠ some (whileBase spec + r) := by
        intro j hj hj_gt
        simp only [whileLoopPrologue, concat, List.getElem_append] at hj ⊢
        have hclear_len : (clearRegistersFrom (whileBase spec) (spec.body.maxReg + 1)).length =
            spec.body.maxReg + 1 := clearRegistersFrom_length _ _
        by_cases hj_clear : j < spec.body.maxReg + 1
        · -- clearRegistersFrom case: instruction is Z (whileBase + j)
          simp only [hclear_len, hj_clear, ↓reduceDIte, clearRegistersFrom, List.getElem_map,
            List.getElem_range, List.length_map, List.length_range]
          simp only [Instr.writesTo]
          -- Goal: some (whileBase spec + j) ≠ some (whileBase spec + r)
          intro heq
          have : whileBase spec + j = whileBase spec + r := Option.some_injective _ heq
          omega
        · simp only [hclear_len, hj_clear, ↓reduceDIte, shiftJumps, List.getElem_map,
            List.getElem_append]
          have hcopy_len : (copyRegisterRange (whileSavedInputsStart spec) (whileBase spec) spec.n).length =
              spec.n := copyRegisterRange_length _ _ _
          by_cases hj_copy : j - (spec.body.maxReg + 1) < spec.n
          · -- copyRegisterRange case: instruction is T (saved + i) (base + i)
            simp only [hcopy_len, hj_copy, ↓reduceDIte, copyRegisterRange, List.getElem_map,
              List.getElem_range, List.length_map, List.length_range]
            simp only [Instr.shiftJumps, Instr.writesTo]
            -- Goal: some (whileBase spec + (j - (maxReg + 1))) ≠ some (whileBase spec + r)
            intro heq
            have : whileBase spec + (j - (spec.body.maxReg + 1)) = whileBase spec + r :=
              Option.some_injective _ heq
            have hj_ge : j ≥ spec.body.maxReg + 1 := Nat.not_lt.mp hj_clear
            omega
          · -- T instruction for counter
            simp only [hcopy_len, hj_copy, ↓reduceDIte, List.getElem_singleton]
            simp only [Instr.shiftJumps, Instr.writesTo]
            -- Goal: some (whileBase spec + spec.n) ≠ some (whileBase spec + r)
            intro heq
            have : whileBase spec + spec.n = whileBase spec + r := Option.some_injective _ heq
            omega
      have hzero := straightLine_zeros_register hsl s (whileBase spec + r) r hk_lt hwrite hnowrite
      simp only [whileBase, Nat.max_eq_right hn_maxReg] at hzero ⊢
      rw [Nat.add_comm r spec.body.maxReg]
      exact hzero

/-! ## Iteration Execution -/

/-- Execute one iteration of the while loop.
This is the key lemma that factors out the common loop iteration pattern
from both minimization and primitive recursion. -/
theorem while_single_iteration (spec : WhileSpec)
    (hbody_arity : spec.body.arity = spec.n + 1)
    (hn_maxReg : spec.n ≤ spec.body.maxReg)
    (hbody_sf : spec.body.program.IsStandardForm)
    (inputs : Fin spec.n → ℕ)
    (s : State)
    (k : ℕ)
    (hs_counter : s.read (whileCounterReg spec) = k)
    (hs_zero : s.read (whileZeroReg spec) = 0)
    (hs_saved : ∀ i : Fin spec.n, s.read (whileSavedInputsStart spec + i) = inputs i)
    (bodyFunc : (Fin (spec.n + 1) → ℕ) → Part ℕ)
    (hbody_computes : spec.body.ComputesN (spec.n + 1) bodyFunc)
    (hbody_dom : (bodyFunc (Fin.snoc inputs k)).Dom) :
    ∃ result : WhileIterationResult spec inputs s k bodyFunc, True := by
  -- High-level structure:
  -- 1. Execute prologue: s → s_prologue (sets up body inputs)
  -- 2. Execute body: s_prologue → s_body (computes bodyFunc)
  -- 3. Execute epilogue: s_body → s_final (exit or continue based on result)

  -- Get bodyResult from the function
  have hbody_halts : Halts spec.body.program (List.ofFn (Fin.snoc inputs k)) := by
    rw [(hbody_computes (Fin.snoc inputs k)).1]
    exact hbody_dom
  let bodyResult := Result spec.body.program (List.ofFn (Fin.snoc inputs k)) hbody_halts

  -- Case split on whether bodyResult = 0 (exit) or ≠ 0 (continue)
  by_cases hresult : bodyResult = 0
  · -- Exit case: body returned 0, jump to output
    -- Phase 1: Execute prologue - work with straightLineFinalState directly
    let hsl_prologue := whileLoopPrologue_isStraightLine spec
    let s_prologue := straightLineFinalState hsl_prologue s

    -- Get the prologue results: body inputs set up, high registers preserved
    have hprologue_high := whileLoopPrologue_preserves_high spec s hn_maxReg
    -- Counter, zero, saved are preserved
    have hs_prol_counter : s_prologue.read (whileCounterReg spec) = k := by
      exact hprologue_high.1 ▸ hs_counter
    have hs_prol_zero : s_prologue.read (whileZeroReg spec) = 0 := by
      exact hprologue_high.2.1 ▸ hs_zero

    -- Use the helper lemma for agreement condition
    have hagree := whileLoopPrologue_body_agreement spec s k inputs hn_maxReg hs_counter hs_saved

    -- Execute body using Halts.shift_from_state
    obtain ⟨c_body, hsteps_body, hhalted_body, hresult_body⟩ :=
      Halts.shift_from_state (whileBase spec) hbody_halts hagree

    -- The body result in R[base] equals bodyResult
    have hbody_result_base : c_body.state.read (whileBase spec) = bodyResult := hresult_body

    -- Phase 1 in whileProgram: Execute prologue using execWhilePrologue
    let prologueExec := execWhilePrologue spec s
    have hsteps_prologue_lifted := prologueExec.liftedSteps

    -- Phase 2 in whileProgram: Lift body steps using Steps.shiftJumps_at_offset
    -- Body is at offset whileBodyOffset in whileProgram
    have hbody_embed : ∀ i, i < (spec.body.compile (whileBase spec)).length →
        (whileProgram spec).getInstr (whileBodyOffset spec + i) =
        ((spec.body.compile (whileBase spec)).shiftJumps (whileBodyOffset spec)).getInstr i := by
      intro i hi
      rw [compile_length] at hi
      exact whileBody_embed spec i hi
    have hsteps_body_lifted := Steps.shiftJumps_at_offset (whileBodyOffset spec) hbody_embed hsteps_body

    -- Show that body halts at PC = body.program.length in the shifted program
    -- Use standard form property: when halted, pc = length
    have hbody_sf_shifted := Program.IsStandardForm.shiftRegisters hbody_sf (whileBase spec)
    have hbody_pc : c_body.pc = spec.body.program.length := by
      have h := Program.IsStandardForm.pc_eq_length_of_halted hbody_sf_shifted hsteps_body (Nat.zero_le _) hhalted_body
      simp only [Program.shiftRegisters_length] at h
      exact h

    -- Chain prologue and body steps
    -- Prologue: ⟨loopStartPC, s⟩ → ⟨loopStartPC + prologueLen, prologueExec.finalState⟩
    -- Body: ⟨bodyOffset, s_prologue⟩ → ⟨bodyOffset + body.length, c_body.state⟩
    -- We need: loopStartPC + prologueLen = bodyOffset
    have hprologue_to_body : whileLoopStartPC spec + (whileLoopPrologue spec).length = whileBodyOffset spec :=
      execWhilePrologue_pc spec s

    -- The prologue final state equals s_prologue
    have hprologue_state_eq : prologueExec.phaseResult.config.state = s_prologue := rfl

    -- Rewrite body steps to start from the prologue endpoint
    have hsteps_body_from_prologue : Steps (whileProgram spec)
        ⟨whileLoopStartPC spec + (whileLoopPrologue spec).length, prologueExec.phaseResult.config.state⟩
        ⟨whileBodyOffset spec + c_body.pc, c_body.state⟩ := by
      rw [hprologue_state_eq]
      convert hsteps_body_lifted using 2 <;> omega

    -- Chain the steps
    have hsteps_prologue_body := Relation.ReflTransGen.trans hsteps_prologue_lifted hsteps_body_from_prologue

    -- Phase 3: Execute J instruction to jump to output
    -- After body, we're at PC = bodyOffset + body.length
    -- The J instruction is at this position
    have hpc_after_body : whileBodyOffset spec + c_body.pc = whileBodyOffset spec + spec.body.program.length := by
      rw [hbody_pc]

    -- The J instruction: J base zeroReg outputPC
    -- This is the first instruction in whileLoopEpilogue, which starts right after body
    have hJ_instr : (whileProgram spec).getInstr (whileBodyOffset spec + spec.body.program.length) =
        some (Instr.J (whileBase spec) (whileZeroReg spec) (whileOutputPC spec)) := by
      -- The epilogue position is bodyOffset + body.length
      -- In whileProgram, the epilogue is embedded with shiftJumps applied
      -- The first instruction is J base zeroReg outputPC
      -- After shiftJumps, jump target is unchanged since outputPC is already absolute
      simp only [whileProgram, whileBodyOffset, whileOutputPC, whileSetupLength,
        whileLoopPrologueLength, whileLoopEpilogueLength, Program.getInstr, concat]
      -- We need to navigate through the nested structure
      -- Position = setupLen + prologueLen + body.length
      -- setupPhase.length = setupLen, so we skip it
      rw [List.getElem?_append_right (by simp only [whileSetupPhase_length, whileSetupLength]; omega)]
      simp only [whileSetupPhase_length, whileSetupLength, shiftJumps, List.getElem?_map]
      -- Now in (loopPrologue.concat rest).shiftJumps setupLen
      -- Position = setupLen + prologueLen + body.length - setupLen = prologueLen + body.length
      rw [List.getElem?_append_right (by simp only [whileLoopPrologue_length, whileLoopPrologueLength]; omega)]
      simp only [whileLoopPrologue_length, whileLoopPrologueLength, List.getElem?_map]
      -- Now in (body.compile.concat rest).shiftJumps prologueLen
      -- Position = prologueLen + body.length - prologueLen = body.length
      rw [List.getElem?_append_right (by simp only [compile_length]; omega)]
      simp only [compile_length, List.getElem?_map]
      -- Now in (epilogue.concat output).shiftJumps body.length
      -- Position = body.length - body.length = 0
      -- So we're at epilogue[0] = J base zeroReg outputPC
      have h0 : spec.n + 2 + (spec.body.maxReg + 1 + spec.n + 1) + spec.body.program.length -
          (spec.n + 2) - (spec.body.maxReg + 1 + spec.n + 1) - spec.body.program.length = 0 := by omega
      rw [h0]
      simp only [whileLoopEpilogue]
      -- First instruction in epilogue.concat output is epilogue[0]
      have hepilogue_len : ([Instr.J (whileBase spec) (whileZeroReg spec) (whileOutputPC spec),
                            Instr.S (whileCounterReg spec),
                            Instr.J (whileZeroReg spec) (whileZeroReg spec) (whileLoopStartPC spec)] : Program).length = 3 := rfl
      rw [List.getElem?_append_left (by simp only [hepilogue_len]; omega)]
      simp only [List.getElem?_cons_zero, Option.map_some, Instr.shiftJumps, Instr.shiftJumps, Instr.shiftJumps]
      -- After three shiftJumps: J target becomes J base zeroReg (outputPC + 0 + 0 + 0)
      -- But actually shiftJumps adds offset to jump target, not the instruction
      -- J base zeroReg outputPC after shiftJumps becomes J base zeroReg (outputPC + offset)
      -- We need to verify the final target equals whileOutputPC
      -- TODO: The program construction using nested concat causes incorrect jump target shifting.
      -- The epilogue's absolute jump targets get shifted multiple times by concat's shiftJumps.
      -- This needs a fix in whileProgram construction to either:
      -- 1. Use relative targets in epilogue that become correct after shifting, or
      -- 2. Construct the program manually without concat for epilogue/output phases
      sorry

    -- R[base] = bodyResult = 0 (exit case)
    have hbase_zero : c_body.state.read (whileBase spec) = 0 := by rw [hbody_result_base, hresult]

    -- R[zeroReg] = 0 is preserved through body execution
    -- Standard form body only writes to R[0..maxReg] when compiled at base, so zeroReg is preserved
    have hzero_preserved : c_body.state.read (whileZeroReg spec) = 0 := by
      -- zeroReg = base + maxReg + 2 is above the body's write range [base..base+maxReg]
      -- Body standard form + shiftRegisters means writes are in [base..base+maxReg]
      -- This is a consequence of standard form execution preserving higher registers
      -- For now, use the fact that body halts with result in R[base], preserving higher regs
      -- Since s_prologue.read zeroReg = 0 (from hs_prol_zero) and body only writes to ≤ base+maxReg
      have hzero_above : whileZeroReg spec > whileBase spec + spec.body.program.maxRegister := by
        -- maxReg = program.maxRegister, so whileZeroReg = base + maxReg + 2 > base + maxReg
        simp only [whileZeroReg, whileBase, maxReg]
        omega
      -- The body execution preserves registers above its write range
      -- Use Steps.register_preservation or similar
      sorry

    -- J instruction jumps to outputPC since R[base] = R[zeroReg] = 0
    have hJ_step : Step (whileProgram spec)
        ⟨whileBodyOffset spec + spec.body.program.length, c_body.state⟩
        ⟨whileOutputPC spec, c_body.state⟩ := by
      have hinstr := hJ_instr
      have heq : c_body.state.read (whileBase spec) = c_body.state.read (whileZeroReg spec) := by
        rw [hbase_zero, hzero_preserved]
      exact Step.jump_eq hinstr heq

    -- Chain all steps: prologue → body → J
    have hsteps_all := Relation.ReflTransGen.trans hsteps_prologue_body
      (hpc_after_body ▸ Relation.ReflTransGen.single hJ_step)

    -- Construct the result
    exact ⟨⟨
      ⟨whileOutputPC spec, c_body.state⟩,  -- config
      hsteps_all,  -- steps
      bodyResult,  -- bodyResult
      Or.inl ⟨rfl, hresult⟩,  -- outcome: exit case
      fun h => absurd hresult h,  -- zeroPreserved (vacuous for exit)
      fun h => absurd hresult h,  -- savedPreserved (vacuous for exit)
      fun _ => by  -- counterPreservedExit
        -- Counter = base + maxReg + 1 is above body's write range, so preserved
        have hcounter_above : whileCounterReg spec > whileBase spec + spec.body.program.maxRegister := by
          -- maxReg = program.maxRegister, so whileCounterReg = base + maxReg + 1 > base + maxReg
          simp only [whileCounterReg, whileBase, maxReg]
          omega
        sorry,  -- Similar preservation argument as zeroReg
      hbody_halts,  -- hBodyHalts
      rfl  -- bodyResultEq
    ⟩, trivial⟩
  · -- Continue case: body returned non-zero, increment counter and loop
    -- Similar structure to exit case, but:
    -- 1. After body, execute J (no jump since result ≠ 0)
    -- 2. Execute S counter
    -- 3. Execute J (unconditional jump back to loopStart)
    -- 4. Show counter = k+1 in final state
    -- 5. Show zero and saved registers preserved
    sorry

/-- Execute k iterations of the while loop starting from a state satisfying the invariants. -/
theorem while_k_iterations (spec : WhileSpec)
    (hbody_sf : spec.body.program.IsStandardForm)
    (inputs : Fin spec.n → ℕ)
    (s : State)
    (startCounter : ℕ)
    (hs_counter : s.read (whileCounterReg spec) = startCounter)
    (hs_zero : s.read (whileZeroReg spec) = 0)
    (hs_saved : ∀ i : Fin spec.n, s.read (whileSavedInputsStart spec + i) = inputs i)
    (bodyFunc : (Fin (spec.n + 1) → ℕ) → Part ℕ)
    (hbody_computes : spec.body.ComputesN (spec.n + 1) bodyFunc)
    (k : ℕ)
    -- All iterations from startCounter to startCounter + k - 1 have non-zero results
    (hall_nonzero : ∀ j, j < k → (bodyFunc (Fin.snoc inputs (startCounter + j))).Dom ∧
      ∃ v, (bodyFunc (Fin.snoc inputs (startCounter + j))) = Part.some v ∧ v ≠ 0) :
    ∃ result : WhileKIterationsResult spec inputs s k (startCounter + k) bodyFunc, True := by
  sorry

/-! ## Correctness -/

/-- The while function: repeatedly apply body until it returns 0, returning the value
of resultReg when it exits. -/
def whileFunction (spec : WhileSpec) (bodyFunc : (Fin (spec.n + 1) → ℕ) → Part ℕ)
    (resultFunc : (Fin spec.n → ℕ) → ℕ → ℕ) : (Fin spec.n → ℕ) → Part ℕ :=
  fun inputs =>
    -- Find least k such that bodyFunc(inputs, k) = 0
    (Nat.rfind fun k => (bodyFunc (Fin.snoc inputs k)).map (· == 0)).map
      (fun k => resultFunc inputs k)

/-- Specialized while function for minimization: resultFunc returns the counter. -/
def whileFunctionMin (spec : WhileSpec) (bodyFunc : (Fin (spec.n + 1) → ℕ) → Part ℕ) :
    (Fin spec.n → ℕ) → Part ℕ :=
  fun inputs =>
    Nat.rfind fun k => (bodyFunc (Fin.snoc inputs k)).map (· == 0)

/-- While loop correctness theorem.

If body computes bodyFunc, then the while combinator computes whileFunction
with the appropriate result extraction based on resultReg. -/
theorem while_correct (spec : WhileSpec)
    (hbody_arity : spec.body.arity = spec.n + 1)
    (hresult_bounded : spec.resultReg ≤ whileMaxReg spec)
    (hbody_sf : spec.body.program.IsStandardForm)
    (bodyFunc : (Fin (spec.n + 1) → ℕ) → Part ℕ)
    (hbody_computes : spec.body.ComputesN (spec.n + 1) bodyFunc)
    -- Result function: what value is in resultReg when loop exits at iteration k
    (resultFunc : (Fin spec.n → ℕ) → ℕ → ℕ)
    (hresult_spec : ∀ inputs k, (bodyFunc (Fin.snoc inputs k)) = Part.some 0 →
      -- When body returns 0 at iteration k, resultReg contains resultFunc inputs k
      True) : -- Placeholder for result register specification
    (URMBlock.while' spec hbody_arity hresult_bounded).ComputesN spec.n
      (whileFunction spec bodyFunc resultFunc) := by
  intro inputs
  simp only [whileFunction]
  constructor
  · -- Halting equivalence
    constructor
    · -- Forward: program halts → function defined
      intro hHalts
      sorry
    · -- Backward: function defined → program halts
      intro hDom
      sorry
  · -- Result correctness
    intro hHalts hDom
    sorry

/-! ## Specialized Correctness for Minimization -/

/-- For minimization, the result register is the counter register.
This gives us the μ-recursion combinator. -/
theorem while_correct_min (spec : WhileSpec)
    (hbody_arity : spec.body.arity = spec.n + 1)
    (hresult_is_counter : spec.resultReg = whileCounterReg spec)
    (hresult_bounded : spec.resultReg ≤ whileMaxReg spec)
    (hbody_sf : spec.body.program.IsStandardForm)
    (bodyFunc : (Fin (spec.n + 1) → ℕ) → Part ℕ)
    (hbody_computes : spec.body.ComputesN (spec.n + 1) bodyFunc) :
    (URMBlock.while' spec hbody_arity hresult_bounded).ComputesN spec.n
      (whileFunctionMin spec bodyFunc) := by
  intro inputs
  simp only [whileFunctionMin]
  constructor
  · -- Halting equivalence
    constructor
    · -- Forward: program halts → function defined
      intro hHalts
      sorry
    · -- Backward: function defined → program halts
      intro hDom
      sorry
  · -- Result correctness
    intro hHalts hDom
    sorry

end URMBlock

end Urm
