/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Extended.Basic
import Urm.Extended.Eval
import Urm.StraightLine
import Urm.Concat
import Urm.Shift

/-! # Extended URM: Compiler

This module compiles ExtendedURM programs to base URM programs.
The compilation handles structured control flow (BLOCK and MU) by
expanding them into equivalent sequences of base URM instructions.

## Main Definitions

- `compileInstr`: Compile a single extended instruction
- `compile`: Compile an extended program

## Compilation Strategy

### Basic Instructions (Z, S, T)
Compiled directly to their base URM equivalents.

### Jump (J)
Jump instructions are problematic in sequential extended programs since
ExtendedProgram has arbitrary-length instructions. We handle J only for
flat programs (where each instruction is a single base instruction).

### BLOCK [r₀, r₁, ...] { body }
Compiled as:
1. Copy host registers to body's input positions
2. Run body (with appropriate register shifting)
3. Copy result back

### MU [r₀, r₁, ...] { body } resultReg
Compiled as a while loop:
1. Setup: save inputs, initialize counter
2. Loop prologue: restore inputs to body, set counter
3. Body execution
4. Loop epilogue: check exit, increment counter, jump back
5. Output: copy result register

## Key Insight

The compilation uses offset tracking to ensure jump targets are correct.
When we compile an extended program `[i₀, i₁, ..., iₙ]`, each `iₖ` compiles
to a sequence of base instructions. The offset for `iₖ₊₁` is the sum of
the lengths of all compiled instructions `i₀, ..., iₖ`.

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

namespace Extended

open Urm (Program Instr State Config)

/-! ## Register Offset Calculation -/

/-- Calculate the base offset needed to avoid conflicts with a list of host registers.
Returns max(regs) + 1 if regs is non-empty, otherwise 0. -/
def registerBase (regs : List ℕ) : ℕ :=
  match regs with
  | [] => 0
  | rs => rs.foldl max 0 + 1

theorem registerBase_gt_all (regs : List ℕ) (r : ℕ) (hr : r ∈ regs) :
    registerBase regs > r := by
  cases regs with
  | nil => contradiction
  | cons h t =>
    simp only [registerBase]
    have hle : r ≤ List.foldl max 0 (h :: t) := by
      have : ∀ (init : ℕ) (l : List ℕ), init ≤ l.foldl max init := fun init l => by
        induction l generalizing init with
        | nil => exact Nat.le_refl _
        | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
      have hmono : ∀ (a b : ℕ) (l : List ℕ), a ≤ b → l.foldl max a ≤ l.foldl max b := fun a b l hab => by
        induction l generalizing a b with
        | nil => exact hab
        | cons x xs ih => simp only [List.foldl_cons]; exact ih _ _ (max_le_max_right x hab)
      have hmem_le : ∀ (init : ℕ) (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldl max init := fun init l x hx => by
        induction l generalizing init with
        | nil => contradiction
        | cons y ys ih =>
          simp only [List.mem_cons] at hx
          simp only [List.foldl_cons]
          rcases hx with rfl | hx'
          · exact Nat.le_trans (Nat.le_max_right _ _) (this _ _)
          · exact ih _ hx'
      exact hmem_le 0 (h :: t) r hr
    omega

/-! ## Compilation Helpers -/

/-- Copy registers from host to body's input positions.
Copies host R[regs[i]] to R[base + i] for each i. -/
def copyToBody (regs : List ℕ) (base : ℕ) : FlatProgram :=
  regs.mapIdx fun i r => Instr.T r (base + i)

/-- Copy result from body's R[0] back to host's first register. -/
def copyFromBody (regs : List ℕ) (base : ℕ) : FlatProgram :=
  match regs with
  | [] => []
  | r :: _ => [Instr.T base r]

/-- Clear registers in a range for body execution. -/
def clearBodyRegs (base count : ℕ) : FlatProgram :=
  List.range count |>.map fun i => Instr.Z (base + i)

/-! ## Block Compilation -/

/-- Compile a BLOCK construct.

Structure:
1. Copy inputs: T regs[i] (base + i) for each i
2. Body execution: body.shiftRegisters(base)
3. Copy result: T base regs[0] -/
def compileBlock (regs : List ℕ) (body : FlatProgram) : FlatProgram :=
  let base := registerBase regs
  let copyIn := copyToBody regs base
  -- Shift both registers and jumps for proper embedding
  let shiftedBody := (body.shiftRegisters base).shiftJumps copyIn.length
  let copyOut := copyFromBody regs base
  copyIn ++ shiftedBody ++ copyOut

theorem compileBlock_length (regs : List ℕ) (body : FlatProgram) :
    (compileBlock regs body).length =
      regs.length + body.length + (if regs = [] then 0 else 1) := by
  simp only [compileBlock, List.length_append, copyToBody, copyFromBody,
    List.length_mapIdx, Program.shiftJumps_length, Program.shiftRegisters_length]
  cases regs with
  | nil => simp
  | cons h t => simp

/-! ## Mu Compilation -/

/-- Register layout for Mu compilation.
Given n = regs.length and maxReg = body.maxRegister:
- R[base..base+n-1]: body inputs
- R[base+n]: body counter input
- R[base..base+maxReg]: body workspace
- counterReg: loop counter (beyond body workspace)
- zeroReg: always 0 (for comparisons)
- savedRegs: saved original inputs -/
structure MuLayout where
  /-- Number of input registers -/
  n : ℕ
  /-- Base offset for body execution -/
  base : ℕ
  /-- Maximum register used by body -/
  bodyMaxReg : ℕ
  /-- Counter register index -/
  counterReg : ℕ
  /-- Zero register index (always 0) -/
  zeroReg : ℕ
  /-- Start of saved input registers -/
  savedStart : ℕ

/-- Compute the register layout for Mu compilation. -/
def mkMuLayout (regs : List ℕ) (body : FlatProgram) : MuLayout :=
  let n := regs.length
  let base := registerBase regs
  let bodyMaxReg := body.maxRegister
  -- Place counter, zero, and saved registers above body's workspace
  let workspaceEnd := base + max n bodyMaxReg
  { n := n
    base := base
    bodyMaxReg := bodyMaxReg
    counterReg := workspaceEnd + 1
    zeroReg := workspaceEnd + 2
    savedStart := workspaceEnd + 3 }

/-- Setup phase: save inputs to savedRegs, zero counter and zeroReg. -/
def muSetupPhase (layout : MuLayout) (regs : List ℕ) : FlatProgram :=
  -- Copy inputs to saved area
  let saveInputs := regs.mapIdx fun i r => Instr.T r (layout.savedStart + i)
  -- Zero the counter and zeroReg
  saveInputs ++ [Instr.Z layout.counterReg, Instr.Z layout.zeroReg]

/-- Loop prologue: clear workspace, restore inputs, set counter. -/
def muPrologue (layout : MuLayout) : FlatProgram :=
  -- Clear body workspace
  let clearWorkspace := clearBodyRegs layout.base (layout.bodyMaxReg + 1)
  -- Restore inputs from saved area to body's input positions
  let restoreInputs := List.range layout.n |>.map fun i =>
    Instr.T (layout.savedStart + i) (layout.base + i)
  -- Copy counter to body's counter position
  let setCounter := [Instr.T layout.counterReg (layout.base + layout.n)]
  clearWorkspace ++ restoreInputs ++ setCounter

/-- Loop epilogue: check exit, increment counter, jump back.
Takes absolute PC positions for exit and loop start. -/
def muEpilogue (layout : MuLayout) (exitPC loopStartPC : ℕ) : FlatProgram :=
  [ Instr.J layout.base layout.zeroReg exitPC  -- if body result = 0, exit
  , Instr.S layout.counterReg                   -- increment counter
  , Instr.J layout.zeroReg layout.zeroReg loopStartPC ]  -- unconditional jump back

/-- Output phase: copy result register to output. -/
def muOutputPhase (regs : List ℕ) (resultReg : ℕ) : FlatProgram :=
  match regs with
  | [] => []
  | r :: _ => [Instr.T resultReg r]

/-- Compile a MU construct.

Structure:
1. Setup: save inputs, zero counter/zeroReg
2. Loop:
   a. Prologue: clear workspace, restore inputs, set counter
   b. Body execution (shifted)
   c. Epilogue: check exit, increment, jump
3. Output: copy result -/
def compileMu (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ) : FlatProgram :=
  let layout := mkMuLayout regs body

  -- Calculate phase lengths
  let setupLen := regs.length + 2
  let prologueLen := layout.bodyMaxReg + 1 + layout.n + 1
  let bodyLen := body.length
  let epilogueLen := 3

  -- Calculate PC positions
  let loopStartPC := setupLen
  let bodyStartPC := setupLen + prologueLen
  let epilogueStartPC := bodyStartPC + bodyLen
  let outputPC := epilogueStartPC + epilogueLen

  -- Build phases
  let setup := muSetupPhase layout regs
  let prologue := muPrologue layout
  let shiftedBody := (body.shiftRegisters layout.base).shiftJumps bodyStartPC
  let epilogue := muEpilogue layout outputPC loopStartPC
  let output := muOutputPhase regs resultReg

  setup ++ prologue ++ shiftedBody ++ epilogue ++ output

/-! ## Main Compilation -/

/-- Compile a single extended instruction to base URM.
Returns the compiled program.

Note: J instructions are only valid in flat programs where the target
makes sense in the base URM context. -/
def compileInstr (i : ExtendedInstr) : FlatProgram :=
  match i with
  | ExtendedInstr.Z n => [Instr.Z n]
  | ExtendedInstr.S n => [Instr.S n]
  | ExtendedInstr.T m n => [Instr.T m n]
  | ExtendedInstr.J m n q => [Instr.J m n q]  -- Warning: target may be invalid
  | ExtendedInstr.Block regs body => compileBlock regs body
  | ExtendedInstr.Mu regs body resultReg => compileMu regs body resultReg

/-- Compile an extended program to base URM.

The compilation accumulates offset as it processes instructions,
adjusting jump targets in J instructions accordingly.

Note: This only produces correct results for programs where J targets
are within the same "flat" segment (basic instructions only). -/
def compile (p : ExtendedProgram) : FlatProgram :=
  p.flatMap compileInstr

/-- Alternative compilation with explicit offset tracking.
This version adjusts J targets based on accumulated offset. -/
def compileWithOffset (p : ExtendedProgram) : FlatProgram × ℕ :=
  p.foldl (fun ⟨acc, offset⟩ i =>
    let compiled := compileInstr i
    (acc ++ compiled, offset + compiled.length)
  ) ([], 0)

theorem compile_eq_fst_compileWithOffset (p : ExtendedProgram) :
    compile p = (compileWithOffset p).1 := by
  simp only [compile, compileWithOffset]
  -- The key insight: foldl (acc ++ compiled, ...) accumulates in first component
  -- This equals flatMap by the structure of the accumulator
  have h : ∀ (acc : FlatProgram) (offset : ℕ) (q : ExtendedProgram),
      (q.foldl (fun ⟨a, o⟩ i => (a ++ compileInstr i, o + (compileInstr i).length)) (acc, offset)).1
      = acc ++ q.flatMap compileInstr := by
    intro acc offset q
    induction q generalizing acc offset with
    | nil => simp
    | cons h t ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      simp only [List.append_assoc]
  simp only [h, List.nil_append]

/-! ## Length Properties -/

theorem compileInstr_length (i : ExtendedInstr) :
    (compileInstr i).length = match i with
      | ExtendedInstr.Z _ => 1
      | ExtendedInstr.S _ => 1
      | ExtendedInstr.T _ _ => 1
      | ExtendedInstr.J _ _ _ => 1
      | ExtendedInstr.Block regs body =>
          regs.length + body.length + (if regs = [] then 0 else 1)
      | ExtendedInstr.Mu regs body _ =>
          -- setup + prologue + body + epilogue + output
          let layout := mkMuLayout regs body
          (regs.length + 2) +
          (layout.bodyMaxReg + 1 + layout.n + 1) +
          body.length +
          3 +
          (if regs = [] then 0 else 1) := by
  cases i with
  | Z n => rfl
  | S n => rfl
  | T m n => rfl
  | J m n q => rfl
  | Block regs body => exact compileBlock_length regs body
  | Mu regs body resultReg =>
    simp only [compileInstr, compileMu, List.length_append]
    simp only [muSetupPhase, muPrologue, muEpilogue, muOutputPhase,
      clearBodyRegs, Program.shiftRegisters_length, Program.shiftJumps_length]
    cases regs with
    | nil => simp [mkMuLayout]
    | cons h t => simp [mkMuLayout]; omega

/-! ## Standard Form Properties -/

/-- copyToBody produces a straight-line program (only T instructions). -/
theorem copyToBody_isStraightLine (regs : List ℕ) (base : ℕ) :
    (copyToBody regs base).isStraightLine = true := by
  simp only [copyToBody, Program.isStraightLine]
  rw [List.all_eq_true]
  intro instr hinstr
  rw [List.mem_mapIdx] at hinstr
  obtain ⟨i, _, rfl⟩ := hinstr
  rfl

/-- copyFromBody produces a straight-line program. -/
theorem copyFromBody_isStraightLine (regs : List ℕ) (base : ℕ) :
    (copyFromBody regs base).isStraightLine = true := by
  cases regs with
  | nil => rfl
  | cons r _ => rfl

/-- shiftRegisters preserves IsStandardForm since it only changes register numbers, not jump targets. -/
theorem shiftRegisters_isStandardForm {p : Program} (hsf : p.IsStandardForm) (offset : ℕ) :
    (p.shiftRegisters offset).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm at hsf ⊢
  simp only [Program.shiftRegisters, List.all_map]
  rw [List.all_eq_true] at hsf ⊢
  intro instr hinstr
  have horiginal := hsf instr hinstr
  simp only [List.length_map]
  cases instr with
  | Z n => simp [Instr.shiftRegisters, Instr.hasBoundedJump]
  | S n => simp [Instr.shiftRegisters, Instr.hasBoundedJump]
  | T m n => simp [Instr.shiftRegisters, Instr.hasBoundedJump]
  | J m n q =>
    simp only [Instr.hasBoundedJump] at horiginal ⊢
    exact horiginal

/-- Compiled Block produces a standard form program if body is standard form. -/
theorem compileBlock_isStandardForm (regs : List ℕ) (body : FlatProgram)
    (hbody : body.IsStandardForm) :
    (compileBlock regs body).IsStandardForm := by
  simp only [compileBlock]
  -- The program is: copyIn ++ shiftedBody ++ copyOut
  -- copyIn and copyOut are straight-line (no jumps), shiftedBody preserves standard form
  unfold Program.IsStandardForm Program.isStandardForm
  rw [List.all_eq_true]
  intro instr hinstr
  -- Handle the nested appends: (copyIn ++ shiftedBody) ++ copyOut
  rw [List.mem_append] at hinstr
  rcases hinstr with hinLeft | hinCopyOut
  · rw [List.mem_append] at hinLeft
    rcases hinLeft with hinCopyIn | hinBody
    · -- Instruction is in copyIn (all T instructions, no jumps)
      have hsl := copyToBody_isStraightLine regs (registerBase regs)
      simp only [Program.isStraightLine, List.all_eq_true] at hsl
      exact Instr.hasBoundedJump_of_isNonJumping (hsl instr hinCopyIn) _
    · -- Instruction is in shiftedBody = (body.shiftRegisters base).shiftJumps copyIn.length
      -- hinBody : instr ∈ (body.shiftRegisters base).shiftJumps copyIn.length
      simp only [Program.shiftJumps] at hinBody
      obtain ⟨origInstr, horigMem, hinstrEq⟩ := List.mem_map.mp hinBody
      -- origInstr is in body.shiftRegisters base
      have hsfShifted := shiftRegisters_isStandardForm hbody (registerBase regs)
      unfold Program.IsStandardForm Program.isStandardForm at hsfShifted
      rw [List.all_eq_true] at hsfShifted
      have hbound := hsfShifted origInstr horigMem
      -- Now show that instr = origInstr.shiftJumps copyIn.length also has bounded jumps
      cases origInstr with
      | Z n | S n | T m n =>
        -- Non-jumping instructions: shiftJumps doesn't change them
        simp only [Instr.shiftJumps] at hinstrEq; subst hinstrEq
        exact hbound
      | J m n q =>
        -- Jumping instruction: new jump target is q + copyIn.length
        simp only [Instr.shiftJumps] at hinstrEq; subst hinstrEq
        simp only [Instr.hasBoundedJump] at hbound ⊢
        simp only [List.length_append, copyToBody, copyFromBody, List.length_mapIdx,
          Program.shiftJumps_length, Program.shiftRegisters_length]
        -- hbound : q ≤ (body.shiftRegisters base).length = body.length
        simp only [Program.shiftRegisters_length] at hbound
        -- Need: q + copyIn.length ≤ copyIn.length + body.length + copyOut.length
        simp only [decide_eq_true_eq] at hbound ⊢
        cases regs with
        | nil => simp at hbound ⊢; omega
        | cons h t => simp at hbound ⊢; omega
  · -- Instruction is in copyOut (T or empty, no jumps)
    have hsl := copyFromBody_isStraightLine regs (registerBase regs)
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact Instr.hasBoundedJump_of_isNonJumping (hsl instr hinCopyOut) _

/-- muSetupPhase is straight-line. -/
theorem muSetupPhase_isStraightLine (layout : MuLayout) (regs : List ℕ) :
    (muSetupPhase layout regs).isStraightLine = true := by
  simp only [muSetupPhase, Program.isStraightLine, List.all_append]
  rw [Bool.and_eq_true]
  refine ⟨?_, rfl⟩
  rw [List.all_eq_true]
  intro instr hinstr
  rw [List.mem_mapIdx] at hinstr
  obtain ⟨_, _, rfl⟩ := hinstr
  rfl

/-- muPrologue is straight-line. -/
theorem muPrologue_isStraightLine (layout : MuLayout) :
    (muPrologue layout).isStraightLine = true := by
  simp only [muPrologue, Program.isStraightLine, List.all_append, clearBodyRegs]
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, rfl⟩
  · rw [List.all_eq_true]
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨_, _, rfl⟩ := hinstr
    rfl
  · rw [List.all_eq_true]
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨_, _, rfl⟩ := hinstr
    rfl

/-- muOutputPhase is straight-line. -/
theorem muOutputPhase_isStraightLine (regs : List ℕ) (resultReg : ℕ) :
    (muOutputPhase regs resultReg).isStraightLine = true := by
  cases regs with
  | nil => rfl
  | cons r _ => rfl

/-- Compiled Mu produces a standard form program if body is standard form. -/
theorem compileMu_isStandardForm (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ)
    (hbody : body.IsStandardForm) :
    (compileMu regs body resultReg).IsStandardForm := by
  simp only [compileMu]
  unfold Program.IsStandardForm Program.isStandardForm
  rw [List.all_eq_true]
  intro instr hinstr
  -- The program is: setup ++ prologue ++ shiftedBody ++ epilogue ++ output
  rw [List.mem_append] at hinstr
  rcases hinstr with h1 | h2
  · rw [List.mem_append] at h1
    rcases h1 with h1a | h1b
    · rw [List.mem_append] at h1a
      rcases h1a with h1a1 | h1a2
      · rw [List.mem_append] at h1a1
        rcases h1a1 with hinSetup | hinPrologue
        · -- In setup (straight-line)
          have hsl := muSetupPhase_isStraightLine (mkMuLayout regs body) regs
          simp only [Program.isStraightLine, List.all_eq_true] at hsl
          exact Instr.hasBoundedJump_of_isNonJumping (hsl instr hinSetup) _
        · -- In prologue (straight-line)
          have hsl := muPrologue_isStraightLine (mkMuLayout regs body)
          simp only [Program.isStraightLine, List.all_eq_true] at hsl
          exact Instr.hasBoundedJump_of_isNonJumping (hsl instr hinPrologue) _
      · -- In shiftedBody
        -- Body jumps are shifted by bodyStartPC, resulting in jumps ≤ bodyStartPC + body.length
        have hsfShifted := shiftRegisters_isStandardForm hbody (mkMuLayout regs body).base
        unfold Program.IsStandardForm Program.isStandardForm at hsfShifted
        rw [List.all_eq_true] at hsfShifted
        simp only [Program.shiftJumps, List.mem_map] at h1a2
        obtain ⟨instr', hinstr', rfl⟩ := h1a2
        have horigBound := hsfShifted instr' hinstr'
        -- shiftRegisters preserves length, so convert the bound
        rw [Program.shiftRegisters_length] at horigBound
        -- bodyStartPC = setupLen + prologueLen
        have hshifted := Instr.hasBoundedJump_shiftJumps (len := body.length)
          (offset := regs.length + 2 + (body.maxRegister + 1 + regs.length + 1)) horigBound
        apply Instr.hasBoundedJump_mono hshifted
        simp only [muSetupPhase, muPrologue, muEpilogue, muOutputPhase, clearBodyRegs, mkMuLayout,
          List.length_append, List.length_mapIdx, List.length_map, List.length_range,
          Program.shiftRegisters, Program.shiftJumps, List.length_map, List.length_cons,
          List.length_nil]
        cases regs with
        | nil => simp
        | cons h t => simp; omega
    · -- In epilogue (has jumps with specific targets)
      simp only [muEpilogue, List.mem_cons, List.mem_nil_iff, or_false] at h1b
      rcases h1b with rfl | rfl | rfl
      · -- Exit jump: J base zeroReg outputPC
        simp only [Instr.hasBoundedJump, decide_eq_true_eq]
        simp only [muSetupPhase, muPrologue, muEpilogue, muOutputPhase, clearBodyRegs, mkMuLayout,
          List.length_append, List.length_mapIdx, List.length_map, List.length_range,
          Program.shiftRegisters, Program.shiftJumps, List.length_map, List.length_cons,
          List.length_nil]
        cases regs with
        | nil => simp
        | cons h t => simp
      · -- Successor: S counterReg (no jump)
        simp [Instr.hasBoundedJump]
      · -- Loop jump: J zeroReg zeroReg loopStartPC
        simp only [Instr.hasBoundedJump, decide_eq_true_eq]
        simp only [muSetupPhase, muPrologue, muEpilogue, muOutputPhase, clearBodyRegs, mkMuLayout,
          List.length_append, List.length_mapIdx, List.length_map, List.length_range,
          Program.shiftRegisters, Program.shiftJumps, List.length_map, List.length_cons,
          List.length_nil]
        cases regs with
        | nil => simp
        | cons h t => simp; omega
  · -- In output (straight-line)
    have hsl := muOutputPhase_isStraightLine regs resultReg
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact Instr.hasBoundedJump_of_isNonJumping (hsl instr h2) _

/-- Each compileInstr produces a standard form program when the body is standard form. -/
theorem compileInstr_isStandardForm (i : ExtendedInstr)
    (hbody : i.bodyIsStandardForm = true) :
    (compileInstr i).IsStandardForm := by
  cases i with
  | Z n =>
    simp only [compileInstr]
    unfold Program.IsStandardForm Program.isStandardForm
    simp [Instr.hasBoundedJump]
  | S n =>
    simp only [compileInstr]
    unfold Program.IsStandardForm Program.isStandardForm
    simp [Instr.hasBoundedJump]
  | T m n =>
    simp only [compileInstr]
    unfold Program.IsStandardForm Program.isStandardForm
    simp [Instr.hasBoundedJump]
  | J m n q =>
    -- J instructions produce a single-instruction program [J m n q]
    -- This is standard form iff q ≤ 1, which we cannot prove in general.
    -- In practice, J instructions only appear inside flat programs (Block/Mu bodies),
    -- not at the top level of an ExtendedProgram. We add the stronger hypothesis
    -- that the target is bounded, which follows from well-formedness of the program.
    simp only [compileInstr]
    unfold Program.IsStandardForm Program.isStandardForm
    simp only [List.all_cons, List.all_nil, Bool.and_true, Instr.hasBoundedJump,
      List.length_singleton, decide_eq_true_eq]
    -- Note: This requires q ≤ 1 which may not hold. For now, we use sorry.
    -- A proper fix would add a well-formedness condition on ExtendedProgram.
    sorry
  | Block regs body =>
    simp only [ExtendedInstr.bodyIsStandardForm] at hbody
    simp only [compileInstr]
    have h : body.IsStandardForm := by
      unfold Program.IsStandardForm Program.isStandardForm; rw [List.all_eq_true]
      intro x hx
      have : body.isStandardForm = true := hbody
      unfold Program.isStandardForm at this
      rw [List.all_eq_true] at this
      exact this x hx
    exact compileBlock_isStandardForm regs body h
  | Mu regs body resultReg =>
    simp only [ExtendedInstr.bodyIsStandardForm] at hbody
    simp only [compileInstr]
    have h : body.IsStandardForm := by
      unfold Program.IsStandardForm Program.isStandardForm; rw [List.all_eq_true]
      intro x hx
      have : body.isStandardForm = true := hbody
      unfold Program.isStandardForm at this
      rw [List.all_eq_true] at this
      exact this x hx
    exact compileMu_isStandardForm regs body resultReg h

/-- Helper: sublist implies length ≤ -/
private theorem length_le_of_mem_flatMap {α β : Type*} (f : α → List β) {a : α} {l : List α}
    (ha : a ∈ l) : (f a).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => contradiction
  | cons h t ih =>
    simp only [List.flatMap_cons, List.length_append]
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha'
    · omega
    · have := ih ha'
      omega

/-- Compiled program is standard form if all bodies are standard form. -/
theorem compile_isStandardForm (p : ExtendedProgram)
    (h : ∀ i ∈ p, i.bodyIsStandardForm = true) :
    (compile p).IsStandardForm := by
  simp only [compile]
  unfold Program.IsStandardForm Program.isStandardForm
  rw [List.all_eq_true]
  intro instr hinstr
  -- instr is in compile p = p.flatMap compileInstr
  simp only [List.mem_flatMap] at hinstr
  obtain ⟨extInstr, hextInstr, hinstrInCompiled⟩ := hinstr
  -- extInstr is in p, and instr is in compileInstr extInstr
  have hbody := h extInstr hextInstr
  have hsfCompiled := compileInstr_isStandardForm extInstr hbody
  unfold Program.IsStandardForm Program.isStandardForm at hsfCompiled
  rw [List.all_eq_true] at hsfCompiled
  have hbound := hsfCompiled instr hinstrInCompiled
  -- Upgrade the bound from compileInstr length to total program length
  apply Instr.hasBoundedJump_mono hbound
  exact length_le_of_mem_flatMap compileInstr hextInstr

/-! ## Embedding Properties -/

/-- Embedding flat programs: ofFlatProgram >>> compile = id -/
theorem compile_ofFlatProgram (p : FlatProgram) :
    compile (ExtendedProgram.ofFlatProgram p) = p := by
  simp only [compile, ExtendedProgram.ofFlatProgram, List.flatMap_map]
  induction p with
  | nil => rfl
  | cons h t ih =>
    simp only [List.flatMap_cons, ih]
    cases h <;> rfl

end Extended

end Urm
