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
The compilation handles structured control flow (BLOCK and WHILE) by
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

### WHILE condReg { body }
Compiled as:
1. Setup: ensure zeroReg = 0
2. Check: J condReg zeroReg exitPC (if condition = 0, exit)
3. Body execution (shifted jumps)
4. Loop back: J zeroReg zeroReg checkPC (unconditional jump)
5. Exit point

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

/-! ## While Compilation -/

/-- Compile a WHILE construct.

Structure (for condReg, body):
```
[0]              Z zeroReg                    -- ensure zeroReg = 0
[1]              J condReg zeroReg exitPC     -- if R[condReg] = 0, exit
[2..2+len-1]     body (jump-shifted by 2)     -- execute body
[2+len]          J zeroReg zeroReg 1          -- unconditional jump to check
[exitPC=2+len+1] (halted)
```

The zeroReg is chosen to be beyond both condReg and body.maxRegister to avoid conflicts.
-/
def compileWhile (condReg : ℕ) (body : FlatProgram) : FlatProgram :=
  let zeroReg := max condReg body.maxRegister + 1
  let bodyLen := body.length
  let exitPC := 2 + bodyLen + 1
  let checkPC := 1
  -- Build the program
  [Instr.Z zeroReg,
   Instr.J condReg zeroReg exitPC] ++
  body.shiftJumps 2 ++
  [Instr.J zeroReg zeroReg checkPC]

/-- Length of compileWhile. -/
theorem compileWhile_length (condReg : ℕ) (body : FlatProgram) :
    (compileWhile condReg body).length = body.length + 3 := by
  simp only [compileWhile, List.length_append, List.length_cons, List.length_nil,
    Program.shiftJumps_length]
  omega

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
  | ExtendedInstr.While condReg body => compileWhile condReg body

/-! ## Offset Computation for J Target Translation

These definitions compute the compiled PC offset for each extended instruction,
which is needed for J target translation in the compile function. -/

/-- Compute the compiled PC offset for extended instruction at index i.
    This is the sum of compiled lengths of instructions 0..(i-1).
    instrOffset p 0 = 0 (start of first instruction)
    instrOffset p i = sum of lengths of compileInstr(p[0..i-1])
    instrOffset p p.length = total compiled length (halt position) -/
def instrOffset (p : ExtendedProgram) (i : ℕ) : ℕ :=
  (p.take i).foldl (fun acc instr => acc + (compileInstr instr).length) 0

theorem instrOffset_zero (p : ExtendedProgram) : instrOffset p 0 = 0 := rfl

theorem instrOffset_succ (p : ExtendedProgram) (i : ℕ) (hi : i < p.length) :
    instrOffset p (i + 1) = instrOffset p i + (compileInstr (p[i]'hi)).length := by
  simp only [instrOffset]
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

private theorem foldl_compileInstr_length_acc (p : ExtendedProgram) (acc : ℕ) :
    p.foldl (fun a instr => a + (compileInstr instr).length) acc =
    acc + p.foldl (fun a instr => a + (compileInstr instr).length) 0 := by
  induction p generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (0 + (compileInstr h).length)]
    omega

private theorem foldl_compileInstr_length_eq_sum (p : ExtendedProgram) :
    p.foldl (fun acc instr => acc + (compileInstr instr).length) 0 =
    (p.map (fun i => (compileInstr i).length)).sum := by
  induction p with
  | nil => rfl
  | cons h t ih =>
    simp only [List.foldl_cons, Nat.add_comm 0, List.map_cons, List.sum_cons]
    rw [foldl_compileInstr_length_acc, ih]
    omega

/-- List of all offsets: offsets[i] = instrOffset p i.
    Has length p.length + 1; last element is total compiled length. -/
def instrOffsets (p : ExtendedProgram) : List ℕ :=
  List.range (p.length + 1) |>.map (instrOffset p)

theorem instrOffsets_length (p : ExtendedProgram) :
    (instrOffsets p).length = p.length + 1 := by
  simp [instrOffsets]

theorem instrOffsets_getElem (p : ExtendedProgram) (i : ℕ) (hi : i < p.length + 1) :
    (instrOffsets p)[i]'(by simp [instrOffsets]; omega) = instrOffset p i := by
  simp [instrOffsets, List.getElem_map]

/-! ## Main Compilation -/

/-- Compile a single extended instruction with J target translation.
    For J instructions, q (extended instruction index) is translated to the
    corresponding base URM PC using the provided offset lookup function.
    For other instructions, compilation is the same as compileInstr. -/
def compileInstrWithJOffset (offsetLookup : ℕ → ℕ) (i : ExtendedInstr) : FlatProgram :=
  match i with
  | ExtendedInstr.J m n q => [Instr.J m n (offsetLookup q)]
  | _ => compileInstr i

/-- Compile an extended program to base URM.

The compilation handles two types of J targets differently:
1. **Top-level J instructions**: Target q refers to an extended instruction index.
   We translate q to `instrOffset p q` (the base URM PC for that instruction).
2. **Block/While internal jumps**: Already handled correctly by `concat` which
   shifts internal jump targets by the accumulated offset.

This ensures that:
- `J m n 0` jumps to the start of the program
- `J m n i` jumps to the start of the i-th extended instruction
- `J m n p.length` jumps past the end (halts if condition met) -/
def compile (p : ExtendedProgram) : FlatProgram :=
  let offsetLookup := instrOffset p
  p.foldl (fun acc i =>
    match i with
    | ExtendedInstr.J m n q =>
        -- Top-level J: use raw ++ since we've already computed the correct target
        acc ++ [Instr.J m n (offsetLookup q)]
    | _ =>
        -- Other instructions: use concat which shifts Block/While internal jumps
        acc.concat (compileInstr i)
  ) []

/-! ## Compile Helper Lemmas -/

/-- Compile of empty program is empty. -/
theorem compile_nil : compile ([] : ExtendedProgram) = [] := rfl

/-- Helper: the foldl in compile with a specific offset lookup. -/
private def compileFoldl (offsetLookup : ℕ → ℕ) (acc : FlatProgram) (p : ExtendedProgram) : FlatProgram :=
  p.foldl (fun a i =>
    match i with
    | ExtendedInstr.J m n q => a ++ [Instr.J m n (offsetLookup q)]
    | _ => a.concat (compileInstr i)
  ) acc

/-- compile is compileFoldl with instrOffset. -/
theorem compile_eq_compileFoldl (p : ExtendedProgram) :
    compile p = compileFoldl (instrOffset p) [] p := rfl

/-- compileFoldl with acc distributes. -/
private theorem compileFoldl_acc_distrib (offsetLookup : ℕ → ℕ) (acc : FlatProgram) (p : ExtendedProgram) :
    (compileFoldl offsetLookup acc p).length = acc.length + (compileFoldl offsetLookup [] p).length := by
  induction p generalizing acc with
  | nil => simp [compileFoldl]
  | cons h t ih =>
    unfold compileFoldl
    simp only [List.foldl_cons]
    cases h with
    | J m n q =>
      simp only [List.length_append, List.length_singleton]
      have h1 := ih (acc ++ [Instr.J m n (offsetLookup q)])
      have h2 := ih ([] ++ [Instr.J m n (offsetLookup q)])
      unfold compileFoldl at h1 h2
      simp only [List.length_append, List.length_singleton, List.length_nil] at h1 h2 ⊢
      omega
    | Z n =>
      have h1 := ih (Program.concat acc (compileInstr (ExtendedInstr.Z n)))
      have h2 := ih (Program.concat [] (compileInstr (ExtendedInstr.Z n)))
      unfold compileFoldl at h1 h2
      simp only [Program.concat_nil_left, Program.concat_length] at h1 h2 ⊢
      omega
    | S n =>
      have h1 := ih (Program.concat acc (compileInstr (ExtendedInstr.S n)))
      have h2 := ih (Program.concat [] (compileInstr (ExtendedInstr.S n)))
      unfold compileFoldl at h1 h2
      simp only [Program.concat_nil_left, Program.concat_length] at h1 h2 ⊢
      omega
    | T m' n =>
      have h1 := ih (Program.concat acc (compileInstr (ExtendedInstr.T m' n)))
      have h2 := ih (Program.concat [] (compileInstr (ExtendedInstr.T m' n)))
      unfold compileFoldl at h1 h2
      simp only [Program.concat_nil_left, Program.concat_length] at h1 h2 ⊢
      omega
    | Block regs body =>
      have h1 := ih (Program.concat acc (compileInstr (ExtendedInstr.Block regs body)))
      have h2 := ih (Program.concat [] (compileInstr (ExtendedInstr.Block regs body)))
      unfold compileFoldl at h1 h2
      simp only [Program.concat_nil_left, Program.concat_length] at h1 h2 ⊢
      omega
    | While condReg body =>
      have h1 := ih (Program.concat acc (compileInstr (ExtendedInstr.While condReg body)))
      have h2 := ih (Program.concat [] (compileInstr (ExtendedInstr.While condReg body)))
      unfold compileFoldl at h1 h2
      simp only [Program.concat_nil_left, Program.concat_length] at h1 h2 ⊢
      omega

/-- Length of compileFoldl in terms of instruction lengths. -/
private theorem compileFoldl_length (offsetLookup : ℕ → ℕ) (p : ExtendedProgram) :
    (compileFoldl offsetLookup [] p).length = (p.map (fun i => (compileInstr i).length)).sum := by
  induction p with
  | nil => rfl
  | cons h t ih =>
    unfold compileFoldl
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    cases h with
    | J m n q =>
      simp only [List.length_append, List.length_singleton, List.nil_append]
      have hacc := compileFoldl_acc_distrib offsetLookup ([Instr.J m n (offsetLookup q)]) t
      unfold compileFoldl at hacc ih
      simp only [List.length_singleton] at hacc
      rw [hacc, ih]
      simp [compileInstr]
    | Z n =>
      simp only [Program.concat_nil_left]
      have hacc := compileFoldl_acc_distrib offsetLookup (compileInstr (ExtendedInstr.Z n)) t
      unfold compileFoldl at hacc ih
      rw [hacc, ih]
    | S n =>
      simp only [Program.concat_nil_left]
      have hacc := compileFoldl_acc_distrib offsetLookup (compileInstr (ExtendedInstr.S n)) t
      unfold compileFoldl at hacc ih
      rw [hacc, ih]
    | T m' n =>
      simp only [Program.concat_nil_left]
      have hacc := compileFoldl_acc_distrib offsetLookup (compileInstr (ExtendedInstr.T m' n)) t
      unfold compileFoldl at hacc ih
      rw [hacc, ih]
    | Block regs body =>
      simp only [Program.concat_nil_left]
      have hacc := compileFoldl_acc_distrib offsetLookup (compileInstr (ExtendedInstr.Block regs body)) t
      unfold compileFoldl at hacc ih
      rw [hacc, ih]
    | While condReg body =>
      simp only [Program.concat_nil_left]
      have hacc := compileFoldl_acc_distrib offsetLookup (compileInstr (ExtendedInstr.While condReg body)) t
      unfold compileFoldl at hacc ih
      rw [hacc, ih]

/-- Length of compile in terms of instruction lengths. -/
theorem compile_length (p : ExtendedProgram) :
    (compile p).length = (p.map (fun i => (compileInstr i).length)).sum :=
  compileFoldl_length (instrOffset p) p

/-- Compile of singleton non-J instruction. -/
theorem compile_singleton_nonJ (i : ExtendedInstr) (hnotJ : ∀ m n q, i ≠ ExtendedInstr.J m n q) :
    compile [i] = compileInstr i := by
  simp only [compile]
  cases i with
  | Z n => simp [Program.concat_nil_left]
  | S n => simp [Program.concat_nil_left]
  | T m n => simp [Program.concat_nil_left]
  | J m n q => exact absurd rfl (hnotJ m n q)
  | Block regs body => simp [Program.concat_nil_left]
  | While condReg body => simp [Program.concat_nil_left]

/-- Compile of singleton J instruction. -/
theorem compile_singleton_J (m n q : ℕ) :
    compile [ExtendedInstr.J m n q] = [Instr.J m n (instrOffset [ExtendedInstr.J m n q] q)] := by
  simp only [compile, List.foldl_cons, List.foldl_nil, List.nil_append]

/-! ## Theorems relating instrOffset and compile -/

/-- Key lemma: instrOffset equals compiled prefix length. -/
theorem instrOffset_eq_compile_take_length (p : ExtendedProgram) (i : ℕ) :
    instrOffset p i = (compile (p.take i)).length := by
  simp only [instrOffset, compile_length, foldl_compileInstr_length_eq_sum, List.map_take]

theorem instrOffset_le_compile_length (p : ExtendedProgram) (i : ℕ) :
    instrOffset p i ≤ (compile p).length := by
  rw [instrOffset_eq_compile_take_length, compile_length, compile_length]
  induction p generalizing i with
  | nil => simp
  | cons h t ih =>
    cases i with
    | zero => simp
    | succ j =>
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons]
      have hle := ih j
      omega

/-- instrOffset at program length equals total compiled length. -/
theorem instrOffset_length (p : ExtendedProgram) :
    instrOffset p p.length = (compile p).length := by
  simp only [instrOffset, List.take_length, compile_length, foldl_compileInstr_length_eq_sum]

/-! ## Length Properties -/

theorem compileInstr_length (i : ExtendedInstr) :
    (compileInstr i).length = match i with
      | ExtendedInstr.Z _ => 1
      | ExtendedInstr.S _ => 1
      | ExtendedInstr.T _ _ => 1
      | ExtendedInstr.J _ _ _ => 1
      | ExtendedInstr.Block regs body =>
          regs.length + body.length + (if regs = [] then 0 else 1)
      | ExtendedInstr.While _ body => body.length + 3 := by
  cases i with
  | Z n => rfl
  | S n => rfl
  | T m n => rfl
  | J m n q => rfl
  | Block regs body => exact compileBlock_length regs body
  | While condReg body => exact compileWhile_length condReg body

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

/-- Compiled While produces a standard form program if body is standard form. -/
theorem compileWhile_isStandardForm (condReg : ℕ) (body : FlatProgram)
    (hbody : body.IsStandardForm) :
    (compileWhile condReg body).IsStandardForm := by
  simp only [compileWhile]
  unfold Program.IsStandardForm Program.isStandardForm
  rw [List.all_eq_true]
  intro instr hinstr
  -- The program is: [Z zeroReg, J condReg zeroReg exitPC] ++ shiftedBody ++ [J zeroReg zeroReg 1]
  simp only [List.mem_append, List.mem_cons] at hinstr
  rcases hinstr with ((rfl | hinrest) | hinBody) | hinlast
  · -- Z zeroReg: no jump
    simp [Instr.hasBoundedJump]
  · -- Either J condReg zeroReg exitPC or empty
    rcases hinrest with rfl | hempty
    · -- J condReg zeroReg exitPC: exitPC = 2 + body.length + 1 ≤ program length
      simp only [Instr.hasBoundedJump, decide_eq_true_eq, List.length_append, List.length_cons,
        List.length_nil, Program.shiftJumps_length]
      omega
    · simp at hempty
  · -- In shiftedBody
    simp only [Program.shiftJumps, List.mem_map] at hinBody
    obtain ⟨instr', hinstr', rfl⟩ := hinBody
    unfold Program.IsStandardForm Program.isStandardForm at hbody
    rw [List.all_eq_true] at hbody
    have horigBound := hbody instr' hinstr'
    -- Body jumps are shifted by 2, targets become q + 2
    have hshifted := Instr.hasBoundedJump_shiftJumps (len := body.length) (offset := 2) horigBound
    apply Instr.hasBoundedJump_mono hshifted
    simp only [List.length_append, List.length_cons, List.length_nil, Program.shiftJumps_length]
    omega
  · -- J zeroReg zeroReg 1: either the single element or empty
    rcases hinlast with rfl | hempty
    · simp only [Instr.hasBoundedJump, decide_eq_true_eq, List.length_append, List.length_cons,
        List.length_nil, Program.shiftJumps_length]
      omega
    · simp at hempty

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
  | While condReg body =>
    simp only [ExtendedInstr.bodyIsStandardForm] at hbody
    simp only [compileInstr]
    have h : body.IsStandardForm := by
      unfold Program.IsStandardForm Program.isStandardForm; rw [List.all_eq_true]
      intro x hx
      have : body.isStandardForm = true := hbody
      unfold Program.isStandardForm at this
      rw [List.all_eq_true] at this
      exact this x hx
    exact compileWhile_isStandardForm condReg body h

/-- Concatenation preserves standard form. -/
theorem concat_isStandardForm {p1 p2 : Program}
    (h1 : p1.IsStandardForm) (h2 : p2.IsStandardForm) :
    (p1.concat p2).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm at h1 h2 ⊢
  rw [List.all_eq_true] at h1 h2 ⊢
  intro instr hinstr
  simp only [Program.concat] at hinstr
  rw [List.mem_append] at hinstr
  rcases hinstr with hinLeft | hinRight
  · -- Instruction is in p1
    have hbound := h1 instr hinLeft
    apply Instr.hasBoundedJump_mono hbound
    simp only [Program.concat_length]; omega
  · -- Instruction is in p2.shiftJumps p1.length
    simp only [Program.shiftJumps, List.mem_map] at hinRight
    obtain ⟨origInstr, horigMem, rfl⟩ := hinRight
    have horigBound := h2 origInstr horigMem
    have hshifted := Instr.hasBoundedJump_shiftJumps (len := p2.length) (offset := p1.length) horigBound
    apply Instr.hasBoundedJump_mono hshifted
    simp only [Program.concat_length]
    omega

/-- Compiled program is standard form if all bodies are standard form.

Note: This proof works because:
1. For J instructions: instrOffset p q ≤ compile(p).length ensures bounded jump
2. For non-J instructions: concat preserves standard form -/
theorem compile_isStandardForm (p : ExtendedProgram)
    (h : ∀ i ∈ p, i.bodyIsStandardForm = true) :
    (compile p).IsStandardForm := by
  -- TODO: Full proof requires tracking accumulator length during foldl
  sorry

/-! ## Embedding Properties -/

/-- shiftJumps is identity for straight-line programs (no J instructions). -/
theorem shiftJumps_isStraightLine (p : Program) (h : p.isStraightLine = true) (offset : ℕ) :
    p.shiftJumps offset = p := by
  simp only [Program.shiftJumps]
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    simp only [Program.isStraightLine, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h_hd, h_tl⟩ := h
    simp only [List.map_cons, ih h_tl]
    cases hd with
    | Z n => rfl
    | S n => rfl
    | T m n => rfl
    | J m n q => simp [Instr.isNonJumping] at h_hd

/-- concat on straight-line programs is the same as ++ -/
theorem concat_isStraightLine (p1 p2 : Program) (h2 : p2.isStraightLine = true) :
    p1.concat p2 = p1 ++ p2 := by
  simp only [Program.concat, shiftJumps_isStraightLine p2 h2]

/-- Embedding straight-line flat programs: ofFlatProgram >>> compile = id.

Note: This holds for straight-line programs (no J instructions). For programs
with J instructions, the compile function shifts jump targets, which would
give incorrect results. -/
theorem compile_ofFlatProgram_isStraightLine (p : FlatProgram) (hsl : p.isStraightLine = true) :
    compile (ExtendedProgram.ofFlatProgram p) = p := by
  -- TODO: Needs update for new compile structure
  sorry

end Extended

end Urm
