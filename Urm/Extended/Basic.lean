/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Basic
import Urm.StandardForm

/-! # Extended URM: Core Types

This module defines the ExtendedURM intermediate representation, which adds
structured control flow (BLOCK and MU) to basic URM instructions. This allows
for cleaner semantics and easier proofs when dealing with composition and
μ-recursion.

## Main Definitions

- `FlatProgram`: Alias for base URM programs (no nesting)
- `ExtendedInstr`: Extended instructions including BLOCK and MU constructs
- `ExtendedProgram`: A list of extended instructions

## Design

The key insight is that BLOCK and MU bodies are flat (base URM) programs,
not nested ExtendedPrograms. This prevents arbitrary nesting depth and makes
compilation and semantics simpler:

- **Semantics**: Each construct has clear, compositional semantics
- **Compilation**: Translation to base URM is mechanical and uniform
- **Equivalence**: Maps directly to Partrec (Block ↔ composition, Mu ↔ rfind)

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

namespace Extended

/-- Base URM program - BLOCK and MU bodies are this type (no nesting).
This is just an alias for the standard Urm.Program type. -/
abbrev FlatProgram := Urm.Program

/-- Extended URM instructions with structured control flow.

Basic instructions (Z, S, T, J) behave identically to their base URM counterparts.
The structured constructs are:

- `Block regs body`: Execute `body` with registers mapped through `regs`,
  writing the result back to the first mapped register.

- `While condReg body`: Loop while R[condReg] ≠ 0, executing body each iteration.
-/
inductive ExtendedInstr : Type where
  /-- Zero: set register n to 0 -/
  | Z : ℕ → ExtendedInstr
  /-- Successor: increment register n -/
  | S : ℕ → ExtendedInstr
  /-- Transfer: copy register m to register n -/
  | T : ℕ → ℕ → ExtendedInstr
  /-- Jump: if R[m] = R[n], jump to instruction q -/
  | J : ℕ → ℕ → ℕ → ExtendedInstr
  /-- Block: execute body with register mapping.

  `Block [r₀, r₁, ...] body` executes as:
  1. Create sub-state: body's R[i] ← host's R[rᵢ]
  2. Run body (base URM) until halt
  3. Write back: host's R[r₀] ← body's R[0]

  The body sees inputs at R[0], R[1], ..., R[n-1] where n = regs.length.
  -/
  | Block : List ℕ → FlatProgram → ExtendedInstr
  /-- While: loop while condition register is non-zero.

  `While condReg body` executes as:
  1. Check R[condReg]: if = 0, exit loop
  2. Run body (base URM) until halt
  3. Go to step 1

  This is the machine-level while loop primitive. μ-recursion can be
  implemented using While combined with arithmetic operations.
  -/
  | While : ℕ → FlatProgram → ExtendedInstr
deriving DecidableEq, Repr

namespace ExtendedInstr

/-- Check if an extended instruction is a basic (non-structured) instruction. -/
def isBasic : ExtendedInstr → Bool
  | Z _ | S _ | T _ _ | J _ _ _ => true
  | Block _ _ | While _ _ => false

/-- Convert a basic ExtendedInstr to a base Instr, if applicable. -/
def toBaseInstr? : ExtendedInstr → Option Instr
  | Z n => some (Instr.Z n)
  | S n => some (Instr.S n)
  | T m n => some (Instr.T m n)
  | J m n q => some (Instr.J m n q)
  | Block _ _ | While _ _ => none

/-- Embed a base Instr as an ExtendedInstr. -/
def ofInstr : Instr → ExtendedInstr
  | Instr.Z n => Z n
  | Instr.S n => S n
  | Instr.T m n => T m n
  | Instr.J m n q => J m n q

theorem ofInstr_toBaseInstr (i : Instr) : (ofInstr i).toBaseInstr? = some i := by
  cases i <;> rfl

theorem toBaseInstr_ofInstr {ei : ExtendedInstr} {i : Instr}
    (h : ei.toBaseInstr? = some i) : ofInstr i = ei := by
  cases ei with
  | Z n => simp only [toBaseInstr?, Option.some.injEq] at h; subst h; rfl
  | S n => simp only [toBaseInstr?, Option.some.injEq] at h; subst h; rfl
  | T m n => simp only [toBaseInstr?, Option.some.injEq] at h; subst h; rfl
  | J m n q => simp only [toBaseInstr?, Option.some.injEq] at h; subst h; rfl
  | Block _ _ => simp [toBaseInstr?] at h
  | While _ _ => simp [toBaseInstr?] at h

/-- The input registers referenced by an extended instruction.
For basic instructions, this is the registers read.
For Block, this is the mapped register list.
For While, this is the condition register. -/
def inputRegisters : ExtendedInstr → List ℕ
  | Z _ => []
  | S n => [n]
  | T m _ => [m]
  | J m n _ => [m, n]
  | Block regs _ => regs
  | While condReg _ => [condReg]

/-- The output register written by an extended instruction (primary output).
For basic instructions: the register written (if any).
For Block: the first mapped register (where result is written).
For While: none (writes to various registers via body). -/
def outputRegister? : ExtendedInstr → Option ℕ
  | Z n => some n
  | S n => some n
  | T _ n => some n
  | J _ _ _ => none
  | Block regs _ => regs.head?
  | While _ _ => none

/-- Get the body program of a structured instruction, if any. -/
def body? : ExtendedInstr → Option FlatProgram
  | Z _ | S _ | T _ _ | J _ _ _ => none
  | Block _ body => some body
  | While _ body => some body

/-- Check if a Block/While body is in standard form (bounded jumps). -/
def bodyIsStandardForm : ExtendedInstr → Bool
  | Block _ body => body.isStandardForm
  | While _ body => body.isStandardForm
  | _ => true

end ExtendedInstr

/-- An extended URM program is a list of extended instructions. -/
abbrev ExtendedProgram := List ExtendedInstr

namespace ExtendedProgram

/-- Get instruction at position i. -/
def getInstr (p : ExtendedProgram) (i : ℕ) : Option ExtendedInstr := p[i]?

/-- Check if all Block/Mu bodies in the program are in standard form. -/
def allBodiesStandardForm (p : ExtendedProgram) : Bool :=
  p.all ExtendedInstr.bodyIsStandardForm

/-- Convert a flat (base URM) program to an extended program by embedding each instruction. -/
def ofFlatProgram (p : FlatProgram) : ExtendedProgram :=
  p.map ExtendedInstr.ofInstr

/-- A program is flat if it contains only basic instructions (no Block/Mu). -/
def isFlat (p : ExtendedProgram) : Bool :=
  p.all ExtendedInstr.isBasic

/-- Convert a flat extended program back to a base URM program.
Returns none if any instruction is structured (Block/Mu). -/
def toFlatProgram? (p : ExtendedProgram) : Option FlatProgram :=
  p.mapM ExtendedInstr.toBaseInstr?

theorem ofFlatProgram_isFlat (p : FlatProgram) : (ofFlatProgram p).isFlat = true := by
  simp only [ofFlatProgram, isFlat, List.all_map]
  induction p with
  | nil => rfl
  | cons h t ih =>
    simp only [List.all_cons, ih, Bool.and_true]
    cases h <;> rfl

theorem toFlatProgram_ofFlatProgram (p : FlatProgram) :
    (ofFlatProgram p).toFlatProgram? = some p := by
  simp only [ofFlatProgram, toFlatProgram?, List.mapM_map]
  induction p with
  | nil => rfl
  | cons h t ih =>
    simp only [List.mapM_cons, Function.comp_apply, ExtendedInstr.ofInstr_toBaseInstr, ih]
    rfl

end ExtendedProgram

/-! ## Well-formedness Predicates -/

/-- A Block instruction is well-formed if:
1. The register list is non-empty (need somewhere to write result)
2. The body is in standard form (bounded jumps) -/
def ExtendedInstr.BlockWellFormed : ExtendedInstr → Prop
  | Block regs body => regs ≠ [] ∧ body.IsStandardForm
  | _ => True

/-- A While instruction is well-formed if the body is in standard form. -/
def ExtendedInstr.WhileWellFormed : ExtendedInstr → Prop
  | While _ body => body.IsStandardForm
  | _ => True

/-- A J instruction is well-formed relative to program length if target is bounded.
    q ≤ progLen means J can jump to any instruction index or to halt (index = progLen). -/
def ExtendedInstr.JWellFormedAt (progLen : ℕ) : ExtendedInstr → Prop
  | J _ _ q => q ≤ progLen
  | _ => True

/-- An extended instruction is well-formed (without program context).
    Note: J well-formedness requires program context and is checked separately. -/
def ExtendedInstr.WellFormed (i : ExtendedInstr) : Prop :=
  i.BlockWellFormed ∧ i.WhileWellFormed

/-- All J targets in program are bounded by program length. -/
def ExtendedProgram.JWellFormed (p : ExtendedProgram) : Prop :=
  ∀ i ∈ p, i.JWellFormedAt p.length

/-- An extended program has well-formed instructions if all its instructions are well-formed. -/
def ExtendedProgram.InstrWellFormed (p : ExtendedProgram) : Prop :=
  ∀ i ∈ p, i.WellFormed

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

/-! ## Workspace Safety -/

/-- Check if a register is in the workspace range for a Block.
The workspace of Block regs body consists of registers r + registerBase regs
where regs.length ≤ r ≤ body.maxRegister. -/
def inWorkspaceRange (n : ℕ) (regs : List ℕ) (body : FlatProgram) : Prop :=
  ∃ r, regs.length ≤ r ∧ r ≤ body.maxRegister ∧ n = r + registerBase regs

/-- Check if a register is a workspace register for any Block in the program. -/
def isWorkspaceOf (n : ℕ) : ExtendedProgram → Prop
  | [] => False
  | ExtendedInstr.Block regs body :: rest =>
      inWorkspaceRange n regs body ∨ isWorkspaceOf n rest
  | _ :: rest => isWorkspaceOf n rest

/-- Check if a register is in the write range of a compiled Block.
The write range includes the output register regs[0] and the workspace used during
compilation: [registerBase regs, registerBase regs + max(regs.length - 1, body.maxRegister)]. -/
def inBlockWriteRange (n : ℕ) (regs : List ℕ) (body : FlatProgram) : Prop :=
  (regs.head? = some n) ∨
  (registerBase regs ≤ n ∧ n ≤ registerBase regs + max (regs.length - 1) body.maxRegister)

/-- Check if a register is in the write range of a compiled While.
The write range is [0, max(condReg, body.maxRegister) + 1] since:
- While runs body repeatedly, modifying registers up to body.maxRegister
- The compiled While uses a "zero register" at max(condReg, body.maxRegister) + 1 -/
def inWhileWriteRange (n : ℕ) (condReg : ℕ) (body : FlatProgram) : Prop :=
  n ≤ max condReg body.maxRegister + 1

/-- A Block instruction preserves subsequent Blocks' workspaces if its write range
doesn't overlap with their workspace ranges. -/
def BlockPreservesSubsequentWorkspaces (regs : List ℕ) (body : FlatProgram)
    (rest : ExtendedProgram) : Prop :=
  ∀ j ∈ rest, ∀ regs' body', j = ExtendedInstr.Block regs' body' →
    ∀ n, inBlockWriteRange n regs body → ¬inWorkspaceRange n regs' body'

/-- A While instruction preserves subsequent Blocks' workspaces if its write range
doesn't overlap with their workspace ranges. -/
def WhilePreservesSubsequentWorkspaces (condReg : ℕ) (body : FlatProgram)
    (rest : ExtendedProgram) : Prop :=
  ∀ j ∈ rest, ∀ regs' body', j = ExtendedInstr.Block regs' body' →
    ∀ n, inWhileWriteRange n condReg body → ¬inWorkspaceRange n regs' body'

/-- Blocks and Whiles preserve subsequent Blocks' workspaces throughout the program. -/
def ExtendedProgram.BlocksPreserveWorkspaces : ExtendedProgram → Prop
  | [] => True
  | ExtendedInstr.Block regs body :: rest =>
      BlockPreservesSubsequentWorkspaces regs body rest ∧ BlocksPreserveWorkspaces rest
  | ExtendedInstr.While condReg body :: rest =>
      WhilePreservesSubsequentWorkspaces condReg body rest ∧ BlocksPreserveWorkspaces rest
  | _ :: rest => BlocksPreserveWorkspaces rest

/-- A program is workspace-safe: S and T don't write to workspace of subsequent Blocks. -/
def ExtendedProgram.WorkspaceSafe : ExtendedProgram → Prop
  | [] => True
  | ExtendedInstr.S n :: rest => ¬isWorkspaceOf n rest ∧ WorkspaceSafe rest
  | ExtendedInstr.T _ n :: rest => ¬isWorkspaceOf n rest ∧ WorkspaceSafe rest
  | _ :: rest => WorkspaceSafe rest

/-- An extended program is well-formed if:
    1. All instructions are well-formed (Block/While bodies are standard form)
    2. All J targets are bounded (≤ program length)
    3. Workspace-safe (S/T don't write to subsequent Block workspaces)
    4. Blocks preserve subsequent Block workspaces -/
def ExtendedProgram.WellFormed (p : ExtendedProgram) : Prop :=
  p.InstrWellFormed ∧ p.JWellFormed ∧ p.WorkspaceSafe ∧ p.BlocksPreserveWorkspaces

/-! ## Workspace Safety Helper Lemmas -/

theorem WorkspaceSafe_nil : ExtendedProgram.WorkspaceSafe [] := trivial

theorem WorkspaceSafe_cons_S {n : ℕ} {rest : ExtendedProgram}
    (h : ExtendedProgram.WorkspaceSafe (ExtendedInstr.S n :: rest)) :
    ¬isWorkspaceOf n rest ∧ ExtendedProgram.WorkspaceSafe rest :=
  h

theorem WorkspaceSafe_cons_T {m n : ℕ} {rest : ExtendedProgram}
    (h : ExtendedProgram.WorkspaceSafe (ExtendedInstr.T m n :: rest)) :
    ¬isWorkspaceOf n rest ∧ ExtendedProgram.WorkspaceSafe rest :=
  h

theorem WorkspaceSafe_cons_rest {i : ExtendedInstr} {rest : ExtendedProgram}
    (h : ExtendedProgram.WorkspaceSafe (i :: rest)) :
    ExtendedProgram.WorkspaceSafe rest := by
  cases i with
  | S n => exact h.2
  | T m n => exact h.2
  | Z _ | J _ _ _ | Block _ _ | While _ _ => exact h

theorem isWorkspaceOf_of_mem_Block {j : ExtendedInstr} {rest : ExtendedProgram}
    {regs : List ℕ} {body : FlatProgram} {n : ℕ}
    (hj : j ∈ rest) (hj_eq : j = ExtendedInstr.Block regs body)
    (hws : inWorkspaceRange n regs body) :
    isWorkspaceOf n rest := by
  induction rest with
  | nil => simp only [List.mem_nil_iff] at hj
  | cons head tail ih =>
    simp only [List.mem_cons] at hj
    cases hj with
    | inl heq =>
      subst heq hj_eq
      simp only [isWorkspaceOf]
      left; exact hws
    | inr htail =>
      cases head with
      | Block regs' body' =>
        simp only [isWorkspaceOf]
        right; exact ih htail
      | Z _ | S _ | T _ _ | J _ _ _ | While _ _ =>
        simp only [isWorkspaceOf]
        exact ih htail

/-! ## BlocksPreserveWorkspaces Helper Lemmas -/

theorem BlocksPreserveWorkspaces_nil : ExtendedProgram.BlocksPreserveWorkspaces [] := trivial

theorem BlocksPreserveWorkspaces_cons_Block {regs : List ℕ} {body : FlatProgram}
    {rest : ExtendedProgram}
    (h : ExtendedProgram.BlocksPreserveWorkspaces (ExtendedInstr.Block regs body :: rest)) :
    BlockPreservesSubsequentWorkspaces regs body rest ∧
    ExtendedProgram.BlocksPreserveWorkspaces rest :=
  h

theorem BlocksPreserveWorkspaces_cons_While {condReg : ℕ} {body : FlatProgram}
    {rest : ExtendedProgram}
    (h : ExtendedProgram.BlocksPreserveWorkspaces (ExtendedInstr.While condReg body :: rest)) :
    WhilePreservesSubsequentWorkspaces condReg body rest ∧
    ExtendedProgram.BlocksPreserveWorkspaces rest :=
  h

theorem BlocksPreserveWorkspaces_cons_rest {i : ExtendedInstr} {rest : ExtendedProgram}
    (h : ExtendedProgram.BlocksPreserveWorkspaces (i :: rest)) :
    ExtendedProgram.BlocksPreserveWorkspaces rest := by
  cases i with
  | Block _ _ => exact h.2
  | While _ _ => exact h.2
  | Z _ | S _ | T _ _ | J _ _ _ => exact h

/-- Extract the JWellFormed component from WellFormed. -/
theorem WellFormed_JWellFormed {p : ExtendedProgram}
    (h : ExtendedProgram.WellFormed p) : ExtendedProgram.JWellFormed p :=
  h.2.1

/-- Extract the WorkspaceSafe component from WellFormed. -/
theorem WellFormed_WorkspaceSafe {p : ExtendedProgram}
    (h : ExtendedProgram.WellFormed p) : ExtendedProgram.WorkspaceSafe p :=
  h.2.2.1

/-- Extract the BlocksPreserveWorkspaces component from WellFormed. -/
theorem WellFormed_BlocksPreserveWorkspaces {p : ExtendedProgram}
    (h : ExtendedProgram.WellFormed p) : ExtendedProgram.BlocksPreserveWorkspaces p :=
  h.2.2.2

end Extended

end Urm
