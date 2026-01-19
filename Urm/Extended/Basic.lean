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

- `Mu regs body resultReg`: Execute `body` repeatedly with an incrementing counter
  until body's R[0] = 0, then write `resultReg` to the first mapped register.
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
  /-- Mu: unbounded loop with built-in counter, modeling μ-recursion.

  `Mu [r₀, r₁, ...] body resultReg` executes as:

  **Register layout** (for n = regs.length):
  - Body's R[0..n-1]: inputs from host's R[r₀, r₁, ...]
  - Body's R[n]: counter (starts at 0, incremented each iteration)

  **Semantics**:
  1. **Setup**: Create body sub-state
     - Body's R[i] ← host's R[rᵢ] for i in 0..n-1
     - Body's R[n] ← 0 (counter)

  2. **Loop iteration**:
     - Run body until halt
     - Check body's R[0]: if 0, exit loop
     - Otherwise: increment body's R[n], repeat

  3. **Write back**: host's R[r₀] ← body's R[resultReg]

  **Usage patterns**:
  - **μ-recursion** (minimization): resultReg = n (return counter when f(x,k) = 0)
  - **primitive recursion**: resultReg = accumulator register
  -/
  | Mu : List ℕ → FlatProgram → ℕ → ExtendedInstr
deriving DecidableEq, Repr

namespace ExtendedInstr

/-- Check if an extended instruction is a basic (non-structured) instruction. -/
def isBasic : ExtendedInstr → Bool
  | Z _ | S _ | T _ _ | J _ _ _ => true
  | Block _ _ | Mu _ _ _ => false

/-- Convert a basic ExtendedInstr to a base Instr, if applicable. -/
def toBaseInstr? : ExtendedInstr → Option Instr
  | Z n => some (Instr.Z n)
  | S n => some (Instr.S n)
  | T m n => some (Instr.T m n)
  | J m n q => some (Instr.J m n q)
  | Block _ _ | Mu _ _ _ => none

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
  | Mu _ _ _ => simp [toBaseInstr?] at h

/-- The input registers referenced by an extended instruction.
For basic instructions, this is the registers read.
For Block/Mu, this is the mapped register list. -/
def inputRegisters : ExtendedInstr → List ℕ
  | Z _ => []
  | S n => [n]
  | T m _ => [m]
  | J m n _ => [m, n]
  | Block regs _ => regs
  | Mu regs _ _ => regs

/-- The output register written by an extended instruction (primary output).
For basic instructions: the register written (if any).
For Block/Mu: the first mapped register (where result is written). -/
def outputRegister? : ExtendedInstr → Option ℕ
  | Z n => some n
  | S n => some n
  | T _ n => some n
  | J _ _ _ => none
  | Block regs _ => regs.head?
  | Mu regs _ _ => regs.head?

/-- Get the body program of a structured instruction, if any. -/
def body? : ExtendedInstr → Option FlatProgram
  | Z _ | S _ | T _ _ | J _ _ _ => none
  | Block _ body => some body
  | Mu _ body _ => some body

/-- Check if a Block body is in standard form (bounded jumps). -/
def bodyIsStandardForm : ExtendedInstr → Bool
  | Block _ body => body.isStandardForm
  | Mu _ body _ => body.isStandardForm
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

/-- A Mu instruction is well-formed if:
1. The register list is non-empty
2. The body is in standard form
3. The result register is valid (≤ body's max register or the counter position) -/
def ExtendedInstr.MuWellFormed : ExtendedInstr → Prop
  | Mu regs body resultReg => regs ≠ [] ∧ body.IsStandardForm ∧ resultReg ≤ regs.length + body.maxRegister
  | _ => True

/-- An extended instruction is well-formed. -/
def ExtendedInstr.WellFormed (i : ExtendedInstr) : Prop :=
  i.BlockWellFormed ∧ i.MuWellFormed

/-- An extended program is well-formed if all its instructions are well-formed. -/
def ExtendedProgram.WellFormed (p : ExtendedProgram) : Prop :=
  ∀ i ∈ p, i.WellFormed

end Extended

end Urm
