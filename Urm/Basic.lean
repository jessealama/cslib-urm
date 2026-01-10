/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Cslib.Init
import Mathlib.Logic.Function.Basic

/-! # Unlimited Register Machines (URMs)

Unlimited Register Machines are a model of computation introduced by Shepherdson and Sturgis, and
popularized by Cutland's textbook on computability theory.

## Main definitions

- `Urm.Instr`: The four URM instructions (Z, S, T, J)
- `Urm.Program`: A finite sequence of instructions
- `Urm.State`: Register contents as a function `ℕ → ℕ`
- `Urm.Config`: Machine configuration (program counter + state)

## Conventions

We use 0-indexed registers, so R₀ is the first input and output register.
This differs from Cutland's 1-indexed convention but aligns with standard Lean/Mathlib practice.

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
* [J.C. Shepherdson and H.E. Sturgis,
  *Computability of Recursive Functions*][ShepherdsonSturgis1963]
-/

namespace Urm

/-- URM instructions.
- `Z n`: Set register n to zero
- `S n`: Increment register n by one
- `T m n`: Transfer (copy) the contents of register m to register n
- `J m n q`: If registers m and n have equal contents, jump to instruction q;
             otherwise proceed to the next instruction
-/
@[grind]
inductive Instr : Type where
  | Z : ℕ → Instr
  | S : ℕ → Instr
  | T : ℕ → ℕ → Instr
  | J : ℕ → ℕ → ℕ → Instr
deriving DecidableEq, Repr

namespace Instr

/-- The registers read by an instruction. -/
@[scoped grind =]
def readsFrom : Instr → List ℕ
  | Z _ => []
  | S n => [n]
  | T m _ => [m]
  | J m n _ => [m, n]

/-- The register written to by an instruction, if any. -/
@[scoped grind =]
def writesTo : Instr → Option ℕ
  | Z n => some n
  | S n => some n
  | T _ n => some n
  | J _ _ _ => none

/-- The maximum register index referenced by an instruction. -/
@[scoped grind =]
def maxRegister : Instr → ℕ
  | Z n => n
  | S n => n
  | T m n => max m n
  | J m n _ => max m n

/-- Shift all jump targets in an instruction by `offset`.
Used when concatenating programs to maintain correct jump destinations. -/
@[scoped grind =]
def shiftJumps (offset : ℕ) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (q + offset)

/-- Shift all register references in an instruction by `offset`.
Used to isolate register usage when composing programs. -/
@[scoped grind =]
def shiftRegisters (offset : ℕ) : Instr → Instr
  | Z n => Z (n + offset)
  | S n => S (n + offset)
  | T m n => T (m + offset) (n + offset)
  | J m n q => J (m + offset) (n + offset) q

end Instr

/-- A URM program is a list of instructions. -/
abbrev Program := List Instr

namespace Program

/-- Get the instruction at position i (0-indexed). Returns `none` if out of bounds. -/
@[scoped grind =]
def getInstr (p : Program) (i : ℕ) : Option Instr := p[i]?

/-- The maximum register index referenced by any instruction in the program. -/
@[scoped grind =]
def maxRegister (p : Program) : ℕ :=
  p.foldl (fun acc instr => max acc instr.maxRegister) 0

/-- Shift all jump targets in a program by `offset`.
Used when concatenating programs: the second program's jumps must be adjusted
by the length of the first program. -/
@[scoped grind =]
def shiftJumps (offset : ℕ) (p : Program) : Program :=
  p.map (Instr.shiftJumps offset)

/-- Shift all register references in a program by `offset`.
Used to isolate register usage when composing programs. -/
@[scoped grind =]
def shiftRegisters (offset : ℕ) (p : Program) : Program :=
  p.map (Instr.shiftRegisters offset)

end Program

/-- Register state: maps register indices to natural number contents.

Uses the functional representation `ℕ → ℕ` for efficiency with rewrites,
following the advice from the `grind` tactic documentation. -/
abbrev State := ℕ → ℕ

namespace State

/-- The zero state where all registers contain 0. -/
@[scoped grind =]
def zero : State := fun _ => 0

/-- Read the contents of register n. -/
@[scoped grind =]
def read (σ : State) (n : ℕ) : ℕ := σ n

/-- Write value v to register n. -/
@[scoped grind =]
def write (σ : State) (n : ℕ) (v : ℕ) : State := Function.update σ n v

/-- Initialize state with input values in registers 0, 1, ..., k-1.
Registers beyond the inputs are initialized to 0. -/
@[scoped grind =]
def fromInputs (inputs : List ℕ) : State := fun n => inputs.getD n 0

/-- Extract output from register 0. -/
@[scoped grind =]
def output (σ : State) : ℕ := σ 0

-- Basic lemmas about state operations

@[simp, scoped grind =]
theorem read_zero (n : ℕ) : zero.read n = 0 := rfl

@[simp, scoped grind =]
theorem write_read_same (σ : State) (n v : ℕ) : (σ.write n v).read n = v := by
  simp only [write, read, Function.update_self]

@[simp, scoped grind =]
theorem write_read_diff (σ : State) (m n v : ℕ) (h : m ≠ n) :
    (σ.write n v).read m = σ.read m := by
  simp only [write, read, Function.update_of_ne h]

@[simp, scoped grind =]
theorem fromInputs_in_range (inputs : List ℕ) (n : ℕ) (h : n < inputs.length) :
    (fromInputs inputs).read n = inputs[n] := by
  simp only [fromInputs, read, List.getD]
  simp [List.getElem?_eq_getElem h]

@[simp, scoped grind =]
theorem fromInputs_out_of_range (inputs : List ℕ) (n : ℕ) (h : inputs.length ≤ n) :
    (fromInputs inputs).read n = 0 := by
  simp only [fromInputs, read, List.getD]
  simp [List.getElem?_eq_none h]

end State

/-- Machine configuration: program counter (0-indexed) and register state. -/
structure Config where
  /-- Program counter (0-indexed). -/
  pc : ℕ
  /-- Register state. -/
  state : State

namespace Config

/-- Initial configuration for a program with given inputs.
The program counter starts at 0, and inputs are loaded into registers 0, 1, .... -/
@[scoped grind =]
def init (inputs : List ℕ) : Config := ⟨0, State.fromInputs inputs⟩

/-- A configuration is halted if the program counter is at or beyond the program length. -/
@[scoped grind =]
def isHalted (c : Config) (p : Program) : Prop := p.length ≤ c.pc

instance (c : Config) (p : Program) : Decidable (c.isHalted p) :=
  inferInstanceAs (Decidable (p.length ≤ c.pc))

@[simp]
theorem isHalted_def (c : Config) (p : Program) : c.isHalted p ↔ p.length ≤ c.pc := Iff.rfl

@[simp, scoped grind =]
theorem init_pc (inputs : List ℕ) : (init inputs).pc = 0 := rfl

@[simp, scoped grind =]
theorem init_state (inputs : List ℕ) : (init inputs).state = State.fromInputs inputs := rfl

/-- Extensionality for Config: two configs are equal iff their components are equal. -/
@[ext]
theorem ext {c₁ c₂ : Config} (hpc : c₁.pc = c₂.pc) (hstate : c₁.state = c₂.state) : c₁ = c₂ := by
  cases c₁; cases c₂; simp only at hpc hstate; simp [hpc, hstate]

instance : Inhabited Config := ⟨init []⟩

instance : Repr Config where
  reprPrec c _ := s!"Config(pc={c.pc})"

end Config

end Urm
