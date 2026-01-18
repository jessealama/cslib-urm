/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Shift
import Urm.StandardForm

/-! # URMBlock: Structured Subroutine Abstraction

A URMBlock represents a URM subroutine with an isolated register namespace.
Each block uses "local" registers 0, 1, ..., maxReg which are compiled to
disjoint actual registers via register shifting.

## Main definitions

- `URMBlock`: A subroutine with isolated register namespace
- `URMBlock.Computes`: A block computes a partial function
- `URMBlock.compile`: Compile a block at a register offset

## Key theorem

- `URMBlock.compile_preserves_computation`: Computation is preserved under
  register shifting. This single theorem, proven once, replaces scattered
  register preservation lemmas in composition/primitive recursion/minimization.

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-- A subroutine with isolated register namespace.

- Uses "local" registers 0, 1, ..., program.maxRegister
- Inputs in R₀..R_{arity-1}
- Output in R₀ on termination
- After compilation, local register r becomes actual register (offset + r)
- The program must be in standard form (all jumps target valid positions)

Note: The arity can exceed maxRegister + 1 (some inputs may be ignored by the program). -/
structure URMBlock where
  /-- The URM program implementing this block. -/
  program : Program
  /-- Number of input registers (0, 1, ..., arity-1). -/
  arity : ℕ
  /-- The program is in standard form (all jumps are bounded). -/
  h_sf : program.IsStandardForm

/-- Convenience accessor for the maximum register used by a block. -/
abbrev URMBlock.maxReg (b : URMBlock) : ℕ := b.program.maxRegister

namespace URMBlock

/-- Compile a block at a register offset.
Local register r becomes actual register (offset + r). -/
def compile (b : URMBlock) (offset : ℕ) : Program :=
  b.program.shiftRegisters offset

/-- The compiled program's length equals the original. -/
@[simp]
theorem compile_length (b : URMBlock) (offset : ℕ) :
    (b.compile offset).length = b.program.length := by
  simp [compile]

/-- A block computes a partial function f if:
1. The program halts iff f is defined on the inputs
2. When halted, R₀ contains f's value

This is parameterized by the arity n separately to avoid reduction issues. -/
def ComputesN (b : URMBlock) (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∀ inputs : Fin n → ℕ,
    let inputList := List.ofFn inputs
    (Halts b.program inputList ↔ (f inputs).Dom) ∧
    ∀ (hHalts : Halts b.program inputList) (hDom : (f inputs).Dom),
      Result b.program inputList hHalts = (f inputs).get hDom

/-- A block computes a partial function f (using the block's declared arity). -/
abbrev Computes (b : URMBlock) (f : (Fin b.arity → ℕ) → Part ℕ) : Prop :=
  b.ComputesN b.arity f

/-- Create a block from a program with given arity. -/
def ofProgram (p : Program) (arity : ℕ) (h_sf : p.IsStandardForm) : URMBlock :=
  { program := p
    arity := arity
    h_sf := h_sf }

/-- A trivial block that immediately halts (empty program). Returns input 0. -/
def identity : URMBlock where
  program := []
  arity := 1
  h_sf := by simp [Program.IsStandardForm, Program.isStandardForm]

@[simp] theorem identity_program : identity.program = [] := rfl
@[simp] theorem identity_arity : identity.arity = 1 := rfl
@[simp] theorem identity_maxReg : identity.maxReg = 0 := rfl

theorem identity_computes :
    identity.ComputesN 1 (fun inputs => Part.some (inputs 0)) := by
  intro inputs
  simp only [identity_program]
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨Config.init (List.ofFn inputs), Relation.ReflTransGen.refl, by simp [Config.init]⟩
  · intro hHalts _
    simp only [Result, Part.get_some]
    have ⟨hsteps, hhalted⟩ := Classical.choose_spec hHalts
    have heq : Classical.choose hHalts = Config.init (List.ofFn inputs) :=
      Steps.halts_unique hsteps hhalted (Steps.refl _) (by simp [Config.init])
    simp only [heq, State.output, Config.init, State.fromInputs, List.getD_eq_getElem?_getD,
               List.getElem?_ofFn]
    simp only [show (0 : ℕ) < 1 from Nat.zero_lt_one, ↓reduceDIte, Option.getD_some]
    rfl

/-- The successor block: S(x) = x + 1. Uses [S 0]. -/
def succ : URMBlock where
  program := [Instr.S 0]
  arity := 1
  h_sf := straightLine_isStandardForm (by rfl)

@[simp] theorem succ_program : succ.program = [Instr.S 0] := rfl
@[simp] theorem succ_arity : succ.arity = 1 := rfl
@[simp] theorem succ_maxReg : succ.maxReg = 0 := rfl

theorem succ_computes :
    succ.ComputesN 1 (fun inputs => Part.some (inputs 0 + 1)) := by
  intro inputs
  simp only [succ_program]
  let inputList := List.ofFn inputs
  let finalState := (State.fromInputs inputList).write 0 ((State.fromInputs inputList).read 0 + 1)
  have hstep : Step [Instr.S 0] (Config.init inputList) ⟨1, finalState⟩ := Step.succ rfl
  have hhalted : (⟨1, finalState⟩ : Config).isHalted [Instr.S 0] := by simp
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨⟨1, finalState⟩, Steps.single hstep, hhalted⟩
  · intro hHalts _
    simp only [Result, Part.get_some]
    have ⟨hsteps, hhalted'⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps hhalted' (Steps.single hstep) hhalted
    simp only [heq, finalState, Config.init, State.output, State.write, Function.update_self,
               State.read, inputList, State.fromInputs, List.getD_eq_getElem?_getD,
               List.getElem?_ofFn, Nat.zero_lt_one, ↓reduceDIte, Option.getD_some]
    rfl

/-- The projection block: proj_k(x₀,...,xₙ₋₁) = xₖ. Uses [T k 0]. -/
def proj (n : ℕ) (k : Fin n) : URMBlock where
  program := [Instr.T k 0]
  arity := n
  h_sf := straightLine_isStandardForm (by rfl)

@[simp] theorem proj_program (n : ℕ) (k : Fin n) : (proj n k).program = [Instr.T k 0] := rfl
@[simp] theorem proj_arity (n : ℕ) (k : Fin n) : (proj n k).arity = n := rfl
@[simp] theorem proj_maxReg (n : ℕ) (k : Fin n) : (proj n k).maxReg = k := by
  simp [maxReg, Program.maxRegister, List.foldl, Instr.maxRegister]

theorem proj_computes (n : ℕ) (k : Fin n) :
    (proj n k).ComputesN n (fun inputs => Part.some (inputs k)) := by
  intro inputs
  simp only [proj_program]
  let inputList := List.ofFn inputs
  let finalState := (State.fromInputs inputList).write 0 ((State.fromInputs inputList).read k)
  have hstep : Step [Instr.T k 0] (Config.init inputList) ⟨1, finalState⟩ := Step.trans rfl
  have hhalted : (⟨1, finalState⟩ : Config).isHalted [Instr.T k 0] := by simp
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨⟨1, finalState⟩, Steps.single hstep, hhalted⟩
  · intro hHalts _
    simp only [Result, Part.get_some]
    have ⟨hsteps, hhalted'⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps hhalted' (Steps.single hstep) hhalted
    simp only [heq, finalState, Config.init, State.output, State.write, Function.update_self,
               State.read, inputList, State.fromInputs, List.getD_eq_getElem?_getD,
               List.getElem?_ofFn, k.isLt, ↓reduceDIte, Option.getD_some]

/-- The zero constant block: zero() = 0. Uses [Z 0]. -/
def zero : URMBlock where
  program := [Instr.Z 0]
  arity := 0
  h_sf := straightLine_isStandardForm (by rfl)

@[simp] theorem zero_program : zero.program = [Instr.Z 0] := rfl
@[simp] theorem zero_arity : zero.arity = 0 := rfl
@[simp] theorem zero_maxReg : zero.maxReg = 0 := rfl

theorem zero_computes :
    zero.ComputesN 0 (fun _ => Part.some 0) := by
  intro inputs
  simp only [zero_program]
  let inputList := List.ofFn inputs
  let finalState := (State.fromInputs inputList).write 0 0
  have hstep : Step [Instr.Z 0] (Config.init inputList) ⟨1, finalState⟩ := Step.zero rfl
  have hhalted : (⟨1, finalState⟩ : Config).isHalted [Instr.Z 0] := by simp
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨⟨1, finalState⟩, Steps.single hstep, hhalted⟩
  · intro hHalts _
    simp only [Result, Part.get_some]
    have ⟨hsteps, hhalted'⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps hhalted' (Steps.single hstep) hhalted
    simp only [heq, finalState, Config.init, State.output, State.write, Function.update_self]

end URMBlock

/-- A partial function is URMBlock-computable if witnessed by some block. -/
def URMBlockComputable (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∃ b : URMBlock, b.arity = n ∧ b.ComputesN n f

/-- URMBlockComputable implies URMComputable. -/
theorem URMBlockComputable.toURMComputable {n : ℕ} {f : (Fin n → ℕ) → Part ℕ}
    (h : URMBlockComputable n f) : URMComputable n f := by
  obtain ⟨b, _, hcomp⟩ := h
  exact ⟨b.program, hcomp⟩

end Urm
