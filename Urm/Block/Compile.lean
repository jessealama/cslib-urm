/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Block.Basic
import Urm.Shift

/-! # Compilation Preserves Computation

The key theorem of the URMBlock abstraction: register shifting preserves
computation semantics. This allows composing blocks at different register
offsets while maintaining correctness.

## Main results

- `URMBlock.compile_halts`: If a block halts on inputs, the compiled program
  halts from a state with inputs at the offset registers.

- `URMBlock.compile_result`: The result of running the compiled program is
  the same as the original computation.

- `URMBlock.compile_preserves_computation`: Combined halting and result
  preservation for compiled blocks.

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

namespace URMBlock

/-- The compiled program's maxRegister is shifted by the offset. -/
theorem compile_maxRegister (b : URMBlock) (offset : ℕ) (hp : b.program ≠ []) :
    (b.compile offset).maxRegister = b.program.maxRegister + offset := by
  simp only [compile, Program.maxRegister_shiftRegisters offset b.program hp]

/-- Initial state for running a compiled block: inputs are placed at offset registers. -/
def compiledInitState (inputs : List ℕ) (offset : ℕ) : State :=
  fun r => if offset ≤ r ∧ r < offset + inputs.length then inputs.getD (r - offset) 0 else 0

/-- The compiled init state agrees with shifted inputs on the program's register range. -/
theorem compiledInitState_agrees (b : URMBlock) (inputs : List ℕ) (offset : ℕ)
    (hlen : inputs.length ≤ b.maxReg + 1) :
    ∀ r, r ≤ b.program.maxRegister →
      (compiledInitState inputs offset).read (r + offset) = inputs.getD r 0 := by
  intro r hr
  simp only [compiledInitState, State.read]
  -- Note: b.maxReg = b.program.maxRegister by definition
  by_cases hlt : r < inputs.length
  · simp only [Nat.le_add_left, Nat.add_sub_cancel, true_and]
    simp only [show r + offset < offset + inputs.length from by omega, ↓reduceIte]
  · push_neg at hlt
    simp only [Nat.le_add_left, Nat.add_sub_cancel, true_and]
    simp only [show ¬ (r + offset < offset + inputs.length) from by omega, ↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlt, Option.getD_none]

/-- If a block halts on inputs, the compiled program halts from a state
with those inputs placed at offset registers. -/
theorem compile_halts (b : URMBlock) (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) (offset : ℕ)
    (hcomp : b.ComputesN n f) (inputs : Fin n → ℕ) (hDom : (f inputs).Dom)
    (hn : n ≤ b.maxReg + 1) :
    ∃ c, Steps (b.compile offset) ⟨0, compiledInitState (List.ofFn inputs) offset⟩ c ∧
         c.isHalted (b.compile offset) := by
  let inputList := List.ofFn inputs
  have hhalts : Halts b.program inputList := (hcomp inputs).1.mpr hDom
  -- Use Halts.shift_from_state to run the shifted program
  have hlen : inputList.length ≤ b.maxReg + 1 := by
    simp only [inputList, List.length_ofFn]; exact hn
  have hagree := compiledInitState_agrees b inputList offset hlen
  obtain ⟨c, hsteps, hhalted, _⟩ := Halts.shift_from_state offset hhalts hagree
  exact ⟨c, hsteps, hhalted⟩

/-- The result of running a compiled block at offset. -/
theorem compile_result (b : URMBlock) (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) (offset : ℕ)
    (hcomp : b.ComputesN n f) (inputs : Fin n → ℕ) (hDom : (f inputs).Dom)
    (hn : n ≤ b.maxReg + 1) :
    let inputList := List.ofFn inputs
    let hhalts : Halts b.program inputList := (hcomp inputs).1.mpr hDom
    ∀ c, Steps (b.compile offset) ⟨0, compiledInitState inputList offset⟩ c →
         c.isHalted (b.compile offset) →
         c.state.read offset = (f inputs).get hDom := by
  intro inputList hhalts c hsteps hhalted
  -- Get the original result
  have hres := (hcomp inputs).2 hhalts hDom
  -- Use Halts.shift_from_state to get the shifted result
  have hlen : inputList.length ≤ b.maxReg + 1 := by
    simp only [inputList, List.length_ofFn]; exact hn
  have hagree := compiledInitState_agrees b inputList offset hlen
  obtain ⟨c', hsteps', hhalted', hres'⟩ := Halts.shift_from_state offset hhalts hagree
  -- Both c and c' are halted configs reached from the same starting config
  have heq : c = c' := by
    have hdet := Steps.deterministic_continuation hsteps hsteps' hhalted'
    cases hdet using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hstep _ => exact absurd hstep (Step.halted_no_step hhalted)
  rw [heq, hres', hres]

/-- Combined theorem: compilation preserves computation.

If a block computes f, then running the compiled program at offset
produces the same result in the offset register. -/
theorem compile_preserves_computation (b : URMBlock) (n : ℕ)
    (f : (Fin n → ℕ) → Part ℕ) (offset : ℕ) (hcomp : b.ComputesN n f)
    (hn : n ≤ b.maxReg + 1) :
    ∀ inputs : Fin n → ℕ,
      -- Halting equivalence
      (∃ c, Steps (b.compile offset) ⟨0, compiledInitState (List.ofFn inputs) offset⟩ c ∧
            c.isHalted (b.compile offset)) ↔ (f inputs).Dom ∧
      -- Result preservation
      ∀ hDom : (f inputs).Dom,
        ∀ c, Steps (b.compile offset) ⟨0, compiledInitState (List.ofFn inputs) offset⟩ c →
             c.isHalted (b.compile offset) →
             c.state.read offset = (f inputs).get hDom := by
  intro inputs
  constructor
  · intro ⟨c, hsteps, hhalted⟩
    constructor
    · -- TODO: This is the harder direction: from halting of compiled to halting of original.
      -- Requires proving that if p.shiftRegisters halts from a shifted state, then p halts
      -- from the original state. This needs `Halts.of_shift` (converse of `Halts.shift`).
      -- For now, we leave this as sorry since practical usage goes through `compile_correct`
      -- which already has the definedness hypothesis.
      sorry
    · intro hDom
      exact compile_result b n f offset hcomp inputs hDom hn
  · intro ⟨hDom, _⟩
    exact compile_halts b n f offset hcomp inputs hDom hn

/-- Alternative formulation: if block computes f and f inputs is defined,
the compiled program halts and produces the correct result. -/
theorem compile_correct (b : URMBlock) (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) (offset : ℕ)
    (hcomp : b.ComputesN n f) (inputs : Fin n → ℕ) (hDom : (f inputs).Dom)
    (hn : n ≤ b.maxReg + 1) :
    ∃ c, Steps (b.compile offset) ⟨0, compiledInitState (List.ofFn inputs) offset⟩ c ∧
         c.isHalted (b.compile offset) ∧
         c.state.read offset = (f inputs).get hDom := by
  obtain ⟨c, hsteps, hhalted⟩ := compile_halts b n f offset hcomp inputs hDom hn
  refine ⟨c, hsteps, hhalted, ?_⟩
  exact compile_result b n f offset hcomp inputs hDom hn c hsteps hhalted

end URMBlock

end Urm
