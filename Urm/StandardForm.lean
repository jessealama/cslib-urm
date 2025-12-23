/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.StraightLine

/-! # Standard Form Programs

This file defines standard-form programs (those that halt exactly at their length).
This property is essential for sequential composition.

## Main definitions

- `Program.IsStandardForm`: a program halts exactly at its length
- `URMComputableSF`: computability by a standard-form program

## Main results

- `straightLine_isStandardForm`: straight-line programs are standard form

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Standard Form

A program is in "standard form" if it always halts exactly at its length (by falling through
the end, not by jumping beyond). This property is essential for sequential composition:
when we concatenate programs, the first program must terminate exactly at its length so
the second program starts at the correct position.

We assume all programs are in standard form. Later, we will prove that every program
has a computationally equivalent standard form program. -/

/-- A program is in standard form if, whenever it halts, the program counter equals
the program length. -/
def Program.IsStandardForm (p : Program) : Prop :=
  ∀ (inputs : List ℕ) (c : Config),
    Steps p (Config.init inputs) c →
    c.isHalted p →
    c.pc = p.length

/-- A partial function is URM-computable by a standard form program. -/
def URMComputableSF (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∃ p : Program, p.IsStandardForm ∧
    ∀ inputs : Fin n → ℕ,
      let inputList := List.ofFn inputs
      (Halts p inputList ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts p inputList) (hDom : (f inputs).Dom),
        Result p inputList hHalts = (f inputs).get hDom

/-- Straight-line programs are in standard form.

Since straight-line programs have no jumps, they can only increment the program counter
by 1 at each step, so they must halt exactly at the program length. -/
theorem straightLine_isStandardForm {p : Program} (hsl : p.isStraightLine = true) :
    p.IsStandardForm := by
  intro inputs c hsteps hhalted
  have hHalts : Halts p inputs := ⟨c, hsteps, hhalted⟩
  have hHalts' := straightLine_halts hsl inputs
  obtain ⟨hsteps', hhalted'⟩ := Classical.choose_spec hHalts'
  have heq := Steps.halts_unique hsteps hhalted hsteps' hhalted'
  rw [heq]
  exact straightLine_halts_at_length hsl inputs

end Urm
