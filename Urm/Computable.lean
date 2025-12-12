/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Execution

/-! # URM-Computable Functions

This file defines the notion of URM-computability for partial functions on natural numbers.

## Main definitions

- `Urm.URMComputable`: A partial function is URM-computable if there exists a URM program that
  computes it.

## Future work

- Proofs that basic functions (zero, successor, projection) are URM-computable
- Closure of URM-computable functions under composition
- Closure under primitive recursion
- Closure under minimization (μ-recursion)
- Equivalence with partial recursive functions

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-- A partial function `f : (Fin n → ℕ) → Part ℕ` is URM-computable if there exists a URM program
such that for any input:
- The program halts iff the function is defined on that input
- When both are defined, the program's output equals the function's value

Note: Inputs are provided in registers 0, 1, ..., n-1 and output is read from register 0. -/
def URMComputable (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∃ p : Program, ∀ inputs : Fin n → ℕ,
    let inputList := List.ofFn inputs
    (Halts p inputList ↔ (f inputs).Dom) ∧
    ∀ (hHalts : Halts p inputList) (hDom : (f inputs).Dom),
      Result p inputList hHalts = (f inputs).get hDom

/-- Alternative formulation: the partial function computed by a program equals `f`. -/
def URMComputable' (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∃ p : Program, ∀ inputs : Fin n → ℕ,
    eval p (List.ofFn inputs) = f inputs

/-- A total function is URM-computable if its partial version is. -/
def TotalURMComputable (n : ℕ) (f : (Fin n → ℕ) → ℕ) : Prop :=
  URMComputable n (fun inputs => Part.some (f inputs))

namespace URMComputable

/-- Helper for single-instruction programs: proves both halting and result. -/
private theorem single_instr_computes {instr : Instr} {inputs : List ℕ} {finalState : State}
    (hstep : Step [instr] (Config.init inputs) ⟨1, finalState⟩) :
    Halts [instr] inputs ∧
    ∀ h : Halts [instr] inputs, Result [instr] inputs h = finalState.output := by
  have h_final_halted : (⟨1, finalState⟩ : Config).isHalted [instr] := by
    simp [Config.isHalted]
  constructor
  · exact ⟨⟨1, finalState⟩, Steps.single hstep, h_final_halted⟩
  · intro hHalts
    obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps hhalted (Steps.single hstep) h_final_halted
    simp only [Result, heq]

/-- The zero function `Z() = 0` (nullary) is URM-computable.

Program: Empty program - register 0 is initialized to 0. -/
theorem zero_computable : URMComputable 0 (fun _ => Part.some 0) := by
  use []
  intro inputs
  constructor
  · simp only [Part.some_dom, iff_true]
    exact Halts.empty_halts (List.ofFn inputs)
  · intro hHalts _
    -- Result is the output of the chosen halted config
    -- The empty program halts immediately at Config.init, so this equals 0
    obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec hHalts
    -- The init config is also halted for the empty program
    have h_init_halted : (Config.init (List.ofFn inputs)).isHalted [] := by
      simp [Config.isHalted]
    -- By uniqueness of halted configs, the chosen one equals init
    have heq := Steps.halts_unique hsteps hhalted (Steps.refl _) h_init_halted
    simp only [Result, heq, State.output, Config.init, State.fromInputs, List.getD, List.ofFn_zero,
      List.getElem?_nil, Part.get_some, Option.getD]

/-- The constant zero function of any arity is URM-computable.

Program: `[Z 0]` - set register 0 to 0 and halt. -/
theorem const_zero_computable (n : ℕ) : URMComputable n (fun _ => Part.some 0) := by
  use [Instr.Z 0]
  intro inputs
  have h := single_instr_computes (inputs := List.ofFn inputs)
    (Step.zero (p := [Instr.Z 0]) rfl)
  refine ⟨by simp [h.1], fun hHalts _ => ?_⟩
  simp only [h.2 hHalts, State.output, State.write, Function.update_self, Part.get_some]

/-- The successor function `S(x) = x + 1` is URM-computable.

Program: `[S 0]` - increment register 0 and halt. -/
theorem succ_computable : URMComputable 1 (fun inputs => Part.some (inputs 0 + 1)) := by
  use [Instr.S 0]
  intro inputs
  have h := single_instr_computes (inputs := List.ofFn inputs)
    (Step.succ (p := [Instr.S 0]) rfl)
  refine ⟨by simp only [Part.some_dom, iff_true]; exact h.1, fun hHalts _ => ?_⟩
  convert h.2 hHalts using 1

/-- General projection function `Uₖⁿ(x₀, ..., xₙ₋₁) = xₖ` is URM-computable.

Program: `[T k 0]` - copy register k to register 0. -/
theorem proj_computable (n : ℕ) (k : Fin n) :
    URMComputable n (fun inputs => Part.some (inputs k)) := by
  use [Instr.T k 0]
  intro inputs
  have h := single_instr_computes (inputs := List.ofFn inputs)
    (Step.trans (p := [Instr.T k 0]) rfl)
  refine ⟨by simp only [Part.some_dom, iff_true]; exact h.1, fun hHalts _ => ?_⟩
  simp only [h.2 hHalts, State.output, State.write, State.read, Function.update_self,
             Config.init, State.fromInputs, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
             k.isLt, ↓reduceDIte, Option.getD_some, Part.get_some]

/-- The identity/projection function `U₁¹(x) = x` is URM-computable.

This is a special case of `proj_computable` with n = 1 and k = 0. -/
theorem id_computable : URMComputable 1 (fun inputs => Part.some (inputs 0)) :=
  proj_computable 1 0

end URMComputable

end Urm
