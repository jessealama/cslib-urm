/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable
import Urm.Arithmetic
import Urm.Composition.Basic
import Urm.PrimitiveRecursion.Basic
import Urm.Minimization.Basic
import Mathlib.Computability.Partrec
import Mathlib.Data.Nat.Sqrt

/-! # URM Computability and Partial Recursive Functions

This file proves that all partial recursive functions (as defined by Mathlib's `Nat.Partrec`)
are URM-computable, establishing equivalence between these computation models.

## Main results

- `Nat.Partrec.toURMComputable1`: Every `Nat.Partrec` function is URM-computable

## Strategy

We prove this by induction on the `Nat.Partrec` inductive type:
- `zero`: constant 0 - trivial
- `succ`: successor - existing theorem
- `left`/`right`: unpair components - need arithmetic helpers
- `pair`: pairing two functions - composition with pairing
- `comp`: composition - existing closure theorem
- `prec`: primitive recursion - existing closure theorem (adapted)
- `rfind`: minimization - existing closure theorem

## References

* Mathlib's `Mathlib.Computability.Partrec`
* N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*
-/

namespace Urm

open Nat (pair unpair)
open Part

/-! ## Unary Function Wrapper -/

/-- A unary partial function `ℕ →. ℕ` is URM-computable. -/
def URMComputable1 (f : ℕ →. ℕ) : Prop :=
  URMComputable 1 (fun x => f (x 0))

namespace URMComputable1

/-! ## Basic Lemmas -/

/-- Convert between URMComputable 1 and URMComputable1 -/
theorem of_URMComputable {f : (Fin 1 → ℕ) → Part ℕ}
    (hf : URMComputable 1 f) :
    URMComputable1 (fun n => f (fun _ => n)) := by
  unfold URMComputable1
  convert hf using 1
  ext x
  -- Goal: (fun n => f (fun _ => n)) (x 0) = f x
  -- Since x : Fin 1 → ℕ, we have (fun _ => x 0) = x
  have h : (fun _ : Fin 1 => x 0) = x := by ext i; simp [Fin.eq_zero i]
  simp only [h]

theorem to_URMComputable {f : ℕ →. ℕ}
    (hf : URMComputable1 f) : URMComputable 1 (fun x => f (x 0)) :=
  hf

end URMComputable1

/-! ## Arithmetic Helpers -/

section Arithmetic

-- add_computable is now provided by Urm.Arithmetic
-- pred_computable is now provided by Urm.Arithmetic

/-- Monus (truncated subtraction) is URM-computable.
    sub(x, 0) = x, sub(x, y+1) = pred(sub(x, y)) -/
theorem sub_computable : URMComputable 2 (fun xy => Part.some (xy 0 - xy 1)) := by
  sorry

-- mul_computable is now provided by Urm.Arithmetic

/-- URM program that computes sign: sign(0) = 0, sign(n) = 1 for n > 0

Uses R1 as a zero register for comparison. -/
def signProgram : Program := [
  Instr.Z 1,      -- 0: Clear R1 (zero for comparison)
  Instr.J 0 1 4,  -- 1: If R0 = R1 (=0), jump to 4 (halt with 0)
  Instr.Z 0,      -- 2: Clear R0
  Instr.S 0       -- 3: Set R0 = 1, then halt (pc goes to 4)
]                 -- 4: Program ends (halted)

namespace signProgram

-- Helper lemmas about getInstr
@[simp] theorem getInstr_0 : signProgram.getInstr 0 = some (Instr.Z 1) := rfl
@[simp] theorem getInstr_1 : signProgram.getInstr 1 = some (Instr.J 0 1 4) := rfl
@[simp] theorem getInstr_2 : signProgram.getInstr 2 = some (Instr.Z 0) := rfl
@[simp] theorem getInstr_3 : signProgram.getInstr 3 = some (Instr.S 0) := rfl
@[simp] theorem length_eq : signProgram.length = 4 := rfl

/-- Clear R1 for zero check (pc 0 → 1). -/
theorem step_clear_r1 (s : State) :
    Step signProgram ⟨0, s⟩ ⟨1, s.write 1 0⟩ :=
  Step.zero getInstr_0

/-- When R0 = 0 (= R1 after clear), jump to halt (pc 1 → 4). -/
theorem step_zero_exit (s : State) (heq : s.read 0 = s.read 1) :
    Step signProgram ⟨1, s⟩ ⟨4, s⟩ :=
  Step.jump_eq getInstr_1 heq

/-- When R0 ≠ 0, continue to clear R0 (pc 1 → 2). -/
theorem step_nonzero_continue (s : State) (hne : s.read 0 ≠ s.read 1) :
    Step signProgram ⟨1, s⟩ ⟨2, s⟩ :=
  Step.jump_ne getInstr_1 hne

/-- Clear R0 (pc 2 → 3). -/
theorem step_clear_r0 (s : State) :
    Step signProgram ⟨2, s⟩ ⟨3, s.write 0 0⟩ :=
  Step.zero getInstr_2

/-- Increment R0 to 1 (pc 3 → 4). -/
theorem step_inc_r0 (s : State) :
    Step signProgram ⟨3, s⟩ ⟨4, s.write 0 (s.read 0 + 1)⟩ :=
  Step.succ getInstr_3

/-- Configuration at pc=4 is halted. -/
theorem halted_at_4 (s : State) : (⟨4, s⟩ : Config).isHalted signProgram := by
  simp [Config.isHalted, length_eq]

/-- Full execution for input 0: halts at pc=4 with R0=0. -/
theorem execution_zero :
    ∃ s, Steps signProgram (Config.init [0]) ⟨4, s⟩ ∧
         s.read 0 = 0 ∧
         (⟨4, s⟩ : Config).isHalted signProgram := by
  let s0 := State.fromInputs [0]
  let s1 := s0.write 1 0
  -- Step 0→1: clear R1
  have h1 : Step signProgram ⟨0, s0⟩ ⟨1, s1⟩ := step_clear_r1 s0
  -- Step 1→4: jump (R0 = R1 = 0)
  have heq : s1.read 0 = s1.read 1 := by
    simp [s1, s0, State.write, State.read, State.fromInputs, Function.update_of_ne]
  have h2 : Step signProgram ⟨1, s1⟩ ⟨4, s1⟩ := step_zero_exit s1 heq
  use s1
  refine ⟨Steps.trans (Steps.single h1) (Steps.single h2), ?_, halted_at_4 s1⟩
  simp [s1, s0, State.write, State.read, State.fromInputs, Function.update_of_ne]

/-- Full execution for input n > 0: halts at pc=4 with R0=1. -/
theorem execution_nonzero (n : ℕ) (hn : n > 0) :
    ∃ s, Steps signProgram (Config.init [n]) ⟨4, s⟩ ∧
         s.read 0 = 1 ∧
         (⟨4, s⟩ : Config).isHalted signProgram := by
  let s0 := State.fromInputs [n]
  let s1 := s0.write 1 0
  let s2 := s1.write 0 0
  let s3 := s2.write 0 (s2.read 0 + 1)
  -- Step 0→1: clear R1
  have h1 : Step signProgram ⟨0, s0⟩ ⟨1, s1⟩ := step_clear_r1 s0
  -- Step 1→2: no jump (R0 = n ≠ 0 = R1)
  have hne : s1.read 0 ≠ s1.read 1 := by
    simp [s1, s0, State.write, State.read, State.fromInputs, Function.update_of_ne]
    omega
  have h2 : Step signProgram ⟨1, s1⟩ ⟨2, s1⟩ := step_nonzero_continue s1 hne
  -- Step 2→3: clear R0
  have h3 : Step signProgram ⟨2, s1⟩ ⟨3, s2⟩ := step_clear_r0 s1
  -- Step 3→4: increment R0 to 1
  have h4 : Step signProgram ⟨3, s2⟩ ⟨4, s3⟩ := step_inc_r0 s2
  use s3
  refine ⟨Steps.trans (Steps.trans (Steps.trans (Steps.single h1) (Steps.single h2))
                      (Steps.single h3)) (Steps.single h4), ?_, halted_at_4 s3⟩
  simp [s3, s2, s1, s0, State.write, State.read, Function.update_self]

end signProgram

/-- Sign function: sign(0) = 0, sign(n+1) = 1 -/
theorem sign_computable : URMComputable 1 (fun x => Part.some (if x 0 = 0 then 0 else 1)) := by
  use signProgram
  intro inputs
  let n := inputs 0
  have h_ofFn : List.ofFn inputs = [n] := by simp only [List.ofFn]; rfl
  constructor
  · -- Halting: always halts
    simp only [Part.some_dom, iff_true]
    by_cases hn : n = 0
    · -- n = 0 case
      rw [h_ofFn]
      simp only [hn]
      obtain ⟨s, hsteps, _, hhalted⟩ := signProgram.execution_zero
      exact ⟨⟨4, s⟩, hsteps, hhalted⟩
    · -- n > 0 case
      rw [h_ofFn]
      have hn' : n > 0 := Nat.pos_of_ne_zero hn
      obtain ⟨s, hsteps, _, hhalted⟩ := signProgram.execution_nonzero n hn'
      exact ⟨⟨4, s⟩, hsteps, hhalted⟩
  · -- Result equality
    intro hHalts _
    obtain ⟨hsteps_chosen, hhalted_chosen⟩ := Classical.choose_spec hHalts
    by_cases hn : n = 0
    · -- n = 0 case: result = 0
      obtain ⟨s, hsteps, hr0, hhalted⟩ := signProgram.execution_zero
      have hsteps' : Steps signProgram (Config.init (List.ofFn inputs)) ⟨4, s⟩ := by
        simp only [h_ofFn, hn]; exact hsteps
      have heq := Steps.halts_unique hsteps_chosen hhalted_chosen hsteps' hhalted
      simp only [Result, heq, State.output, Part.get_some, State.read] at hr0 ⊢
      rw [show inputs 0 = 0 from hn, if_pos rfl]
      exact hr0
    · -- n > 0 case: result = 1
      have hn' : n > 0 := Nat.pos_of_ne_zero hn
      obtain ⟨s, hsteps, hr0, hhalted⟩ := signProgram.execution_nonzero n hn'
      have hsteps' : Steps signProgram (Config.init (List.ofFn inputs)) ⟨4, s⟩ := by
        simp only [h_ofFn]; exact hsteps
      have heq := Steps.halts_unique hsteps_chosen hhalted_chosen hsteps' hhalted
      simp only [Result, heq, State.output, Part.get_some, State.read] at hr0 ⊢
      rw [if_neg (show inputs 0 ≠ 0 from hn)]
      exact hr0

/-- Helper: sign(y - x) equals the characteristic function of x < y -/
private theorem sign_sub_swap_eq_lt (x y : ℕ) :
    (if y - x = 0 then 0 else 1) = if x < y then 1 else 0 := by
  by_cases h : x < y
  · -- x < y: y - x > 0, so sign = 1
    have hsub : y - x ≠ 0 := Nat.sub_ne_zero_of_lt h
    simp [hsub, h]
  · -- x ≥ y: y - x = 0, so sign = 0
    have hsub : y - x = 0 := Nat.sub_eq_zero_of_le (Nat.not_lt.mp h)
    simp [hsub, h]

/-- The inner functions for lt: swap projections (y, x) for monus. -/
private def ltSwapGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun xy => Part.some (xy 1)) else (fun xy => Part.some (xy 0))

@[simp] private theorem ltSwapGs_zero : ltSwapGs 0 = fun xy => Part.some (xy 1) := rfl
@[simp] private theorem ltSwapGs_one : ltSwapGs 1 = fun xy => Part.some (xy 0) := rfl

/-- Helper: Composing monus with swapped projections computes y - x. -/
private theorem lt_rev_sub_eq (xy : Fin 2 → ℕ) :
    compFunction 2 2 (fun ab => Part.some (ab 0 - ab 1)) ltSwapGs xy =
    Part.some (xy 1 - xy 0) := by
  have h0 : ltSwapGs 0 xy = Part.some (xy 1) := rfl
  have h1 : ltSwapGs (Fin.succ 0) xy = Part.some (xy 0) := rfl
  simp only [compFunction, Part.sequence, h0, h1, Part.bind_some, Part.map_some]
  rfl

/-- Helper: The full lt composition function. -/
private def ltOuterG : Fin 1 → (Fin 2 → ℕ) → Part ℕ :=
  fun _ xy => Part.some (xy 1 - xy 0)

/-- Helper: Composing sign with (y - x) computes lt. -/
private theorem lt_comp_eq (xy : Fin 2 → ℕ) :
    compFunction 1 2 (fun x => Part.some (if x 0 = 0 then 0 else 1)) ltOuterG xy =
    Part.some (if xy 0 < xy 1 then 1 else 0) := by
  have h0 : ltOuterG 0 xy = Part.some (xy 1 - xy 0) := rfl
  simp only [compFunction, Part.sequence, h0, Part.bind_some, Part.map_some]
  simp only [Fin.cons_zero]
  exact congrArg Part.some (sign_sub_swap_eq_lt (xy 0) (xy 1))

/-- Less-than comparison returns 1 if x < y, else 0.
    lt(x, y) = sign(y - x) -/
theorem lt_computable : URMComputable 2 (fun xy => Part.some (if xy 0 < xy 1 then 1 else 0)) := by
  -- Step 1: Compose monus with swapped projections to compute (y - x)
  have hRevSub : URMComputableSF 2 (fun xy => Part.some (xy 1 - xy 0)) := by
    have hgs : ∀ i, URMComputable 2 (ltSwapGs i) := by
      intro i; fin_cases i <;> simp only [ltSwapGs] <;> exact URMComputable.proj_computable 2 _
    have h := URMComputable.comp_general (m := 2) (n := 2) monus_computable hgs
    convert h using 1
    funext xy
    exact (lt_rev_sub_eq xy).symm
  -- Step 2: Compose sign with reversed subtraction
  have hLt := URMComputable.comp_general (m := 1) (n := 2)
    sign_computable
    (fun _ => hRevSub.toComputable)
  -- Step 3: Convert to desired form
  convert hLt.toComputable using 1
  funext xy
  -- The inner function of hLt is (fun _ => hRevSub.toComputable) which equals ltOuterG
  -- We need to show the compFunction equals the desired result
  simp only [compFunction, Part.sequence, Part.bind_some, Part.map_some, Fin.cons_zero]
  exact congrArg Part.some (sign_sub_swap_eq_lt (xy 0) (xy 1)).symm

/-- Helper: 1 - sign(x - y) equals the characteristic function of x ≤ y -/
private theorem one_minus_sign_sub_eq_le (x y : ℕ) :
    1 - (if x - y = 0 then 0 else 1) = if x ≤ y then 1 else 0 := by
  by_cases h : x ≤ y
  · -- x ≤ y: x - y = 0, so 1 - 0 = 1
    have hsub : x - y = 0 := Nat.sub_eq_zero_of_le h
    simp [hsub, h]
  · -- x > y: x - y > 0, so 1 - 1 = 0
    have hgt : x > y := Nat.not_le.mp h
    have hsub : x - y ≠ 0 := Nat.sub_ne_zero_of_lt hgt
    simp [hsub, h]

/-- The inner functions for le: standard projections (x, y) for monus. -/
private def leGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun xy => Part.some (xy 0)) else (fun xy => Part.some (xy 1))

@[simp] private theorem leGs_zero : leGs 0 = fun xy => Part.some (xy 0) := rfl
@[simp] private theorem leGs_one : leGs 1 = fun xy => Part.some (xy 1) := rfl

/-- Helper: Composing monus with standard projections computes x - y. -/
private theorem le_sub_eq (xy : Fin 2 → ℕ) :
    compFunction 2 2 (fun ab => Part.some (ab 0 - ab 1)) leGs xy =
    Part.some (xy 0 - xy 1) := by
  have h0 : leGs 0 xy = Part.some (xy 0) := rfl
  have h1 : leGs (Fin.succ 0) xy = Part.some (xy 1) := rfl
  simp only [compFunction, Part.sequence, h0, h1, Part.bind_some, Part.map_some]
  rfl

/-- The intermediate function: sign(x - y). -/
private def leSignXY : (Fin 2 → ℕ) → Part ℕ :=
  fun xy => Part.some (if xy 0 - xy 1 = 0 then 0 else 1)

/-- sign(x - y) is computable in standard form. -/
private theorem leSignXY_computable : URMComputableSF 2 leSignXY := by
  -- First compose monus with leGs to get x - y
  have hSub : URMComputableSF 2 (fun xy => Part.some (xy 0 - xy 1)) := by
    have hgs : ∀ i, URMComputable 2 (leGs i) := by
      intro i; fin_cases i <;> simp only [leGs] <;> exact URMComputable.proj_computable 2 _
    have h := URMComputable.comp_general (m := 2) (n := 2) monus_computable hgs
    convert h using 1
    funext xy
    exact (le_sub_eq xy).symm
  -- Then compose sign with subtraction
  have h := URMComputable.comp_general (m := 1) (n := 2)
    sign_computable
    (fun _ => hSub.toComputable)
  convert h using 1
  funext xy
  simp only [compFunction, Part.sequence, Part.bind_some, Part.map_some, Fin.cons_zero, leSignXY]

/-- The outer functions for le: (constant 1, sign(x - y)). -/
private def leOuterGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun _ => Part.some 1) else leSignXY

@[simp] private theorem leOuterGs_zero : leOuterGs 0 = fun _ => Part.some 1 := rfl
@[simp] private theorem leOuterGs_one : leOuterGs 1 = leSignXY := rfl

/-- Constant 1 is URMComputable 2 (program: Z 0, S 0). -/
private theorem const_one_computable : URMComputable 2 (fun _ : Fin 2 → ℕ => Part.some 1) := by
  use [Instr.Z 0, Instr.S 0]
  intro inputs
  -- Build the execution: Z 0 clears R0, S 0 increments to 1, then halt at pc=2
  let s0 := State.fromInputs (List.ofFn inputs)
  let s1 := s0.write 0 0
  let s2 := s1.write 0 (s1.read 0 + 1)
  have hstep1 : Step [Instr.Z 0, Instr.S 0] ⟨0, s0⟩ ⟨1, s1⟩ := Step.zero rfl
  have hstep2 : Step [Instr.Z 0, Instr.S 0] ⟨1, s1⟩ ⟨2, s2⟩ := Step.succ rfl
  have hhalted : (⟨2, s2⟩ : Config).isHalted [Instr.Z 0, Instr.S 0] := by simp
  have hsteps : Steps [Instr.Z 0, Instr.S 0] (Config.init (List.ofFn inputs)) ⟨2, s2⟩ :=
    Steps.trans (Steps.single hstep1) (Steps.single hstep2)
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨⟨2, s2⟩, hsteps, hhalted⟩
  · intro hHalts _
    obtain ⟨hsteps', hhalted'⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps' hhalted' hsteps hhalted
    simp only [Result, heq, State.output, s2, s1, s0, State.write, State.read,
      Function.update_self, Part.get_some]

/-- Helper: Composing monus with (const 1, sign(x-y)) computes 1 - sign(x-y). -/
private theorem le_comp_eq (xy : Fin 2 → ℕ) :
    compFunction 2 2 (fun ab => Part.some (ab 0 - ab 1)) leOuterGs xy =
    Part.some (if xy 0 ≤ xy 1 then 1 else 0) := by
  have h0 : leOuterGs 0 xy = Part.some 1 := rfl
  have h1 : leOuterGs (Fin.succ 0) xy = Part.some (if xy 0 - xy 1 = 0 then 0 else 1) := rfl
  simp only [compFunction, Part.sequence, h0, h1, Part.bind_some, Part.map_some, Fin.cons_zero]
  exact congrArg Part.some (one_minus_sign_sub_eq_le (xy 0) (xy 1))

/-- Less-than-or-equal comparison returns 1 if x ≤ y, else 0.
    le(x, y) = 1 - sign(x - y) -/
theorem le_computable : URMComputable 2 (fun xy => Part.some (if xy 0 ≤ xy 1 then 1 else 0)) := by
  -- Compose monus with (const 1, sign(x-y)) to compute 1 - sign(x-y)
  have hgs : ∀ i, URMComputable 2 (leOuterGs i) := by
    intro i; fin_cases i
    · simp only [leOuterGs]; exact const_one_computable
    · simp only [leOuterGs]; exact leSignXY_computable.toComputable
  have h := URMComputable.comp_general (m := 2) (n := 2) monus_computable hgs
  convert h.toComputable using 1
  funext xy
  exact (le_comp_eq xy).symm

/-- Helper: le(x,y) * le(y,x) equals the characteristic function of x = y -/
private theorem le_mul_le_swap_eq_eq (x y : ℕ) :
    (if x ≤ y then 1 else 0) * (if y ≤ x then 1 else 0) = if x = y then 1 else 0 := by
  by_cases h : x = y
  · -- x = y: both conditions true, 1 * 1 = 1
    simp [h]
  · -- x ≠ y: at least one condition false
    have hne : x < y ∨ y < x := Nat.lt_or_lt_of_ne h
    rcases hne with hlt | hgt
    · -- x < y: y ≤ x is false
      simp [Nat.le_of_lt hlt, Nat.not_le.mpr hlt, h]
    · -- y < x: x ≤ y is false
      simp [Nat.le_of_lt hgt, Nat.not_le.mpr hgt, h]

/-- The inner functions for eq: le(x,y) and le(y,x). -/
private def eqGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0
           then (fun xy => Part.some (if xy 0 ≤ xy 1 then 1 else 0))
           else (fun xy => Part.some (if xy 1 ≤ xy 0 then 1 else 0))

@[simp] private theorem eqGs_zero : eqGs 0 = fun xy => Part.some (if xy 0 ≤ xy 1 then 1 else 0) := rfl
@[simp] private theorem eqGs_one : eqGs 1 = fun xy => Part.some (if xy 1 ≤ xy 0 then 1 else 0) := rfl

/-- Swapped projections for computing le(y, x). -/
private def leSwapGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun xy => Part.some (xy 1)) else (fun xy => Part.some (xy 0))

@[simp] private theorem leSwapGs_zero : leSwapGs 0 = fun xy => Part.some (xy 1) := rfl
@[simp] private theorem leSwapGs_one : leSwapGs 1 = fun xy => Part.some (xy 0) := rfl

/-- Helper: Composing le with swapped projections computes le(y, x). -/
private theorem leSwap_comp_eq (xy : Fin 2 → ℕ) :
    compFunction 2 2 (fun ab => Part.some (if ab 0 ≤ ab 1 then 1 else 0)) leSwapGs xy =
    Part.some (if xy 1 ≤ xy 0 then 1 else 0) := by
  have h0 : leSwapGs 0 xy = Part.some (xy 1) := rfl
  have h1 : leSwapGs (Fin.succ 0) xy = Part.some (xy 0) := rfl
  simp only [compFunction, Part.sequence, h0, h1, Part.bind_some, Part.map_some]
  rfl

/-- le(y, x) is computable (le with swapped arguments). -/
private theorem leSwap_computable : URMComputable 2 (fun xy => Part.some (if xy 1 ≤ xy 0 then 1 else 0)) := by
  -- Compose le_computable with swapped projections
  have hgs : ∀ i, URMComputable 2 (leSwapGs i) := by
    intro i; fin_cases i <;> simp only [leSwapGs] <;> exact URMComputable.proj_computable 2 _
  have h := URMComputable.comp_general (m := 2) (n := 2) le_computable hgs
  convert h.toComputable using 1
  funext xy
  exact (leSwap_comp_eq xy).symm

/-- Helper: Composing mul with (le(x,y), le(y,x)) computes equality. -/
private theorem eq_comp_eq (xy : Fin 2 → ℕ) :
    compFunction 2 2 (fun ab => Part.some (ab 0 * ab 1)) eqGs xy =
    Part.some (if xy 0 = xy 1 then 1 else 0) := by
  have h0 : eqGs 0 xy = Part.some (if xy 0 ≤ xy 1 then 1 else 0) := rfl
  have h1 : eqGs (Fin.succ 0) xy = Part.some (if xy 1 ≤ xy 0 then 1 else 0) := rfl
  simp only [compFunction, Part.sequence, h0, h1, Part.bind_some, Part.map_some]
  exact congrArg Part.some (le_mul_le_swap_eq_eq (xy 0) (xy 1))

/-- Equality check returns 1 if x = y, else 0.
    eq(x, y) = le(x, y) * le(y, x) -/
theorem eq_computable : URMComputable 2 (fun xy => Part.some (if xy 0 = xy 1 then 1 else 0)) := by
  -- Compose mul with (le(x,y), le(y,x)) to compute le(x,y) * le(y,x)
  have hgs : ∀ i, URMComputable 2 (eqGs i) := by
    intro i; fin_cases i
    · simp only [eqGs]; exact le_computable
    · simp only [eqGs]; exact leSwap_computable
  have h := URMComputable.comp_general (m := 2) (n := 2) mul_computable hgs
  convert h.toComputable using 1
  funext xy
  exact (eq_comp_eq xy).symm

end Arithmetic

/-! ## Square Root via Minimization -/

section Sqrt

/-! ### Step 1: Build s+1 from inputs (n, s) -/

/-- Helper functions for computing s+1: [proj_s, const_1].
    gs 0 = s (projection of second argument)
    gs 1 = 1 (constant) -/
private def sqrtSPlus1Gs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun ns => Part.some (ns 1)) else (fun _ => Part.some 1)

@[simp] private theorem sqrtSPlus1Gs_zero : sqrtSPlus1Gs 0 = fun ns => Part.some (ns 1) := rfl
@[simp] private theorem sqrtSPlus1Gs_one : sqrtSPlus1Gs 1 = fun _ => Part.some 1 := rfl

/-- Composing add with [proj_s, const_1] computes s + 1. -/
private theorem sqrtSPlus1_comp_eq (ns : Fin 2 → ℕ) :
    compFunction 2 2 (fun xy => Part.some (xy 0 + xy 1)) sqrtSPlus1Gs ns =
    Part.some (ns 1 + 1) := by
  have h0 : sqrtSPlus1Gs 0 ns = Part.some (ns 1) := rfl
  have h1 : sqrtSPlus1Gs (Fin.succ 0) ns = Part.some 1 := rfl
  simp only [compFunction, Part.sequence, h0, h1, Part.bind_some, Part.map_some]
  rfl

/-- s + 1 is computable as a function of (n, s). -/
private theorem sqrtSPlus1_computable : URMComputable 2 (fun ns => Part.some (ns 1 + 1)) := by
  have hgs : ∀ i, URMComputable 2 (sqrtSPlus1Gs i) := by
    intro i; fin_cases i
    · simp only [sqrtSPlus1Gs]; exact URMComputable.proj_computable 2 1
    · simp only [sqrtSPlus1Gs]; exact const_one_computable
  have h := URMComputable.comp_general (m := 2) (n := 2) add_computable hgs
  convert h.toComputable using 1
  funext ns
  exact (sqrtSPlus1_comp_eq ns).symm

/-! ### Step 2: Build (s+1)² from inputs (n, s) -/

/-- Helper functions for computing (s+1)²: [s+1, s+1]. -/
private def sqrtSquareGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun _ ns => Part.some (ns 1 + 1)

@[simp] private theorem sqrtSquareGs_def (i : Fin 2) : sqrtSquareGs i = fun ns => Part.some (ns 1 + 1) := rfl

/-- Composing mul with [s+1, s+1] computes (s+1)². -/
private theorem sqrtSquare_comp_eq (ns : Fin 2 → ℕ) :
    compFunction 2 2 (fun xy => Part.some (xy 0 * xy 1)) sqrtSquareGs ns =
    Part.some ((ns 1 + 1) * (ns 1 + 1)) := by
  have h0 : sqrtSquareGs 0 ns = Part.some (ns 1 + 1) := rfl
  have h1 : sqrtSquareGs (Fin.succ 0) ns = Part.some (ns 1 + 1) := rfl
  simp only [compFunction, Part.sequence, h0, h1, Part.bind_some, Part.map_some]
  rfl

/-- (s+1)² is computable as a function of (n, s). -/
private theorem sqrtSquare_computable : URMComputable 2 (fun ns => Part.some ((ns 1 + 1) * (ns 1 + 1))) := by
  have hgs : ∀ i, URMComputable 2 (sqrtSquareGs i) := fun _ => sqrtSPlus1_computable
  have h := URMComputable.comp_general (m := 2) (n := 2) mul_computable hgs
  convert h.toComputable using 1
  funext ns
  exact (sqrtSquare_comp_eq ns).symm

/-! ### Step 3: Build predicate (s+1)² ≤ n -/

/-- Helper functions for the predicate: [(s+1)², n]. -/
private def sqrtPredGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0
           then (fun ns => Part.some ((ns 1 + 1) * (ns 1 + 1)))
           else (fun ns => Part.some (ns 0))

@[simp] private theorem sqrtPredGs_zero : sqrtPredGs 0 = fun ns => Part.some ((ns 1 + 1) * (ns 1 + 1)) := rfl
@[simp] private theorem sqrtPredGs_one : sqrtPredGs 1 = fun ns => Part.some (ns 0) := rfl

/-- Composing le with [(s+1)², n] computes: if (s+1)² ≤ n then 1 else 0. -/
private theorem sqrtPred_comp_eq (ns : Fin 2 → ℕ) :
    compFunction 2 2 (fun xy => Part.some (if xy 0 ≤ xy 1 then 1 else 0)) sqrtPredGs ns =
    Part.some (if (ns 1 + 1) * (ns 1 + 1) ≤ ns 0 then 1 else 0) := by
  have h0 : sqrtPredGs 0 ns = Part.some ((ns 1 + 1) * (ns 1 + 1)) := rfl
  have h1 : sqrtPredGs (Fin.succ 0) ns = Part.some (ns 0) := rfl
  simp only [compFunction, Part.sequence, h0, h1, Part.bind_some, Part.map_some]
  rfl

/-- The predicate (s+1)² ≤ n is computable.
    Returns 1 if (s+1)² ≤ n (continue searching), 0 if (s+1)² > n (stop). -/
private theorem sqrtPred_computable :
    URMComputable 2 (fun ns => Part.some (if (ns 1 + 1) * (ns 1 + 1) ≤ ns 0 then 1 else 0)) := by
  have hgs : ∀ i, URMComputable 2 (sqrtPredGs i) := by
    intro i; fin_cases i
    · simp only [sqrtPredGs]; exact sqrtSquare_computable
    · simp only [sqrtPredGs]; exact URMComputable.proj_computable 2 0
  have h := URMComputable.comp_general (m := 2) (n := 2) le_computable hgs
  convert h.toComputable using 1
  funext ns
  exact (sqrtPred_comp_eq ns).symm

/-! ### Step 4: Connect μ to Nat.sqrt -/

/-- The predicate function for minimization. -/
private def sqrtPredFun : (Fin 2 → ℕ) → Part ℕ :=
  fun ns => Part.some (if (ns 1 + 1) * (ns 1 + 1) ≤ ns 0 then 1 else 0)

/-- Helper: simplify Fin.snoc at index 0 -/
private theorem snoc_at_zero (n s : ℕ) : (Fin.snoc (fun _ : Fin 1 => n) s : Fin 2 → ℕ) 0 = n := rfl

/-- Helper: simplify Fin.snoc at index 1 -/
private theorem snoc_at_one (n s : ℕ) : (Fin.snoc (fun _ : Fin 1 => n) s : Fin 2 → ℕ) 1 = s := by
  simp [Fin.snoc]

/-- For s < sqrt(n), we have (s+1)² ≤ n, so the predicate returns 1 (non-zero). -/
private theorem sqrt_pred_nonzero_below (n s : ℕ) (hs : s < Nat.sqrt n) :
    sqrtPredFun (Fin.snoc (fun _ => n) s) ≠ Part.some 0 := by
  simp only [sqrtPredFun, snoc_at_zero, snoc_at_one]
  -- s < sqrt(n) implies s + 1 ≤ sqrt(n) implies (s+1)² ≤ n
  have h1 : s + 1 ≤ Nat.sqrt n := hs
  have h2 : (s + 1) * (s + 1) ≤ n := Nat.le_sqrt.mp h1
  simp only [h2, ↓reduceIte, ne_eq, Part.some_inj]
  exact Nat.one_ne_zero

/-- At s = sqrt(n), we have (s+1)² > n, so the predicate returns 0. -/
private theorem sqrt_pred_zero_at (n : ℕ) :
    sqrtPredFun (Fin.snoc (fun _ => n) (Nat.sqrt n)) = Part.some 0 := by
  simp only [sqrtPredFun, snoc_at_zero, snoc_at_one]
  -- At s = sqrt(n), (s+1)² = (sqrt(n)+1)² > n by Nat.lt_succ_sqrt
  have h : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  simp only [Nat.not_le.mpr h, ↓reduceIte]

/-- Helper: extendInputs (fun _ => n) s equals Fin.snoc (fun _ => n) s -/
private theorem extendInputs_eq_snoc (n s : ℕ) :
    extendInputs (fun _ : Fin 1 => n) s = Fin.snoc (fun _ : Fin 1 => n) s := rfl

/-- Key lemma: μ(sqrtPredFun) equals Nat.sqrt. -/
private theorem sqrt_mu_eq (n : ℕ) :
    μFunction sqrtPredFun (fun _ : Fin 1 => n) = Part.some (Nat.sqrt n) := by
  -- We need to show that the minimization finds Nat.sqrt n
  -- μ finds the least s where sqrtPredFun returns 0
  rw [μFunction, μ]
  -- Use Nat.mem_rfind to show Nat.sqrt n ∈ the result
  rw [Part.eq_some_iff]
  rw [Nat.mem_rfind]
  constructor
  · -- true ∈ checkZero at sqrt(n): the predicate returns 0 here
    rw [checkZero_true_iff, extendInputs_eq_snoc]
    rw [sqrt_pred_zero_at]
    exact Part.mem_some 0
  · -- For all y < sqrt(n), false ∈ checkZero: the predicate returns non-zero
    intro y hy
    rw [checkZero_false_iff, extendInputs_eq_snoc]
    use 1
    constructor
    · exact one_ne_zero
    · -- For y < sqrt(n), (y+1)² ≤ n, so sqrtPredFun returns 1
      have h1 : y + 1 ≤ Nat.sqrt n := hy
      have h2 : (y + 1) * (y + 1) ≤ n := Nat.le_sqrt.mp h1
      simp only [sqrtPredFun, snoc_at_zero, snoc_at_one, h2, ↓reduceIte]
      exact Part.mem_some 1

/-- Square root is URM-computable.
    sqrt(n) = μs. [(s+1)² > n] -/
theorem sqrt_computable : URMComputable 1 (fun x => Part.some (Nat.sqrt (x 0))) := by
  -- Apply minimization to sqrtPred_computable
  have h_pred : URMComputable 2 sqrtPredFun := sqrtPred_computable
  have h_min := URMComputable.min h_pred
  -- h_min : URMComputableSF 1 (μFunction sqrtPredFun)
  convert h_min.toComputable using 1
  funext x
  -- x : Fin 1 → ℕ, and (fun _ => x 0) = x for Fin 1 → ℕ
  have hx : (fun _ : Fin 1 => x 0) = x := funext (fun i => by simp [Fin.eq_zero i])
  rw [← hx]
  exact (sqrt_mu_eq (x 0)).symm

end Sqrt

/-! ## Square Function -/

section Square

/-- The inner functions for squaring: (x, x) for multiplication. -/
private def sqGs : Fin 2 → (Fin 1 → ℕ) → Part ℕ :=
  fun _ => fun x => Part.some (x 0)

@[simp] private theorem sqGs_eval (i : Fin 2) (x : Fin 1 → ℕ) : sqGs i x = Part.some (x 0) := rfl

/-- Helper: Composing mul with (x, x) computes x². -/
private theorem sq_comp_eq (x : Fin 1 → ℕ) :
    compFunction 2 1 (fun ab => Part.some (ab 0 * ab 1)) sqGs x =
    Part.some (x 0 * x 0) := by
  simp only [compFunction, Part.sequence, sqGs_eval, Part.bind_some, Part.map_some]
  rfl

/-- Square function is URM-computable. sq(x) = x * x -/
theorem sq_computable : URMComputable 1 (fun x => Part.some ((x 0) * (x 0))) := by
  have hgs : ∀ i, URMComputable 1 (sqGs i) := fun _ => URMComputable.proj_computable 1 0
  have h := URMComputable.comp_general (m := 2) (n := 1) mul_computable hgs
  convert h.toComputable using 1
  funext x
  exact (sq_comp_eq x).symm

end Square

/-! ## Pairing Functions -/

section Pairing

/-- The branchless formula for Cantor pairing equals Nat.pair.
    pair(a, b) = lt(a,b) * (b² + a) + (1 - lt(a,b)) * (a² + a + b) -/
private theorem pair_branchless_eq (a b : ℕ) :
    (if a < b then 1 else 0) * (b * b + a) +
    (1 - if a < b then 1 else 0) * (a * a + a + b) =
    pair a b := by
  unfold pair
  by_cases h : a < b
  · simp [h]
  · simp [h]

-- Helper: b² is computable (as a 2-arg function extracting b)
private def sqBGs : Fin 1 → (Fin 2 → ℕ) → Part ℕ :=
  fun _ => fun xy => Part.some (xy 1)

private theorem sqB_computable : URMComputableSF 2 (fun xy => Part.some ((xy 1) * (xy 1))) := by
  have hgs : ∀ i, URMComputable 2 (sqBGs i) := fun _ => URMComputable.proj_computable 2 1
  have h := URMComputable.comp_general (m := 1) (n := 2) sq_computable hgs
  convert h using 1
  funext xy
  simp only [compFunction, Part.sequence, sqBGs, Part.bind_some, Part.map_some, Fin.cons_zero]

-- Helper: a² is computable (as a 2-arg function extracting a)
private def sqAGs : Fin 1 → (Fin 2 → ℕ) → Part ℕ :=
  fun _ => fun xy => Part.some (xy 0)

private theorem sqA_computable : URMComputableSF 2 (fun xy => Part.some ((xy 0) * (xy 0))) := by
  have hgs : ∀ i, URMComputable 2 (sqAGs i) := fun _ => URMComputable.proj_computable 2 0
  have h := URMComputable.comp_general (m := 1) (n := 2) sq_computable hgs
  convert h using 1
  funext xy
  simp only [compFunction, Part.sequence, sqAGs, Part.bind_some, Part.map_some, Fin.cons_zero]

-- Helper: b² + a is computable
private def termLtGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun xy => Part.some (xy 1 * xy 1)) else (fun xy => Part.some (xy 0))

private theorem termLt_computable : URMComputableSF 2 (fun xy => Part.some (xy 1 * xy 1 + xy 0)) := by
  have hgs : ∀ i, URMComputable 2 (termLtGs i) := by
    intro i; fin_cases i
    · simp only [termLtGs]; exact sqB_computable.toComputable
    · simp only [termLtGs]; exact URMComputable.proj_computable 2 0
  have h := URMComputable.comp_general (m := 2) (n := 2) add_computable hgs
  convert h using 1
  funext xy
  simp only [compFunction, Part.sequence, termLtGs, Part.bind_some, Part.map_some,
    Fin.val_zero, ↓reduceIte, Fin.cons_zero, Fin.cons_one,
    Fin.val_succ, Nat.add_one_ne_zero]

-- Helper: a² + a is computable
private def sqAPlusAGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun xy => Part.some (xy 0 * xy 0)) else (fun xy => Part.some (xy 0))

private theorem sqAPlusA_computable : URMComputableSF 2 (fun xy => Part.some (xy 0 * xy 0 + xy 0)) := by
  have hgs : ∀ i, URMComputable 2 (sqAPlusAGs i) := by
    intro i; fin_cases i
    · simp only [sqAPlusAGs]; exact sqA_computable.toComputable
    · simp only [sqAPlusAGs]; exact URMComputable.proj_computable 2 0
  have h := URMComputable.comp_general (m := 2) (n := 2) add_computable hgs
  convert h using 1
  funext xy
  simp only [compFunction, Part.sequence, sqAPlusAGs, Part.bind_some, Part.map_some,
    Fin.val_zero, ↓reduceIte, Fin.cons_zero, Fin.cons_one,
    Fin.val_succ, Nat.add_one_ne_zero]

-- Helper: a² + a + b is computable
private def termGeGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun xy => Part.some (xy 0 * xy 0 + xy 0)) else (fun xy => Part.some (xy 1))

private theorem termGe_computable : URMComputableSF 2 (fun xy => Part.some (xy 0 * xy 0 + xy 0 + xy 1)) := by
  have hgs : ∀ i, URMComputable 2 (termGeGs i) := by
    intro i; fin_cases i
    · simp only [termGeGs]; exact sqAPlusA_computable.toComputable
    · simp only [termGeGs]; exact URMComputable.proj_computable 2 1
  have h := URMComputable.comp_general (m := 2) (n := 2) add_computable hgs
  convert h using 1
  funext xy
  simp only [compFunction, Part.sequence, termGeGs, Part.bind_some, Part.map_some,
    Fin.val_zero, ↓reduceIte, Fin.cons_zero, Fin.cons_one,
    Fin.val_succ, Nat.add_one_ne_zero]

-- Helper: lt(a,b) * (b² + a) is computable
private def mulLtGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun xy => Part.some (if xy 0 < xy 1 then 1 else 0))
           else (fun xy => Part.some (xy 1 * xy 1 + xy 0))

private theorem mulLt_computable : URMComputableSF 2
    (fun xy => Part.some ((if xy 0 < xy 1 then 1 else 0) * (xy 1 * xy 1 + xy 0))) := by
  have hgs : ∀ i, URMComputable 2 (mulLtGs i) := by
    intro i; fin_cases i
    · simp only [mulLtGs]; exact lt_computable
    · simp only [mulLtGs]; exact termLt_computable.toComputable
  have h := URMComputable.comp_general (m := 2) (n := 2) mul_computable hgs
  convert h using 1
  funext xy
  simp only [compFunction, Part.sequence, mulLtGs, Part.bind_some, Part.map_some,
    Fin.val_zero, ↓reduceIte, Fin.cons_zero, Fin.cons_one,
    Fin.val_succ, Nat.add_one_ne_zero]

-- Helper: 1 - lt(a,b) is computable (ge indicator)
private def geGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun _ => Part.some 1)
           else (fun xy => Part.some (if xy 0 < xy 1 then 1 else 0))

private theorem ge_computable : URMComputableSF 2
    (fun xy => Part.some (1 - if xy 0 < xy 1 then 1 else 0)) := by
  have hgs : ∀ i, URMComputable 2 (geGs i) := by
    intro i; fin_cases i
    · simp only [geGs]; exact const_one_computable
    · simp only [geGs]; exact lt_computable
  have h := URMComputable.comp_general (m := 2) (n := 2) monus_computable hgs
  convert h using 1
  funext xy
  simp only [compFunction, Part.sequence, geGs, Part.bind_some, Part.map_some,
    Fin.val_zero, ↓reduceIte, Fin.cons_zero, Fin.cons_one,
    Fin.val_succ, Nat.add_one_ne_zero]

-- Helper: (1 - lt(a,b)) * (a² + a + b) is computable
private def mulGeGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun xy => Part.some (1 - if xy 0 < xy 1 then 1 else 0))
           else (fun xy => Part.some (xy 0 * xy 0 + xy 0 + xy 1))

private theorem mulGe_computable : URMComputableSF 2
    (fun xy => Part.some ((1 - if xy 0 < xy 1 then 1 else 0) * (xy 0 * xy 0 + xy 0 + xy 1))) := by
  have hgs : ∀ i, URMComputable 2 (mulGeGs i) := by
    intro i; fin_cases i
    · simp only [mulGeGs]; exact ge_computable.toComputable
    · simp only [mulGeGs]; exact termGe_computable.toComputable
  have h := URMComputable.comp_general (m := 2) (n := 2) mul_computable hgs
  convert h using 1
  funext xy
  simp only [compFunction, Part.sequence, mulGeGs, Part.bind_some, Part.map_some,
    Fin.val_zero, ↓reduceIte, Fin.cons_zero, Fin.cons_one,
    Fin.val_succ, Nat.add_one_ne_zero]

-- Final composition: pair(a,b) = mulLt + mulGe
private def pairGs : Fin 2 → (Fin 2 → ℕ) → Part ℕ :=
  fun i => if i.val = 0 then (fun xy => Part.some ((if xy 0 < xy 1 then 1 else 0) * (xy 1 * xy 1 + xy 0)))
           else (fun xy => Part.some ((1 - if xy 0 < xy 1 then 1 else 0) * (xy 0 * xy 0 + xy 0 + xy 1)))

private theorem pair_comp_eq (xy : Fin 2 → ℕ) :
    compFunction 2 2 (fun ab => Part.some (ab 0 + ab 1)) pairGs xy =
    Part.some ((if xy 0 < xy 1 then 1 else 0) * (xy 1 * xy 1 + xy 0) +
               (1 - if xy 0 < xy 1 then 1 else 0) * (xy 0 * xy 0 + xy 0 + xy 1)) := by
  simp only [compFunction, Part.sequence, pairGs, Part.bind_some, Part.map_some,
    Fin.val_zero, ↓reduceIte, Fin.cons_zero, Fin.cons_one,
    Fin.val_succ, Nat.add_one_ne_zero]

/-- Pairing function is URM-computable.
    pair(a, b) = if a < b then b² + a else a² + a + b -/
theorem pair_computable : URMComputable 2 (fun xy => Part.some (pair (xy 0) (xy 1))) := by
  have hgs : ∀ i, URMComputable 2 (pairGs i) := by
    intro i; fin_cases i
    · simp only [pairGs]; exact mulLt_computable.toComputable
    · simp only [pairGs]; exact mulGe_computable.toComputable
  have h := URMComputable.comp_general (m := 2) (n := 2) add_computable hgs
  convert h.toComputable using 1
  funext xy
  rw [pair_comp_eq]
  exact congrArg Part.some (pair_branchless_eq (xy 0) (xy 1)).symm

/-- Left unpair component is URM-computable. -/
theorem unpairLeft_computable : URMComputable 1 (fun x => Part.some (x 0).unpair.1) := by
  sorry

/-- Right unpair component is URM-computable. -/
theorem unpairRight_computable : URMComputable 1 (fun x => Part.some (x 0).unpair.2) := by
  sorry

end Pairing

/-! ## URMComputable1 Closure Properties -/

section URMComputable1Closure

/-- Constant zero is URMComputable1. -/
theorem URMComputable1.zero : URMComputable1 (pure 0) := by
  unfold URMComputable1
  -- pure 0 (x 0) = Part.some 0
  have h : (fun x : Fin 1 → ℕ => (pure 0 : ℕ →. ℕ) (x 0)) = fun _ => Part.some 0 := by
    funext x; rfl
  rw [h]
  -- Program: [Z 0] - zero register 0 and halt
  use [Instr.Z 0]
  intro inputs
  -- Build the final state after Z 0 executes
  let finalState := (Config.init (List.ofFn inputs)).state.write 0 0
  have hstep : Step [Instr.Z 0] (Config.init (List.ofFn inputs)) ⟨1, finalState⟩ :=
    Step.zero rfl
  have hhalted : (⟨1, finalState⟩ : Config).isHalted [Instr.Z 0] := by simp
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨⟨1, finalState⟩, Steps.single hstep, hhalted⟩
  · intro hHalts _
    obtain ⟨hsteps, hhalted'⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps hhalted' (Steps.single hstep) hhalted
    simp only [Result, heq, State.output]
    rfl

/-- Successor is URMComputable1. -/
theorem URMComputable1.succ : URMComputable1 Nat.succ := by
  unfold URMComputable1
  -- Need: URMComputable 1 (fun x => Part.some (x 0 + 1))
  exact URMComputable.succ_computable

/-- Left unpair is URMComputable1. -/
theorem URMComputable1.left : URMComputable1 ↑fun n => n.unpair.1 := by
  unfold URMComputable1
  convert unpairLeft_computable using 1

/-- Right unpair is URMComputable1. -/
theorem URMComputable1.right : URMComputable1 ↑fun n => n.unpair.2 := by
  unfold URMComputable1
  convert unpairRight_computable using 1

/-- Pairing preserves URMComputable1.

    Proof approach: Use composition with pair_computable as outer function
    and f, g as inner functions. -/
theorem URMComputable1.pair {f g : ℕ →. ℕ}
    (hf : URMComputable1 f) (hg : URMComputable1 g) :
    URMComputable1 (fun n => Nat.pair <$> f n <*> g n) := by
  -- pair(f(x), g(x)) = compose pair_computable with [f, g]
  unfold URMComputable1 at *
  -- Define inner functions: gs 0 = f, gs 1 = g
  have hGs : ∀ i : Fin 2, URMComputable 1 (fun x : Fin 1 → ℕ =>
      if i = 0 then f (x 0) else g (x 0)) := by
    intro i; fin_cases i
    · simp only [Fin.isValue]; exact hf
    · simp only [Fin.isValue]; convert hg using 1
  -- Apply comp_general with m=2, n=1
  have h := URMComputable.comp_general (m := 2) (n := 1) pair_computable hGs
  -- Show compFunction equals our goal
  convert h.toComputable using 1
  funext x
  -- Both sides compute the same thing:
  -- LHS: Nat.pair <$> f (x 0) <*> g (x 0)
  -- RHS: compFunction with pair_computable and [f, g]
  -- They're definitionally equal after unfolding
  simp only [compFunction, Part.sequence, Part.bind_eq_bind, Part.map_eq_map,
    seq_eq_bind_map, Part.bind_assoc, Part.bind_map, Part.map_bind, Part.bind_some,
    Part.map_some, Fin.cons_zero, Fin.cons_one]
  congr 1
  funext a
  have hif : (Fin.succ 0 : Fin 2) = 0 ↔ False := by decide
  simp only [hif, ↓reduceIte]
  exact (Part.bind_some_eq_map _ _).symm

/-- Composition preserves URMComputable1.

    Proof approach: Use comp_general with f as outer, g as inner. -/
theorem URMComputable1.comp {f g : ℕ →. ℕ}
    (hf : URMComputable1 f) (hg : URMComputable1 g) :
    URMComputable1 (fun n => g n >>= f) := by
  unfold URMComputable1 at *
  -- Apply comp_general with m=1, n=1
  have h := URMComputable.comp_general (m := 1) (n := 1) hf (fun _ => hg)
  -- Show compFunction equals our goal
  convert h.toComputable using 1
  funext x
  simp only [compFunction, Part.sequence]
  rw [Part.bind_assoc]
  congr 1
  funext a
  simp only [Part.map_some, Part.bind_some, Fin.cons_zero]

/-- Primitive recursion preserves URMComputable1.

    Proof approach: Adapt Mathlib's pair-encoded primitive recursion to
    our multi-arity PrFunction, then compose with unpair. -/
theorem URMComputable1.prec {f g : ℕ →. ℕ}
    (hf : URMComputable1 f) (hg : URMComputable1 g) :
    URMComputable1 (Nat.unpaired fun a n =>
      n.rec (f a) fun y IH => do let i ← IH; g (Nat.pair a (Nat.pair y i))) := by
  -- Adapt: f_base(x) = f(x 0), g_step(x,k,acc) = g(pair(x 0, pair(k, acc)))
  -- Then compose PrFunction with unpair using unpairLeft_computable, unpairRight_computable
  sorry

/-- Minimization preserves URMComputable1.

    Proof approach: Define f_adapted(a, n) = f(pair(a, n)), show it's URMComputable 2,
    then apply URMComputable.min. -/
theorem URMComputable1.rfind {f : ℕ →. ℕ} (hf : URMComputable1 f) :
    URMComputable1 (fun a => Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)) := by
  -- f_adapted(a,n) = f(pair(a,n)) via composition with pair_computable
  -- Then μFunction f_adapted equals the goal, apply URMComputable.min
  sorry

end URMComputable1Closure

/-! ## Main Theorem -/

/-- Every partial recursive function is URM-computable. -/
theorem Nat.Partrec.toURMComputable1 {f : ℕ →. ℕ} (hf : Nat.Partrec f) : URMComputable1 f := by
  induction hf with
  | zero => exact URMComputable1.zero
  | succ => exact URMComputable1.succ
  | left => exact URMComputable1.left
  | right => exact URMComputable1.right
  | pair _ _ ihf ihg => exact URMComputable1.pair ihf ihg
  | comp _ _ ihf ihg => exact URMComputable1.comp ihf ihg
  | prec _ _ ihf ihg => exact URMComputable1.prec ihf ihg
  | rfind _ ihf => exact URMComputable1.rfind ihf

end Urm
