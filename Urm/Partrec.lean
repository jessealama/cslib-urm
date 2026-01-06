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

/-- Less-than-or-equal comparison returns 1 if x ≤ y, else 0. -/
theorem le_computable : URMComputable 2 (fun xy => Part.some (if xy 0 ≤ xy 1 then 1 else 0)) := by
  sorry

/-- Equality check returns 1 if x = y, else 0. -/
theorem eq_computable : URMComputable 2 (fun xy => Part.some (if xy 0 = xy 1 then 1 else 0)) := by
  sorry

end Arithmetic

/-! ## Square Root via Minimization -/

section Sqrt

/-- Square root is URM-computable.
    sqrt(n) = μs. [(s+1)² > n] -/
theorem sqrt_computable : URMComputable 1 (fun x => Part.some (Nat.sqrt (x 0))) := by
  sorry

end Sqrt

/-! ## Pairing Functions -/

section Pairing

/-- Pairing function is URM-computable.
    pair(a, b) = if a < b then b² + a else a² + a + b -/
theorem pair_computable : URMComputable 2 (fun xy => Part.some (pair (xy 0) (xy 1))) := by
  sorry

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
  sorry

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
