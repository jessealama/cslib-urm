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

/-! ## Binary Composition with Computed Inner Functions -/

/-- Helper to build a Fin 2 → ℕ from two values. -/
private def mkPair (a b : ℕ) : Fin 2 → ℕ := Fin.cons a (Fin.cons b Fin.elim0)

@[simp] private theorem mkPair_zero (a b : ℕ) : mkPair a b 0 = a := rfl
@[simp] private theorem mkPair_one (a b : ℕ) : mkPair a b 1 = b := rfl

/-- Build a binary Gs from two computed functions: gs 0 = g₀, gs 1 = g₁. -/
private def binaryGs {n : ℕ} (g₀ g₁ : (Fin n → ℕ) → Part ℕ) : Fin 2 → (Fin n → ℕ) → Part ℕ :=
  fun k => if k.val = 0 then g₀ else g₁

@[simp] private theorem binaryGs_zero {n : ℕ} (g₀ g₁ : (Fin n → ℕ) → Part ℕ) :
    binaryGs g₀ g₁ 0 = g₀ := rfl

@[simp] private theorem binaryGs_one {n : ℕ} (g₀ g₁ : (Fin n → ℕ) → Part ℕ) :
    binaryGs g₀ g₁ 1 = g₁ := rfl

/-- Compose a binary function with two computed inner functions.
    Given f(a, b) computable and g₀, g₁ computable, proves f(g₀(x), g₁(x)) computable.
    Note: The result is expressed as compFunction to match comp_general's output type. -/
theorem URMComputable.comp_binary {n : ℕ} {f : (Fin 2 → ℕ) → Part ℕ}
    {g₀ g₁ : (Fin n → ℕ) → Part ℕ}
    (hf : URMComputable 2 f) (hg₀ : URMComputable n g₀) (hg₁ : URMComputable n g₁) :
    URMComputable n (compFunction 2 n f (binaryGs g₀ g₁)) := by
  have hgs : ∀ k, URMComputable n (binaryGs g₀ g₁ k) := by
    intro k; fin_cases k
    · simp only [binaryGs]; exact hg₀
    · simp only [binaryGs]; exact hg₁
  exact (URMComputable.comp_general hf hgs).toComputable

/-- compFunction with total binary Gs simplifies to direct application. -/
private theorem compFunction_binary_total_eq {n : ℕ} (f : (Fin 2 → ℕ) → Part ℕ)
    (v₀ v₁ : (Fin n → ℕ) → ℕ) (x : Fin n → ℕ) :
    compFunction 2 n f (binaryGs (fun x => Part.some (v₀ x)) (fun x => Part.some (v₁ x))) x =
    f (mkPair (v₀ x) (v₁ x)) := by
  simp only [compFunction, binaryGs, Part.sequence, Part.bind_some, Part.map_some,
    Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.add_one_ne_zero, mkPair]

/-- Compose a binary function with two total computed inner functions.
    This is the common case where g₀, g₁ return Part.some. -/
theorem URMComputable.comp_binary_total {n : ℕ} {f : (Fin 2 → ℕ) → Part ℕ}
    {v₀ v₁ : (Fin n → ℕ) → ℕ}
    (hf : URMComputable 2 f)
    (hg₀ : URMComputable n (fun x => Part.some (v₀ x)))
    (hg₁ : URMComputable n (fun x => Part.some (v₁ x))) :
    URMComputable n (fun x => f (mkPair (v₀ x) (v₁ x))) := by
  have h := URMComputable.comp_binary hf hg₀ hg₁
  convert h using 1
  funext x
  exact (compFunction_binary_total_eq f v₀ v₁ x).symm

/-- Compose a 2-ary function with two projections.
    Given f(a, b) computable and indices i, j, this proves f(x[i], x[j]) is computable.
    This is a special case of comp_binary_total where the inner functions are projections. -/
theorem URMComputable.comp_proj2 {n : ℕ} {f : (Fin 2 → ℕ) → Part ℕ}
    (hf : URMComputable 2 f) (i j : Fin n) :
    URMComputable n (fun x => f (mkPair (x i) (x j))) :=
  URMComputable.comp_binary_total hf
    (URMComputable.proj_computable n i)
    (URMComputable.proj_computable n j)

/-! ## Unary Composition Helper -/

/-- Build a unary Gs from one computed function: gs 0 = g. -/
private def unaryGs {n : ℕ} (g : (Fin n → ℕ) → Part ℕ) : Fin 1 → (Fin n → ℕ) → Part ℕ :=
  fun _ => g

/-- Compose a unary function with a total computed inner function.
    Given f(a) computable and v computable, proves f(v(x)) is computable. -/
theorem URMComputable.comp_unary_total {n : ℕ} {f : (Fin 1 → ℕ) → Part ℕ}
    {v : (Fin n → ℕ) → ℕ}
    (hf : URMComputable 1 f)
    (hg : URMComputable n (fun x => Part.some (v x))) :
    URMComputable n (fun x => f (fun _ => v x)) := by
  have hgs : ∀ k, URMComputable n (unaryGs (fun x => Part.some (v x)) k) := fun _ => hg
  have h := URMComputable.comp_general hf hgs
  convert h.toComputable using 1
  funext x
  simp only [compFunction, unaryGs, Part.sequence, Part.bind_some, Part.map_some]
  congr 1
  funext i
  simp only [Fin.cons_zero, Fin.eq_zero i]

/-! ## Unary Function Wrapper -/

/-- A unary partial function `ℕ →. ℕ` is URM-computable. -/
def URMComputable1 (f : ℕ →. ℕ) : Prop :=
  URMComputable 1 (fun x => f (x 0))

/-! ## Arithmetic Helpers -/

section Arithmetic

-- add_computable is now provided by Urm.Arithmetic
-- pred_computable is now provided by Urm.Arithmetic
-- sub_computable is now provided by Urm.Arithmetic
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
  refine ⟨by aesop_steps, ?_, halted_at_4 s1⟩
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
  refine ⟨by aesop_steps, ?_, halted_at_4 s3⟩
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

/-- Less-than comparison returns 1 if x < y, else 0.
    lt(x, y) = sign(y - x) -/
theorem lt_computable : URMComputable 2 (fun xy => Part.some (if xy 0 < xy 1 then 1 else 0)) := by
  -- Compute (y - x) via comp_proj2
  have hRevSub : URMComputable 2 (fun xy => Part.some (xy 1 - xy 0)) := by
    let h := URMComputable.comp_proj2 sub_computable (1 : Fin 2) (0 : Fin 2)
    simp only [mkPair] at h; exact h
  -- Compose sign with reversed subtraction
  have h := URMComputable.comp_unary_total sign_computable hRevSub
  convert h using 1
  funext xy
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

/-- The intermediate function: sign(x - y). -/
private def leSignXY : (Fin 2 → ℕ) → Part ℕ :=
  fun xy => Part.some (if xy 0 - xy 1 = 0 then 0 else 1)

/-- sign(x - y) is computable in standard form. -/
private theorem leSignXY_computable : URMComputableSF 2 leSignXY := by
  have hSub : URMComputable 2 (fun xy => Part.some (xy 0 - xy 1)) := by
    let h := URMComputable.comp_proj2 sub_computable (0 : Fin 2) (1 : Fin 2)
    simp only [mkPair] at h; exact h
  have h := URMComputable.comp_unary_total sign_computable hSub
  convert h.toSF using 1

/-- Constant 1 is URMComputable n for any arity (program: Z 0, S 0). -/
private theorem const_one_n_computable (n : ℕ) : URMComputable n (fun _ : Fin n → ℕ => Part.some 1) := by
  use [Instr.Z 0, Instr.S 0]
  intro inputs
  let s0 := State.fromInputs (List.ofFn inputs)
  let s1 := s0.write 0 0
  let s2 := s1.write 0 (s1.read 0 + 1)
  have hstep1 : Step [Instr.Z 0, Instr.S 0] ⟨0, s0⟩ ⟨1, s1⟩ := Step.zero rfl
  have hstep2 : Step [Instr.Z 0, Instr.S 0] ⟨1, s1⟩ ⟨2, s2⟩ := Step.succ rfl
  have hhalted : (⟨2, s2⟩ : Config).isHalted [Instr.Z 0, Instr.S 0] := by simp
  have hsteps : Steps [Instr.Z 0, Instr.S 0] (Config.init (List.ofFn inputs)) ⟨2, s2⟩ := by aesop_steps
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨⟨2, s2⟩, hsteps, hhalted⟩
  · intro hHalts _
    obtain ⟨hsteps', hhalted'⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps' hhalted' hsteps hhalted
    simp only [Result, heq, State.output, s2, s1, s0, State.write, State.read,
      Function.update_self, Part.get_some]

/-- Constant 1 is URMComputable 2. -/
private theorem const_one_computable : URMComputable 2 (fun _ : Fin 2 → ℕ => Part.some 1) :=
  const_one_n_computable 2

/-- Less-than-or-equal comparison returns 1 if x ≤ y, else 0.
    le(x, y) = 1 - sign(x - y) -/
theorem le_computable : URMComputable 2 (fun xy => Part.some (if xy 0 ≤ xy 1 then 1 else 0)) := by
  have h := URMComputable.comp_binary_total sub_computable
    const_one_computable
    leSignXY_computable.toComputable
  convert h using 1
  funext xy
  simp only [mkPair_zero, mkPair_one]
  exact congrArg Part.some (one_minus_sign_sub_eq_le (xy 0) (xy 1)).symm

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

/-- le(y, x) is computable (le with swapped arguments). -/
private theorem leSwap_computable : URMComputable 2 (fun xy => Part.some (if xy 1 ≤ xy 0 then 1 else 0)) := by
  have h := URMComputable.comp_proj2 le_computable (1 : Fin 2) (0 : Fin 2)
  simp only [mkPair] at h; exact h

end Arithmetic

/-! ## Square Root via Minimization -/

section Sqrt

/-! ### Step 1: Build s+1 from inputs (n, s) -/

/-- s + 1 is computable as a function of (n, s). -/
private theorem sqrtSPlus1_computable : URMComputable 2 (fun ns => Part.some (ns 1 + 1)) :=
  URMComputable.comp_binary_total add_computable
    (URMComputable.proj_computable 2 1)
    const_one_computable

/-! ### Step 2: Build (s+1)² from inputs (n, s) -/

/-- (s+1)² is computable as a function of (n, s). -/
private theorem sqrtSquare_computable : URMComputable 2 (fun ns => Part.some ((ns 1 + 1) * (ns 1 + 1))) :=
  URMComputable.comp_binary_total mul_computable
    sqrtSPlus1_computable
    sqrtSPlus1_computable

/-! ### Step 3: Build predicate (s+1)² ≤ n -/

/-- The predicate (s+1)² ≤ n is computable.
    Returns 1 if (s+1)² ≤ n (continue searching), 0 if (s+1)² > n (stop). -/
private theorem sqrtPred_computable :
    URMComputable 2 (fun ns => Part.some (if (ns 1 + 1) * (ns 1 + 1) ≤ ns 0 then 1 else 0)) :=
  URMComputable.comp_binary_total le_computable
    sqrtSquare_computable
    (URMComputable.proj_computable 2 0)

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

/-- Square function is URM-computable. sq(x) = x * x -/
theorem sq_computable : URMComputable 1 (fun x => Part.some ((x 0) * (x 0))) :=
  URMComputable.comp_binary_total mul_computable
    (URMComputable.proj_computable 1 0)
    (URMComputable.proj_computable 1 0)

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
private theorem sqB_computable : URMComputableSF 2 (fun xy => Part.some ((xy 1) * (xy 1))) :=
  (URMComputable.comp_unary_total sq_computable (URMComputable.proj_computable 2 1)).toSF

-- Helper: a² is computable (as a 2-arg function extracting a)
private theorem sqA_computable : URMComputableSF 2 (fun xy => Part.some ((xy 0) * (xy 0))) :=
  (URMComputable.comp_unary_total sq_computable (URMComputable.proj_computable 2 0)).toSF

-- Helper: b² + a is computable
private theorem termLt_computable : URMComputableSF 2 (fun xy => Part.some (xy 1 * xy 1 + xy 0)) := by
  have h := URMComputable.comp_binary_total add_computable
    sqB_computable.toComputable
    (URMComputable.proj_computable 2 0)
  convert h.toSF using 1

-- Helper: a² + a is computable
private theorem sqAPlusA_computable : URMComputableSF 2 (fun xy => Part.some (xy 0 * xy 0 + xy 0)) := by
  have h := URMComputable.comp_binary_total add_computable
    sqA_computable.toComputable
    (URMComputable.proj_computable 2 0)
  convert h.toSF using 1

-- Helper: a² + a + b is computable
private theorem termGe_computable : URMComputableSF 2 (fun xy => Part.some (xy 0 * xy 0 + xy 0 + xy 1)) := by
  have h := URMComputable.comp_binary_total add_computable
    sqAPlusA_computable.toComputable
    (URMComputable.proj_computable 2 1)
  convert h.toSF using 1

-- Helper: lt(a,b) * (b² + a) is computable
private theorem mulLt_computable : URMComputableSF 2
    (fun xy => Part.some ((if xy 0 < xy 1 then 1 else 0) * (xy 1 * xy 1 + xy 0))) := by
  have h := URMComputable.comp_binary_total mul_computable
    lt_computable
    termLt_computable.toComputable
  convert h.toSF using 1

-- Helper: 1 - lt(a,b) is computable (ge indicator)
private theorem ge_computable : URMComputableSF 2
    (fun xy => Part.some (1 - if xy 0 < xy 1 then 1 else 0)) := by
  have h := URMComputable.comp_binary_total sub_computable
    const_one_computable
    lt_computable
  convert h.toSF using 1

-- Helper: (1 - lt(a,b)) * (a² + a + b) is computable
private theorem mulGe_computable : URMComputableSF 2
    (fun xy => Part.some ((1 - if xy 0 < xy 1 then 1 else 0) * (xy 0 * xy 0 + xy 0 + xy 1))) := by
  have h := URMComputable.comp_binary_total mul_computable
    ge_computable.toComputable
    termGe_computable.toComputable
  convert h.toSF using 1

/-- Pairing function is URM-computable.
    pair(a, b) = if a < b then b² + a else a² + a + b -/
theorem pair_computable : URMComputable 2 (fun xy => Part.some (pair (xy 0) (xy 1))) := by
  have h := URMComputable.comp_binary_total add_computable
    mulLt_computable.toComputable
    mulGe_computable.toComputable
  convert h using 1
  funext xy
  exact congrArg Part.some (pair_branchless_eq (xy 0) (xy 1)).symm

/-! ### Unpair Helpers

We prove unpair components are computable using branchless formulas.
From Mathlib: `unpair n = if d < s then (d, s) else (s, d - s)`
where `s = sqrt(n)` and `d = n - s*s`.

Branchless formulas:
- `unpair.1 = lt(d,s) * d + (1 - lt(d,s)) * s`
- `unpair.2 = lt(d,s) * s + (1 - lt(d,s)) * (d - s)`
-/

-- Helper: sqrt(n)² is computable
private theorem sqrtSq_computable : URMComputable 1 (fun x => Part.some (Nat.sqrt (x 0) * Nat.sqrt (x 0))) :=
  URMComputable.comp_unary_total sq_computable sqrt_computable

-- Helper: d = n - sqrt(n)² is computable
private theorem unpairD_computable : URMComputable 1 (fun x => Part.some (x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0))) :=
  URMComputable.comp_binary_total sub_computable
    (URMComputable.proj_computable 1 0)
    sqrtSq_computable

-- Helper: lt(d, s) is computable (returns 0 or 1)
private theorem unpairLtDS_computable :
    URMComputable 1 (fun x => Part.some (if x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0) < Nat.sqrt (x 0) then 1 else 0)) :=
  URMComputable.comp_binary_total lt_computable
    unpairD_computable
    sqrt_computable

-- Helper: constant 1 as a 1-ary function
private theorem const_one_1_computable : URMComputable 1 (fun _ : Fin 1 → ℕ => Part.some 1) :=
  const_one_n_computable 1

-- Helper: 1 - lt(d, s) is computable (ge indicator)
private theorem unpairGeDS_computable :
    URMComputable 1 (fun x => Part.some (1 - if x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0) < Nat.sqrt (x 0) then 1 else 0)) :=
  URMComputable.comp_binary_total sub_computable
    const_one_1_computable
    unpairLtDS_computable

-- Helper: d - s is computable
private theorem unpairDMinusS_computable :
    URMComputable 1 (fun x => Part.some (x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0) - Nat.sqrt (x 0))) :=
  URMComputable.comp_binary_total sub_computable
    unpairD_computable
    sqrt_computable

-- Helper for unpairLeft: lt(d,s) * d
private theorem unpairLeftTerm1_computable :
    URMComputable 1 (fun x => Part.some ((if x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0) < Nat.sqrt (x 0) then 1 else 0) *
                                         (x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0)))) :=
  URMComputable.comp_binary_total mul_computable
    unpairLtDS_computable
    unpairD_computable

-- Helper for unpairLeft: (1 - lt(d,s)) * s
private theorem unpairLeftTerm2_computable :
    URMComputable 1 (fun x => Part.some ((1 - if x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0) < Nat.sqrt (x 0) then 1 else 0) *
                                         Nat.sqrt (x 0))) :=
  URMComputable.comp_binary_total mul_computable
    unpairGeDS_computable
    sqrt_computable

-- Helper for unpairRight: lt(d,s) * s
private theorem unpairRightTerm1_computable :
    URMComputable 1 (fun x => Part.some ((if x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0) < Nat.sqrt (x 0) then 1 else 0) *
                                         Nat.sqrt (x 0))) :=
  URMComputable.comp_binary_total mul_computable
    unpairLtDS_computable
    sqrt_computable

-- Helper for unpairRight: (1 - lt(d,s)) * (d - s)
private theorem unpairRightTerm2_computable :
    URMComputable 1 (fun x => Part.some ((1 - if x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0) < Nat.sqrt (x 0) then 1 else 0) *
                                         (x 0 - Nat.sqrt (x 0) * Nat.sqrt (x 0) - Nat.sqrt (x 0)))) :=
  URMComputable.comp_binary_total mul_computable
    unpairGeDS_computable
    unpairDMinusS_computable

-- Branchless formula for unpair.1 equals Nat.unpair.1
private theorem unpairLeft_branchless_eq (n : ℕ) :
    (if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then 1 else 0) * (n - Nat.sqrt n * Nat.sqrt n) +
    (1 - if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then 1 else 0) * Nat.sqrt n =
    (Nat.unpair n).1 := by
  rw [Nat.unpair.eq_1]
  by_cases h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
  · simp [h]
  · simp [h]

-- Branchless formula for unpair.2 equals Nat.unpair.2
private theorem unpairRight_branchless_eq (n : ℕ) :
    (if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then 1 else 0) * Nat.sqrt n +
    (1 - if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then 1 else 0) * (n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n) =
    (Nat.unpair n).2 := by
  rw [Nat.unpair.eq_1]
  by_cases h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
  · simp [h]
  · simp [h]

/-- Left unpair component is URM-computable. -/
theorem unpairLeft_computable : URMComputable 1 (fun x => Part.some (x 0).unpair.1) := by
  have h := URMComputable.comp_binary_total add_computable
    unpairLeftTerm1_computable
    unpairLeftTerm2_computable
  convert h using 1
  funext x
  exact congrArg Part.some (unpairLeft_branchless_eq (x 0)).symm

/-- Right unpair component is URM-computable. -/
theorem unpairRight_computable : URMComputable 1 (fun x => Part.some (x 0).unpair.2) := by
  have h := URMComputable.comp_binary_total add_computable
    unpairRightTerm1_computable
    unpairRightTerm2_computable
  convert h using 1
  funext x
  exact congrArg Part.some (unpairRight_branchless_eq (x 0)).symm

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

    Proof approach: Use comp_binary with pair_computable as outer function
    and f, g as inner functions. -/
theorem URMComputable1.pair {f g : ℕ →. ℕ}
    (hf : URMComputable1 f) (hg : URMComputable1 g) :
    URMComputable1 (fun n => Nat.pair <$> f n <*> g n) := by
  unfold URMComputable1 at *
  have h := URMComputable.comp_binary pair_computable hf hg
  convert h using 1
  funext x
  simp only [compFunction, Part.sequence, Part.bind_eq_bind, Part.map_eq_map,
    seq_eq_bind_map, Part.bind_assoc, Part.bind_map, Part.map_bind, Part.bind_some,
    Part.map_some, Fin.cons_zero, Fin.cons_one, binaryGs, Fin.val_zero, ↓reduceIte,
    Fin.val_succ, Nat.add_one_ne_zero]
  congr 1; funext a
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
  unfold URMComputable1 at *

  -- Step 1: Build nested pair: (Fin 3 → ℕ) → Part ℕ computing pair(x0, pair(x1, x2))

  -- Inner pair: pair(xka 1, xka 2) via comp_proj2
  have h_innerPair : URMComputable 3 (fun xka => Part.some (Nat.pair (xka 1) (xka 2))) := by
    let h := URMComputable.comp_proj2 pair_computable (1 : Fin 3) (2 : Fin 3)
    simp only [mkPair] at h; exact h

  -- Outer pair: compose pair with (proj 0, innerPair) to get pair(xka 0, pair(xka 1, xka 2))
  have h_nestedPair : URMComputable 3 (fun xka => Part.some (Nat.pair (xka 0) (Nat.pair (xka 1) (xka 2)))) := by
    let h := URMComputable.comp_binary_total pair_computable
      (URMComputable.proj_computable 3 0) h_innerPair
    convert h using 1

  -- Step 2: Build g_step = g ∘ nestedPair via comp_unary_total
  have h_gstep_computable : URMComputable 3 (fun xka => g (Nat.pair (xka 0) (Nat.pair (xka 1) (xka 2)))) := by
    let h := URMComputable.comp_unary_total hg h_nestedPair
    convert h using 1

  -- Step 3: Apply primRec
  have h_primRec := URMComputable.primRec (n := 1) hf h_gstep_computable

  -- Step 4: Compose with unpair to get URMComputable 1
  have h_final := URMComputable.comp_binary_total h_primRec
    unpairLeft_computable unpairRight_computable

  -- Step 5: Prove semantic equivalence (types are definitionally equal)
  convert h_final using 1

/-- Minimization preserves URMComputable1.

    Proof approach: Define f_adapted(a, n) = f(pair(a, n)), show it's URMComputable 2,
    then apply URMComputable.min. -/
theorem URMComputable1.rfind {f : ℕ →. ℕ} (hf : URMComputable1 f) :
    URMComputable1 (fun a => Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)) := by
  unfold URMComputable1 at *
  -- Step 1: Define f_adapted via composition with pair_computable
  let pairGs : Fin 1 → (Fin 2 → ℕ) → Part ℕ :=
    fun _ xy => Part.some (Nat.pair (xy 0) (xy 1))
  have h_pair : ∀ i, URMComputable 2 (pairGs i) := fun _ => pair_computable
  have h_adapted := URMComputable.comp_general (m := 1) (n := 2) hf h_pair

  -- Step 2: Apply minimization
  have h_min := URMComputable.min h_adapted.toComputable

  -- Step 3: Convert to goal form
  convert h_min.toComputable using 1
  funext x
  simp only [μFunction, μ]
  congr 1
  funext n
  simp only [checkZero, extendInputs, compFunction, Part.sequence,
             Part.bind_some, pairGs]
  congr 2
  simp only [Part.map_some, Part.bind_some, Fin.cons_zero]
  simp only [Fin.snoc, Fin.val_zero, Fin.val_one, Nat.lt_irrefl, dite_false]
  have h01 : (0 : ℕ) < 1 := by omega
  simp only [h01, ↓reduceDIte]
  rfl

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
