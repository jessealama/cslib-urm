/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable
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

/-- Addition is URM-computable.
    Uses primitive recursion: add(x, 0) = x, add(x, y+1) = S(add(x, y))

    Proof sketch:
    - f(x) = x (projection)
    - g(x, k, acc) = S(acc) (successor of accumulator)
    - PrFunction f g (x, y) = x + y by induction on y -/
theorem add_computable : URMComputable 2 (fun xy => Part.some (xy 0 + xy 1)) := by
  -- Via primitive recursion with f(x) = x and g(x,k,acc) = acc + 1
  sorry

/-- Predecessor is URM-computable.
    pred(0) = 0, pred(n+1) = n -/
theorem pred_computable : URMComputable 1 (fun x => Part.some (x 0 - 1)) := by
  sorry

/-- Monus (truncated subtraction) is URM-computable.
    sub(x, 0) = x, sub(x, y+1) = pred(sub(x, y)) -/
theorem sub_computable : URMComputable 2 (fun xy => Part.some (xy 0 - xy 1)) := by
  sorry

/-- Multiplication is URM-computable.
    mul(x, 0) = 0, mul(x, y+1) = add(x, mul(x, y)) -/
theorem mul_computable : URMComputable 2 (fun xy => Part.some (xy 0 * xy 1)) := by
  sorry

/-- Sign function: sign(0) = 0, sign(n+1) = 1 -/
theorem sign_computable : URMComputable 1 (fun x => Part.some (if x 0 = 0 then 0 else 1)) := by
  sorry

/-- Less-than comparison returns 1 if x < y, else 0.
    lt(x, y) = sign(y - x) -/
theorem lt_computable : URMComputable 2 (fun xy => Part.some (if xy 0 < xy 1 then 1 else 0)) := by
  sorry

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
  -- Need: URMComputable 1 (fun x => Part.some 0)
  -- This is the constant 0 function, ignoring input
  sorry

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

/-- Pairing preserves URMComputable1. -/
theorem URMComputable1.pair {f g : ℕ →. ℕ}
    (hf : URMComputable1 f) (hg : URMComputable1 g) :
    URMComputable1 (fun n => Nat.pair <$> f n <*> g n) := by
  sorry

/-- Composition preserves URMComputable1. -/
theorem URMComputable1.comp {f g : ℕ →. ℕ}
    (hf : URMComputable1 f) (hg : URMComputable1 g) :
    URMComputable1 (fun n => g n >>= f) := by
  sorry

/-- Primitive recursion preserves URMComputable1. -/
theorem URMComputable1.prec {f g : ℕ →. ℕ}
    (hf : URMComputable1 f) (hg : URMComputable1 g) :
    URMComputable1 (Nat.unpaired fun a n =>
      n.rec (f a) fun y IH => do let i ← IH; g (Nat.pair a (Nat.pair y i))) := by
  sorry

/-- Minimization preserves URMComputable1. -/
theorem URMComputable1.rfind {f : ℕ →. ℕ} (hf : URMComputable1 f) :
    URMComputable1 (fun a => Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)) := by
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
