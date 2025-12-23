/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.StraightLine

/-! # Standard Form Programs

This file defines standard-form programs (those with bounded jump targets).
A program is in standard form if all jump instructions target positions at most
equal to the program length. This allows jumps to any instruction (0..length-1)
or to the "virtual halt" position (length).

This property is essential for sequential composition: when we concatenate
programs, jump targets in the second program are shifted, and the bounded
property ensures they remain valid.

## Main definitions

- `Instr.hasBoundedJump`: checks if an instruction has a bounded jump target
- `Program.isStandardForm`: decidable check for standard form (Bool)
- `Program.IsStandardForm`: Prop version of standard form
- `URMComputableSF`: computability by a standard-form program

## Main results

- `straightLine_isStandardForm`: straight-line programs are standard form

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Standard Form

A program is in "standard form" if all jump targets are bounded by the program length.
This is a syntactic property: jumps can target any instruction index (0..length-1) or
the "virtual halt" position (length), but nothing beyond.

This property is essential for sequential composition: when concatenating programs,
jump targets in the second program are shifted by the first program's length, and
the bounded property ensures the shifted targets remain valid. -/

/-- Check if an instruction has a bounded jump target relative to a given length.
Non-jump instructions trivially satisfy this. -/
def Instr.hasBoundedJump (len : ℕ) : Instr → Bool
  | Instr.Z _ => true
  | Instr.S _ => true
  | Instr.T _ _ => true
  | Instr.J _ _ q => q ≤ len

/-- A program is in standard form if all jump targets are bounded by the program length.
Jumps can target any instruction (0..length-1) or the "virtual halt" position (length). -/
def Program.isStandardForm (p : Program) : Bool :=
  p.all (Instr.hasBoundedJump p.length)

/-- Prop version: a program is in standard form. -/
def Program.IsStandardForm (p : Program) : Prop :=
  p.isStandardForm = true

/-- A partial function is URM-computable by a standard form program. -/
def URMComputableSF (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∃ p : Program, p.IsStandardForm ∧
    ∀ inputs : Fin n → ℕ,
      let inputList := List.ofFn inputs
      (Halts p inputList ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts p inputList) (hDom : (f inputs).Dom),
        Result p inputList hHalts = (f inputs).get hDom

/-- Non-jumping instructions have bounded jumps for any length. -/
theorem Instr.hasBoundedJump_of_isNonJumping {instr : Instr} (h : instr.isNonJumping = true)
    (len : ℕ) : instr.hasBoundedJump len = true := by
  cases instr <;> simp_all [isNonJumping, hasBoundedJump]

/-- hasBoundedJump is monotonic: if bounded for len1, then bounded for any len2 ≥ len1. -/
theorem Instr.hasBoundedJump_mono {instr : Instr} {len1 len2 : ℕ}
    (h : instr.hasBoundedJump len1 = true) (hle : len1 ≤ len2) :
    instr.hasBoundedJump len2 = true := by
  cases instr with
  | Z _ => simp [hasBoundedJump]
  | S _ => simp [hasBoundedJump]
  | T _ _ => simp [hasBoundedJump]
  | J _ _ q =>
    simp only [hasBoundedJump, decide_eq_true_eq] at h ⊢
    exact Nat.le_trans h hle

/-- shiftJumps preserves bounded jumps with adjusted bound.
If an instruction has bounded jumps for len, then after shifting by offset,
it has bounded jumps for (offset + len). -/
theorem Instr.hasBoundedJump_shiftJumps {instr : Instr} {len offset : ℕ}
    (h : instr.hasBoundedJump len = true) :
    (instr.shiftJumps offset).hasBoundedJump (offset + len) = true := by
  cases instr with
  | Z _ => simp [shiftJumps, hasBoundedJump]
  | S _ => simp [shiftJumps, hasBoundedJump]
  | T _ _ => simp [shiftJumps, hasBoundedJump]
  | J _ _ q =>
    simp only [shiftJumps, hasBoundedJump, decide_eq_true_eq] at h ⊢
    omega

/-- Straight-line programs are in standard form.

Since straight-line programs have no jumps, all instructions trivially satisfy
the bounded jump property. -/
theorem straightLine_isStandardForm {p : Program} (hsl : p.isStraightLine = true) :
    p.IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm
  rw [List.all_eq_true]
  intro instr hinstr
  have h := List.all_eq_true.mp hsl instr hinstr
  exact Instr.hasBoundedJump_of_isNonJumping h p.length

/-! ## Semantic Consequence

The syntactic standard form property implies that whenever a program halts,
it halts exactly at the program length (not beyond). This is because:
1. Non-jump instructions increment pc by 1
2. Jump instructions set pc to at most p.length (by the bounded jump property)
3. Therefore pc can never exceed p.length
4. The only way to halt (pc ≥ p.length) is to have pc = p.length -/

/-- Standard form programs halt exactly at their length.

This is the key semantic consequence of the syntactic bounded-jump property. -/
theorem Program.IsStandardForm.halts_at_length {p : Program} (hsf : p.IsStandardForm)
    (inputs : List ℕ) (c : Config) (hsteps : Steps p (Config.init inputs) c)
    (hhalted : c.isHalted p) : c.pc = p.length := by
  -- The program counter can never exceed p.length because:
  -- 1. It starts at 0
  -- 2. Non-jump instructions increment by 1
  -- 3. Jump instructions set pc to at most p.length (by standard form)
  -- So if halted (pc ≥ p.length), we must have pc = p.length
  by_contra hne
  have hgt : c.pc > p.length := Nat.lt_of_le_of_ne hhalted (Ne.symm hne)
  -- We'll derive a contradiction by showing pc can never exceed p.length
  -- This requires induction on the steps, showing pc ≤ p.length is an invariant
  -- except at the final halted state where pc = p.length
  sorry

end Urm
