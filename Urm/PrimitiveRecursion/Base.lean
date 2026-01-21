/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.PrimitiveRecursion.Core

/-! # Base Register Computation for Primitive Recursion

This file defines the base register and register layout for the primitive recursion
witness program.

## Register Layout

For primitive recursion with:
- f : (Fin n → ℕ) → Part ℕ (base case, computed by pF)
- g : (Fin (n+2) → ℕ) → Part ℕ (recursive step, computed by pG)

Register layout:
- R[0..n-1]           = working input space for pF (restored each iteration)
- R[n]                = for pG: receives counter k
- R[n+1]              = for pG: receives accumulator value
- R[base+1..base+n]   = saved inputs x₁,...,xₙ (preserved throughout)
- R[base+n+1]         = savedY (original recursion depth y)
- R[base+n+2]         = counter (current iteration 0..y)
- R[base+n+3]         = accumulator (result from previous iteration)
- R[base+n+4]         = zero register (always 0, for J comparisons)

The base is chosen as max(n+1, max(pF.max_register, pG.max_register)) to ensure
neither pF nor pG clobbers the saved registers, and that saved registers
don't overlap with pG's input space (registers 0 through n+1).
-/

namespace Urm

open Program

/-! ## Base register -/

/-- The base register for primitive recursion, ensuring neither pF nor pG
    clobbers saved registers, and saved registers don't overlap with pG's
    input space (registers 0 through n+1). -/
def primitive_recursion_base (n : ℕ) (pF pG : Program) : ℕ :=
  max (n + 1) (max pF.max_register pG.max_register)

/-! ## Register indices -/

/-- The start of saved input registers R[base+1..base+n]. -/
def pr_saved_inputs_start (n : ℕ) (pF pG : Program) : ℕ :=
  primitive_recursion_base n pF pG + 1

/-- The register storing the original y value (recursion depth). -/
def pr_saved_y_reg (n : ℕ) (pF pG : Program) : ℕ :=
  primitive_recursion_base n pF pG + n + 1

/-- The counter register (tracks current iteration 0..y). -/
def pr_counter_reg (n : ℕ) (pF pG : Program) : ℕ :=
  primitive_recursion_base n pF pG + n + 2

/-- The accumulator register (holds result from previous iteration). -/
def pr_accumulator_reg (n : ℕ) (pF pG : Program) : ℕ :=
  primitive_recursion_base n pF pG + n + 3

/-- The zero register (always 0, used for J comparisons). -/
def pr_zero_reg (n : ℕ) (pF pG : Program) : ℕ :=
  primitive_recursion_base n pF pG + n + 4

/-- Tactic for solving register arithmetic goals in primitive recursion.
    Unfolds register definitions and calls omega. -/
macro "pr_register_omega" : tactic =>
  `(tactic| (simp only [pr_saved_inputs_start, pr_saved_y_reg, pr_counter_reg,
      pr_accumulator_reg, pr_zero_reg, primitive_recursion_base]; omega))

/-! ## Bound lemmas for primitive_recursion_base -/

@[simp] theorem primitive_recursion_base_ge_n_succ (n : ℕ) (pF pG : Program) :
    n + 1 ≤ primitive_recursion_base n pF pG := le_max_left (n + 1) _

@[simp] theorem primitive_recursion_base_ge_n (n : ℕ) (pF pG : Program) :
    n ≤ primitive_recursion_base n pF pG := by
  have := primitive_recursion_base_ge_n_succ n pF pG; omega

@[simp] theorem primitive_recursion_base_gt_n (n : ℕ) (pF pG : Program) :
    n < primitive_recursion_base n pF pG := by
  have := primitive_recursion_base_ge_n_succ n pF pG; omega

@[simp] theorem primitive_recursion_base_ge_pF (n : ℕ) (pF pG : Program) :
    pF.max_register ≤ primitive_recursion_base n pF pG := by
  simp only [primitive_recursion_base]; exact le_max_of_le_right (le_max_left _ _)

@[simp] theorem primitive_recursion_base_ge_pG (n : ℕ) (pF pG : Program) :
    pG.max_register ≤ primitive_recursion_base n pF pG := by
  simp only [primitive_recursion_base]; exact le_max_of_le_right (le_max_right _ _)

/-! ## Register ordering lemmas -/

@[simp] theorem pr_saved_inputs_start_gt_base (n : ℕ) (pF pG : Program) :
    primitive_recursion_base n pF pG < pr_saved_inputs_start n pF pG := by pr_register_omega

@[simp] theorem pr_saved_y_reg_gt_base (n : ℕ) (pF pG : Program) :
    primitive_recursion_base n pF pG < pr_saved_y_reg n pF pG := by pr_register_omega

@[simp] theorem pr_counter_reg_gt_base (n : ℕ) (pF pG : Program) :
    primitive_recursion_base n pF pG < pr_counter_reg n pF pG := by pr_register_omega

@[simp] theorem pr_accumulator_reg_gt_base (n : ℕ) (pF pG : Program) :
    primitive_recursion_base n pF pG < pr_accumulator_reg n pF pG := by pr_register_omega

@[simp] theorem pr_zero_reg_gt_base (n : ℕ) (pF pG : Program) :
    primitive_recursion_base n pF pG < pr_zero_reg n pF pG := by pr_register_omega

/-! ## Register distinctness lemmas -/

@[simp] theorem pr_saved_y_reg_ne_pr_counter_reg (n : ℕ) (pF pG : Program) :
    pr_saved_y_reg n pF pG ≠ pr_counter_reg n pF pG := by pr_register_omega

@[simp] theorem pr_saved_y_reg_ne_pr_accumulator_reg (n : ℕ) (pF pG : Program) :
    pr_saved_y_reg n pF pG ≠ pr_accumulator_reg n pF pG := by pr_register_omega

@[simp] theorem pr_saved_y_reg_ne_pr_zero_reg (n : ℕ) (pF pG : Program) :
    pr_saved_y_reg n pF pG ≠ pr_zero_reg n pF pG := by pr_register_omega

@[simp] theorem pr_counter_reg_ne_pr_accumulator_reg (n : ℕ) (pF pG : Program) :
    pr_counter_reg n pF pG ≠ pr_accumulator_reg n pF pG := by pr_register_omega

@[simp] theorem pr_counter_reg_ne_pr_zero_reg (n : ℕ) (pF pG : Program) :
    pr_counter_reg n pF pG ≠ pr_zero_reg n pF pG := by pr_register_omega

@[simp] theorem pr_accumulator_reg_ne_pr_zero_reg (n : ℕ) (pF pG : Program) :
    pr_accumulator_reg n pF pG ≠ pr_zero_reg n pF pG := by pr_register_omega

/-! ## Saved inputs don't overlap with working space -/

@[simp] theorem pr_saved_inputs_start_ge_n (n : ℕ) (pF pG : Program) :
    n ≤ pr_saved_inputs_start n pF pG := by pr_register_omega

theorem pr_saved_input_reg_ne_working (n : ℕ) (pF pG : Program) (i : Fin n) :
    pr_saved_inputs_start n pF pG + i ≠ i.val := by pr_register_omega

/-! ## Saved inputs don't overlap with high registers -/

@[simp] theorem pr_saved_input_ne_pr_saved_y_reg (n : ℕ) (pF pG : Program) (i : Fin n) :
    pr_saved_inputs_start n pF pG + i ≠ pr_saved_y_reg n pF pG := by pr_register_omega

@[simp] theorem pr_saved_input_ne_pr_counter_reg (n : ℕ) (pF pG : Program) (i : Fin n) :
    pr_saved_inputs_start n pF pG + i ≠ pr_counter_reg n pF pG := by pr_register_omega

@[simp] theorem pr_saved_input_ne_pr_accumulator_reg (n : ℕ) (pF pG : Program) (i : Fin n) :
    pr_saved_inputs_start n pF pG + i ≠ pr_accumulator_reg n pF pG := by pr_register_omega

@[simp] theorem pr_saved_input_ne_pr_zero_reg (n : ℕ) (pF pG : Program) (i : Fin n) :
    pr_saved_inputs_start n pF pG + i ≠ pr_zero_reg n pF pG := by pr_register_omega

/-! ## Generic "doesn't touch" lemmas

Any program bounded by primitive_recursion_base doesn't touch high registers. -/

theorem program_doesnt_touch_pr_saved_inputs (n : ℕ) (pF pG : Program) (p : Program)
    (hp : p.max_register ≤ primitive_recursion_base n pF pG) (i : Fin n) :
    p.max_register < pr_saved_inputs_start n pF pG + i := by
  simp only [pr_saved_inputs_start]; omega

theorem program_doesnt_touch_pr_saved_y_reg (n : ℕ) (pF pG : Program) (p : Program)
    (hp : p.max_register ≤ primitive_recursion_base n pF pG) :
    p.max_register < pr_saved_y_reg n pF pG := by
  simp only [pr_saved_y_reg]; omega

theorem program_doesnt_touch_pr_counter_reg (n : ℕ) (pF pG : Program) (p : Program)
    (hp : p.max_register ≤ primitive_recursion_base n pF pG) :
    p.max_register < pr_counter_reg n pF pG := by
  simp only [pr_counter_reg]; omega

theorem program_doesnt_touch_pr_zero_reg (n : ℕ) (pF pG : Program) (p : Program)
    (hp : p.max_register ≤ primitive_recursion_base n pF pG) :
    p.max_register < pr_zero_reg n pF pG := by
  simp only [pr_zero_reg]; omega

/-! ## High registers are above n + 1 (for pG input space) -/

@[simp] theorem pr_saved_inputs_start_gt_n_plus_1 (n : ℕ) (pF pG : Program) :
    n + 1 < pr_saved_inputs_start n pF pG := by pr_register_omega

@[simp] theorem pr_saved_y_reg_gt_n_plus_1 (n : ℕ) (pF pG : Program) :
    n + 1 < pr_saved_y_reg n pF pG := by pr_register_omega

@[simp] theorem pr_counter_reg_gt_n_plus_1 (n : ℕ) (pF pG : Program) :
    n + 1 < pr_counter_reg n pF pG := by pr_register_omega

@[simp] theorem pr_accumulator_reg_gt_n_plus_1 (n : ℕ) (pF pG : Program) :
    n + 1 < pr_accumulator_reg n pF pG := by pr_register_omega

@[simp] theorem pr_zero_reg_gt_n_plus_1 (n : ℕ) (pF pG : Program) :
    n + 1 < pr_zero_reg n pF pG := by pr_register_omega

end Urm
