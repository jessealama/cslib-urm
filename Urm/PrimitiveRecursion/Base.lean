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

The base is chosen as max(n+1, max(pF.maxRegister, pG.maxRegister)) to ensure
neither pF nor pG clobbers the saved registers, and that saved registers
don't overlap with pG's input space (registers 0 through n+1).
-/

namespace Urm

open Program

/-! ## Base register -/

/-- The base register for primitive recursion, ensuring neither pF nor pG
    clobbers saved registers, and saved registers don't overlap with pG's
    input space (registers 0 through n+1). -/
def primitiveRecursionBase (n : ℕ) (pF pG : Program) : ℕ :=
  max (n + 1) (max pF.maxRegister pG.maxRegister)

/-! ## Register indices -/

/-- The start of saved input registers R[base+1..base+n]. -/
def prSavedInputsStart (n : ℕ) (pF pG : Program) : ℕ :=
  primitiveRecursionBase n pF pG + 1

/-- The register storing the original y value (recursion depth). -/
def prSavedYReg (n : ℕ) (pF pG : Program) : ℕ :=
  primitiveRecursionBase n pF pG + n + 1

/-- The counter register (tracks current iteration 0..y). -/
def prCounterReg (n : ℕ) (pF pG : Program) : ℕ :=
  primitiveRecursionBase n pF pG + n + 2

/-- The accumulator register (holds result from previous iteration). -/
def prAccumulatorReg (n : ℕ) (pF pG : Program) : ℕ :=
  primitiveRecursionBase n pF pG + n + 3

/-- The zero register (always 0, used for J comparisons). -/
def prZeroReg (n : ℕ) (pF pG : Program) : ℕ :=
  primitiveRecursionBase n pF pG + n + 4

/-- Tactic for solving register arithmetic goals in primitive recursion.
    Unfolds register definitions and calls omega. -/
macro "pr_register_omega" : tactic =>
  `(tactic| (simp only [prSavedInputsStart, prSavedYReg, prCounterReg,
      prAccumulatorReg, prZeroReg, primitiveRecursionBase]; omega))

/-! ## Bound lemmas for primitiveRecursionBase -/

@[simp] theorem primitiveRecursionBase_ge_n_succ (n : ℕ) (pF pG : Program) :
    n + 1 ≤ primitiveRecursionBase n pF pG := le_max_left (n + 1) _

@[simp] theorem primitiveRecursionBase_ge_n (n : ℕ) (pF pG : Program) :
    n ≤ primitiveRecursionBase n pF pG := by
  have := primitiveRecursionBase_ge_n_succ n pF pG; omega

@[simp] theorem primitiveRecursionBase_gt_n (n : ℕ) (pF pG : Program) :
    n < primitiveRecursionBase n pF pG := by
  have := primitiveRecursionBase_ge_n_succ n pF pG; omega

@[simp] theorem primitiveRecursionBase_ge_pF (n : ℕ) (pF pG : Program) :
    pF.maxRegister ≤ primitiveRecursionBase n pF pG := by
  simp only [primitiveRecursionBase]; exact le_max_of_le_right (le_max_left _ _)

@[simp] theorem primitiveRecursionBase_ge_pG (n : ℕ) (pF pG : Program) :
    pG.maxRegister ≤ primitiveRecursionBase n pF pG := by
  simp only [primitiveRecursionBase]; exact le_max_of_le_right (le_max_right _ _)

/-! ## Register ordering lemmas -/

@[simp] theorem prSavedInputsStart_gt_base (n : ℕ) (pF pG : Program) :
    primitiveRecursionBase n pF pG < prSavedInputsStart n pF pG := by pr_register_omega

@[simp] theorem prSavedYReg_gt_base (n : ℕ) (pF pG : Program) :
    primitiveRecursionBase n pF pG < prSavedYReg n pF pG := by pr_register_omega

@[simp] theorem prCounterReg_gt_base (n : ℕ) (pF pG : Program) :
    primitiveRecursionBase n pF pG < prCounterReg n pF pG := by pr_register_omega

@[simp] theorem prAccumulatorReg_gt_base (n : ℕ) (pF pG : Program) :
    primitiveRecursionBase n pF pG < prAccumulatorReg n pF pG := by pr_register_omega

@[simp] theorem prZeroReg_gt_base (n : ℕ) (pF pG : Program) :
    primitiveRecursionBase n pF pG < prZeroReg n pF pG := by pr_register_omega

/-! ## Register distinctness lemmas -/

@[simp] theorem prSavedYReg_ne_prCounterReg (n : ℕ) (pF pG : Program) :
    prSavedYReg n pF pG ≠ prCounterReg n pF pG := by pr_register_omega

@[simp] theorem prSavedYReg_ne_prAccumulatorReg (n : ℕ) (pF pG : Program) :
    prSavedYReg n pF pG ≠ prAccumulatorReg n pF pG := by pr_register_omega

@[simp] theorem prSavedYReg_ne_prZeroReg (n : ℕ) (pF pG : Program) :
    prSavedYReg n pF pG ≠ prZeroReg n pF pG := by pr_register_omega

@[simp] theorem prCounterReg_ne_prAccumulatorReg (n : ℕ) (pF pG : Program) :
    prCounterReg n pF pG ≠ prAccumulatorReg n pF pG := by pr_register_omega

@[simp] theorem prCounterReg_ne_prZeroReg (n : ℕ) (pF pG : Program) :
    prCounterReg n pF pG ≠ prZeroReg n pF pG := by pr_register_omega

@[simp] theorem prAccumulatorReg_ne_prZeroReg (n : ℕ) (pF pG : Program) :
    prAccumulatorReg n pF pG ≠ prZeroReg n pF pG := by pr_register_omega

/-! ## Saved inputs don't overlap with working space -/

@[simp] theorem prSavedInputsStart_ge_n (n : ℕ) (pF pG : Program) :
    n ≤ prSavedInputsStart n pF pG := by pr_register_omega

theorem prSavedInput_reg_ne_working (n : ℕ) (pF pG : Program) (i : Fin n) :
    prSavedInputsStart n pF pG + i ≠ i.val := by pr_register_omega

/-! ## Saved inputs don't overlap with high registers -/

@[simp] theorem prSavedInput_ne_prSavedYReg (n : ℕ) (pF pG : Program) (i : Fin n) :
    prSavedInputsStart n pF pG + i ≠ prSavedYReg n pF pG := by pr_register_omega

@[simp] theorem prSavedInput_ne_prCounterReg (n : ℕ) (pF pG : Program) (i : Fin n) :
    prSavedInputsStart n pF pG + i ≠ prCounterReg n pF pG := by pr_register_omega

@[simp] theorem prSavedInput_ne_prAccumulatorReg (n : ℕ) (pF pG : Program) (i : Fin n) :
    prSavedInputsStart n pF pG + i ≠ prAccumulatorReg n pF pG := by pr_register_omega

@[simp] theorem prSavedInput_ne_prZeroReg (n : ℕ) (pF pG : Program) (i : Fin n) :
    prSavedInputsStart n pF pG + i ≠ prZeroReg n pF pG := by pr_register_omega

/-! ## Generic "doesn't touch" lemmas

Any program bounded by primitiveRecursionBase doesn't touch high registers. -/

theorem program_doesnt_touch_prSavedInputs (n : ℕ) (pF pG : Program) (p : Program)
    (hp : p.maxRegister ≤ primitiveRecursionBase n pF pG) (i : Fin n) :
    p.maxRegister < prSavedInputsStart n pF pG + i := by
  simp only [prSavedInputsStart]; omega

theorem program_doesnt_touch_prSavedYReg (n : ℕ) (pF pG : Program) (p : Program)
    (hp : p.maxRegister ≤ primitiveRecursionBase n pF pG) :
    p.maxRegister < prSavedYReg n pF pG := by
  simp only [prSavedYReg]; omega

theorem program_doesnt_touch_prCounterReg (n : ℕ) (pF pG : Program) (p : Program)
    (hp : p.maxRegister ≤ primitiveRecursionBase n pF pG) :
    p.maxRegister < prCounterReg n pF pG := by
  simp only [prCounterReg]; omega

theorem program_doesnt_touch_prZeroReg (n : ℕ) (pF pG : Program) (p : Program)
    (hp : p.maxRegister ≤ primitiveRecursionBase n pF pG) :
    p.maxRegister < prZeroReg n pF pG := by
  simp only [prZeroReg]; omega

/-! ## High registers are above n + 1 (for pG input space) -/

@[simp] theorem prSavedInputsStart_gt_n_plus_1 (n : ℕ) (pF pG : Program) :
    n + 1 < prSavedInputsStart n pF pG := by pr_register_omega

@[simp] theorem prSavedYReg_gt_n_plus_1 (n : ℕ) (pF pG : Program) :
    n + 1 < prSavedYReg n pF pG := by pr_register_omega

@[simp] theorem prCounterReg_gt_n_plus_1 (n : ℕ) (pF pG : Program) :
    n + 1 < prCounterReg n pF pG := by pr_register_omega

@[simp] theorem prAccumulatorReg_gt_n_plus_1 (n : ℕ) (pF pG : Program) :
    n + 1 < prAccumulatorReg n pF pG := by pr_register_omega

@[simp] theorem prZeroReg_gt_n_plus_1 (n : ℕ) (pF pG : Program) :
    n + 1 < prZeroReg n pF pG := by pr_register_omega

end Urm
