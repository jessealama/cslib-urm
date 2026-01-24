/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.Core

/-! # Base Register Computation for Minimization

This file defines the base register for the minimization witness program.

## Register Layout

For minimization of f : (Fin (n+1) → ℕ) → Part ℕ with program pF:

- R[0..n-1]         = working input space (restored each iteration)
- R[n]              = receives counter y before pF execution
- R[base+1..base+n] = saved inputs (preserved throughout)
- R[base+n+1]       = counter y (incremented each iteration)
- R[base+n+2]       = zero register (always 0, for J comparisons)

The base is chosen as max(n, pF.max_register) to ensure pF doesn't clobber
the saved registers.
-/

namespace Urm

open Program

/-- The base register for minimization, ensuring pF doesn't clobber saved registers. -/
@[grind =] def minimization_base (n : ℕ) (pF : Program) : ℕ :=
  max n pF.max_register

/-- The register where counter y is stored. -/
@[grind =] def counter_reg (n : ℕ) (pF : Program) : ℕ :=
  minimization_base n pF + n + 1

/-- The zero register (always contains 0, used for J comparisons). -/
@[grind =] def zero_reg (n : ℕ) (pF : Program) : ℕ :=
  minimization_base n pF + n + 2

/-- The start of saved input registers. -/
@[grind =] def savedInputsStart (n : ℕ) (pF : Program) : ℕ :=
  minimization_base n pF + 1

/-- Tactic for solving register arithmetic goals in minimization.
    Unfolds register definitions and calls grind. -/
macro "min_register_omega" : tactic =>
  `(tactic| grind)

/-! ## Bound lemmas for minimization_base -/

@[simp] theorem minimization_base_ge_n (n : ℕ) (pF : Program) :
    n ≤ minimization_base n pF := le_max_left n pF.max_register

@[simp] theorem minimization_base_ge_pF (n : ℕ) (pF : Program) :
    pF.max_register ≤ minimization_base n pF := le_max_right n pF.max_register

/-! ## Register distinctness lemmas -/

@[simp] theorem counter_reg_gt_base (n : ℕ) (pF : Program) :
    minimization_base n pF < counter_reg n pF := by min_register_omega

@[simp] theorem zero_reg_gt_counter_reg (n : ℕ) (pF : Program) :
    counter_reg n pF < zero_reg n pF := by min_register_omega

@[simp] theorem zero_reg_gt_base (n : ℕ) (pF : Program) :
    minimization_base n pF < zero_reg n pF := by min_register_omega

@[simp] theorem savedInputsStart_gt_base (n : ℕ) (pF : Program) :
    minimization_base n pF < savedInputsStart n pF := by min_register_omega

@[simp] theorem counter_reg_ne_zero_reg (n : ℕ) (pF : Program) :
    counter_reg n pF ≠ zero_reg n pF := Nat.ne_of_lt (zero_reg_gt_counter_reg n pF)

/-! ## Saved inputs don't overlap with working space -/

@[simp] theorem savedInputsStart_gt_n (n : ℕ) (pF : Program) :
    n ≤ savedInputsStart n pF := by min_register_omega

theorem savedInput_reg_distinct (n : ℕ) (pF : Program) (i : Fin n) :
    savedInputsStart n pF + i ≠ i.val := by min_register_omega

@[simp] theorem savedInputs_ne_counter_reg (n : ℕ) (pF : Program) (i : Fin n) :
    savedInputsStart n pF + i ≠ counter_reg n pF := by min_register_omega

/-! ## Generic "doesn't touch" lemmas

Any program bounded by minimization_base doesn't touch high registers. -/

theorem program_doesnt_touch_savedInputs (n : ℕ) (pF : Program) (p : Program)
    (hp : p.max_register ≤ minimization_base n pF) (i : Fin n) :
    p.max_register < savedInputsStart n pF + i := by
  simp only [savedInputsStart]; omega

theorem program_doesnt_touch_counter (n : ℕ) (pF : Program) (p : Program)
    (hp : p.max_register ≤ minimization_base n pF) :
    p.max_register < counter_reg n pF := by
  simp only [counter_reg]; omega

theorem program_doesnt_touch_zero_reg (n : ℕ) (pF : Program) (p : Program)
    (hp : p.max_register ≤ minimization_base n pF) :
    p.max_register < zero_reg n pF := by
  simp only [zero_reg]; omega

end Urm
