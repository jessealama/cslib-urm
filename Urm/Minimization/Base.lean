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

The base is chosen as max(n, pF.maxRegister) to ensure pF doesn't clobber
the saved registers.
-/

namespace Urm

open Program

/-- The base register for minimization, ensuring pF doesn't clobber saved registers. -/
def minimizationBase (n : ℕ) (pF : Program) : ℕ :=
  max n pF.maxRegister

/-- The register where counter y is stored. -/
def counterReg (n : ℕ) (pF : Program) : ℕ :=
  minimizationBase n pF + n + 1

/-- The zero register (always contains 0, used for J comparisons). -/
def zeroReg (n : ℕ) (pF : Program) : ℕ :=
  minimizationBase n pF + n + 2

/-- The start of saved input registers. -/
def savedInputsStart (n : ℕ) (pF : Program) : ℕ :=
  minimizationBase n pF + 1

/-! ## Bound lemmas for minimizationBase -/

@[simp] theorem minimizationBase_ge_n (n : ℕ) (pF : Program) :
    n ≤ minimizationBase n pF := le_max_left n pF.maxRegister

@[simp] theorem minimizationBase_ge_pF (n : ℕ) (pF : Program) :
    pF.maxRegister ≤ minimizationBase n pF := le_max_right n pF.maxRegister

/-! ## Register distinctness lemmas -/

@[simp] theorem counterReg_gt_base (n : ℕ) (pF : Program) :
    minimizationBase n pF < counterReg n pF := by
  simp only [counterReg]; omega

@[simp] theorem zeroReg_gt_counterReg (n : ℕ) (pF : Program) :
    counterReg n pF < zeroReg n pF := by
  simp only [counterReg, zeroReg]; omega

@[simp] theorem zeroReg_gt_base (n : ℕ) (pF : Program) :
    minimizationBase n pF < zeroReg n pF := by
  simp only [zeroReg]; omega

@[simp] theorem savedInputsStart_gt_base (n : ℕ) (pF : Program) :
    minimizationBase n pF < savedInputsStart n pF := by
  simp only [savedInputsStart]; omega

@[simp] theorem counterReg_ne_zeroReg (n : ℕ) (pF : Program) :
    counterReg n pF ≠ zeroReg n pF := Nat.ne_of_lt (zeroReg_gt_counterReg n pF)

/-! ## Saved inputs don't overlap with working space -/

@[simp] theorem savedInputsStart_gt_n (n : ℕ) (pF : Program) :
    n ≤ savedInputsStart n pF := by
  simp only [savedInputsStart]; have := minimizationBase_ge_n n pF; omega

@[simp] theorem savedInput_reg_distinct (n : ℕ) (pF : Program) (i : Fin n) :
    savedInputsStart n pF + i ≠ i.val := by
  simp only [savedInputsStart]; have := minimizationBase_ge_n n pF; omega

@[simp] theorem savedInputs_ne_counterReg (n : ℕ) (pF : Program) (i : Fin n) :
    savedInputsStart n pF + i ≠ counterReg n pF := by
  simp only [savedInputsStart, counterReg, minimizationBase]; omega

/-! ## pF doesn't touch high registers -/

@[simp] theorem pF_doesnt_touch_savedInputs (n : ℕ) (pF : Program) (i : Fin n) :
    pF.maxRegister < savedInputsStart n pF + i := by
  simp only [savedInputsStart]; have := minimizationBase_ge_pF n pF; omega

@[simp] theorem pF_doesnt_touch_counter (n : ℕ) (pF : Program) :
    pF.maxRegister < counterReg n pF := by
  simp only [counterReg]; have := minimizationBase_ge_pF n pF; omega

@[simp] theorem pF_doesnt_touch_zeroReg (n : ℕ) (pF : Program) :
    pF.maxRegister < zeroReg n pF := by
  simp only [zeroReg]; have := minimizationBase_ge_pF n pF; omega

end Urm
