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

/-- Tactic for solving register arithmetic goals in minimization.
    Unfolds register definitions and calls omega. -/
macro "min_register_omega" : tactic =>
  `(tactic| (simp only [savedInputsStart, counterReg, zeroReg, minimizationBase]; omega))

/-! ## Bound lemmas for minimizationBase -/

@[simp] theorem minimizationBase_ge_n (n : ℕ) (pF : Program) :
    n ≤ minimizationBase n pF := le_max_left n pF.maxRegister

@[simp] theorem minimizationBase_ge_pF (n : ℕ) (pF : Program) :
    pF.maxRegister ≤ minimizationBase n pF := le_max_right n pF.maxRegister

/-! ## Register distinctness lemmas -/

@[simp] theorem counterReg_gt_base (n : ℕ) (pF : Program) :
    minimizationBase n pF < counterReg n pF := by min_register_omega

@[simp] theorem zeroReg_gt_counterReg (n : ℕ) (pF : Program) :
    counterReg n pF < zeroReg n pF := by min_register_omega

@[simp] theorem zeroReg_gt_base (n : ℕ) (pF : Program) :
    minimizationBase n pF < zeroReg n pF := by min_register_omega

@[simp] theorem savedInputsStart_gt_base (n : ℕ) (pF : Program) :
    minimizationBase n pF < savedInputsStart n pF := by min_register_omega

@[simp] theorem counterReg_ne_zeroReg (n : ℕ) (pF : Program) :
    counterReg n pF ≠ zeroReg n pF := Nat.ne_of_lt (zeroReg_gt_counterReg n pF)

/-! ## Saved inputs don't overlap with working space -/

@[simp] theorem savedInputsStart_gt_n (n : ℕ) (pF : Program) :
    n ≤ savedInputsStart n pF := by min_register_omega

@[simp] theorem savedInput_reg_distinct (n : ℕ) (pF : Program) (i : Fin n) :
    savedInputsStart n pF + i ≠ i.val := by min_register_omega

@[simp] theorem savedInputs_ne_counterReg (n : ℕ) (pF : Program) (i : Fin n) :
    savedInputsStart n pF + i ≠ counterReg n pF := by min_register_omega

/-! ## Generic "doesn't touch" lemmas

Any program bounded by minimizationBase doesn't touch high registers. -/

theorem program_doesnt_touch_savedInputs (n : ℕ) (pF : Program) (p : Program)
    (hp : p.maxRegister ≤ minimizationBase n pF) (i : Fin n) :
    p.maxRegister < savedInputsStart n pF + i := by
  simp only [savedInputsStart]; omega

theorem program_doesnt_touch_counter (n : ℕ) (pF : Program) (p : Program)
    (hp : p.maxRegister ≤ minimizationBase n pF) :
    p.maxRegister < counterReg n pF := by
  simp only [counterReg]; omega

theorem program_doesnt_touch_zeroReg (n : ℕ) (pF : Program) (p : Program)
    (hp : p.maxRegister ≤ minimizationBase n pF) :
    p.maxRegister < zeroReg n pF := by
  simp only [zeroReg]; omega

/-! ## Automation tactics for minimization proofs -/

/-- Try to discharge a writesTo ≠ some r goal using omega with minimization register definitions. -/
macro "min_writesTo_omega" : tactic =>
  `(tactic| (simp only [Instr.writesTo, ne_eq, Option.some.injEq,
      savedInputsStart, counterReg, zeroReg, minimizationBase]; omega))

/-- Tactic for discharging nowrite goals in minimization proofs.
    Handles both copyRegisterRange and fixed instruction cases. -/
macro "min_discharge_nowrite" : tactic =>
  `(tactic| first
    | (simp only [Instr.writesTo, ne_eq, Option.some.injEq, Program.copyRegisterRange,
        List.getElem_map, List.getElem_range, Nat.zero_add]; omega)
    | min_writesTo_omega
    | (simp only [List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq];
       min_register_omega)
    | (simp only [List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo, ne_eq,
        Option.some.injEq]; min_register_omega))

/-- Handle the case of a 2-element suffix list [I₀, I₁] for minimization proofs. -/
macro "min_suffix2_nowrite" idx:term : tactic =>
  `(tactic| (
    rcases Nat.eq_zero_or_pos $idx with h | hpos
    · simp only [h, List.getElem_cons_zero, List.getElem_cons_succ, Instr.writesTo, ne_eq,
        Option.some.injEq, savedInputsStart, counterReg, zeroReg, minimizationBase] <;> omega
    · have h : $idx = 1 := by omega
      simp only [h, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo, ne_eq,
        Option.some.injEq, savedInputsStart, counterReg, zeroReg, minimizationBase] <;> omega))

end Urm
