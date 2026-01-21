/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.PrimitiveRecursion.StandardForm
import Urm.Shift



/-! # Preservation Lemmas for Primitive Recursion

This file proves register preservation during primitive recursion program execution.

## Main results

- Setup phase initializes registers correctly
- Loop iterations preserve saved inputs
- Zero register remains zero
-/

namespace Urm

open Program

/-! ## Setup Phase Lemmas -/

/-- Helper: no instruction in prSetupPhase writes to registers below n+1.
    (copyRegisterRange writes to savedInputsStart+i, counter writes to prCounterReg,
    zero writes to prZeroReg - all are > n.) -/
private theorem prSetupPhase_no_write_low (n : ℕ) (pF pG : Program) (r : ℕ) (hr : r < n + 1) :
    ∀ instr, instr ∈ prSetupPhase n pF pG → instr.writesTo ≠ some r := by
  intro instr hmem
  simp only [prSetupPhase, List.mem_append, List.mem_cons, List.mem_nil_iff] at hmem
  rcases hmem with hcopy | hcounter | hzero | hfalse
  · simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
    obtain ⟨k, _, rfl⟩ := hcopy
    simp only [Instr.writesTo, ne_eq, Option.some.injEq]
    have := prSavedInputsStart_gt_n_plus_1 n pF pG; omega
  · rw [hcounter]; simp only [Instr.writesTo, ne_eq, Option.some.injEq]
    have := prCounterReg_gt_n_plus_1 n pF pG; omega
  · rw [hzero]; simp only [Instr.writesTo, ne_eq, Option.some.injEq]
    have := prZeroReg_gt_n_plus_1 n pF pG; omega
  · exact hfalse.elim

/-- Helper: no instruction in prLoopPrologue writes to registers above primitiveRecursionBase. -/
private theorem prLoopPrologue_no_write_high (n : ℕ) (pF pG : Program) (r : ℕ)
    (hr : primitiveRecursionBase n pF pG < r) :
    ∀ instr, instr ∈ prLoopPrologue n pF pG → instr.writesTo ≠ some r := by
  intro instr hinstr
  simp only [prLoopPrologue, List.mem_append, List.mem_cons, List.mem_nil_iff] at hinstr
  rcases hinstr with (hclear | hcopy) | hT1 | hT2 | hfalse
  · simp only [Program.clearRegisters, List.mem_map, List.mem_range] at hclear
    obtain ⟨j, hj, rfl⟩ := hclear
    writesTo_omega
  · simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
    obtain ⟨j, hj, rfl⟩ := hcopy
    simp only [Instr.writesTo, ne_eq, Option.some.injEq, Nat.zero_add]
    have := primitiveRecursionBase_ge_n n pF pG; omega
  · rw [hT1]; simp only [Instr.writesTo, ne_eq, Option.some.injEq]
    have := primitiveRecursionBase_ge_n n pF pG; omega
  · rw [hT2]; simp only [Instr.writesTo, ne_eq, Option.some.injEq]
    have := primitiveRecursionBase_ge_n_succ n pF pG; omega
  · exact hfalse.elim

/-- Setup phase is a straight-line program. -/
theorem prSetupPhase_isStraightLine (n : ℕ) (pF pG : Program) :
    (prSetupPhase n pF pG).isStraightLine = true := by
  simp only [prSetupPhase, Program.isStraightLine, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  refine ⟨copyRegisterRange_isStraightLine 0 (prSavedInputsStart n pF pG) (n + 1), ?_, rfl⟩
  simp [Instr.isNonJumping]

/-- Base case prologue is a straight-line program. -/
theorem prBaseCasePrologue_isStraightLine (n : ℕ) (pF pG : Program) :
    (prBaseCasePrologue n pF pG).isStraightLine = true := by
  simp only [prBaseCasePrologue, Program.isStraightLine, List.all_append, Bool.and_eq_true]
  exact ⟨clearRegisters_isStraightLine (primitiveRecursionBase n pF pG),
         copyRegisterRange_isStraightLine (prSavedInputsStart n pF pG) 0 n⟩

/-- Loop prologue is a straight-line program. -/
theorem prLoopPrologue_isStraightLine (n : ℕ) (pF pG : Program) :
    (prLoopPrologue n pF pG).isStraightLine = true := by
  simp only [prLoopPrologue, Program.isStraightLine, List.all_append, Bool.and_eq_true]
  refine ⟨⟨clearRegisters_isStraightLine (primitiveRecursionBase n pF pG),
          copyRegisterRange_isStraightLine (prSavedInputsStart n pF pG) 0 n⟩, ?_⟩
  simp only [List.all_cons, List.all_nil, Instr.isNonJumping, Bool.and_self]

/-! ## Setup Phase Invariants -/

/-- After setup phase, saved inputs contain original inputs. -/
theorem prSetupPhase_saves_inputs (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (hs : s = State.fromInputs (List.ofFn (Fin.snoc inputs y)))
    (c' : Config) (hsteps : Steps (prSetupPhase n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prSetupPhase n pF pG)) (i : Fin n) :
    c'.state.read (prSavedInputsStart n pF pG + i) = inputs i := by
  have hsl := prSetupPhase_isStraightLine n pF pG
  have hk : ↑i < (prSetupPhase n pF pG).length := by
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length]; omega
  have hwrite : (prSetupPhase n pF pG)[↑i] = Instr.T i (prSavedInputsStart n pF pG + i) := by
    simp only [prSetupPhase, Program.copyRegisterRange, Nat.zero_add]
    grind
  have hnowrite_after : ∀ j (hj : j < (prSetupPhase n pF pG).length), ↑i < j →
      ((prSetupPhase n pF pG)[j]).writesTo ≠ some (prSavedInputsStart n pF pG + i) := by
    intro j hj hij
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length] at hj
    simp only [prSetupPhase, List.getElem_append, copyRegisterRange_length]
    split_ifs with hj_copy
    · simp only [Program.copyRegisterRange, List.getElem_map, List.getElem_range,
        Instr.writesTo, ne_eq, Option.some.injEq]; omega
    · have hj_small : j - (n + 1) = 0 ∨ j - (n + 1) = 1 := by omega
      rcases hj_small with h0 | h1
      · simp only [h0, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]; pr_register_omega
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo, ne_eq,
          Option.some.injEq]; pr_register_omega
  obtain ⟨s_before, ⟨c_i, hsteps_i, _, hs_before_eq⟩, htransfer⟩ := straightLine_transfer_result hsl s
    (↑i) (↑i) (prSavedInputsStart n pF pG + i) hk hwrite hnowrite_after
  have hs_before_val : s_before.read (↑i) = s.read (↑i) := by
    rw [← hs_before_eq]
    exact Steps.straightLine_preserves hsl hsteps_i (prSetupPhase_no_write_low n pF pG i (Nat.lt_succ_of_lt i.isLt))
  let hinput_val : s.read ↑i = inputs i := by
    simp only [hs, State.fromInputs, State.read, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, Fin.snoc]
    let hi_lt : (i : ℕ) < n := i.isLt
    let hi_lt' : (i : ℕ) < n + 1 := Nat.lt_succ_of_lt hi_lt
    simp only [hi_lt', ↓reduceDIte, hi_lt, Option.getD_some]
    simp only [cast_eq, Fin.castLT_mk, Fin.eta]
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  have heq : c'.state = straightLineFinalState hsl s := by
    rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val, hinput_val]

/-- After setup phase, savedY contains y. -/
theorem prSetupPhase_saves_y (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (hs : s = State.fromInputs (List.ofFn (Fin.snoc inputs y)))
    (c' : Config) (hsteps : Steps (prSetupPhase n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prSetupPhase n pF pG)) :
    c'.state.read (prSavedYReg n pF pG) = y := by
  have hsl := prSetupPhase_isStraightLine n pF pG
  have hSavedY_eq : prSavedYReg n pF pG = prSavedInputsStart n pF pG + n := by
    pr_register_omega
  rw [hSavedY_eq]
  have hk : n < (prSetupPhase n pF pG).length := by
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length]; omega
  have hwrite : (prSetupPhase n pF pG)[n] = Instr.T n (prSavedInputsStart n pF pG + n) := by
    simp only [prSetupPhase, Program.copyRegisterRange, Nat.zero_add]
    grind
  have hnowrite_after : ∀ j (hj : j < (prSetupPhase n pF pG).length), n < j →
      ((prSetupPhase n pF pG)[j]).writesTo ≠ some (prSavedInputsStart n pF pG + n) := by
    intro j hj hjn
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length] at hj
    simp only [prSetupPhase, List.getElem_append, copyRegisterRange_length]
    split_ifs with hj_copy
    · simp only [Program.copyRegisterRange, List.getElem_map, List.getElem_range,
        Instr.writesTo, ne_eq, Option.some.injEq]; omega
    · have hj_small : j - (n + 1) = 0 ∨ j - (n + 1) = 1 := by omega
      rcases hj_small with h0 | h1
      · simp only [h0, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]; pr_register_omega
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo, ne_eq,
          Option.some.injEq]; pr_register_omega
  obtain ⟨s_before, ⟨c_n, hsteps_n, _, hs_before_eq⟩, htransfer⟩ := straightLine_transfer_result hsl s
    n n (prSavedInputsStart n pF pG + n) hk hwrite hnowrite_after
  have hs_before_val : s_before.read n = s.read n := by
    rw [← hs_before_eq]
    exact Steps.straightLine_preserves hsl hsteps_n (prSetupPhase_no_write_low n pF pG n (Nat.lt_succ_self n))
  let hy_val : s.read n = y := by
    simp only [hs, State.fromInputs, State.read, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, Fin.snoc]
    let hn_lt : n < n + 1 := Nat.lt_succ_self n
    simp only [hn_lt, ↓reduceDIte, show ¬(n < n) by omega, Option.getD_some, cast_eq]
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  have heq : c'.state = straightLineFinalState hsl s := by
    rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val, hy_val]

/-- After setup phase, counter is 0. -/
theorem prSetupPhase_counter_zero (n : ℕ) (pF pG : Program)
    (s : State)
    (c' : Config) (hsteps : Steps (prSetupPhase n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prSetupPhase n pF pG)) :
    c'.state.read (prCounterReg n pF pG) = 0 := by
  have hsl := prSetupPhase_isStraightLine n pF pG
  have hk : n + 1 < (prSetupPhase n pF pG).length := by
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length]; omega
  have hwrite : (prSetupPhase n pF pG)[n + 1] = Instr.Z (prCounterReg n pF pG) := by
    simp only [prSetupPhase, List.getElem_append, copyRegisterRange_length]
    simp
  have hnowrite : ∀ j (hj : j < (prSetupPhase n pF pG).length), n + 1 < j →
      ((prSetupPhase n pF pG)[j]).writesTo ≠ some (prCounterReg n pF pG) := by
    intro j hj hjn
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length] at hj
    obtain rfl : j = n + 2 := by omega
    simp only [prSetupPhase, List.getElem_append, copyRegisterRange_length]
    simp only [show ¬(n + 2 < n + 1) by omega, dite_false, show n + 2 - (n + 1) = 1 by omega]
    simp [Instr.writesTo, prZeroReg, prCounterReg]
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  exact straightLine_zeros_register hsl s (prCounterReg n pF pG) (n + 1) hk hwrite hnowrite

/-- After setup phase, zero register is 0. -/
theorem prSetupPhase_zero_zero (n : ℕ) (pF pG : Program)
    (s : State)
    (c' : Config) (hsteps : Steps (prSetupPhase n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prSetupPhase n pF pG)) :
    c'.state.read (prZeroReg n pF pG) = 0 := by
  have hsl := prSetupPhase_isStraightLine n pF pG
  have hk : n + 2 < (prSetupPhase n pF pG).length := by
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length]; omega
  have hwrite : (prSetupPhase n pF pG)[n + 2] = Instr.Z (prZeroReg n pF pG) := by
    simp only [prSetupPhase, List.getElem_append, copyRegisterRange_length]
    simp only [show ¬(n + 2 < n + 1) by omega, dite_false, show n + 2 - (n + 1) = 1 by omega]
    simp
  have hnowrite : ∀ j (hj : j < (prSetupPhase n pF pG).length), n + 2 < j →
      ((prSetupPhase n pF pG)[j]).writesTo ≠ some (prZeroReg n pF pG) := by
    intro j hj hjn
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length] at hj
    omega
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  exact straightLine_zeros_register hsl s (prZeroReg n pF pG) (n + 2) hk hwrite hnowrite

/-! ## Base Case Prologue Invariants -/

/-- After base case prologue, R[0..n-1] contain saved inputs from s. -/
theorem prBaseCasePrologue_restores_inputs (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (prBaseCasePrologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prBaseCasePrologue n pF pG)) (i : Fin n) :
    c'.state.read i = s.read (prSavedInputsStart n pF pG + i) := by
  have hsl := prBaseCasePrologue_isStraightLine n pF pG
  have hi : ↑i < n := i.2
  have hk : (primitiveRecursionBase n pF pG + 1) + ↑i < (prBaseCasePrologue n pF pG).length := by
    simp only [prBaseCasePrologue, List.length_append, clearRegisters_length, copyRegisterRange_length]
    omega
  have hwrite : (prBaseCasePrologue n pF pG)[(primitiveRecursionBase n pF pG + 1) + ↑i] =
      Instr.T (prSavedInputsStart n pF pG + i) i := by
    simp only [prBaseCasePrologue]
    let h_not_in_clear : ¬((primitiveRecursionBase n pF pG + 1) + ↑i < (clearRegisters (primitiveRecursionBase n pF pG)).length) := by
      simp only [clearRegisters_length]; omega
    rw [List.getElem_append_right (Nat.not_lt.mp h_not_in_clear)]
    let hidx : (primitiveRecursionBase n pF pG + 1) + ↑i - (clearRegisters (primitiveRecursionBase n pF pG)).length = ↑i := by
      simp only [clearRegisters_length]; omega
    simp only [hidx, Program.copyRegisterRange, List.getElem_map, List.getElem_range, Nat.zero_add]
  have hnowrite_after : ∀ j (hj : j < (prBaseCasePrologue n pF pG).length),
      (primitiveRecursionBase n pF pG + 1) + ↑i < j →
      ((prBaseCasePrologue n pF pG)[j]).writesTo ≠ some ↑i := by
    intro j hj hjk
    simp only [prBaseCasePrologue, List.length_append, clearRegisters_length, copyRegisterRange_length] at hj
    simp only [prBaseCasePrologue]
    by_cases hj_clear : j < (clearRegisters (primitiveRecursionBase n pF pG)).length
    · simp only [clearRegisters_length] at hj_clear; omega
    · rw [List.getElem_append_right (Nat.not_lt.mp hj_clear)]
      simp only [Program.copyRegisterRange, List.getElem_map, List.getElem_range,
        Instr.writesTo, ne_eq, Option.some.injEq, Nat.zero_add, clearRegisters_length]
      omega
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before⟩, htransfer⟩ :=
    straightLine_transfer_result hsl s ((primitiveRecursionBase n pF pG + 1) + ↑i) (prSavedInputsStart n pF pG + i) ↑i hk hwrite hnowrite_after
  let hs_before_val : s_before.read (prSavedInputsStart n pF pG + ↑i) =
      s.read (prSavedInputsStart n pF pG + ↑i) := by
    rw [← hs_before]
    let hnowrite_before : ∀ instr, instr ∈ prBaseCasePrologue n pF pG →
        instr.writesTo ≠ some (prSavedInputsStart n pF pG + ↑i) := by
      intro instr hinstr
      simp only [prBaseCasePrologue, List.mem_append] at hinstr
      cases hinstr with
      | inl hclear =>
        simp only [Program.clearRegisters, List.mem_map, List.mem_range] at hclear
        obtain ⟨j, hj, rfl⟩ := hclear
        simp only [Instr.writesTo, ne_eq, Option.some.injEq]
        let h := prSavedInputsStart_gt_base n pF pG; omega
      | inr hcopy =>
        simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
        obtain ⟨j, hj, rfl⟩ := hcopy
        simp only [Instr.writesTo, ne_eq, Option.some.injEq, Nat.zero_add]
        let h := prSavedInputsStart_ge_n n pF pG; omega
    exact Steps.straightLine_preserves hsl hsteps_k hnowrite_before
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  have heq : c'.state = straightLineFinalState hsl s := by
    rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val]

/-- Base case prologue preserves high registers (above primitiveRecursionBase). -/
theorem prBaseCasePrologue_preserves_high_register (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (prBaseCasePrologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prBaseCasePrologue n pF pG))
    (r : ℕ) (hr : primitiveRecursionBase n pF pG < r) :
    c'.state.read r = s.read r := by
  have hsl := prBaseCasePrologue_isStraightLine n pF pG
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  apply Steps.straightLine_preserves hsl hsteps'
  intro instr hinstr
  simp only [prBaseCasePrologue, List.mem_append] at hinstr
  cases hinstr with
  | inl hclear =>
    simp only [Program.clearRegisters, List.mem_map, List.mem_range] at hclear
    obtain ⟨j, hj, rfl⟩ := hclear
    writesTo_omega
  | inr hcopy =>
    simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
    obtain ⟨j, hj, rfl⟩ := hcopy
    simp only [Instr.writesTo, ne_eq, Option.some.injEq, Nat.zero_add]
    have := primitiveRecursionBase_ge_n n pF pG; omega

/-- After base case prologue, registers in [n..base] are cleared to 0. -/
theorem prBaseCasePrologue_clears_above_n (n : ℕ) (pF pG : Program) (s : State) (c : Config)
    (hsteps : Steps (prBaseCasePrologue n pF pG) ⟨0, s⟩ c)
    (hhalted : c.isHalted (prBaseCasePrologue n pF pG))
    (r : ℕ) (hr_ge : n ≤ r) (hr_le : r ≤ primitiveRecursionBase n pF pG) :
    c.state.read r = 0 := by
  have hsl := prBaseCasePrologue_isStraightLine n pF pG
  have hk : r < (prBaseCasePrologue n pF pG).length := by
    simp only [prBaseCasePrologue, List.length_append, clearRegisters_length, copyRegisterRange_length]
    omega
  have hwrite : (prBaseCasePrologue n pF pG)[r] = Instr.Z r := by
    simp only [prBaseCasePrologue]
    let h_in_clear : r < (clearRegisters (primitiveRecursionBase n pF pG)).length := by
      simp only [clearRegisters_length]; exact Nat.lt_succ_of_le hr_le
    rw [List.getElem_append_left h_in_clear]
    simp only [Program.clearRegisters, List.getElem_map, List.getElem_range]
  have hnowrite : ∀ j (hj : j < (prBaseCasePrologue n pF pG).length), r < j →
      ((prBaseCasePrologue n pF pG)[j]).writesTo ≠ some r := by
    intro j hj hjr
    simp only [prBaseCasePrologue, List.length_append, clearRegisters_length,
      copyRegisterRange_length] at hj
    simp only [prBaseCasePrologue]
    by_cases hj_clear1 : j < (clearRegisters (primitiveRecursionBase n pF pG) ++
        copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length
    · by_cases hj_clear : j < primitiveRecursionBase n pF pG + 1
      · let h2 : j < (clearRegisters (primitiveRecursionBase n pF pG)).length := by
          simp only [clearRegisters_length]; exact hj_clear
        rw [List.getElem_append_left h2]
        simp only [Program.clearRegisters, List.getElem_map, List.getElem_range,
          Instr.writesTo, ne_eq, Option.some.injEq]
        intro heq; exact Nat.ne_of_lt hjr heq.symm
      · let h2 : ¬ j < (clearRegisters (primitiveRecursionBase n pF pG)).length := by
          simp only [clearRegisters_length]; omega
        let h2' : (clearRegisters (primitiveRecursionBase n pF pG)).length ≤ j := Nat.not_lt.mp h2
        rw [List.getElem_append_right h2']
        simp only [clearRegisters_length, Program.copyRegisterRange,
          List.getElem_map, List.getElem_range, Nat.zero_add, Instr.writesTo, ne_eq, Option.some.injEq]
        simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear1
        omega
    · simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear1
      omega
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  exact straightLine_zeros_register hsl s r r hk hwrite hnowrite

/-- After loop prologue, registers 0..n-1 contain the saved inputs. -/
theorem prLoopPrologue_restores_inputs (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (prLoopPrologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prLoopPrologue n pF pG)) (i : Fin n) :
    c'.state.read i = s.read (prSavedInputsStart n pF pG + i) := by
  have hsl := prLoopPrologue_isStraightLine n pF pG
  have hk : (primitiveRecursionBase n pF pG + 1) + ↑i < (prLoopPrologue n pF pG).length := by
    simp only [prLoopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
      List.length]
    omega
  have hwrite : (prLoopPrologue n pF pG)[(primitiveRecursionBase n pF pG + 1) + ↑i] =
      Instr.T (prSavedInputsStart n pF pG + i) i := by
    simp only [prLoopPrologue]
    let h_in_clear_copy : (primitiveRecursionBase n pF pG + 1) + ↑i <
        (clearRegisters (primitiveRecursionBase n pF pG) ++
         copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length := by len_append_omega
    rw [List.getElem_append_left h_in_clear_copy]
    let h_not_in_clear : ¬((primitiveRecursionBase n pF pG + 1) + ↑i <
        (clearRegisters (primitiveRecursionBase n pF pG)).length) := by
      simp only [clearRegisters_length]; omega
    rw [List.getElem_append_right (Nat.not_lt.mp h_not_in_clear)]
    let hidx : (primitiveRecursionBase n pF pG + 1) + ↑i -
        (clearRegisters (primitiveRecursionBase n pF pG)).length = ↑i := by
      simp only [clearRegisters_length]; omega
    simp only [hidx, Program.copyRegisterRange, List.getElem_map, List.getElem_range, Nat.zero_add]
  have hnowrite_after : ∀ j (hj : j < (prLoopPrologue n pF pG).length),
      (primitiveRecursionBase n pF pG + 1) + ↑i < j →
      ((prLoopPrologue n pF pG)[j]).writesTo ≠ some ↑i := by
    intro j hj hjk
    simp only [prLoopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
      List.length] at hj
    simp only [prLoopPrologue]
    by_cases hj_in_main : j < (clearRegisters (primitiveRecursionBase n pF pG) ++
        copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length
    · rw [List.getElem_append_left hj_in_main]
      by_cases hj_clear : j < (clearRegisters (primitiveRecursionBase n pF pG)).length
      · simp only [clearRegisters_length] at hj_clear; omega
      · rw [List.getElem_append_right (Nat.not_lt.mp hj_clear)]
        simp only [Program.copyRegisterRange, List.getElem_map, List.getElem_range,
          Instr.writesTo, ne_eq, Option.some.injEq, Nat.zero_add, clearRegisters_length]
        simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_in_main
        omega
    · rw [List.getElem_append_right (Nat.not_lt.mp hj_in_main)]
      have hj_idx : j - (clearRegisters (primitiveRecursionBase n pF pG) ++
          copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length = 0 ∨
          j - (clearRegisters (primitiveRecursionBase n pF pG) ++
          copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length = 1 := by
        simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_in_main hj ⊢
        omega
      rcases hj_idx with h0 | h1
      · simp only [h0, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
        have := primitiveRecursionBase_ge_n n pF pG; omega
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo, ne_eq,
          Option.some.injEq]
        have := primitiveRecursionBase_ge_n n pF pG; omega
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before⟩, htransfer⟩ :=
    straightLine_transfer_result hsl s ((primitiveRecursionBase n pF pG + 1) + ↑i)
      (prSavedInputsStart n pF pG + i) ↑i hk hwrite hnowrite_after
  have hs_before_val : s_before.read (prSavedInputsStart n pF pG + ↑i) =
      s.read (prSavedInputsStart n pF pG + ↑i) := by
    rw [← hs_before]
    apply Steps.straightLine_preserves hsl hsteps_k
    have h := prSavedInputsStart_gt_base n pF pG
    exact prLoopPrologue_no_write_high n pF pG _ (by omega)
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  have heq : c'.state = straightLineFinalState hsl s := by
    rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val]

/-- After loop prologue, R[n] contains k (from counter register). -/
theorem prLoopPrologue_sets_Rn (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (prLoopPrologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prLoopPrologue n pF pG)) :
    c'.state.read n = s.read (prCounterReg n pF pG) := by
  have hsl := prLoopPrologue_isStraightLine n pF pG
  have hk : (primitiveRecursionBase n pF pG + 1) + n < (prLoopPrologue n pF pG).length := by
    simp only [prLoopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
      List.length]; omega
  have hwrite : (prLoopPrologue n pF pG)[(primitiveRecursionBase n pF pG + 1) + n] =
      Instr.T (prCounterReg n pF pG) n := by
    simp only [prLoopPrologue]
    let h_not_in_clear_copy : ¬((primitiveRecursionBase n pF pG + 1) + n <
        (clearRegisters (primitiveRecursionBase n pF pG) ++
         copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length) := by len_append_omega
    rw [List.getElem_append_right (Nat.not_lt.mp h_not_in_clear_copy)]
    let hidx : (primitiveRecursionBase n pF pG + 1) + n -
        (clearRegisters (primitiveRecursionBase n pF pG) ++
         copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length = 0 := by len_append_omega
    simp only [hidx, List.getElem_cons_zero]
  have hnowrite_after : ∀ j (hj : j < (prLoopPrologue n pF pG).length),
      (primitiveRecursionBase n pF pG + 1) + n < j →
      ((prLoopPrologue n pF pG)[j]).writesTo ≠ some n := by
    intro j hj hjk
    simp only [prLoopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
      List.length] at hj
    simp only [prLoopPrologue]
    let h_not_in_clear_copy : ¬(j < (clearRegisters (primitiveRecursionBase n pF pG) ++
        copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length) := by len_append_omega
    rw [List.getElem_append_right (Nat.not_lt.mp h_not_in_clear_copy)]
    let hidx : j - (clearRegisters (primitiveRecursionBase n pF pG) ++
        copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length = 1 := by len_append_omega
    simp only [hidx]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
    let h := primitiveRecursionBase_ge_n n pF pG; omega
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before⟩, htransfer⟩ :=
    straightLine_transfer_result hsl s ((primitiveRecursionBase n pF pG + 1) + n)
      (prCounterReg n pF pG) n hk hwrite hnowrite_after
  have hs_before_val : s_before.read (prCounterReg n pF pG) = s.read (prCounterReg n pF pG) := by
    rw [← hs_before]
    apply Steps.straightLine_preserves hsl hsteps_k
    exact prLoopPrologue_no_write_high n pF pG _ (prCounterReg_gt_base n pF pG)
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  have heq : c'.state = straightLineFinalState hsl s := by
    rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val]

/-- After loop prologue, R[n+1] contains accBefore (from accumulator register). -/
theorem prLoopPrologue_sets_Rn1 (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (prLoopPrologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prLoopPrologue n pF pG)) :
    c'.state.read (n + 1) = s.read (prAccumulatorReg n pF pG) := by
  have hsl := prLoopPrologue_isStraightLine n pF pG
  have hk : (primitiveRecursionBase n pF pG + 2) + n < (prLoopPrologue n pF pG).length := by
    simp only [prLoopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
      List.length]; omega
  have hwrite : (prLoopPrologue n pF pG)[(primitiveRecursionBase n pF pG + 2) + n] =
      Instr.T (prAccumulatorReg n pF pG) (n + 1) := by
    simp only [prLoopPrologue]
    let h_not_in_clear_copy : ¬((primitiveRecursionBase n pF pG + 2) + n <
        (clearRegisters (primitiveRecursionBase n pF pG) ++
         copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length) := by len_append_omega
    rw [List.getElem_append_right (Nat.not_lt.mp h_not_in_clear_copy)]
    let hidx : (primitiveRecursionBase n pF pG + 2) + n -
        (clearRegisters (primitiveRecursionBase n pF pG) ++
         copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length = 1 := by len_append_omega
    simp only [hidx, List.getElem_cons_succ, List.getElem_cons_zero]
  have hnowrite_after : ∀ j (hj : j < (prLoopPrologue n pF pG).length),
      (primitiveRecursionBase n pF pG + 2) + n < j →
      ((prLoopPrologue n pF pG)[j]).writesTo ≠ some (n + 1) := by
    intro j hj hjk
    simp only [prLoopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
      List.length] at hj; omega
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before⟩, htransfer⟩ :=
    straightLine_transfer_result hsl s ((primitiveRecursionBase n pF pG + 2) + n)
      (prAccumulatorReg n pF pG) (n + 1) hk hwrite hnowrite_after
  have hs_before_val : s_before.read (prAccumulatorReg n pF pG) = s.read (prAccumulatorReg n pF pG) := by
    rw [← hs_before]
    apply Steps.straightLine_preserves hsl hsteps_k
    exact prLoopPrologue_no_write_high n pF pG _ (prAccumulatorReg_gt_base n pF pG)
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  have heq : c'.state = straightLineFinalState hsl s := by
    rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val]

/-- Loop prologue preserves high registers (above primitiveRecursionBase). -/
theorem prLoopPrologue_preserves_high_register (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (prLoopPrologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prLoopPrologue n pF pG))
    (r : ℕ) (hr : primitiveRecursionBase n pF pG < r) :
    c'.state.read r = s.read r := by
  have hsl := prLoopPrologue_isStraightLine n pF pG
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  exact Steps.straightLine_preserves hsl hsteps' (prLoopPrologue_no_write_high n pF pG r hr)

/-- Loop prologue zeros registers in range (n+1, primitiveRecursionBase]. -/
theorem prLoopPrologue_clears_pG_range (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (prLoopPrologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prLoopPrologue n pF pG))
    (r : ℕ) (hr_gt : n + 1 < r) (hr_le : r ≤ primitiveRecursionBase n pF pG) :
    c'.state.read r = 0 := by
  have hsl := prLoopPrologue_isStraightLine n pF pG
  have hk : r < (prLoopPrologue n pF pG).length := by
    simp only [prLoopPrologue, List.length_append, clearRegisters_length,
      copyRegisterRange_length, List.length]; omega
  have h_in_clear : r < (clearRegisters (primitiveRecursionBase n pF pG)).length := by
    simp only [clearRegisters_length]; exact Nat.lt_succ_of_le hr_le
  have h_in_ext2 : r < (clearRegisters (primitiveRecursionBase n pF pG) ++
      copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length := by len_append_omega
  have hwrite : (prLoopPrologue n pF pG)[r] = Instr.Z r := by
    simp only [prLoopPrologue]
    rw [List.getElem_append_left h_in_ext2, List.getElem_append_left h_in_clear]
    simp only [Program.clearRegisters, List.getElem_map, List.getElem_range]
  have hnowrite : ∀ j (hj : j < (prLoopPrologue n pF pG).length), r < j →
      ((prLoopPrologue n pF pG)[j]).writesTo ≠ some r := by
    intro j hj hjr
    simp only [prLoopPrologue, List.length_append, clearRegisters_length,
      copyRegisterRange_length, List.length] at hj
    simp only [prLoopPrologue]
    by_cases hj_clear2 : j < (clearRegisters (primitiveRecursionBase n pF pG) ++
        copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length
    · rw [List.getElem_append_left hj_clear2]
      by_cases hj_in_clear : j < (clearRegisters (primitiveRecursionBase n pF pG)).length
      · rw [List.getElem_append_left hj_in_clear]
        simp only [Program.clearRegisters, List.getElem_map, List.getElem_range,
          Instr.writesTo, ne_eq, Option.some.injEq]; omega
      · rw [List.getElem_append_right (Nat.not_lt.mp hj_in_clear)]
        simp only [clearRegisters_length, Program.copyRegisterRange, List.getElem_map,
          List.getElem_range, Nat.zero_add, Instr.writesTo, ne_eq, Option.some.injEq]
        simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear2
        simp only [clearRegisters_length] at hj_in_clear; omega
    · rw [List.getElem_append_right (Nat.not_lt.mp hj_clear2)]
      simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear2 ⊢
      have hidx : j - (primitiveRecursionBase n pF pG + 1 + n) = 0 ∨
          j - (primitiveRecursionBase n pF pG + 1 + n) = 1 := by omega
      rcases hidx with h0 | h1
      · simp only [h0, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]; omega
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo, ne_eq,
          Option.some.injEq]; omega
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  exact straightLine_zeros_register hsl s r r hk hwrite hnowrite

/-- State agreement helper: After loop prologue, state agrees with extendInputsForG initial state
    on pG's register range. This abstracts the common pattern used in pr_loop_iteration and
    primitiveRecursionProgram_halts_imp_dom. -/
theorem prLoopPrologue_state_agreeOn_pG_init (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (prLoopPrologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prLoopPrologue n pF pG))
    (inputs : Fin n → ℕ) (k : ℕ) (acc : ℕ)
    (hR_inputs : ∀ i : Fin n, c'.state.read i = inputs i)
    (hRn : c'.state.read n = k)
    (hRn1 : c'.state.read (n + 1) = acc) :
    c'.state.agreeOn
      (Config.init (List.ofFn (extendInputsForG inputs k acc))).state
      0 pG.maxRegister := by
  intro r _ hr_hi
  let initStateG := (Config.init (List.ofFn (extendInputsForG inputs k acc))).state
  by_cases hr_lt_n : r < n
  · -- Case 1: r < n (input registers)
    have hleft : c'.state.read r = inputs ⟨r, hr_lt_n⟩ := hR_inputs ⟨r, hr_lt_n⟩
    have hlen : r < (n + 2) := by omega
    have hright : initStateG.read r = inputs ⟨r, hr_lt_n⟩ := by
      unfold initStateG Config.init State.fromInputs State.read
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hlen, ↓reduceDIte]
      exact extendInputsForG_castSucc_castSucc inputs k acc ⟨r, hr_lt_n⟩
    rw [hleft, hright]
  · by_cases hr_eq_n : r = n
    · -- Case 2: r = n (counter register position)
      subst hr_eq_n
      have hleft : c'.state.read r = k := hRn
      have hr : r < r + 2 := by omega
      have heq : (⟨r, hr⟩ : Fin (r + 2)) = Fin.castSucc (Fin.last r) := by
        ext; simp [Fin.castSucc, Fin.last]
      have hright : initStateG.read r = k := by
        unfold initStateG Config.init State.fromInputs State.read
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hr, ↓reduceDIte]
        rw [heq]
        exact extendInputsForG_castSucc_last inputs k acc
      rw [hleft, hright]
    · by_cases hr_eq_n1 : r = n + 1
      · -- Case 3: r = n + 1 (accumulator register position)
        subst hr_eq_n1
        have hleft : c'.state.read (n + 1) = acc := hRn1
        have hlt : n + 1 < n + 2 := Nat.lt_succ_self _
        have hright : initStateG.read (n + 1) = acc := by
          unfold initStateG Config.init State.fromInputs State.read
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [hlt, ↓reduceDIte, Option.getD_some]
          exact extendInputsForG_last inputs k acc
        rw [hleft, hright]
      · -- Case 4: r > n + 1 (high registers, cleared to 0)
        have hr_gt_n1 : n + 1 < r := by omega
        have hr_le_pG_max : r ≤ pG.maxRegister := hr_hi
        have hpG_le_base : pG.maxRegister ≤ primitiveRecursionBase n pF pG :=
          primitiveRecursionBase_ge_pG n pF pG
        have hr_le_base : r ≤ primitiveRecursionBase n pF pG := Nat.le_trans hr_le_pG_max hpG_le_base
        have hleft : c'.state.read r = 0 :=
          prLoopPrologue_clears_pG_range n pF pG s c' hsteps hhalted r hr_gt_n1 hr_le_base
        have hr_ge : ¬ r < n + 2 := by omega
        have hright : initStateG.read r = 0 := by
          unfold initStateG Config.init State.fromInputs State.read
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr_ge, dite_false, Option.getD_none]
        rw [hleft, hright]

end Urm
