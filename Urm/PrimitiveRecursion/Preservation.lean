/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.PrimitiveRecursion.StandardForm

/-! # Preservation Lemmas for Primitive Recursion

This file proves register preservation during primitive recursion program execution.

## Main results

- pF and pG don't touch counter, accumulator, savedY, zero, or saved input registers
- Setup phase initializes registers correctly
- Loop iterations preserve saved inputs
- Zero register remains zero
-/

namespace Urm

open Program

/-! ## General register preservation -/

/-- General lemma: pF execution preserves any register beyond its maxRegister. -/
theorem prPF_preserves_high_reg (pF : Program) (s s' : State)
    (c' : Config) (hsteps : Steps pF ⟨0, s⟩ c') (hstate_eq : c'.state = s')
    (r : ℕ) (hr : pF.maxRegister < r) :
    s'.read r = s.read r := by
  subst hstate_eq
  exact Steps.preserves_high_register hsteps r hr

/-- General lemma: pG execution preserves any register beyond its maxRegister. -/
theorem prPG_preserves_high_reg (pG : Program) (s s' : State)
    (c' : Config) (hsteps : Steps pG ⟨0, s⟩ c') (hstate_eq : c'.state = s')
    (r : ℕ) (hr : pG.maxRegister < r) :
    s'.read r = s.read r := by
  subst hstate_eq
  exact Steps.preserves_high_register hsteps r hr

/-! ## Setup Phase Lemmas -/

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
  simp only [List.all_cons, List.all_nil, Bool.and_true, Instr.isNonJumping, Bool.and_self]

/-! ## Specific preservation lemmas -/

/-- pF preserves saved inputs. -/
theorem pF_preserves_prSavedInputs (n : ℕ) (pF pG : Program) (s : State)
    (c' : Config) (hsteps : Steps pF ⟨0, s⟩ c') (i : Fin n) :
    c'.state.read (prSavedInputsStart n pF pG + i) = s.read (prSavedInputsStart n pF pG + i) := by
  exact prPF_preserves_high_reg pF s c'.state c' hsteps rfl
    (prSavedInputsStart n pF pG + i) (pF_doesnt_touch_prSavedInputs n pF pG i)

/-- pF preserves savedY register. -/
theorem pF_preserves_prSavedYReg (n : ℕ) (pF pG : Program) (s : State)
    (c' : Config) (hsteps : Steps pF ⟨0, s⟩ c') :
    c'.state.read (prSavedYReg n pF pG) = s.read (prSavedYReg n pF pG) := by
  exact prPF_preserves_high_reg pF s c'.state c' hsteps rfl
    (prSavedYReg n pF pG) (pF_doesnt_touch_prSavedYReg n pF pG)

/-- pF preserves counter register. -/
theorem pF_preserves_prCounterReg (n : ℕ) (pF pG : Program) (s : State)
    (c' : Config) (hsteps : Steps pF ⟨0, s⟩ c') :
    c'.state.read (prCounterReg n pF pG) = s.read (prCounterReg n pF pG) := by
  exact prPF_preserves_high_reg pF s c'.state c' hsteps rfl
    (prCounterReg n pF pG) (pF_doesnt_touch_prCounterReg n pF pG)

/-- pF preserves accumulator register. -/
theorem pF_preserves_prAccumulatorReg (n : ℕ) (pF pG : Program) (s : State)
    (c' : Config) (hsteps : Steps pF ⟨0, s⟩ c') :
    c'.state.read (prAccumulatorReg n pF pG) = s.read (prAccumulatorReg n pF pG) := by
  exact prPF_preserves_high_reg pF s c'.state c' hsteps rfl
    (prAccumulatorReg n pF pG) (pF_doesnt_touch_prAccumulatorReg n pF pG)

/-- pF preserves zero register. -/
theorem pF_preserves_prZeroReg (n : ℕ) (pF pG : Program) (s : State)
    (c' : Config) (hsteps : Steps pF ⟨0, s⟩ c') :
    c'.state.read (prZeroReg n pF pG) = s.read (prZeroReg n pF pG) := by
  exact prPF_preserves_high_reg pF s c'.state c' hsteps rfl
    (prZeroReg n pF pG) (pF_doesnt_touch_prZeroReg n pF pG)

/-- pG preserves saved inputs. -/
theorem pG_preserves_prSavedInputs (n : ℕ) (pF pG : Program) (s : State)
    (c' : Config) (hsteps : Steps pG ⟨0, s⟩ c') (i : Fin n) :
    c'.state.read (prSavedInputsStart n pF pG + i) = s.read (prSavedInputsStart n pF pG + i) := by
  exact prPG_preserves_high_reg pG s c'.state c' hsteps rfl
    (prSavedInputsStart n pF pG + i) (pG_doesnt_touch_prSavedInputs n pF pG i)

/-- pG preserves savedY register. -/
theorem pG_preserves_prSavedYReg (n : ℕ) (pF pG : Program) (s : State)
    (c' : Config) (hsteps : Steps pG ⟨0, s⟩ c') :
    c'.state.read (prSavedYReg n pF pG) = s.read (prSavedYReg n pF pG) := by
  exact prPG_preserves_high_reg pG s c'.state c' hsteps rfl
    (prSavedYReg n pF pG) (pG_doesnt_touch_prSavedYReg n pF pG)

/-- pG preserves counter register. -/
theorem pG_preserves_prCounterReg (n : ℕ) (pF pG : Program) (s : State)
    (c' : Config) (hsteps : Steps pG ⟨0, s⟩ c') :
    c'.state.read (prCounterReg n pF pG) = s.read (prCounterReg n pF pG) := by
  exact prPG_preserves_high_reg pG s c'.state c' hsteps rfl
    (prCounterReg n pF pG) (pG_doesnt_touch_prCounterReg n pF pG)

/-- pG preserves accumulator register. -/
theorem pG_preserves_prAccumulatorReg (n : ℕ) (pF pG : Program) (s : State)
    (c' : Config) (hsteps : Steps pG ⟨0, s⟩ c') :
    c'.state.read (prAccumulatorReg n pF pG) = s.read (prAccumulatorReg n pF pG) := by
  exact prPG_preserves_high_reg pG s c'.state c' hsteps rfl
    (prAccumulatorReg n pF pG) (pG_doesnt_touch_prAccumulatorReg n pF pG)

/-- pG preserves zero register. -/
theorem pG_preserves_prZeroReg (n : ℕ) (pF pG : Program) (s : State)
    (c' : Config) (hsteps : Steps pG ⟨0, s⟩ c') :
    c'.state.read (prZeroReg n pF pG) = s.read (prZeroReg n pF pG) := by
  exact prPG_preserves_high_reg pG s c'.state c' hsteps rfl
    (prZeroReg n pF pG) (pG_doesnt_touch_prZeroReg n pF pG)

/-! ## Setup Phase Invariants -/

/-- After setup phase, saved inputs contain original inputs. -/
theorem prSetupPhase_saves_inputs (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (hs : s = State.fromInputs (List.ofFn (Fin.snoc inputs y)))
    (c' : Config) (hsteps : Steps (prSetupPhase n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (prSetupPhase n pF pG)) (i : Fin n) :
    c'.state.read (prSavedInputsStart n pF pG + i) = inputs i := by
  have hsl := prSetupPhase_isStraightLine n pF pG
  -- The T instruction at position i writes to prSavedInputsStart + i
  have hk : ↑i < (prSetupPhase n pF pG).length := by
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length]; omega
  have hwrite : (prSetupPhase n pF pG)[↑i] = Instr.T i (prSavedInputsStart n pF pG + i) := by
    simp only [prSetupPhase, Program.copyRegisterRange, Nat.zero_add]
    grind
  -- No instruction after position i writes to prSavedInputsStart + i
  have hnowrite_after : ∀ j (hj : j < (prSetupPhase n pF pG).length), ↑i < j →
      ((prSetupPhase n pF pG)[j]).writesTo ≠ some (prSavedInputsStart n pF pG + i) := by
    intro j hj hij
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length] at hj
    simp only [prSetupPhase, List.getElem_append, copyRegisterRange_length]
    by_cases hj_copy : j < n + 1
    · -- In copyRegisterRange: writes to prSavedInputsStart + j, which ≠ prSavedInputsStart + i
      simp only [hj_copy, dite_true, Program.copyRegisterRange, List.getElem_map, List.getElem_range,
        Instr.writesTo, ne_eq, Option.some.injEq]; omega
    · -- In [Z counter, Z zero]
      simp only [hj_copy, dite_false]
      have hj_small : j - (n + 1) = 0 ∨ j - (n + 1) = 1 := by omega
      rcases hj_small with h0 | h1
      · simp only [h0, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
        have := prCounterReg_gt_base n pF pG
        have := prSavedInputsStart_gt_base n pF pG
        simp only [prCounterReg, prSavedInputsStart]; omega
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
        have := prZeroReg_gt_base n pF pG
        have := prSavedInputsStart_gt_base n pF pG
        simp only [prZeroReg, prSavedInputsStart]; omega
  -- Use straightLine_transfer_result
  obtain ⟨s_before, ⟨c_i, hsteps_i, _, hs_before_eq⟩, htransfer⟩ := straightLine_transfer_result hsl s
    (↑i) (↑i) (prSavedInputsStart n pF pG + i) hk hwrite hnowrite_after
  -- No instruction before position i writes to i (source register)
  have hnowrite_before : ∀ instr, instr ∈ (prSetupPhase n pF pG) → instr.writesTo ≠ some (↑i) := by
    intro instr hmem
    simp only [prSetupPhase, List.mem_append, List.mem_cons, List.mem_nil_iff] at hmem
    rcases hmem with hcopy | hcounter | hzero | hfalse
    · simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
      obtain ⟨k, _, hk_eq⟩ := hcopy
      simp only [← hk_eq, Instr.writesTo, ne_eq, Option.some.injEq]
      have := prSavedInputsStart_ge_n n pF pG; omega
    · rw [hcounter]
      simp only [Instr.writesTo, ne_eq, Option.some.injEq]
      have := prCounterReg_gt_n_plus_1 n pF pG; omega
    · rw [hzero]
      simp only [Instr.writesTo, ne_eq, Option.some.injEq]
      have := prZeroReg_gt_n_plus_1 n pF pG; omega
    · exact hfalse.elim
  have hs_before_val : s_before.read (↑i) = s.read (↑i) := by
    rw [← hs_before_eq]
    exact Steps.straightLine_preserves hsl hsteps_i hnowrite_before
  -- s.read i = inputs i
  have hinput_val : s.read ↑i = inputs i := by
    simp only [hs, State.fromInputs, State.read, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, Fin.snoc]
    have hi_lt : (i : ℕ) < n := i.isLt
    have hi_lt' : (i : ℕ) < n + 1 := Nat.lt_succ_of_lt hi_lt
    simp only [hi_lt', ↓reduceDIte, hi_lt, Option.getD_some]
    simp only [cast_eq, Fin.castLT_mk, Fin.eta]
  -- Combine via halts_unique
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
  -- prSavedYReg = prSavedInputsStart + n
  have hSavedY_eq : prSavedYReg n pF pG = prSavedInputsStart n pF pG + n := by
    simp only [prSavedYReg, prSavedInputsStart]; omega
  rw [hSavedY_eq]
  -- The T instruction at position n writes to prSavedInputsStart + n
  have hk : n < (prSetupPhase n pF pG).length := by
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length]; omega
  have hwrite : (prSetupPhase n pF pG)[n] = Instr.T n (prSavedInputsStart n pF pG + n) := by
    simp only [prSetupPhase, Program.copyRegisterRange, Nat.zero_add]
    grind
  -- No instruction after position n writes to prSavedInputsStart + n
  have hnowrite_after : ∀ j (hj : j < (prSetupPhase n pF pG).length), n < j →
      ((prSetupPhase n pF pG)[j]).writesTo ≠ some (prSavedInputsStart n pF pG + n) := by
    intro j hj hjn
    simp only [prSetupPhase, List.length_append, copyRegisterRange_length, List.length] at hj
    simp only [prSetupPhase, List.getElem_append, copyRegisterRange_length]
    by_cases hj_copy : j < n + 1
    · -- In copyRegisterRange: writes to prSavedInputsStart + j, which ≠ prSavedInputsStart + n
      simp only [hj_copy, dite_true, Program.copyRegisterRange, List.getElem_map, List.getElem_range,
        Instr.writesTo, ne_eq, Option.some.injEq]; omega
    · -- In [Z counter, Z zero]
      simp only [hj_copy, dite_false]
      have hj_small : j - (n + 1) = 0 ∨ j - (n + 1) = 1 := by omega
      rcases hj_small with h0 | h1
      · simp only [h0, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
        simp only [prSavedInputsStart, prCounterReg]; omega
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
        simp only [prSavedInputsStart, prZeroReg]; omega
  -- Use straightLine_transfer_result
  obtain ⟨s_before, ⟨c_n, hsteps_n, _, hs_before_eq⟩, htransfer⟩ := straightLine_transfer_result hsl s
    n n (prSavedInputsStart n pF pG + n) hk hwrite hnowrite_after
  -- No instruction before position n writes to n (source register)
  have hnowrite_before : ∀ instr, instr ∈ (prSetupPhase n pF pG) → instr.writesTo ≠ some n := by
    intro instr hmem
    simp only [prSetupPhase, List.mem_append, List.mem_cons, List.mem_nil_iff] at hmem
    rcases hmem with hcopy | hcounter | hzero | hfalse
    · simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hcopy
      obtain ⟨k, _, hk_eq⟩ := hcopy
      simp only [← hk_eq, Instr.writesTo, ne_eq, Option.some.injEq]
      have := prSavedInputsStart_gt_n_plus_1 n pF pG; omega
    · rw [hcounter]
      simp only [Instr.writesTo, ne_eq, Option.some.injEq]
      have := prCounterReg_gt_n_plus_1 n pF pG; omega
    · rw [hzero]
      simp only [Instr.writesTo, ne_eq, Option.some.injEq]
      have := prZeroReg_gt_n_plus_1 n pF pG; omega
    · exact hfalse.elim
  have hs_before_val : s_before.read n = s.read n := by
    rw [← hs_before_eq]
    exact Steps.straightLine_preserves hsl hsteps_n hnowrite_before
  -- s.read n = y
  have hy_val : s.read n = y := by
    simp only [hs, State.fromInputs, State.read, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, Fin.snoc]
    have hn_lt : n < n + 1 := Nat.lt_succ_self n
    simp only [hn_lt, ↓reduceDIte, show ¬(n < n) by omega, Option.getD_some, cast_eq]
  -- Combine via halts_unique
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  have heq : c'.state = straightLineFinalState hsl s := by
    rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val, hy_val]

/-- After setup phase, counter is 0. -/
theorem prSetupPhase_counter_zero (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (_hs : s = State.fromInputs (List.ofFn (Fin.snoc inputs y)))
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
    have hj' : j = n + 2 := by omega
    subst hj'
    simp only [prSetupPhase, List.getElem_append, copyRegisterRange_length]
    simp only [show ¬(n + 2 < n + 1) by omega, dite_false, show n + 2 - (n + 1) = 1 by omega]
    simp [Instr.writesTo, prZeroReg, prCounterReg]
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  exact straightLine_zeros_register hsl s (prCounterReg n pF pG) (n + 1) hk hwrite hnowrite

/-- After setup phase, zero register is 0. -/
theorem prSetupPhase_zero_zero (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (_hs : s = State.fromInputs (List.ofFn (Fin.snoc inputs y)))
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

end Urm
