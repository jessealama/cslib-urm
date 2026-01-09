/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.StandardForm



/-! # Preservation Lemmas for Minimization

This file proves register preservation during minimization program execution.

## Main results

- Setup phase initializes registers correctly
- Loop iterations preserve saved inputs
- Zero register remains zero
-/

namespace Urm

open Program

/-! ## Setup Phase Results -/

/-- Setup phase is a straight-line program. -/
theorem setupPhase_isStraightLine (n : ℕ) (pF : Program) :
    (setupPhase n pF).isStraightLine = true := by
  simp only [setupPhase, Program.isStraightLine, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  refine ⟨copyRegisterRange_isStraightLine 0 (savedInputsStart n pF) n, ?_, rfl⟩
  simp [Instr.isNonJumping]

/-- After setup phase, saved inputs contain original inputs. -/
theorem setupPhase_saves_inputs (n : ℕ) (pF : Program) (inputs : Fin n → ℕ)
    (s : State) (hs : s = State.fromInputs (List.ofFn inputs))
    (c' : Config) (hsteps : Steps (setupPhase n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (setupPhase n pF)) (i : Fin n) :
    c'.state.read (savedInputsStart n pF + i) = inputs i := by
  have hsl := setupPhase_isStraightLine n pF
  -- The T instruction at position i writes to savedInputsStart + i
  have hk : ↑i < (setupPhase n pF).length := by
    simp only [setupPhase, List.length_append, copyRegisterRange_length, List.length]; omega
  have hwrite : (setupPhase n pF)[↑i] = Instr.T i (savedInputsStart n pF + i) := by
    simp only [setupPhase, Program.copyRegisterRange, Nat.zero_add]
    grind
  -- No instruction after position i writes to savedInputsStart + i
  have hnowrite_after : ∀ j (hj : j < (setupPhase n pF).length), ↑i < j →
      ((setupPhase n pF)[j]).writesTo ≠ some (savedInputsStart n pF + i) := by
    intro j hj hij
    simp only [setupPhase, List.length_append, copyRegisterRange_length, List.length] at hj
    simp only [setupPhase, List.getElem_append, copyRegisterRange_length]
    by_cases hj_copy : j < n
    · -- In copyRegisterRange: writes to savedInputsStart + j, which ≠ savedInputsStart + i since j > i
      simp only [hj_copy, dite_true, Program.copyRegisterRange, List.getElem_map, List.getElem_range,
        Nat.zero_add, Instr.writesTo, ne_eq, Option.some.injEq]
      omega
    · -- In [Z counter, Z zero]: neither writes to savedInputsStart + i
      simp only [hj_copy, dite_false]
      let hj_suffix : j - n < 2 := by omega
      cases Nat.eq_zero_or_pos (j - n) with
      | inl h0 => simp only [h0, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq,
          savedInputsStart, counterReg, minimizationBase]; omega
      | inr hpos =>
        let h1 : j - n = 1 := by omega
        simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo, ne_eq,
          Option.some.injEq, savedInputsStart, zeroReg, minimizationBase]; omega
  -- Use straightLine_transfer_result
  obtain ⟨s_before, ⟨c_i, hsteps_i, _, hs_before⟩, htransfer⟩ :=
    straightLine_transfer_result hsl s ↑i ↑i (savedInputsStart n pF + i) hk hwrite hnowrite_after
  -- s_before.read i = s.read i (nothing before position i writes to register i)
  have hs_before_val : s_before.read ↑i = s.read ↑i := by
    rw [← hs_before]
    let hnowrite_before : ∀ instr, instr ∈ setupPhase n pF → instr.writesTo ≠ some ↑i := by
      intro instr hinstr
      simp only [setupPhase, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hinstr
      cases hinstr with
      | inl hcopy =>
        -- copyRegisterRange writes to savedInputsStart + j ≥ savedInputsStart > n > i
        obtain ⟨j, _, hwrites⟩ := copyRegisterRange_writesTo _ _ _ instr hcopy
        rw [hwrites]; simp only [ne_eq, Option.some.injEq, savedInputsStart, minimizationBase]; omega
      | inr hz =>
        cases hz with
        | inl hcounter =>
          rw [hcounter]; simp only [Instr.writesTo, ne_eq, Option.some.injEq]
          let _ : counterReg n pF > i := by simp [counterReg, minimizationBase]; omega
          omega
        | inr hzero =>
          rw [hzero]; simp only [Instr.writesTo, ne_eq, Option.some.injEq]
          let _ : zeroReg n pF > i := by simp [zeroReg, minimizationBase]; omega
          omega
    exact Steps.straightLine_preserves hsl hsteps_i hnowrite_before
  -- s.read i = inputs i
  have hinput_val : s.read ↑i = inputs i := by
    simp only [hs, State.fromInputs, State.read, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, i.2, ↓reduceDIte, Option.getD_some]
  -- Combine via halts_unique
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  have heq : c'.state = straightLineFinalState hsl s := by
    rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val, hinput_val]

/-- After setup phase, counter is 0. -/
theorem setupPhase_counter_zero (n : ℕ) (pF : Program) (inputs : Fin n → ℕ)
    (s : State) (_hs : s = State.fromInputs (List.ofFn inputs))
    (c' : Config) (hsteps : Steps (setupPhase n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (setupPhase n pF)) :
    c'.state.read (counterReg n pF) = 0 := by
  have hsl := setupPhase_isStraightLine n pF
  have hk : n < (setupPhase n pF).length := by
    simp only [setupPhase, List.length_append, copyRegisterRange_length, List.length]
    omega
  have hwrite : (setupPhase n pF)[n] = Instr.Z (counterReg n pF) := by
    simp only [setupPhase, List.getElem_append, copyRegisterRange_length]
    simp
  have hnowrite : ∀ j (hj : j < (setupPhase n pF).length), n < j → ((setupPhase n pF)[j]'hj).writesTo ≠ some (counterReg n pF) := by
    intro j hj hjn
    simp only [setupPhase, List.length_append, copyRegisterRange_length, List.length] at hj
    obtain rfl : j = n + 1 := by omega
    -- setupPhase[n+1] = (copyRegisterRange ++ [Z counter, Z zero])[n+1]
    -- Since n+1 ≥ n (length of copyRegisterRange), this is [Z counter, Z zero][1] = Z zero
    simp only [setupPhase, List.getElem_append, copyRegisterRange_length]
    simp only [show ¬(n + 1 < n) by omega, dite_false, show n + 1 - n = 1 by omega]
    simp [Instr.writesTo, zeroReg, counterReg, minimizationBase]
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  exact straightLine_zeros_register hsl s (counterReg n pF) n hk hwrite hnowrite

/-- After setup phase, zero register is 0. -/
theorem setupPhase_zeroReg_zero (n : ℕ) (pF : Program) (inputs : Fin n → ℕ)
    (s : State) (_hs : s = State.fromInputs (List.ofFn inputs))
    (c' : Config) (hsteps : Steps (setupPhase n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (setupPhase n pF)) :
    c'.state.read (zeroReg n pF) = 0 := by
  have hsl := setupPhase_isStraightLine n pF
  have hk : n + 1 < (setupPhase n pF).length := by
    simp only [setupPhase, List.length_append, copyRegisterRange_length, List.length]
    omega
  have hwrite : (setupPhase n pF)[n + 1] = Instr.Z (zeroReg n pF) := by
    simp only [setupPhase, List.getElem_append, copyRegisterRange_length]
    simp
  have hnowrite : ∀ j (hj : j < (setupPhase n pF).length), n + 1 < j → ((setupPhase n pF)[j]'hj).writesTo ≠ some (zeroReg n pF) := by
    intro j hj hjn
    simp only [setupPhase, List.length_append, copyRegisterRange_length, List.length] at hj
    omega
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  exact straightLine_zeros_register hsl s (zeroReg n pF) (n + 1) hk hwrite hnowrite

/-! ## Loop Prologue Results -/

/-- Loop prologue is a straight-line program. -/
theorem loopPrologue_isStraightLine (n : ℕ) (pF : Program) :
    (loopPrologue n pF).isStraightLine = true := by
  simp only [loopPrologue, Program.isStraightLine, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  exact ⟨⟨clearRegisters_isStraightLine (minimizationBase n pF),
           copyRegisterRange_isStraightLine (savedInputsStart n pF) 0 n⟩, rfl⟩

/-- After loop prologue, R[0..n-1] contain saved inputs. -/
theorem loopPrologue_restores_inputs (n : ℕ) (pF : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (loopPrologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (loopPrologue n pF)) (i : Fin n) :
    c'.state.read i = s.read (savedInputsStart n pF + i) := by
  have hsl := loopPrologue_isStraightLine n pF
  -- The T instruction at position (base+1) + i writes to register i
  have hi : ↑i < n := i.2
  let k := (minimizationBase n pF + 1) + ↑i
  have hk : k < (loopPrologue n pF).length := by
    simp only [loopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
      List.length]; omega
  have hwrite : (loopPrologue n pF)[k] = Instr.T (savedInputsStart n pF + i) i := by
    simp only [loopPrologue]
    -- First get past clearRegisters
    let hk_ge_clear : k ≥ (clearRegisters (minimizationBase n pF)).length := by
      simp [clearRegisters_length]; omega
    rw [List.getElem_append]
    simp only [List.length_append, clearRegisters_length, copyRegisterRange_length]
    let hk_lt_clear_copy : k < (minimizationBase n pF + 1) + n := by omega
    simp only [hk_lt_clear_copy, dite_true]
    -- Now get past clearRegisters part
    rw [List.getElem_append]
    simp only [clearRegisters_length]
    let hk_not_in_clear : ¬k < minimizationBase n pF + 1 := by omega
    simp only [hk_not_in_clear, dite_false]
    -- Now in copyRegisterRange
    let hidx : k - (minimizationBase n pF + 1) = ↑i := by omega
    simp only [hidx]
    simp only [Program.copyRegisterRange, List.getElem_map, List.getElem_range, Nat.zero_add]
  -- No instruction after position k writes to register i
  have hnowrite_after : ∀ j (hj : j < (loopPrologue n pF).length), k < j →
      ((loopPrologue n pF)[j]).writesTo ≠ some ↑i := by
    intro j hj hjk
    simp only [loopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
      List.length] at hj
    simp only [loopPrologue, List.getElem_append, List.length_append, clearRegisters_length,
      copyRegisterRange_length]
    by_cases hj_copy : j < (minimizationBase n pF + 1) + n
    · -- In clearRegisters ++ copyRegisterRange section
      simp only [hj_copy, dite_true]
      by_cases hj_clear : j < minimizationBase n pF + 1
      · -- In clearRegisters: but hjk says j > k ≥ base+1, contradiction
        omega
      · -- In copyRegisterRange: writes to 0 + j' = j' where j' > i
        simp only [hj_clear, dite_false]
        simp only [Program.copyRegisterRange, List.getElem_map, List.getElem_range,
          Instr.writesTo, ne_eq, Option.some.injEq, Nat.zero_add]
        omega
    · -- In [T counter n]: writes to n ≠ i
      simp only [hj_copy, dite_false]
      let hj_suffix : j - ((minimizationBase n pF + 1) + n) = 0 := by omega
      simp only [hj_suffix, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
      omega
  -- Use straightLine_transfer_result
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before⟩, htransfer⟩ :=
    straightLine_transfer_result hsl s k (savedInputsStart n pF + i) ↑i hk hwrite hnowrite_after
  -- s_before.read (savedInputsStart + i) = s.read (savedInputsStart + i)
  -- Nothing before position k writes to savedInputsStart + i
  have hs_before_val : s_before.read (savedInputsStart n pF + ↑i) = s.read (savedInputsStart n pF + ↑i) := by
    rw [← hs_before]
    let hnowrite_before : ∀ instr, instr ∈ loopPrologue n pF →
        instr.writesTo ≠ some (savedInputsStart n pF + ↑i) := by
      intro instr hinstr
      simp only [loopPrologue, List.mem_append, List.mem_singleton] at hinstr
      cases hinstr with
      | inl h =>
        cases h with
        | inl hclear =>
          -- clearRegisters writes to 0..base, savedInputsStart = base+1
          simp only [Program.clearRegisters, List.mem_map, List.mem_range] at hclear
          obtain ⟨j, hj, rfl⟩ := hclear
          simp only [Instr.writesTo, ne_eq, Option.some.injEq, savedInputsStart]; omega
        | inr hcopy =>
          -- copyRegisterRange writes to 0..n-1, savedInputsStart + i > n
          obtain ⟨j, hj, hwrites⟩ := copyRegisterRange_writesTo _ _ _ instr hcopy
          rw [hwrites]; simp only [ne_eq, Option.some.injEq, savedInputsStart, minimizationBase, Nat.zero_add]; omega
      | inr heq =>
        -- T counter n writes to n, savedInputsStart + i > n
        simp only [heq, Instr.writesTo, ne_eq, Option.some.injEq, savedInputsStart, minimizationBase]
        omega
    exact Steps.straightLine_preserves hsl hsteps_k hnowrite_before
  -- Combine via halts_unique
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  have heq : c'.state = straightLineFinalState hsl s := by
    rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val]

/-- After loop prologue, R[n] contains counter value. -/
theorem loopPrologue_sets_counter_input (n : ℕ) (pF : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (loopPrologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (loopPrologue n pF)) :
    c'.state.read n = s.read (counterReg n pF) := by
  have hsl := loopPrologue_isStraightLine n pF
  -- The T instruction is at position k = base+1+n (the last position)
  let k := (minimizationBase n pF + 1) + n
  have hk : k < (loopPrologue n pF).length := by
    simp only [loopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length, List.length]; omega
  have hwrite : (loopPrologue n pF)[k] = Instr.T (counterReg n pF) n := by
    simp only [loopPrologue]
    rw [List.getElem_append]
    let h1 : ¬k < (clearRegisters (minimizationBase n pF) ++ copyRegisterRange (savedInputsStart n pF) 0 n).length := by
      len_append_omega
    simp only [h1, dite_false]
    let h2 : k - (clearRegisters (minimizationBase n pF) ++ copyRegisterRange (savedInputsStart n pF) 0 n).length = 0 := by
      len_append_omega
    simp only [h2, List.getElem_cons_zero]
  -- k is the last instruction, so hnowrite is vacuously true
  have hnowrite : ∀ j (hj : j < (loopPrologue n pF).length), k < j → ((loopPrologue n pF)[j]'hj).writesTo ≠ some n := by
    intro j hj hjk
    simp only [loopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length, List.length] at hj
    omega
  -- Use straightLine_transfer_result
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before⟩, htransfer⟩ :=
    straightLine_transfer_result hsl s k (counterReg n pF) n hk hwrite hnowrite
  -- Show counterReg preserved through the steps to c_k
  -- No instruction in loopPrologue writes to counterReg
  have hcounter_at_k : s_before.read (counterReg n pF) = s.read (counterReg n pF) := by
    rw [← hs_before]
    let hnowrite_counter : ∀ instr, instr ∈ loopPrologue n pF → instr.writesTo ≠ some (counterReg n pF) := by
      intro instr hinstr
      simp only [loopPrologue, List.mem_append, List.mem_singleton] at hinstr
      cases hinstr with
      | inl h =>
        cases h with
        | inl hclear =>
          simp only [Program.clearRegisters, List.mem_map, List.mem_range] at hclear
          obtain ⟨i, _, rfl⟩ := hclear
          simp only [Instr.writesTo, ne_eq, Option.some.injEq, counterReg]; omega
        | inr hcopy =>
          obtain ⟨j, _, hwrites⟩ := copyRegisterRange_writesTo _ _ _ instr hcopy
          rw [hwrites]; simp only [ne_eq, Option.some.injEq, counterReg, minimizationBase]; omega
      | inr heq =>
        simp only [heq, Instr.writesTo, ne_eq, Option.some.injEq, counterReg, minimizationBase]; omega
    exact Steps.straightLine_preserves hsl hsteps_k hnowrite_counter
  -- Combine results
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  have heq := Steps.halts_unique hsteps hhalted hsteps' hhalted'
  simp only [straightLineFinalState] at htransfer
  rw [heq, htransfer, hcounter_at_k]

/-- Loop prologue preserves any register > minimizationBase.
    loopPrologue only writes to registers 0..base (clearRegisters) and 0..n (copyRegisterRange, T). -/
theorem loopPrologue_preserves_high_register (n : ℕ) (pF : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (loopPrologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (loopPrologue n pF))
    (r : ℕ) (hr : r > minimizationBase n pF) :
    c'.state.read r = s.read r := by
  have hsl := loopPrologue_isStraightLine n pF
  have hnowrite : ∀ instr, instr ∈ loopPrologue n pF → instr.writesTo ≠ some r := by
    intro instr hinstr
    simp only [loopPrologue, List.mem_append, List.mem_singleton] at hinstr
    cases hinstr with
    | inl h =>
      cases h with
      | inl hclear =>
        simp only [Program.clearRegisters, List.mem_map, List.mem_range] at hclear
        obtain ⟨i, hi, rfl⟩ := hclear
        writesTo_omega
      | inr hcopy =>
        obtain ⟨j, hj, hwrites⟩ := copyRegisterRange_writesTo _ _ _ instr hcopy
        rw [hwrites]; simp only [ne_eq, Option.some.injEq, minimizationBase] at hr ⊢; omega
    | inr heq =>
      simp only [heq, Instr.writesTo, ne_eq, Option.some.injEq, minimizationBase] at hr ⊢; omega
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  exact Steps.straightLine_preserves hsl hsteps' hnowrite

/-- Loop prologue clears registers in range [n+1, minimizationBase n pF].
    This is because clearRegisters zeros these registers and subsequent
    instructions (copyRegisterRange and T) only write to registers 0..n. -/
theorem loopPrologue_clears_high_registers (n : ℕ) (pF : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (loopPrologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (loopPrologue n pF))
    (r : ℕ) (hr_ge : n + 1 ≤ r) (hr_le : r ≤ minimizationBase n pF) :
    c'.state.read r = 0 := by
  have hsl := loopPrologue_isStraightLine n pF
  -- Instruction at index r in loopPrologue is Z r (from clearRegisters)
  have hr_lt_prologue : r < (loopPrologue n pF).length := by
    simp only [loopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
      List.length]; omega
  have hwrite : (loopPrologue n pF)[r]'hr_lt_prologue = Instr.Z r := by
    simp only [loopPrologue, List.getElem_append, List.length_append, clearRegisters_length,
      copyRegisterRange_length]
    split_ifs with h1 h2
    · simp only [Program.clearRegisters, List.getElem_map, List.getElem_range]
    · omega  -- h1 false means r ≥ base + 1 + n, but r ≤ base
    · omega  -- h2 false means r ≥ base + 1, but r ≤ base
  -- No later instruction writes to r
  have hnowrite : ∀ j (hj : j < (loopPrologue n pF).length), r < j →
      ((loopPrologue n pF)[j]'hj).writesTo ≠ some r := by
    intro j hj hrj
    simp only [loopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
      List.length] at hj
    simp only [loopPrologue, List.getElem_append, List.length_append, clearRegisters_length,
      copyRegisterRange_length]
    split_ifs with h1 h2
    · -- j in clearRegisters range, writes to j ≠ r since j > r
      simp only [Program.clearRegisters, List.getElem_map, List.getElem_range,
                 Instr.writesTo, ne_eq, Option.some.injEq]
      omega
    · -- j in copyRegisterRange, writes to some k < n < r
      simp only [Program.copyRegisterRange, List.getElem_map, List.getElem_range,
                 Instr.writesTo, ne_eq, Option.some.injEq, Nat.zero_add]
      omega
    · -- j in [T counterReg n], writes to n < n + 1 ≤ r
      let hj_suffix : j - ((minimizationBase n pF + 1) + n) = 0 := by omega
      simp only [hj_suffix, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
      omega
  have ⟨hsteps', hhalted', _⟩ := straightLineFinalState_spec hsl s
  rw [Steps.halts_unique hsteps hhalted hsteps' hhalted']
  exact straightLine_zeros_register hsl s r r hr_lt_prologue hwrite hnowrite

end Urm
