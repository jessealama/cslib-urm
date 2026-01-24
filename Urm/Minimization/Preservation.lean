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

section
variable (n : ℕ) (pF : Program)

/-! ## Helper Lemmas -/

/-- No instruction in loop_prologue writes to registers above minimization_base. -/
private theorem loop_prologue_no_write_high (r : ℕ) (hr : minimization_base n pF < r) :
    ∀ instr, instr ∈ loop_prologue n pF → instr.writes_to ≠ some r := by
  intro instr hinstr
  simp only [loop_prologue, List.mem_append, List.mem_singleton] at hinstr
  rcases hinstr with (hclear | hcopy) | heq
  · simp only [Program.clear_registers, List.mem_map, List.mem_range] at hclear
    obtain ⟨i, hi, rfl⟩ := hclear
    writes_to_omega
  · obtain ⟨j, hj, hwrites⟩ := copy_register_range_writes_to _ _ _ instr hcopy
    rw [hwrites]; simp only [ne_eq, Option.some.injEq, minimization_base] at hr ⊢; omega
  · simp only [heq, Instr.writes_to, ne_eq, Option.some.injEq, minimization_base] at hr ⊢; omega

/-! ## Setup Phase Results -/

/-- Setup phase is a straight-line program. -/
theorem setup_phase_is_straight_line :
    (setup_phase n pF).is_straight_line = true := by
  simp only [setup_phase]
  grind [Instr.Z_is_non_jumping, Instr.S_is_non_jumping, Instr.T_is_non_jumping]

/-- After setup phase, saved inputs contain original inputs. -/
theorem setup_phase_saves_inputs (inputs : Fin n → ℕ)
    (s : State) (hs : s = State.of_inputs (List.ofFn inputs))
    (c' : Config) (hsteps : Steps (setup_phase n pF) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (setup_phase n pF)) (i : Fin n) :
    c'.state.read (savedInputsStart n pF + i) = inputs i := by
  have hsl := setup_phase_is_straight_line n pF
  have hk : ↑i < (setup_phase n pF).length := by
    simp only [setup_phase, List.length_append, copy_register_range_length, List.length]; omega
  have hwrite : (setup_phase n pF)[↑i] = Instr.T i (savedInputsStart n pF + i) := by
    simp only [setup_phase, Program.copy_register_range, Nat.zero_add]; grind
  have hnowrite_after : ∀ j (hj : j < (setup_phase n pF).length), ↑i < j →
      ((setup_phase n pF)[j]).writes_to ≠ some (savedInputsStart n pF + i) := by
    intro j hj hij
    simp only [setup_phase, List.length_append, copy_register_range_length, List.length] at hj
    simp only [setup_phase, List.getElem_append, copy_register_range_length]
    by_cases hj_copy : j < n
    · simp only [hj_copy, dite_true, Program.copy_register_range, List.getElem_map, List.getElem_range,
        Nat.zero_add, Instr.writes_to, ne_eq, Option.some.injEq]; omega
    · simp only [hj_copy, dite_false]
      cases Nat.eq_zero_or_pos (j - n) with
      | inl h0 => simp only [h0, List.getElem_cons_zero, Instr.writes_to, ne_eq, Option.some.injEq,
          savedInputsStart, counter_reg, minimization_base]; omega
      | inr hpos =>
        have h1 : j - n = 1 := by omega
        simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writes_to, ne_eq,
          Option.some.injEq, savedInputsStart, zero_reg, minimization_base]; omega
  have hnowrite_src : ∀ instr, instr ∈ setup_phase n pF → instr.writes_to ≠ some ↑i := by
    intro instr hinstr
    simp only [setup_phase, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hinstr
    cases hinstr with
    | inl hcopy =>
      obtain ⟨j, _, hwrites⟩ := copy_register_range_writes_to _ _ _ instr hcopy
      rw [hwrites]; simp only [ne_eq, Option.some.injEq, savedInputsStart, minimization_base]; omega
    | inr hz =>
      cases hz with
      | inl hcounter =>
        rw [hcounter]; simp only [Instr.writes_to, ne_eq, Option.some.injEq]
        have : counter_reg n pF > i := by simp [counter_reg, minimization_base]; omega
        omega
      | inr hzero =>
        rw [hzero]; simp only [Instr.writes_to, ne_eq, Option.some.injEq]
        have : zero_reg n pF > i := by simp [zero_reg, minimization_base]; omega
        omega
  have hfinal := straight_line_transfer_final hsl s c' hsteps hhalted ↑i ↑i
    (savedInputsStart n pF + i) hk hwrite hnowrite_after hnowrite_src
  simp only [hs, State.of_inputs, State.read, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, i.2, ↓reduceDIte, Option.getD_some] at hfinal
  exact hfinal

/-- After setup phase, counter is 0. -/
theorem setup_phase_counter_zero
    (s : State)
    (c' : Config) (hsteps : Steps (setup_phase n pF) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (setup_phase n pF)) :
    c'.state.read (counter_reg n pF) = 0 := by
  have hsl := setup_phase_is_straight_line n pF
  have hk : n < (setup_phase n pF).length := by
    simp only [setup_phase, List.length_append, copy_register_range_length, List.length]; omega
  have hwrite : (setup_phase n pF)[n] = Instr.Z (counter_reg n pF) := by
    simp only [setup_phase, List.getElem_append, copy_register_range_length]; simp
  have hnowrite : ∀ j (hj : j < (setup_phase n pF).length), n < j → ((setup_phase n pF)[j]'hj).writes_to ≠ some (counter_reg n pF) := by
    intro j hj hjn
    simp only [setup_phase, List.length_append, copy_register_range_length, List.length] at hj
    obtain rfl : j = n + 1 := by omega
    simp only [setup_phase, List.getElem_append, copy_register_range_length,
      show ¬(n + 1 < n) by omega, dite_false, show n + 1 - n = 1 by omega]
    simp [Instr.writes_to, zero_reg, counter_reg, minimization_base]
  exact straight_line_zero_final hsl s c' hsteps hhalted n (counter_reg n pF) hk hwrite hnowrite

/-- After setup phase, zero register is 0. -/
theorem setup_phase_zero_reg_zero
    (s : State)
    (c' : Config) (hsteps : Steps (setup_phase n pF) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (setup_phase n pF)) :
    c'.state.read (zero_reg n pF) = 0 := by
  have hsl := setup_phase_is_straight_line n pF
  have hk : n + 1 < (setup_phase n pF).length := by
    simp only [setup_phase, List.length_append, copy_register_range_length, List.length]; omega
  have hwrite : (setup_phase n pF)[n + 1] = Instr.Z (zero_reg n pF) := by
    simp only [setup_phase, List.getElem_append, copy_register_range_length]; simp
  have hnowrite : ∀ j (hj : j < (setup_phase n pF).length), n + 1 < j → ((setup_phase n pF)[j]'hj).writes_to ≠ some (zero_reg n pF) := by
    intro j hj hjn
    simp only [setup_phase, List.length_append, copy_register_range_length, List.length] at hj; omega
  exact straight_line_zero_final hsl s c' hsteps hhalted (n + 1) (zero_reg n pF) hk hwrite hnowrite

/-! ## Loop Prologue Results -/

/-- Loop prologue is a straight-line program. -/
theorem loop_prologue_is_straight_line :
    (loop_prologue n pF).is_straight_line = true := by
  simp only [loop_prologue]
  grind [Instr.Z_is_non_jumping, Instr.S_is_non_jumping, Instr.T_is_non_jumping]

/-- After loop prologue, R[0..n-1] contain saved inputs. -/
theorem loop_prologue_restores_inputs
    (s : State) (c' : Config)
    (hsteps : Steps (loop_prologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (loop_prologue n pF)) (i : Fin n) :
    c'.state.read i = s.read (savedInputsStart n pF + i) := by
  have hsl := loop_prologue_is_straight_line n pF
  have hi : ↑i < n := i.2
  have hk : (minimization_base n pF + 1) + ↑i < (loop_prologue n pF).length := by
    simp only [loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
      List.length]; omega
  have hwrite : (loop_prologue n pF)[(minimization_base n pF + 1) + ↑i] = Instr.T (savedInputsStart n pF + i) i := by
    simp only [loop_prologue]
    rw [List.getElem_append]
    simp only [List.length_append, clear_registers_length, copy_register_range_length]
    have hk_lt_clear_copy : (minimization_base n pF + 1) + ↑i < (minimization_base n pF + 1) + n := by omega
    simp only [hk_lt_clear_copy, dite_true]
    rw [List.getElem_append]
    simp only [clear_registers_length]
    have hk_not_in_clear : ¬(minimization_base n pF + 1) + ↑i < minimization_base n pF + 1 := by omega
    simp only [hk_not_in_clear, dite_false, Program.copy_register_range, List.getElem_map, List.getElem_range, Nat.zero_add]
    congr 1 <;> omega
  have hnowrite_after : ∀ j (hj : j < (loop_prologue n pF).length), (minimization_base n pF + 1) + ↑i < j →
      ((loop_prologue n pF)[j]).writes_to ≠ some ↑i := by
    intro j hj hjk
    simp only [loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
      List.length] at hj
    simp only [loop_prologue, List.getElem_append, List.length_append, clear_registers_length,
      copy_register_range_length]
    by_cases hj_copy : j < (minimization_base n pF + 1) + n
    · simp only [hj_copy, dite_true]
      by_cases hj_clear : j < minimization_base n pF + 1
      · omega
      · simp only [hj_clear, dite_false, Program.copy_register_range, List.getElem_map, List.getElem_range,
          Instr.writes_to, ne_eq, Option.some.injEq, Nat.zero_add]; omega
    · simp only [hj_copy, dite_false]
      have hj_suffix : j - ((minimization_base n pF + 1) + n) = 0 := by omega
      simp only [hj_suffix, List.getElem_cons_zero, Instr.writes_to, ne_eq, Option.some.injEq]; omega
  have hnowrite_src := loop_prologue_no_write_high n pF (savedInputsStart n pF + ↑i)
    (by have h := savedInputsStart_gt_base n pF; omega)
  exact straight_line_transfer_final hsl s c' hsteps hhalted ((minimization_base n pF + 1) + ↑i)
    (savedInputsStart n pF + i) ↑i hk hwrite hnowrite_after hnowrite_src

/-- After loop prologue, R[n] contains counter value. -/
theorem loop_prologue_sets_counter_input
    (s : State) (c' : Config)
    (hsteps : Steps (loop_prologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (loop_prologue n pF)) :
    c'.state.read n = s.read (counter_reg n pF) := by
  have hsl := loop_prologue_is_straight_line n pF
  have hk : (minimization_base n pF + 1) + n < (loop_prologue n pF).length := by
    simp only [loop_prologue, List.length_append, clear_registers_length, copy_register_range_length, List.length]; omega
  have hwrite : (loop_prologue n pF)[(minimization_base n pF + 1) + n] = Instr.T (counter_reg n pF) n := by
    simp only [loop_prologue]
    rw [List.getElem_append]
    have h1 : ¬(minimization_base n pF + 1) + n < (clear_registers (minimization_base n pF) ++ copy_register_range (savedInputsStart n pF) 0 n).length := by
      len_append_omega
    simp only [h1, dite_false]
    have h2 : (minimization_base n pF + 1) + n - (clear_registers (minimization_base n pF) ++ copy_register_range (savedInputsStart n pF) 0 n).length = 0 := by
      len_append_omega
    simp only [h2, List.getElem_cons_zero]
  have hnowrite : ∀ j (hj : j < (loop_prologue n pF).length), (minimization_base n pF + 1) + n < j → ((loop_prologue n pF)[j]'hj).writes_to ≠ some n := by
    intro j hj hjk
    simp only [loop_prologue, List.length_append, clear_registers_length, copy_register_range_length, List.length] at hj; omega
  have hnowrite_src := loop_prologue_no_write_high n pF _ (counter_reg_gt_base n pF)
  exact straight_line_transfer_final hsl s c' hsteps hhalted ((minimization_base n pF + 1) + n)
    (counter_reg n pF) n hk hwrite hnowrite hnowrite_src

/-- Loop prologue preserves any register > minimization_base.
    loop_prologue only writes to registers 0..base (clear_registers) and 0..n (copy_register_range, T). -/
theorem loop_prologue_read_high_register_eq
    (s : State) (c' : Config)
    (hsteps : Steps (loop_prologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (loop_prologue n pF))
    (r : ℕ) (hr : r > minimization_base n pF) :
    c'.state.read r = s.read r :=
  straight_line_preserves_final (loop_prologue_is_straight_line n pF) s c' hsteps hhalted r
    (loop_prologue_no_write_high n pF r hr)

/-- Loop prologue clears registers in range [n+1, minimization_base n pF]. -/
theorem loop_prologue_clears_high_registers
    (s : State) (c' : Config)
    (hsteps : Steps (loop_prologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (loop_prologue n pF))
    (r : ℕ) (hr_ge : n + 1 ≤ r) (hr_le : r ≤ minimization_base n pF) :
    c'.state.read r = 0 := by
  have hsl := loop_prologue_is_straight_line n pF
  have hr_lt_prologue : r < (loop_prologue n pF).length := by
    simp only [loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
      List.length]; omega
  have hwrite : (loop_prologue n pF)[r]'hr_lt_prologue = Instr.Z r := by
    simp only [loop_prologue, List.getElem_append, List.length_append, clear_registers_length,
      copy_register_range_length]
    split_ifs with h1 h2
    · simp only [Program.clear_registers, List.getElem_map, List.getElem_range]
    · omega
    · omega
  have hnowrite : ∀ j (hj : j < (loop_prologue n pF).length), r < j →
      ((loop_prologue n pF)[j]'hj).writes_to ≠ some r := by
    intro j hj hrj
    simp only [loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
      List.length] at hj
    simp only [loop_prologue, List.getElem_append, List.length_append, clear_registers_length,
      copy_register_range_length]
    split_ifs with h1 h2
    · simp only [Program.clear_registers, List.getElem_map, List.getElem_range,
                 Instr.writes_to, ne_eq, Option.some.injEq]; omega
    · simp only [Program.copy_register_range, List.getElem_map, List.getElem_range,
                 Instr.writes_to, ne_eq, Option.some.injEq, Nat.zero_add]; omega
    · have hj_suffix : j - ((minimization_base n pF + 1) + n) = 0 := by omega
      simp only [hj_suffix, List.getElem_cons_zero, Instr.writes_to, ne_eq, Option.some.injEq]; omega
  exact straight_line_zero_final hsl s c' hsteps hhalted r r hr_lt_prologue hwrite hnowrite

end

end Urm
