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

/-- Helper: no instruction in pr_setup_phase writes to registers below n+1.
    (copy_register_range writes to savedInputsStart+i, counter writes to pr_counter_reg,
    zero writes to pr_zero_reg - all are > n.) -/
private theorem pr_setup_phase_no_write_low (n : ℕ) (pF pG : Program) (r : ℕ) (hr : r < n + 1) :
    ∀ instr, instr ∈ pr_setup_phase n pF pG → instr.writes_to ≠ some r := by
  intro instr hmem
  simp only [pr_setup_phase, List.mem_append, List.mem_cons, List.mem_nil_iff] at hmem
  rcases hmem with hcopy | hcounter | hzero | hfalse
  · simp only [Program.copy_register_range, List.mem_map, List.mem_range] at hcopy
    obtain ⟨k, _, rfl⟩ := hcopy
    simp only [Instr.writes_to, ne_eq, Option.some.injEq]
    have := pr_saved_inputs_start_gt_n_plus_1 n pF pG; omega
  · rw [hcounter]; simp only [Instr.writes_to, ne_eq, Option.some.injEq]
    have := pr_counter_reg_gt_n_plus_1 n pF pG; omega
  · rw [hzero]; simp only [Instr.writes_to, ne_eq, Option.some.injEq]
    have := pr_zero_reg_gt_n_plus_1 n pF pG; omega
  · exact hfalse.elim

/-- Helper: no instruction in pr_loop_prologue writes to registers above primitive_recursion_base. -/
private theorem pr_loop_prologue_no_write_high (n : ℕ) (pF pG : Program) (r : ℕ)
    (hr : primitive_recursion_base n pF pG < r) :
    ∀ instr, instr ∈ pr_loop_prologue n pF pG → instr.writes_to ≠ some r := by
  intro instr hinstr
  simp only [pr_loop_prologue, List.mem_append, List.mem_cons, List.mem_nil_iff] at hinstr
  rcases hinstr with (hclear | hcopy) | hT1 | hT2 | hfalse
  · simp only [Program.clear_registers, List.mem_map, List.mem_range] at hclear
    obtain ⟨j, hj, rfl⟩ := hclear
    writes_to_omega
  · simp only [Program.copy_register_range, List.mem_map, List.mem_range] at hcopy
    obtain ⟨j, hj, rfl⟩ := hcopy
    simp only [Instr.writes_to, ne_eq, Option.some.injEq, Nat.zero_add]
    have := primitive_recursion_base_ge_n n pF pG; omega
  · rw [hT1]; simp only [Instr.writes_to, ne_eq, Option.some.injEq]
    have := primitive_recursion_base_ge_n n pF pG; omega
  · rw [hT2]; simp only [Instr.writes_to, ne_eq, Option.some.injEq]
    have := primitive_recursion_base_ge_n_succ n pF pG; omega
  · exact hfalse.elim

/-- Setup phase is a straight-line program. -/
theorem pr_setup_phase_is_straight_line (n : ℕ) (pF pG : Program) :
    (pr_setup_phase n pF pG).is_straight_line = true := by
  simp only [pr_setup_phase]
  grind [Instr.Z_is_non_jumping, Instr.S_is_non_jumping, Instr.T_is_non_jumping]

/-- Base case prologue is a straight-line program. -/
theorem pr_base_case_prologue_is_straight_line (n : ℕ) (pF pG : Program) :
    (pr_base_case_prologue n pF pG).is_straight_line = true := by
  simp only [pr_base_case_prologue]; grind

/-- Loop prologue is a straight-line program. -/
theorem pr_loop_prologue_is_straight_line (n : ℕ) (pF pG : Program) :
    (pr_loop_prologue n pF pG).is_straight_line = true := by
  simp only [pr_loop_prologue]
  grind [Instr.Z_is_non_jumping, Instr.S_is_non_jumping, Instr.T_is_non_jumping]

/-! ## Setup Phase Invariants -/

/-- After setup phase, saved inputs contain original inputs. -/
theorem pr_setup_phase_saves_inputs (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (hs : s = State.of_inputs (List.ofFn (Fin.snoc inputs y)))
    (c' : Config) (hsteps : Steps (pr_setup_phase n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_setup_phase n pF pG)) (i : Fin n) :
    c'.state.read (pr_saved_inputs_start n pF pG + i) = inputs i := by
  have hsl := pr_setup_phase_is_straight_line n pF pG
  have hk : ↑i < (pr_setup_phase n pF pG).length := by
    simp only [pr_setup_phase, List.length_append, copy_register_range_length, List.length]; omega
  have hwrite : (pr_setup_phase n pF pG)[↑i] = Instr.T i (pr_saved_inputs_start n pF pG + i) := by
    simp only [pr_setup_phase, Program.copy_register_range, Nat.zero_add]
    grind
  have hnowrite_after : ∀ j (hj : j < (pr_setup_phase n pF pG).length), ↑i < j →
      ((pr_setup_phase n pF pG)[j]).writes_to ≠ some (pr_saved_inputs_start n pF pG + i) := by
    intro j hj hij
    simp only [pr_setup_phase, List.length_append, copy_register_range_length, List.length] at hj
    simp only [pr_setup_phase, List.getElem_append, copy_register_range_length]
    split_ifs with hj_copy
    · simp only [Program.copy_register_range, List.getElem_map, List.getElem_range,
        Instr.writes_to, ne_eq, Option.some.injEq]; omega
    · have hj_small : j - (n + 1) = 0 ∨ j - (n + 1) = 1 := by omega
      rcases hj_small with h0 | h1
      · simp only [h0, List.getElem_cons_zero, Instr.writes_to, ne_eq, Option.some.injEq]; pr_register_omega
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writes_to, ne_eq,
          Option.some.injEq]; pr_register_omega
  obtain ⟨s_before, ⟨c_i, hsteps_i, _, hs_before_eq⟩, htransfer⟩ := straight_line_transfer_result hsl s
    (↑i) (↑i) (pr_saved_inputs_start n pF pG + i) hk hwrite hnowrite_after
  have hs_before_val : s_before.read (↑i) = s.read (↑i) := by
    rw [← hs_before_eq]
    exact Steps.straight_line_preserves hsl hsteps_i (pr_setup_phase_no_write_low n pF pG i (Nat.lt_succ_of_lt i.isLt))
  let hinput_val : s.read ↑i = inputs i := by
    simp only [hs, State.of_inputs, State.read, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, Fin.snoc]
    let hi_lt : (i : ℕ) < n := i.isLt
    let hi_lt' : (i : ℕ) < n + 1 := Nat.lt_succ_of_lt hi_lt
    simp only [hi_lt', ↓reduceDIte, hi_lt, Option.getD_some]
    simp only [cast_eq, Fin.castLT_mk, Fin.eta]
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  have heq : c'.state = straight_lineFinalState hsl s := by
    rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val, hinput_val]

/-- After setup phase, savedY contains y. -/
theorem pr_setup_phase_saves_y (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (hs : s = State.of_inputs (List.ofFn (Fin.snoc inputs y)))
    (c' : Config) (hsteps : Steps (pr_setup_phase n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_setup_phase n pF pG)) :
    c'.state.read (pr_saved_y_reg n pF pG) = y := by
  have hsl := pr_setup_phase_is_straight_line n pF pG
  have hSavedY_eq : pr_saved_y_reg n pF pG = pr_saved_inputs_start n pF pG + n := by
    pr_register_omega
  rw [hSavedY_eq]
  have hk : n < (pr_setup_phase n pF pG).length := by
    simp only [pr_setup_phase, List.length_append, copy_register_range_length, List.length]; omega
  have hwrite : (pr_setup_phase n pF pG)[n] = Instr.T n (pr_saved_inputs_start n pF pG + n) := by
    simp only [pr_setup_phase, Program.copy_register_range, Nat.zero_add]
    grind
  have hnowrite_after : ∀ j (hj : j < (pr_setup_phase n pF pG).length), n < j →
      ((pr_setup_phase n pF pG)[j]).writes_to ≠ some (pr_saved_inputs_start n pF pG + n) := by
    intro j hj hjn
    simp only [pr_setup_phase, List.length_append, copy_register_range_length, List.length] at hj
    simp only [pr_setup_phase, List.getElem_append, copy_register_range_length]
    split_ifs with hj_copy
    · simp only [Program.copy_register_range, List.getElem_map, List.getElem_range,
        Instr.writes_to, ne_eq, Option.some.injEq]; omega
    · have hj_small : j - (n + 1) = 0 ∨ j - (n + 1) = 1 := by omega
      rcases hj_small with h0 | h1
      · simp only [h0, List.getElem_cons_zero, Instr.writes_to, ne_eq, Option.some.injEq]; pr_register_omega
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writes_to, ne_eq,
          Option.some.injEq]; pr_register_omega
  obtain ⟨s_before, ⟨c_n, hsteps_n, _, hs_before_eq⟩, htransfer⟩ := straight_line_transfer_result hsl s
    n n (pr_saved_inputs_start n pF pG + n) hk hwrite hnowrite_after
  have hs_before_val : s_before.read n = s.read n := by
    rw [← hs_before_eq]
    exact Steps.straight_line_preserves hsl hsteps_n (pr_setup_phase_no_write_low n pF pG n (Nat.lt_succ_self n))
  let hy_val : s.read n = y := by
    simp only [hs, State.of_inputs, State.read, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, Fin.snoc]
    let hn_lt : n < n + 1 := Nat.lt_succ_self n
    simp only [hn_lt, ↓reduceDIte, show ¬(n < n) by omega, Option.getD_some, cast_eq]
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  have heq : c'.state = straight_lineFinalState hsl s := by
    rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val, hy_val]

/-- After setup phase, counter is 0. -/
theorem pr_setup_phase_counter_zero (n : ℕ) (pF pG : Program)
    (s : State)
    (c' : Config) (hsteps : Steps (pr_setup_phase n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_setup_phase n pF pG)) :
    c'.state.read (pr_counter_reg n pF pG) = 0 := by
  have hsl := pr_setup_phase_is_straight_line n pF pG
  have hk : n + 1 < (pr_setup_phase n pF pG).length := by
    simp only [pr_setup_phase, List.length_append, copy_register_range_length, List.length]; omega
  have hwrite : (pr_setup_phase n pF pG)[n + 1] = Instr.Z (pr_counter_reg n pF pG) := by
    simp only [pr_setup_phase, List.getElem_append, copy_register_range_length]
    simp
  have hnowrite : ∀ j (hj : j < (pr_setup_phase n pF pG).length), n + 1 < j →
      ((pr_setup_phase n pF pG)[j]).writes_to ≠ some (pr_counter_reg n pF pG) := by
    intro j hj hjn
    simp only [pr_setup_phase, List.length_append, copy_register_range_length, List.length] at hj
    obtain rfl : j = n + 2 := by omega
    simp only [pr_setup_phase, List.getElem_append, copy_register_range_length]
    simp only [show ¬(n + 2 < n + 1) by omega, dite_false, show n + 2 - (n + 1) = 1 by omega]
    simp [Instr.writes_to, pr_zero_reg, pr_counter_reg]
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']
  exact straight_line_zeros_register hsl s (pr_counter_reg n pF pG) (n + 1) hk hwrite hnowrite

/-- After setup phase, zero register is 0. -/
theorem pr_setup_phase_zero_zero (n : ℕ) (pF pG : Program)
    (s : State)
    (c' : Config) (hsteps : Steps (pr_setup_phase n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_setup_phase n pF pG)) :
    c'.state.read (pr_zero_reg n pF pG) = 0 := by
  have hsl := pr_setup_phase_is_straight_line n pF pG
  have hk : n + 2 < (pr_setup_phase n pF pG).length := by
    simp only [pr_setup_phase, List.length_append, copy_register_range_length, List.length]; omega
  have hwrite : (pr_setup_phase n pF pG)[n + 2] = Instr.Z (pr_zero_reg n pF pG) := by
    simp only [pr_setup_phase, List.getElem_append, copy_register_range_length]
    simp only [show ¬(n + 2 < n + 1) by omega, dite_false, show n + 2 - (n + 1) = 1 by omega]
    simp
  have hnowrite : ∀ j (hj : j < (pr_setup_phase n pF pG).length), n + 2 < j →
      ((pr_setup_phase n pF pG)[j]).writes_to ≠ some (pr_zero_reg n pF pG) := by
    intro j hj hjn
    simp only [pr_setup_phase, List.length_append, copy_register_range_length, List.length] at hj
    omega
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']
  exact straight_line_zeros_register hsl s (pr_zero_reg n pF pG) (n + 2) hk hwrite hnowrite

/-! ## Base Case Prologue Invariants -/

/-- After base case prologue, R[0..n-1] contain saved inputs from s. -/
theorem pr_base_case_prologue_restores_inputs (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (pr_base_case_prologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_base_case_prologue n pF pG)) (i : Fin n) :
    c'.state.read i = s.read (pr_saved_inputs_start n pF pG + i) := by
  have hsl := pr_base_case_prologue_is_straight_line n pF pG
  have hi : ↑i < n := i.2
  have hk : (primitive_recursion_base n pF pG + 1) + ↑i < (pr_base_case_prologue n pF pG).length := by
    simp only [pr_base_case_prologue, List.length_append, clear_registers_length, copy_register_range_length]
    omega
  have hwrite : (pr_base_case_prologue n pF pG)[(primitive_recursion_base n pF pG + 1) + ↑i] =
      Instr.T (pr_saved_inputs_start n pF pG + i) i := by
    simp only [pr_base_case_prologue]
    let h_not_in_clear : ¬((primitive_recursion_base n pF pG + 1) + ↑i < (clear_registers (primitive_recursion_base n pF pG)).length) := by
      simp only [clear_registers_length]; omega
    rw [List.getElem_append_right (Nat.not_lt.mp h_not_in_clear)]
    let hidx : (primitive_recursion_base n pF pG + 1) + ↑i - (clear_registers (primitive_recursion_base n pF pG)).length = ↑i := by
      simp only [clear_registers_length]; omega
    simp only [hidx, Program.copy_register_range, List.getElem_map, List.getElem_range, Nat.zero_add]
  have hnowrite_after : ∀ j (hj : j < (pr_base_case_prologue n pF pG).length),
      (primitive_recursion_base n pF pG + 1) + ↑i < j →
      ((pr_base_case_prologue n pF pG)[j]).writes_to ≠ some ↑i := by
    intro j hj hjk
    simp only [pr_base_case_prologue, List.length_append, clear_registers_length, copy_register_range_length] at hj
    simp only [pr_base_case_prologue]
    by_cases hj_clear : j < (clear_registers (primitive_recursion_base n pF pG)).length
    · simp only [clear_registers_length] at hj_clear; omega
    · rw [List.getElem_append_right (Nat.not_lt.mp hj_clear)]
      simp only [Program.copy_register_range, List.getElem_map, List.getElem_range,
        Instr.writes_to, ne_eq, Option.some.injEq, Nat.zero_add, clear_registers_length]
      omega
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before⟩, htransfer⟩ :=
    straight_line_transfer_result hsl s ((primitive_recursion_base n pF pG + 1) + ↑i) (pr_saved_inputs_start n pF pG + i) ↑i hk hwrite hnowrite_after
  let hs_before_val : s_before.read (pr_saved_inputs_start n pF pG + ↑i) =
      s.read (pr_saved_inputs_start n pF pG + ↑i) := by
    rw [← hs_before]
    let hnowrite_before : ∀ instr, instr ∈ pr_base_case_prologue n pF pG →
        instr.writes_to ≠ some (pr_saved_inputs_start n pF pG + ↑i) := by
      intro instr hinstr
      simp only [pr_base_case_prologue, List.mem_append] at hinstr
      cases hinstr with
      | inl hclear =>
        simp only [Program.clear_registers, List.mem_map, List.mem_range] at hclear
        obtain ⟨j, hj, rfl⟩ := hclear
        simp only [Instr.writes_to, ne_eq, Option.some.injEq]
        let h := pr_saved_inputs_start_gt_base n pF pG; omega
      | inr hcopy =>
        simp only [Program.copy_register_range, List.mem_map, List.mem_range] at hcopy
        obtain ⟨j, hj, rfl⟩ := hcopy
        simp only [Instr.writes_to, ne_eq, Option.some.injEq, Nat.zero_add]
        let h := pr_saved_inputs_start_ge_n n pF pG; omega
    exact Steps.straight_line_preserves hsl hsteps_k hnowrite_before
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  have heq : c'.state = straight_lineFinalState hsl s := by
    rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val]

/-- Base case prologue preserves high registers (above primitive_recursion_base). -/
theorem pr_base_case_prologue_read_high_register_eq (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (pr_base_case_prologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_base_case_prologue n pF pG))
    (r : ℕ) (hr : primitive_recursion_base n pF pG < r) :
    c'.state.read r = s.read r := by
  have hsl := pr_base_case_prologue_is_straight_line n pF pG
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']
  apply Steps.straight_line_preserves hsl hsteps'
  intro instr hinstr
  simp only [pr_base_case_prologue, List.mem_append] at hinstr
  cases hinstr with
  | inl hclear =>
    simp only [Program.clear_registers, List.mem_map, List.mem_range] at hclear
    obtain ⟨j, hj, rfl⟩ := hclear
    writes_to_omega
  | inr hcopy =>
    simp only [Program.copy_register_range, List.mem_map, List.mem_range] at hcopy
    obtain ⟨j, hj, rfl⟩ := hcopy
    simp only [Instr.writes_to, ne_eq, Option.some.injEq, Nat.zero_add]
    have := primitive_recursion_base_ge_n n pF pG; omega

/-- After base case prologue, registers in [n..base] are cleared to 0. -/
theorem pr_base_case_prologue_clears_above_n (n : ℕ) (pF pG : Program) (s : State) (c : Config)
    (hsteps : Steps (pr_base_case_prologue n pF pG) ⟨0, s⟩ c)
    (hhalted : c.is_halted (pr_base_case_prologue n pF pG))
    (r : ℕ) (hr_ge : n ≤ r) (hr_le : r ≤ primitive_recursion_base n pF pG) :
    c.state.read r = 0 := by
  have hsl := pr_base_case_prologue_is_straight_line n pF pG
  have hk : r < (pr_base_case_prologue n pF pG).length := by
    simp only [pr_base_case_prologue, List.length_append, clear_registers_length, copy_register_range_length]
    omega
  have hwrite : (pr_base_case_prologue n pF pG)[r] = Instr.Z r := by
    simp only [pr_base_case_prologue]
    let h_in_clear : r < (clear_registers (primitive_recursion_base n pF pG)).length := by
      simp only [clear_registers_length]; exact Nat.lt_succ_of_le hr_le
    rw [List.getElem_append_left h_in_clear]
    simp only [Program.clear_registers, List.getElem_map, List.getElem_range]
  have hnowrite : ∀ j (hj : j < (pr_base_case_prologue n pF pG).length), r < j →
      ((pr_base_case_prologue n pF pG)[j]).writes_to ≠ some r := by
    intro j hj hjr
    simp only [pr_base_case_prologue, List.length_append, clear_registers_length,
      copy_register_range_length] at hj
    simp only [pr_base_case_prologue]
    by_cases hj_clear1 : j < (clear_registers (primitive_recursion_base n pF pG) ++
        copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length
    · by_cases hj_clear : j < primitive_recursion_base n pF pG + 1
      · let h2 : j < (clear_registers (primitive_recursion_base n pF pG)).length := by
          simp only [clear_registers_length]; exact hj_clear
        rw [List.getElem_append_left h2]
        simp only [Program.clear_registers, List.getElem_map, List.getElem_range,
          Instr.writes_to, ne_eq, Option.some.injEq]
        intro heq; exact Nat.ne_of_lt hjr heq.symm
      · let h2 : ¬ j < (clear_registers (primitive_recursion_base n pF pG)).length := by
          simp only [clear_registers_length]; omega
        let h2' : (clear_registers (primitive_recursion_base n pF pG)).length ≤ j := Nat.not_lt.mp h2
        rw [List.getElem_append_right h2']
        simp only [clear_registers_length, Program.copy_register_range,
          List.getElem_map, List.getElem_range, Nat.zero_add, Instr.writes_to, ne_eq, Option.some.injEq]
        simp only [List.length_append, clear_registers_length, copy_register_range_length] at hj_clear1
        omega
    · simp only [List.length_append, clear_registers_length, copy_register_range_length] at hj_clear1
      omega
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']
  exact straight_line_zeros_register hsl s r r hk hwrite hnowrite

/-- After loop prologue, registers 0..n-1 contain the saved inputs. -/
theorem pr_loop_prologue_restores_inputs (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (pr_loop_prologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_loop_prologue n pF pG)) (i : Fin n) :
    c'.state.read i = s.read (pr_saved_inputs_start n pF pG + i) := by
  have hsl := pr_loop_prologue_is_straight_line n pF pG
  have hk : (primitive_recursion_base n pF pG + 1) + ↑i < (pr_loop_prologue n pF pG).length := by
    simp only [pr_loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
      List.length]
    omega
  have hwrite : (pr_loop_prologue n pF pG)[(primitive_recursion_base n pF pG + 1) + ↑i] =
      Instr.T (pr_saved_inputs_start n pF pG + i) i := by
    simp only [pr_loop_prologue]
    let h_in_clear_copy : (primitive_recursion_base n pF pG + 1) + ↑i <
        (clear_registers (primitive_recursion_base n pF pG) ++
         copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length := by len_append_omega
    rw [List.getElem_append_left h_in_clear_copy]
    let h_not_in_clear : ¬((primitive_recursion_base n pF pG + 1) + ↑i <
        (clear_registers (primitive_recursion_base n pF pG)).length) := by
      simp only [clear_registers_length]; omega
    rw [List.getElem_append_right (Nat.not_lt.mp h_not_in_clear)]
    let hidx : (primitive_recursion_base n pF pG + 1) + ↑i -
        (clear_registers (primitive_recursion_base n pF pG)).length = ↑i := by
      simp only [clear_registers_length]; omega
    simp only [hidx, Program.copy_register_range, List.getElem_map, List.getElem_range, Nat.zero_add]
  have hnowrite_after : ∀ j (hj : j < (pr_loop_prologue n pF pG).length),
      (primitive_recursion_base n pF pG + 1) + ↑i < j →
      ((pr_loop_prologue n pF pG)[j]).writes_to ≠ some ↑i := by
    intro j hj hjk
    simp only [pr_loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
      List.length] at hj
    simp only [pr_loop_prologue]
    by_cases hj_in_main : j < (clear_registers (primitive_recursion_base n pF pG) ++
        copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length
    · rw [List.getElem_append_left hj_in_main]
      by_cases hj_clear : j < (clear_registers (primitive_recursion_base n pF pG)).length
      · simp only [clear_registers_length] at hj_clear; omega
      · rw [List.getElem_append_right (Nat.not_lt.mp hj_clear)]
        simp only [Program.copy_register_range, List.getElem_map, List.getElem_range,
          Instr.writes_to, ne_eq, Option.some.injEq, Nat.zero_add, clear_registers_length]
        simp only [List.length_append, clear_registers_length, copy_register_range_length] at hj_in_main
        omega
    · rw [List.getElem_append_right (Nat.not_lt.mp hj_in_main)]
      have hj_idx : j - (clear_registers (primitive_recursion_base n pF pG) ++
          copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length = 0 ∨
          j - (clear_registers (primitive_recursion_base n pF pG) ++
          copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length = 1 := by
        simp only [List.length_append, clear_registers_length, copy_register_range_length] at hj_in_main hj ⊢
        omega
      rcases hj_idx with h0 | h1
      · simp only [h0, List.getElem_cons_zero, Instr.writes_to, ne_eq, Option.some.injEq]
        have := primitive_recursion_base_ge_n n pF pG; omega
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writes_to, ne_eq,
          Option.some.injEq]
        have := primitive_recursion_base_ge_n n pF pG; omega
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before⟩, htransfer⟩ :=
    straight_line_transfer_result hsl s ((primitive_recursion_base n pF pG + 1) + ↑i)
      (pr_saved_inputs_start n pF pG + i) ↑i hk hwrite hnowrite_after
  have hs_before_val : s_before.read (pr_saved_inputs_start n pF pG + ↑i) =
      s.read (pr_saved_inputs_start n pF pG + ↑i) := by
    rw [← hs_before]
    apply Steps.straight_line_preserves hsl hsteps_k
    have h := pr_saved_inputs_start_gt_base n pF pG
    exact pr_loop_prologue_no_write_high n pF pG _ (by omega)
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  have heq : c'.state = straight_lineFinalState hsl s := by
    rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val]

/-- After loop prologue, R[n] contains k (from counter register). -/
theorem pr_loop_prologue_sets_Rn (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (pr_loop_prologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_loop_prologue n pF pG)) :
    c'.state.read n = s.read (pr_counter_reg n pF pG) := by
  have hsl := pr_loop_prologue_is_straight_line n pF pG
  have hk : (primitive_recursion_base n pF pG + 1) + n < (pr_loop_prologue n pF pG).length := by
    simp only [pr_loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
      List.length]; omega
  have hwrite : (pr_loop_prologue n pF pG)[(primitive_recursion_base n pF pG + 1) + n] =
      Instr.T (pr_counter_reg n pF pG) n := by
    simp only [pr_loop_prologue]
    let h_not_in_clear_copy : ¬((primitive_recursion_base n pF pG + 1) + n <
        (clear_registers (primitive_recursion_base n pF pG) ++
         copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length) := by len_append_omega
    rw [List.getElem_append_right (Nat.not_lt.mp h_not_in_clear_copy)]
    let hidx : (primitive_recursion_base n pF pG + 1) + n -
        (clear_registers (primitive_recursion_base n pF pG) ++
         copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length = 0 := by len_append_omega
    simp only [hidx, List.getElem_cons_zero]
  have hnowrite_after : ∀ j (hj : j < (pr_loop_prologue n pF pG).length),
      (primitive_recursion_base n pF pG + 1) + n < j →
      ((pr_loop_prologue n pF pG)[j]).writes_to ≠ some n := by
    intro j hj hjk
    simp only [pr_loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
      List.length] at hj
    simp only [pr_loop_prologue]
    let h_not_in_clear_copy : ¬(j < (clear_registers (primitive_recursion_base n pF pG) ++
        copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length) := by len_append_omega
    rw [List.getElem_append_right (Nat.not_lt.mp h_not_in_clear_copy)]
    let hidx : j - (clear_registers (primitive_recursion_base n pF pG) ++
        copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length = 1 := by len_append_omega
    simp only [hidx]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, Instr.writes_to, ne_eq, Option.some.injEq]
    let h := primitive_recursion_base_ge_n n pF pG; omega
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before⟩, htransfer⟩ :=
    straight_line_transfer_result hsl s ((primitive_recursion_base n pF pG + 1) + n)
      (pr_counter_reg n pF pG) n hk hwrite hnowrite_after
  have hs_before_val : s_before.read (pr_counter_reg n pF pG) = s.read (pr_counter_reg n pF pG) := by
    rw [← hs_before]
    apply Steps.straight_line_preserves hsl hsteps_k
    exact pr_loop_prologue_no_write_high n pF pG _ (pr_counter_reg_gt_base n pF pG)
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  have heq : c'.state = straight_lineFinalState hsl s := by
    rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val]

/-- After loop prologue, R[n+1] contains accBefore (from accumulator register). -/
theorem pr_loop_prologue_sets_Rn1 (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (pr_loop_prologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_loop_prologue n pF pG)) :
    c'.state.read (n + 1) = s.read (pr_accumulator_reg n pF pG) := by
  have hsl := pr_loop_prologue_is_straight_line n pF pG
  have hk : (primitive_recursion_base n pF pG + 2) + n < (pr_loop_prologue n pF pG).length := by
    simp only [pr_loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
      List.length]; omega
  have hwrite : (pr_loop_prologue n pF pG)[(primitive_recursion_base n pF pG + 2) + n] =
      Instr.T (pr_accumulator_reg n pF pG) (n + 1) := by
    simp only [pr_loop_prologue]
    let h_not_in_clear_copy : ¬((primitive_recursion_base n pF pG + 2) + n <
        (clear_registers (primitive_recursion_base n pF pG) ++
         copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length) := by len_append_omega
    rw [List.getElem_append_right (Nat.not_lt.mp h_not_in_clear_copy)]
    let hidx : (primitive_recursion_base n pF pG + 2) + n -
        (clear_registers (primitive_recursion_base n pF pG) ++
         copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length = 1 := by len_append_omega
    simp only [hidx, List.getElem_cons_succ, List.getElem_cons_zero]
  have hnowrite_after : ∀ j (hj : j < (pr_loop_prologue n pF pG).length),
      (primitive_recursion_base n pF pG + 2) + n < j →
      ((pr_loop_prologue n pF pG)[j]).writes_to ≠ some (n + 1) := by
    intro j hj hjk
    simp only [pr_loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
      List.length] at hj; omega
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before⟩, htransfer⟩ :=
    straight_line_transfer_result hsl s ((primitive_recursion_base n pF pG + 2) + n)
      (pr_accumulator_reg n pF pG) (n + 1) hk hwrite hnowrite_after
  have hs_before_val : s_before.read (pr_accumulator_reg n pF pG) = s.read (pr_accumulator_reg n pF pG) := by
    rw [← hs_before]
    apply Steps.straight_line_preserves hsl hsteps_k
    exact pr_loop_prologue_no_write_high n pF pG _ (pr_accumulator_reg_gt_base n pF pG)
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  have heq : c'.state = straight_lineFinalState hsl s := by
    rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']; rfl
  rw [heq, htransfer, hs_before_val]

/-- Loop prologue preserves high registers (above primitive_recursion_base). -/
theorem pr_loop_prologue_read_high_register_eq (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (pr_loop_prologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_loop_prologue n pF pG))
    (r : ℕ) (hr : primitive_recursion_base n pF pG < r) :
    c'.state.read r = s.read r := by
  have hsl := pr_loop_prologue_is_straight_line n pF pG
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']
  exact Steps.straight_line_preserves hsl hsteps' (pr_loop_prologue_no_write_high n pF pG r hr)

/-- Loop prologue zeros registers in range (n+1, primitive_recursion_base]. -/
theorem pr_loop_prologue_clears_pG_range (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (pr_loop_prologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_loop_prologue n pF pG))
    (r : ℕ) (hr_gt : n + 1 < r) (hr_le : r ≤ primitive_recursion_base n pF pG) :
    c'.state.read r = 0 := by
  have hsl := pr_loop_prologue_is_straight_line n pF pG
  have hk : r < (pr_loop_prologue n pF pG).length := by
    simp only [pr_loop_prologue, List.length_append, clear_registers_length,
      copy_register_range_length, List.length]; omega
  have h_in_clear : r < (clear_registers (primitive_recursion_base n pF pG)).length := by
    simp only [clear_registers_length]; exact Nat.lt_succ_of_le hr_le
  have h_in_ext2 : r < (clear_registers (primitive_recursion_base n pF pG) ++
      copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length := by len_append_omega
  have hwrite : (pr_loop_prologue n pF pG)[r] = Instr.Z r := by
    simp only [pr_loop_prologue]
    rw [List.getElem_append_left h_in_ext2, List.getElem_append_left h_in_clear]
    simp only [Program.clear_registers, List.getElem_map, List.getElem_range]
  have hnowrite : ∀ j (hj : j < (pr_loop_prologue n pF pG).length), r < j →
      ((pr_loop_prologue n pF pG)[j]).writes_to ≠ some r := by
    intro j hj hjr
    simp only [pr_loop_prologue, List.length_append, clear_registers_length,
      copy_register_range_length, List.length] at hj
    simp only [pr_loop_prologue]
    by_cases hj_clear2 : j < (clear_registers (primitive_recursion_base n pF pG) ++
        copy_register_range (pr_saved_inputs_start n pF pG) 0 n).length
    · rw [List.getElem_append_left hj_clear2]
      by_cases hj_in_clear : j < (clear_registers (primitive_recursion_base n pF pG)).length
      · rw [List.getElem_append_left hj_in_clear]
        simp only [Program.clear_registers, List.getElem_map, List.getElem_range,
          Instr.writes_to, ne_eq, Option.some.injEq]; omega
      · rw [List.getElem_append_right (Nat.not_lt.mp hj_in_clear)]
        simp only [clear_registers_length, Program.copy_register_range, List.getElem_map,
          List.getElem_range, Nat.zero_add, Instr.writes_to, ne_eq, Option.some.injEq]
        simp only [List.length_append, clear_registers_length, copy_register_range_length] at hj_clear2
        simp only [clear_registers_length] at hj_in_clear; omega
    · rw [List.getElem_append_right (Nat.not_lt.mp hj_clear2)]
      simp only [List.length_append, clear_registers_length, copy_register_range_length] at hj_clear2 ⊢
      have hidx : j - (primitive_recursion_base n pF pG + 1 + n) = 0 ∨
          j - (primitive_recursion_base n pF pG + 1 + n) = 1 := by omega
      rcases hidx with h0 | h1
      · simp only [h0, List.getElem_cons_zero, Instr.writes_to, ne_eq, Option.some.injEq]; omega
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writes_to, ne_eq,
          Option.some.injEq]; omega
  have ⟨hsteps', hhalted', _⟩ := straight_lineFinalState_spec hsl s
  rw [Steps.eq_of_halts hsteps hhalted hsteps' hhalted']
  exact straight_line_zeros_register hsl s r r hk hwrite hnowrite

/-- State agreement helper: After loop prologue, state agrees with extend_inputs_for_g initial state
    on pG's register range. This abstracts the common pattern used in pr_loop_iteration and
    primitive_recursion_program_halts_imp_dom. -/
theorem pr_loop_prologue_state_agree_on_pG_init (n : ℕ) (pF pG : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (pr_loop_prologue n pF pG) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (pr_loop_prologue n pF pG))
    (inputs : Fin n → ℕ) (k : ℕ) (acc : ℕ)
    (hR_inputs : ∀ i : Fin n, c'.state.read i = inputs i)
    (hRn : c'.state.read n = k)
    (hRn1 : c'.state.read (n + 1) = acc) :
    c'.state.agree_on
      (Config.init (List.ofFn (extend_inputs_for_g inputs k acc))).state
      0 pG.max_register := by
  intro r _ hr_hi
  let initStateG := (Config.init (List.ofFn (extend_inputs_for_g inputs k acc))).state
  by_cases hr_lt_n : r < n
  · -- Case 1: r < n (input registers)
    have hleft : c'.state.read r = inputs ⟨r, hr_lt_n⟩ := hR_inputs ⟨r, hr_lt_n⟩
    have hlen : r < (n + 2) := by omega
    have hright : initStateG.read r = inputs ⟨r, hr_lt_n⟩ := by
      unfold initStateG Config.init State.of_inputs State.read
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hlen, ↓reduceDIte]
      exact extend_inputs_for_g_castSucc_castSucc inputs k acc ⟨r, hr_lt_n⟩
    rw [hleft, hright]
  · by_cases hr_eq_n : r = n
    · -- Case 2: r = n (counter register position)
      subst hr_eq_n
      have hleft : c'.state.read r = k := hRn
      have hr : r < r + 2 := by omega
      have heq : (⟨r, hr⟩ : Fin (r + 2)) = Fin.castSucc (Fin.last r) := by
        ext; simp [Fin.castSucc, Fin.last]
      have hright : initStateG.read r = k := by
        unfold initStateG Config.init State.of_inputs State.read
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hr, ↓reduceDIte]
        rw [heq]
        exact extend_inputs_for_g_castSucc_last inputs k acc
      rw [hleft, hright]
    · by_cases hr_eq_n1 : r = n + 1
      · -- Case 3: r = n + 1 (accumulator register position)
        subst hr_eq_n1
        have hleft : c'.state.read (n + 1) = acc := hRn1
        have hlt : n + 1 < n + 2 := Nat.lt_succ_self _
        have hright : initStateG.read (n + 1) = acc := by
          unfold initStateG Config.init State.of_inputs State.read
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [hlt, ↓reduceDIte, Option.getD_some]
          exact extend_inputs_for_g_last inputs k acc
        rw [hleft, hright]
      · -- Case 4: r > n + 1 (high registers, cleared to 0)
        have hr_gt_n1 : n + 1 < r := by omega
        have hr_le_pG_max : r ≤ pG.max_register := hr_hi
        have hpG_le_base : pG.max_register ≤ primitive_recursion_base n pF pG :=
          primitive_recursion_base_ge_pG n pF pG
        have hr_le_base : r ≤ primitive_recursion_base n pF pG := Nat.le_trans hr_le_pG_max hpG_le_base
        have hleft : c'.state.read r = 0 :=
          pr_loop_prologue_clears_pG_range n pF pG s c' hsteps hhalted r hr_gt_n1 hr_le_base
        have hr_ge : ¬ r < n + 2 := by omega
        have hright : initStateG.read r = 0 := by
          unfold initStateG Config.init State.of_inputs State.read
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr_ge, dite_false, Option.getD_none]
        rw [hleft, hright]

end Urm
