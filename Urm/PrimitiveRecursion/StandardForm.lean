/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.PrimitiveRecursion.Construction

/-! # Standard Form Proofs for Primitive Recursion

This file proves that the primitive recursion witness program is in standard form.
-/

namespace Urm

open Program

/-! ## Component standard form proofs -/

theorem pr_setup_phase_isStandardForm (n : ℕ) (pF pG : Program) :
    (pr_setup_phase n pF pG).IsStandardForm := by
  simp only [pr_setup_phase]
  apply straight_line_isStandardForm
  simp only [Program.is_straight_line, List.all_append, copy_register_range]
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨k, _, hk⟩ := hinstr
    subst hk
    rfl
  · rfl

theorem pr_base_case_prologue_isStandardForm (n : ℕ) (pF pG : Program) :
    (pr_base_case_prologue n pF pG).IsStandardForm := by
  simp only [pr_base_case_prologue]
  apply straight_line_isStandardForm
  simp only [Program.is_straight_line, List.all_append]
  rw [Bool.and_eq_true]
  constructor
  · -- clear_registers is straight-line
    rw [clear_registers, List.all_eq_true]
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨k, _, hk⟩ := hinstr
    subst hk; rfl
  · -- copy_register_range is straight-line
    rw [copy_register_range, List.all_eq_true]
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨k, _, hk⟩ := hinstr
    subst hk; rfl

theorem pr_loop_prologue_isStandardForm (n : ℕ) (pF pG : Program) :
    (pr_loop_prologue n pF pG).IsStandardForm := by
  simp only [pr_loop_prologue]
  apply straight_line_isStandardForm
  simp only [Program.is_straight_line, List.all_append]
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- clear_registers is straight-line
    rw [clear_registers, List.all_eq_true]
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨k, _, hk⟩ := hinstr
    subst hk; rfl
  · -- copy_register_range is straight-line
    rw [copy_register_range, List.all_eq_true]
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨k, _, hk⟩ := hinstr
    subst hk; rfl
  · rfl

/-- The loop check has bounded jumps. -/
theorem pr_loop_check_has_bounded_jumps (n : ℕ) (pF pG : Program) :
    ∀ instr ∈ pr_loop_check n pF pG, instr.has_bounded_jump (pr_output_pc n pF pG + 1) = true := by
  intro instr hinstr
  unfold pr_loop_check at hinstr
  simp only [List.mem_singleton] at hinstr
  subst hinstr
  simp only [Instr.has_bounded_jump, decide_eq_true_eq]
  omega

/-- The loop epilogue has bounded jumps. -/
theorem pr_loop_epilogue_has_bounded_jumps (n : ℕ) (pF pG : Program) :
    ∀ instr ∈ pr_loop_epilogue n pF pG, instr.has_bounded_jump (pr_output_pc n pF pG + 1) = true := by
  intro instr hinstr
  unfold pr_loop_epilogue at hinstr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hinstr
  obtain rfl | rfl | rfl := hinstr
  · -- T 0 accumulator
    simp only [Instr.has_bounded_jump]
  · -- S counterReg
    simp only [Instr.has_bounded_jump]
  · -- J zeroReg zeroReg loopCheckPC
    simp only [Instr.has_bounded_jump, decide_eq_true_eq, pr_loop_check_pc,
      pr_setup_phase_length, pr_base_case_phase_length, pr_output_pc,
      pr_loop_body_pc, pr_loop_body_length, pr_loop_prologue_length, pr_loop_epilogue_length,
      pr_base_case_prologue_length]
    omega

/-! ## Shifted subprogram lemmas -/

/-- If pF is standard form, then pF shifted has bounded jumps for the embedded position. -/
theorem pr_shifted_pF_has_bounded_jumps (n : ℕ) (pF pG : Program) (hF : pF.IsStandardForm) :
    ∀ instr ∈ pF.shift_jumps (pr_pf_offset n pF pG),
      instr.has_bounded_jump (pr_output_pc n pF pG + 1) = true :=
  hF.shift_jumps_has_bounded_jumps (pr_pf_offset n pF pG) (pr_output_pc n pF pG + 1)
    (by simp only [pr_output_pc, pr_loop_body_pc, pr_loop_check_pc, pr_pf_offset,
          pr_setup_phase_length, pr_base_case_phase_length, pr_base_case_prologue_length, pr_loop_body_length]; omega)

/-- If pG is standard form, then pG shifted has bounded jumps for the embedded position. -/
theorem shifted_pG_has_bounded_jumps (n : ℕ) (pF pG : Program) (hG : pG.IsStandardForm) :
    ∀ instr ∈ pG.shift_jumps (pr_pg_offset n pF pG),
      instr.has_bounded_jump (pr_output_pc n pF pG + 1) = true :=
  hG.shift_jumps_has_bounded_jumps (pr_pg_offset n pF pG) (pr_output_pc n pF pG + 1)
    (by simp only [pr_output_pc, pr_loop_body_pc, pr_loop_check_pc, pr_pg_offset,
          pr_setup_phase_length, pr_base_case_phase_length, pr_loop_prologue_length, pr_loop_body_length]; omega)

/-! ## Main standard form theorem -/

/-- The primitive recursion program is in standard form when both pF and pG are. -/
theorem primitive_recursion_program_isStandardForm (n : ℕ) (pF pG : Program)
    (hF : pF.IsStandardForm) (hG : pG.IsStandardForm) :
    (primitive_recursion_program n pF pG).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm
  rw [List.all_eq_true]
  intro instr hinstr
  unfold primitive_recursion_program at hinstr
  rw [primitive_recursion_program_length]
  simp only [List.mem_append, pr_output_phase, List.mem_singleton] at hinstr
  -- Handle each component using match on the disjunction
  match hinstr with
  | Or.inl (Or.inl (Or.inl (Or.inl hinstr))) =>
    -- Setup phase
    have hsf := pr_setup_phase_isStandardForm n pF pG
    unfold Program.IsStandardForm Program.isStandardForm at hsf
    have h := List.all_eq_true.mp hsf instr hinstr
    apply Instr.has_bounded_jump_mono h
    simp only [pr_setup_phase_length_eq, pr_setup_phase_length, pr_output_pc,
      pr_loop_body_pc, pr_loop_check_pc, pr_loop_body_length, pr_base_case_phase_length,
      pr_loop_prologue_length, pr_loop_epilogue_length, pr_base_case_prologue_length]
    omega
  | Or.inl (Or.inl (Or.inl (Or.inr hinstr))) =>
    -- Base case phase
    simp only [pr_base_case_phase, List.mem_append, List.mem_singleton] at hinstr
    match hinstr with
    | Or.inl (Or.inl hinstr) =>
      -- Base case prologue proper
      have hsf := pr_base_case_prologue_isStandardForm n pF pG
      unfold Program.IsStandardForm Program.isStandardForm at hsf
      have h := List.all_eq_true.mp hsf instr hinstr
      apply Instr.has_bounded_jump_mono h
      simp only [pr_base_case_prologue_length_eq, pr_base_case_prologue_length, pr_output_pc,
        pr_loop_body_pc, pr_loop_check_pc, pr_loop_body_length, pr_base_case_phase_length,
        pr_setup_phase_length, pr_loop_prologue_length, pr_loop_epilogue_length]
      omega
    | Or.inl (Or.inr hinstr) =>
      -- Shifted pF
      exact pr_shifted_pF_has_bounded_jumps n pF pG hF instr hinstr
    | Or.inr h =>
      -- T 0 accumulator
      subst h; rfl
  | Or.inl (Or.inl (Or.inr hinstr)) =>
    -- Loop check
    exact pr_loop_check_has_bounded_jumps n pF pG instr hinstr
  | Or.inl (Or.inr hinstr) =>
    -- Loop body
    simp only [pr_loop_body, List.mem_append] at hinstr
    match hinstr with
    | Or.inl (Or.inl hinstr) =>
      -- Loop prologue
      have hsf := pr_loop_prologue_isStandardForm n pF pG
      unfold Program.IsStandardForm Program.isStandardForm at hsf
      have h := List.all_eq_true.mp hsf instr hinstr
      apply Instr.has_bounded_jump_mono h
      simp only [pr_loop_prologue_length_eq, pr_loop_prologue_length, pr_output_pc,
        pr_loop_body_pc, pr_loop_check_pc, pr_loop_body_length, pr_base_case_phase_length,
        pr_setup_phase_length, pr_loop_epilogue_length, pr_base_case_prologue_length]
      omega
    | Or.inl (Or.inr hinstr) =>
      -- Shifted pG
      exact shifted_pG_has_bounded_jumps n pF pG hG instr hinstr
    | Or.inr hinstr =>
      -- Loop epilogue
      exact pr_loop_epilogue_has_bounded_jumps n pF pG instr hinstr
  | Or.inr h =>
    -- Output phase
    subst h
    simp only [Instr.has_bounded_jump]

end Urm
