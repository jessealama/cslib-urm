/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.Construction

/-! # Standard Form Proofs for Minimization

This file proves that the minimization witness program is in standard form.
-/

namespace Urm

open Program

/-! ## Component standard form proofs -/

theorem setup_phase_isStandardForm (n : ℕ) (pF : Program) :
    (setup_phase n pF).IsStandardForm := by
  simp only [setup_phase]
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

theorem loop_prologue_isStandardForm (n : ℕ) (pF : Program) :
    (loop_prologue n pF).IsStandardForm := by
  simp only [loop_prologue]
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

/-- The loop epilogue has bounded jumps when bound is the full program length. -/
theorem loopEpilogue_has_bounded_jumps (n : ℕ) (pF : Program) :
    ∀ instr ∈ loopEpilogue n pF, instr.has_bounded_jump (outputPC n pF + 1) = true := by
  intro instr hinstr
  unfold loopEpilogue at hinstr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hinstr
  obtain rfl | rfl | rfl := hinstr
  · -- J 0 zero_reg outputPC
    simp only [Instr.has_bounded_jump, decide_eq_true_eq]
    omega
  · -- S counter_reg
    simp only [Instr.has_bounded_jump]
  · -- J zero_reg zero_reg loop_start_pc
    simp only [Instr.has_bounded_jump, decide_eq_true_eq, loop_start_pc, setup_phase_length,
      outputPC, pFOffset, loop_prologueLength]
    omega

/-! ## Main standard form theorem -/

/-- Helper: if pF is standard form, then pF shifted has bounded jumps for the embedded position. -/
theorem shiftedPF_has_bounded_jumps (n : ℕ) (pF : Program) (hF : pF.IsStandardForm) :
    ∀ instr ∈ pF.shift_jumps (pFOffset n pF),
      instr.has_bounded_jump (outputPC n pF + 1) = true :=
  hF.shift_jumps_has_bounded_jumps (pFOffset n pF) (outputPC n pF + 1) (by simp only [outputPC]; omega)

/-- The minimization program is in standard form when pF is. -/
theorem minimize_program_isStandardForm (n : ℕ) (pF : Program) (hF : pF.IsStandardForm) :
    (minimize_program n pF).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm
  rw [List.all_eq_true]
  intro instr hinstr
  unfold minimize_program at hinstr
  rw [minimize_program_length]
  simp only [List.mem_append, output_phase, List.mem_singleton] at hinstr
  obtain (((hinstr | hinstr) | hinstr) | hinstr) | rfl := hinstr
  · -- Setup phase
    have hsf := setup_phase_isStandardForm n pF
    unfold Program.IsStandardForm Program.isStandardForm at hsf
    have h := List.all_eq_true.mp hsf instr hinstr
    apply Instr.has_bounded_jump_mono h
    simp only [outputPC, pFOffset, setup_phase_length, setup_phase_len]
    omega
  · -- Loop prologue
    have hsf := loop_prologue_isStandardForm n pF
    unfold Program.IsStandardForm Program.isStandardForm at hsf
    have h := List.all_eq_true.mp hsf instr hinstr
    apply Instr.has_bounded_jump_mono h
    simp only [outputPC, pFOffset, loop_prologue_length, loop_prologueLength]
    omega
  · -- Shifted pF
    exact shiftedPF_has_bounded_jumps n pF hF instr hinstr
  · -- Loop epilogue
    exact loopEpilogue_has_bounded_jumps n pF instr hinstr
  · -- Output phase (instr = Instr.T ...)
    simp only [Instr.has_bounded_jump]

end Urm
