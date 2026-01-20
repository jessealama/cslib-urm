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

theorem setupPhase_isStandardForm (n : ℕ) (pF : Program) :
    (setupPhase n pF).IsStandardForm := by
  simp only [setupPhase]
  apply straightLine_isStandardForm
  simp only [Program.isStraightLine, List.all_append, copyRegisterRange]
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨k, _, hk⟩ := hinstr
    subst hk
    rfl
  · rfl

theorem loopPrologue_isStandardForm (n : ℕ) (pF : Program) :
    (loopPrologue n pF).IsStandardForm := by
  simp only [loopPrologue]
  apply straightLine_isStandardForm
  simp only [Program.isStraightLine, List.all_append]
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- clearRegisters is straight-line
    rw [clearRegisters, List.all_eq_true]
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨k, _, hk⟩ := hinstr
    subst hk; rfl
  · -- copyRegisterRange is straight-line
    rw [copyRegisterRange, List.all_eq_true]
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨k, _, hk⟩ := hinstr
    subst hk; rfl
  · rfl

/-- The loop epilogue has bounded jumps when bound is the full program length. -/
theorem loopEpilogue_hasBoundedJumps (n : ℕ) (pF : Program) :
    ∀ instr ∈ loopEpilogue n pF, instr.hasBoundedJump (outputPC n pF + 1) = true := by
  intro instr hinstr
  unfold loopEpilogue at hinstr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hinstr
  obtain rfl | rfl | rfl := hinstr
  · -- J 0 zeroReg outputPC
    simp only [Instr.hasBoundedJump, decide_eq_true_eq]
    omega
  · -- S counterReg
    simp only [Instr.hasBoundedJump]
  · -- J zeroReg zeroReg loopStartPC
    simp only [Instr.hasBoundedJump, decide_eq_true_eq, loopStartPC, setupPhaseLength,
      outputPC, pFOffset, loopPrologueLength]
    omega

/-! ## Main standard form theorem -/

/-- Helper: if pF is standard form, then pF shifted has bounded jumps for the embedded position. -/
theorem shiftedPF_hasBoundedJumps (n : ℕ) (pF : Program) (hF : pF.IsStandardForm) :
    ∀ instr ∈ pF.shiftJumps (pFOffset n pF),
      instr.hasBoundedJump (outputPC n pF + 1) = true :=
  hF.shiftJumps_hasBoundedJumps (pFOffset n pF) (outputPC n pF + 1) (by simp only [outputPC]; omega)

/-- The minimization program is in standard form when pF is. -/
theorem minimizeProgram_isStandardForm (n : ℕ) (pF : Program) (hF : pF.IsStandardForm) :
    (minimizeProgram n pF).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm
  rw [List.all_eq_true]
  intro instr hinstr
  unfold minimizeProgram at hinstr
  rw [minimizeProgram_length]
  simp only [List.mem_append, outputPhase, List.mem_singleton] at hinstr
  obtain (((hinstr | hinstr) | hinstr) | hinstr) | rfl := hinstr
  · -- Setup phase
    have hsf := setupPhase_isStandardForm n pF
    unfold Program.IsStandardForm Program.isStandardForm at hsf
    have h := List.all_eq_true.mp hsf instr hinstr
    apply Instr.hasBoundedJump_mono h
    simp only [outputPC, pFOffset, setupPhase_length, setupPhaseLength]
    omega
  · -- Loop prologue
    have hsf := loopPrologue_isStandardForm n pF
    unfold Program.IsStandardForm Program.isStandardForm at hsf
    have h := List.all_eq_true.mp hsf instr hinstr
    apply Instr.hasBoundedJump_mono h
    simp only [outputPC, pFOffset, loopPrologue_length, loopPrologueLength]
    omega
  · -- Shifted pF
    exact shiftedPF_hasBoundedJumps n pF hF instr hinstr
  · -- Loop epilogue
    exact loopEpilogue_hasBoundedJumps n pF instr hinstr
  · -- Output phase (instr = Instr.T ...)
    simp only [Instr.hasBoundedJump]

end Urm
