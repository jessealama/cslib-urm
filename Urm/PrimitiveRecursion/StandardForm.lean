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

theorem prSetupPhase_isStandardForm (n : ℕ) (pF pG : Program) :
    (prSetupPhase n pF pG).IsStandardForm := by
  simp only [prSetupPhase]
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

theorem prBaseCasePrologue_isStandardForm (n : ℕ) (pF pG : Program) :
    (prBaseCasePrologue n pF pG).IsStandardForm := by
  simp only [prBaseCasePrologue]
  apply straightLine_isStandardForm
  simp only [Program.isStraightLine, List.all_append]
  rw [Bool.and_eq_true]
  constructor
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

theorem prLoopPrologue_isStandardForm (n : ℕ) (pF pG : Program) :
    (prLoopPrologue n pF pG).IsStandardForm := by
  simp only [prLoopPrologue]
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

/-- The loop check has bounded jumps. -/
theorem prLoopCheck_hasBoundedJumps (n : ℕ) (pF pG : Program) :
    ∀ instr ∈ prLoopCheck n pF pG, instr.hasBoundedJump (prOutputPC n pF pG + 1) = true := by
  intro instr hinstr
  unfold prLoopCheck at hinstr
  simp only [List.mem_singleton] at hinstr
  subst hinstr
  simp only [Instr.hasBoundedJump, decide_eq_true_eq]
  omega

/-- The loop epilogue has bounded jumps. -/
theorem prLoopEpilogue_hasBoundedJumps (n : ℕ) (pF pG : Program) :
    ∀ instr ∈ prLoopEpilogue n pF pG, instr.hasBoundedJump (prOutputPC n pF pG + 1) = true := by
  intro instr hinstr
  unfold prLoopEpilogue at hinstr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hinstr
  obtain rfl | rfl | rfl := hinstr
  · -- T 0 accumulator
    simp only [Instr.hasBoundedJump]
  · -- S counterReg
    simp only [Instr.hasBoundedJump]
  · -- J zeroReg zeroReg loopCheckPC
    simp only [Instr.hasBoundedJump, decide_eq_true_eq, prLoopCheckPC,
      prSetupPhaseLength, prBaseCasePhaseLength, prOutputPC,
      prLoopBodyPC, prLoopBodyLength, prLoopPrologueLength, prLoopEpilogueLength,
      prBaseCasePrologueLength]
    omega

/-! ## Shifted subprogram lemmas -/

/-- If pF is standard form, then pF shifted has bounded jumps for the embedded position. -/
theorem prShiftedPF_hasBoundedJumps (n : ℕ) (pF pG : Program) (hF : pF.IsStandardForm) :
    ∀ instr ∈ pF.shiftJumps (prPFOffset n pF pG),
      instr.hasBoundedJump (prOutputPC n pF pG + 1) = true := by
  intro instr hinstr
  simp only [Program.shiftJumps, List.mem_map] at hinstr
  obtain ⟨instr', hinstr'_mem, hinstr'_eq⟩ := hinstr
  subst hinstr'_eq
  have hbound : instr'.hasBoundedJump pF.length = true := by
    unfold Program.IsStandardForm Program.isStandardForm at hF
    exact List.all_eq_true.mp hF instr' hinstr'_mem
  have hshifted := Instr.hasBoundedJump_shiftJumps (len := pF.length)
    (offset := prPFOffset n pF pG) hbound
  apply Instr.hasBoundedJump_mono hshifted
  simp only [prOutputPC, prLoopBodyPC, prLoopCheckPC, prPFOffset,
    prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength, prLoopBodyLength]
  omega

/-- If pG is standard form, then pG shifted has bounded jumps for the embedded position. -/
theorem shiftedPG_hasBoundedJumps (n : ℕ) (pF pG : Program) (hG : pG.IsStandardForm) :
    ∀ instr ∈ pG.shiftJumps (prPGOffset n pF pG),
      instr.hasBoundedJump (prOutputPC n pF pG + 1) = true := by
  intro instr hinstr
  simp only [Program.shiftJumps, List.mem_map] at hinstr
  obtain ⟨instr', hinstr'_mem, hinstr'_eq⟩ := hinstr
  subst hinstr'_eq
  have hbound : instr'.hasBoundedJump pG.length = true := by
    unfold Program.IsStandardForm Program.isStandardForm at hG
    exact List.all_eq_true.mp hG instr' hinstr'_mem
  have hshifted := Instr.hasBoundedJump_shiftJumps (len := pG.length)
    (offset := prPGOffset n pF pG) hbound
  apply Instr.hasBoundedJump_mono hshifted
  simp only [prOutputPC, prLoopBodyPC, prLoopCheckPC, prPGOffset,
    prSetupPhaseLength, prBaseCasePhaseLength, prLoopPrologueLength, prLoopBodyLength]
  omega

/-! ## Main standard form theorem -/

/-- The primitive recursion program is in standard form when both pF and pG are. -/
theorem primitiveRecursionProgram_isStandardForm (n : ℕ) (pF pG : Program)
    (hF : pF.IsStandardForm) (hG : pG.IsStandardForm) :
    (primitiveRecursionProgram n pF pG).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm
  rw [List.all_eq_true]
  intro instr hinstr
  unfold primitiveRecursionProgram at hinstr
  rw [primitiveRecursionProgram_length]
  simp only [List.mem_append, prOutputPhase, List.mem_singleton] at hinstr
  -- Handle each component using match on the disjunction
  match hinstr with
  | Or.inl (Or.inl (Or.inl (Or.inl hinstr))) =>
    -- Setup phase
    have hsf := prSetupPhase_isStandardForm n pF pG
    unfold Program.IsStandardForm Program.isStandardForm at hsf
    have h := List.all_eq_true.mp hsf instr hinstr
    apply Instr.hasBoundedJump_mono h
    simp only [prSetupPhase_length, prSetupPhaseLength, prOutputPC,
      prLoopBodyPC, prLoopCheckPC, prLoopBodyLength, prBaseCasePhaseLength,
      prLoopPrologueLength, prLoopEpilogueLength, prBaseCasePrologueLength]
    omega
  | Or.inl (Or.inl (Or.inl (Or.inr hinstr))) =>
    -- Base case phase
    simp only [prBaseCasePhase, List.mem_append, List.mem_singleton] at hinstr
    match hinstr with
    | Or.inl (Or.inl hinstr) =>
      -- Base case prologue proper
      have hsf := prBaseCasePrologue_isStandardForm n pF pG
      unfold Program.IsStandardForm Program.isStandardForm at hsf
      have h := List.all_eq_true.mp hsf instr hinstr
      apply Instr.hasBoundedJump_mono h
      simp only [prBaseCasePrologue_length, prBaseCasePrologueLength, prOutputPC,
        prLoopBodyPC, prLoopCheckPC, prLoopBodyLength, prBaseCasePhaseLength,
        prSetupPhaseLength, prLoopPrologueLength, prLoopEpilogueLength]
      omega
    | Or.inl (Or.inr hinstr) =>
      -- Shifted pF
      exact prShiftedPF_hasBoundedJumps n pF pG hF instr hinstr
    | Or.inr h =>
      -- T 0 accumulator
      subst h; rfl
  | Or.inl (Or.inl (Or.inr hinstr)) =>
    -- Loop check
    exact prLoopCheck_hasBoundedJumps n pF pG instr hinstr
  | Or.inl (Or.inr hinstr) =>
    -- Loop body
    simp only [prLoopBody, List.mem_append] at hinstr
    match hinstr with
    | Or.inl (Or.inl hinstr) =>
      -- Loop prologue
      have hsf := prLoopPrologue_isStandardForm n pF pG
      unfold Program.IsStandardForm Program.isStandardForm at hsf
      have h := List.all_eq_true.mp hsf instr hinstr
      apply Instr.hasBoundedJump_mono h
      simp only [prLoopPrologue_length, prLoopPrologueLength, prOutputPC,
        prLoopBodyPC, prLoopCheckPC, prLoopBodyLength, prBaseCasePhaseLength,
        prSetupPhaseLength, prLoopEpilogueLength, prBaseCasePrologueLength]
      omega
    | Or.inl (Or.inr hinstr) =>
      -- Shifted pG
      exact shiftedPG_hasBoundedJumps n pF pG hG instr hinstr
    | Or.inr hinstr =>
      -- Loop epilogue
      exact prLoopEpilogue_hasBoundedJumps n pF pG instr hinstr
  | Or.inr h =>
    -- Output phase
    subst h
    simp only [Instr.hasBoundedJump]

end Urm
