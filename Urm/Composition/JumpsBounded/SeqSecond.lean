/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.JumpsBounded.SeqFirst

/-! # JumpsBounded: Second Program Halting in Sequential Composition

This file proves that if p₁.seq p₂ halts, then p₂ halts from p₁'s final state.

## Main statements

- `Urm.JumpsBounded.seq_second_halts`: If p₁.seq p₂ halts, then p₂ halts from p₁'s output
-/

namespace Urm

namespace JumpsBounded

variable {p₁ p₂ : Program}

/-- If a step in p₁.seq p₂ stays in the p₂ region (PC ≥ p₁.length), the PC stays ≥ p₁.length.
    For JumpsBounded p₂, jumps in p₂ have targets ≤ p₂.length, so when shifted by p₁.length,
    they have targets ≤ p₁.length + p₂.length which is ≥ p₁.length. -/
private theorem seq_step_preserves_p2_region
    (hbounded : JumpsBounded p₂) {c c' : Config}
    (hstep : Step (p₁.seq p₂) c c') (hpc : p₁.length ≤ c.pc) (hpc' : c.pc < p₁.length + p₂.length) :
    p₁.length ≤ c'.pc := by
  -- Analyze the original step by case
  cases hstep with
  | zero h =>
    -- c'.pc = c.pc + 1, so c'.pc ≥ p₁.length
    simp only; omega
  | succ h =>
    simp only; omega
  | trans h =>
    simp only; omega
  | jump_eq h heq =>
    -- The seq instruction at c.pc is a shifted jump from p₂
    -- Need to show the target q ≥ p₁.length
    simp only [Program.seq, Program.getInstr, List.getElem?_append] at h
    split at h
    · omega  -- Can't be in p₁ region
    · -- In p₂ region: instruction is from p₂.shiftJumps
      simp only [Program.shiftJumps, List.getElem?_map] at h
      have hlt : c.pc - p₁.length < p₂.length := by omega
      -- h : Option.map (Instr.shiftJumps p₁.length) p₂[c.pc - p₁.length]? = some (Instr.J m n q)
      rw [List.getElem?_eq_getElem hlt] at h
      simp only [Option.map_some, Option.some.injEq] at h
      -- h : (p₂[c.pc - p₁.length]).shiftJumps p₁.length = Instr.J m n q
      -- Analyze by the type of the p₂ instruction
      unfold Instr.shiftJumps at h
      split at h
      case h_1 _ _ a => cases h  -- Instr.Z case: Z n ≠ J m n q
      case h_2 _ _ a => cases h  -- Instr.S case: S n ≠ J m n q
      case h_3 _ _ _ a => cases h  -- Instr.T case: T m n ≠ J m n q
      case h_4 jm jn jq hp₂_eq =>
        -- hp₂_eq : p₂[c.pc - p₁.length] = Instr.J jm jn jq
        -- h : Instr.J jm jn (jq + p₁.length) = Instr.J m n q
        simp only [Instr.J.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hinstr' : (p₂.getInstr (c.pc - p₁.length)) = some (Instr.J jm jn jq) := by
          simp only [Program.getInstr]
          rw [List.getElem?_eq_getElem hlt]
          simp only [hp₂_eq]
        have hbound := hbounded (c.pc - p₁.length) hlt jm jn jq hinstr'
        simp only
        omega
  | jump_ne h hne =>
    simp only; omega

/-- Extract p₂ steps from seq steps when starting anywhere in p₂ region. -/
private theorem seq_steps_extract_p2
    (hbounded : JumpsBounded p₂) {c c' : Config}
    (hsteps : Steps (p₁.seq p₂) c c') (hpc : p₁.length ≤ c.pc)
    (_hhalted : c'.isHalted (p₁.seq p₂)) :
    Steps p₂ ⟨c.pc - p₁.length, c.state⟩ ⟨c'.pc - p₁.length, c'.state⟩ := by
  -- Induct on hsteps
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head c_start c_mid hstep hrest ih =>
    -- hstep : Step (p₁.seq p₂) c_start c_mid
    -- hrest : Steps (p₁.seq p₂) c_mid c'
    -- hpc : p₁.length ≤ c_start.pc
    -- ih : (hpc' : p₁.length ≤ c_mid.pc) → Steps p₂ ⟨c_mid.pc - p₁.length, c_mid.state⟩ ⟨c'.pc - p₁.length, c'.state⟩
    by_cases hhalted_c : c_start.isHalted (p₁.seq p₂)
    · exact absurd hstep (Step.halted_no_step hhalted_c)
    · have hpc_lt : c_start.pc < p₁.length + p₂.length := by
        simp only [Config.isHalted, Program.seq_length] at hhalted_c; omega
      have hstep_p2 := Steps.seq_step_to_p2_step hstep hpc hpc_lt
      have hmid_ge := seq_step_preserves_p2_region hbounded hstep hpc hpc_lt
      exact Steps.trans (Steps.single hstep_p2) (ih hmid_ge)

/-- Extract p₂ steps from seq steps when starting at the junction. -/
theorem seq_steps_to_p2_steps
    (hbounded : JumpsBounded p₂) {c c' : Config}
    (hsteps : Steps (p₁.seq p₂) c c') (hpc : c.pc = p₁.length)
    (hhalted : c'.isHalted (p₁.seq p₂)) :
    Steps p₂ ⟨0, c.state⟩ ⟨c'.pc - p₁.length, c'.state⟩ := by
  have h := seq_steps_extract_p2 hbounded hsteps (by omega) hhalted
  simp only [hpc, Nat.sub_self] at h
  exact h

/-- If p₁.seq p₂ halts and p₁ is JumpsBounded, then p₂ halts when started from
    the state that p₁ produces.

More precisely: there exists a state σ such that p₁ reaches ⟨p₁.length, σ⟩,
and p₂ halts when started from σ. -/
theorem seq_second_halts (hbounded₁ : JumpsBounded p₁) (hbounded₂ : JumpsBounded p₂) {inputs : List ℕ}
    (hHaltsSeq : Halts (p₁.seq p₂) inputs) :
    ∃ σ : State, Steps p₁ (Config.init inputs) ⟨p₁.length, σ⟩ ∧
    ∃ c₂, Steps p₂ ⟨0, σ⟩ c₂ ∧ c₂.isHalted p₂ := by
  -- p₁ halts because composite halts
  have hpHalts := seq_first_halts hbounded₁ hHaltsSeq
  obtain ⟨c_halt, hsteps_p1, hhalted_p1⟩ := hpHalts

  -- c_halt.pc = p₁.length by halts_at_length
  have h_at_length := halts_at_length hbounded₁ hsteps_p1 hhalted_p1

  use c_halt.state

  constructor
  · have heq : c_halt = ⟨p₁.length, c_halt.state⟩ := by
      cases c_halt; simp only at h_at_length; simp [h_at_length]
    rw [heq] at hsteps_p1
    exact hsteps_p1

  -- Now show p₂ halts from state c_halt.state
  -- Extract the composite execution
  obtain ⟨cFinal, hstepsFinal, hhaltedFinal⟩ := hHaltsSeq

  -- Use: final config in p₂ is ⟨cFinal.pc - p₁.length, cFinal.state⟩
  use ⟨cFinal.pc - p₁.length, cFinal.state⟩

  constructor
  · -- Show Steps p₂ ⟨0, c_halt.state⟩ ⟨cFinal.pc - p₁.length, cFinal.state⟩
    -- Lift p₁ steps to composite
    have hsteps_seq : Steps (p₁.seq p₂) (Config.init inputs) ⟨p₁.length, c_halt.state⟩ := by
      have heq : c_halt = ⟨p₁.length, c_halt.state⟩ := by
        cases c_halt; simp only at h_at_length; simp [h_at_length]
      rw [heq] at hsteps_p1
      by_cases hp₁ : p₁.length = 0
      · -- p₁ is empty, init is at junction
        have hinit_halted : (Config.init inputs).isHalted p₁ := by simp [Config.isHalted, hp₁]
        have heq' := Steps.halts_unique hsteps_p1 (by simp [Config.isHalted, hp₁])
                                       (Steps.refl _) hinit_halted
        simp only [Config.init, hp₁] at heq'
        simp only [hp₁, Config.init, heq']
        exact Steps.refl _
      · apply Steps.seq_steps_first hsteps_p1
        · simp [Config.init]; omega
        · exact Nat.le_refl _

    -- Extract steps from junction to cFinal using determinism
    have hsteps_junction_to_final : Steps (p₁.seq p₂) ⟨p₁.length, c_halt.state⟩ cFinal := by
      by_cases hp₂ : p₂.length = 0
      · -- p₂ empty: junction is already halted
        have hjunction_halted : (⟨p₁.length, c_halt.state⟩ : Config).isHalted (p₁.seq p₂) := by
          simp [Config.isHalted, Program.seq_length, hp₂]
        -- By halts_unique, junction = cFinal
        have heq := Steps.halts_unique hsteps_seq hjunction_halted hstepsFinal hhaltedFinal
        rw [heq]
      · -- p₂ nonempty: use determinism to extract continuation
        exact Steps.deterministic_continuation hsteps_seq hstepsFinal hhaltedFinal

    -- Now apply seq_steps_to_p2_steps
    have h_pc_eq : (⟨p₁.length, c_halt.state⟩ : Config).pc = p₁.length := rfl
    have result := seq_steps_to_p2_steps hbounded₂ hsteps_junction_to_final h_pc_eq hhaltedFinal
    -- result : Steps p₂ ⟨0, (⟨p₁.length, c_halt.state⟩ : Config).state⟩ ⟨cFinal.pc - p₁.length, cFinal.state⟩
    -- This simplifies to: Steps p₂ ⟨0, c_halt.state⟩ ⟨cFinal.pc - p₁.length, cFinal.state⟩
    exact result

  · -- Show halted
    simp only [Config.isHalted]
    simp only [Config.isHalted, Program.seq_length] at hhaltedFinal
    omega

end JumpsBounded

end Urm
