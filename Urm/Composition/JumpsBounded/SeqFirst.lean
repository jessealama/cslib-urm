/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.JumpsBounded.Halting

/-! # JumpsBounded: First Program Halting in Sequential Composition

This file proves that if p₁.seq p₂ halts and p₁ is JumpsBounded, then p₁ halts.

## Main statements

- `Urm.JumpsBounded.seq_first_halts`: If p₁.seq p₂ halts and p₁ is JumpsBounded, then p₁ halts
-/

namespace Urm

namespace JumpsBounded

variable {p₁ p₂ : Program}

/-- Helper: for JumpsBounded p₁, a step in p₁.seq p₂ from pc < p₁.length
    either stays in [0, p₁.length] or reaches exactly p₁.length.
    This is essentially: jumping can't skip over p₁.length. -/
private theorem seq_step_bounded_pc (hbounded : JumpsBounded p₁)
    {c c' : Config} (hstep : Step (p₁.seq p₂) c c')
    (hpc : c.pc < p₁.length) : c'.pc ≤ p₁.length := by
  -- When pc < p₁.length, the instruction comes from p₁
  have hinstr_eq := Program.seq_getInstr_first p₁ p₂ c.pc hpc
  cases hstep with
  | zero hinstr =>
    simp [hinstr_eq] at hinstr
    have hpc' := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega
  | succ hinstr =>
    simp [hinstr_eq] at hinstr
    have hpc' := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega
  | trans hinstr =>
    simp [hinstr_eq] at hinstr
    have hpc' := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega
  | jump_eq hinstr _ =>
    simp [hinstr_eq] at hinstr
    have hpc' := (List.getElem?_eq_some_iff.mp hinstr).1
    exact hbounded _ hpc' _ _ _ hinstr
  | jump_ne hinstr _ =>
    simp [hinstr_eq] at hinstr
    have hpc' := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega

/-- Helper: if execution in p₁.seq p₂ goes from c to c' with c.pc < p₁.length,
    then there's a corresponding step in p₁. -/
private theorem seq_step_to_p1_step {c c' : Config}
    (hstep : Step (p₁.seq p₂) c c') (hpc : c.pc < p₁.length) : Step p₁ c c' := by
  have hinstr_eq := Program.seq_getInstr_first p₁ p₂ c.pc hpc
  cases hstep with
  | zero hinstr =>
    rw [hinstr_eq] at hinstr
    exact Step.zero hinstr
  | succ hinstr =>
    rw [hinstr_eq] at hinstr
    exact Step.succ hinstr
  | trans hinstr =>
    rw [hinstr_eq] at hinstr
    exact Step.trans hinstr
  | jump_eq hinstr heq =>
    rw [hinstr_eq] at hinstr
    exact Step.jump_eq hinstr heq
  | jump_ne hinstr hne =>
    rw [hinstr_eq] at hinstr
    exact Step.jump_ne hinstr hne

/-- Core helper: execution in p₁.seq p₂ from a config with pc < p₁.length
    that eventually reaches pc ≥ p₁.length must produce a halting execution in p₁.

    Returns: Steps p₁ c c_halt where c_halt is halted in p₁. -/
private theorem seq_finds_junction (hbounded : JumpsBounded p₁)
    {c cFinal : Config} (hsteps : Steps (p₁.seq p₂) c cFinal)
    (hpc : c.pc < p₁.length) (hFinalPC : p₁.length ≤ cFinal.pc) :
    ∃ c_halt, Steps p₁ c c_halt ∧ c_halt.isHalted p₁ := by
  -- We induct on the steps, tracking the start config c
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- c = cFinal, but c.pc < p₁.length and cFinal.pc ≥ p₁.length, contradiction
    omega
  | head hstep hrest ih =>
    rename_i c_start c_mid
    -- hstep : Step (p₁.seq p₂) c_start c_mid
    -- hrest : Steps (p₁.seq p₂) c_mid cFinal
    -- ih : c_mid.pc < p₁.length → ∃ c_halt, Steps p₁ c_mid c_halt ∧ c_halt.isHalted p₁
    -- hpc : c_start.pc < p₁.length (we need to clarify this from context)

    -- Check if c_mid.pc < p₁.length or ≥ p₁.length
    by_cases hMidPC : c_mid.pc < p₁.length
    · -- Still in p₁'s range
      -- Get IH for c_mid
      obtain ⟨c_halt, hsteps_rest, hhalted⟩ := ih hMidPC
      -- Build step in p₁ from c_start to c_mid
      have hstep_p1 := seq_step_to_p1_step (p₂ := p₂) hstep hpc
      exact ⟨c_halt, Relation.ReflTransGen.head hstep_p1 hsteps_rest, hhalted⟩
    · -- c_mid.pc ≥ p₁.length after this step
      -- By JumpsBounded, c_mid.pc ≤ p₁.length, so c_mid.pc = p₁.length
      have h_le := seq_step_bounded_pc hbounded hstep hpc
      have h_eq : c_mid.pc = p₁.length := Nat.le_antisymm h_le (Nat.not_lt.mp hMidPC)
      -- Build step in p₁ from c_start to c_mid
      have hstep_p1 := seq_step_to_p1_step (p₂ := p₂) hstep hpc
      -- c_mid is halted in p₁
      have hhalted : c_mid.isHalted p₁ := by simp [Config.isHalted, h_eq]
      exact ⟨c_mid, Relation.ReflTransGen.single hstep_p1, hhalted⟩

/-- Key lemma: if JumpsBounded p₁ and p₁.seq p₂ halts, then p₁ halts.

For standard-form programs (JumpsBounded), execution starting at pc=0 must
pass through pc=p₁.length to reach p₂. At pc=p₁.length, p₁ is halted. -/
theorem seq_first_halts (hbounded : JumpsBounded p₁) {inputs : List ℕ}
    (hHaltsSeq : Halts (p₁.seq p₂) inputs) : Halts p₁ inputs := by
  obtain ⟨cFinal, hstepsFinal, hhaltedFinal⟩ := hHaltsSeq

  -- First, if p₁ is empty, init is immediately halted
  by_cases hp₁ : p₁.length = 0
  · exact ⟨Config.init inputs, Relation.ReflTransGen.refl, by simp [Config.isHalted, hp₁]⟩

  -- cFinal.pc ≥ p₁.length (since it's halted in p₁.seq p₂)
  have hFinalPC : p₁.length ≤ cFinal.pc := by
    have := hhaltedFinal
    simp only [Config.isHalted, Program.seq_length] at this
    omega

  -- init.pc = 0 < p₁.length
  have hInitPC : (Config.init inputs).pc < p₁.length := by simp [Config.init]; omega

  -- Use the helper to find the junction point
  obtain ⟨c_halt, hsteps, hhalted⟩ := seq_finds_junction hbounded hstepsFinal hInitPC hFinalPC
  exact ⟨c_halt, hsteps, hhalted⟩

end JumpsBounded

end Urm
