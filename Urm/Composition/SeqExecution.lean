/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.ShiftLemmas

/-! # Execution in Sequential Programs

This file contains lemmas about executing steps in sequentially composed programs.

## Main statements

- `Urm.Steps.seq_step_first`: A step in p₁ is also a step in p₁.seq p₂
- `Urm.Steps.seq_steps_first`: Steps in p₁ transfer to p₁.seq p₂
- `Urm.Steps.seq_step_second`: A step in p₂ lifts to p₁.seq p₂
- `Urm.Steps.seq_steps_second`: Steps in p₂ lift to p₁.seq p₂
- `Urm.Steps.seq_halts_compose`: Sequential composition of halting programs halts
-/

namespace Urm

namespace Steps

variable {p₁ p₂ : Program}

/-- A step in `p₁` is also a step in `p₁.seq p₂`, as long as we stay within `p₁`. -/
theorem seq_step_first {c c' : Config} (hstep : Step p₁ c c') (hpc : c.pc < p₁.length) :
    Step (p₁.seq p₂) c c' := by
  cases hstep with
  | zero h =>
    have heq : (p₁.seq p₂).getInstr c.pc = p₁.getInstr c.pc :=
      Program.seq_getInstr_first p₁ p₂ c.pc hpc
    exact Step.zero (heq ▸ h)
  | succ h =>
    have heq : (p₁.seq p₂).getInstr c.pc = p₁.getInstr c.pc :=
      Program.seq_getInstr_first p₁ p₂ c.pc hpc
    exact Step.succ (heq ▸ h)
  | trans h =>
    have heq : (p₁.seq p₂).getInstr c.pc = p₁.getInstr c.pc :=
      Program.seq_getInstr_first p₁ p₂ c.pc hpc
    exact Step.trans (heq ▸ h)
  | jump_eq h heq' =>
    have heq : (p₁.seq p₂).getInstr c.pc = p₁.getInstr c.pc :=
      Program.seq_getInstr_first p₁ p₂ c.pc hpc
    exact Step.jump_eq (heq ▸ h) heq'
  | jump_ne h hne =>
    have heq : (p₁.seq p₂).getInstr c.pc = p₁.getInstr c.pc :=
      Program.seq_getInstr_first p₁ p₂ c.pc hpc
    exact Step.jump_ne (heq ▸ h) hne

/-- If we can step from c, then c.pc is within the program bounds. -/
private theorem step_implies_in_bounds {c c' : Config} (hstep : Step p₁ c c') :
    c.pc < p₁.length := by
  cases hstep with
  | zero h => exact (List.getElem?_eq_some_iff.mp h).1
  | succ h => exact (List.getElem?_eq_some_iff.mp h).1
  | trans h => exact (List.getElem?_eq_some_iff.mp h).1
  | jump_eq h _ => exact (List.getElem?_eq_some_iff.mp h).1
  | jump_ne h _ => exact (List.getElem?_eq_some_iff.mp h).1

/-- Steps in `p₁` transfer to `p₁.seq p₂`, as long as we stay within `p₁`.
This is a key lemma for proving that sequential composition works correctly. -/
theorem seq_steps_first {c c' : Config} (hsteps : Steps p₁ c c')
    (hpc : c.pc < p₁.length) (_hpc' : c'.pc ≤ p₁.length) :
    Steps (p₁.seq p₂) c c' := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hstep hrest ih =>
    -- hstep : Step p₁ c c_mid
    -- hrest : Steps p₁ c_mid c'
    -- Need to show: Steps (p₁.seq p₂) c c'
    rename_i c_mid
    -- First, show the step works in the seq program
    have hstep_seq := seq_step_first (p₂ := p₂) hstep hpc
    -- Now we need to show c_mid.pc < p₁.length to continue
    -- If c_mid.pc >= p₁.length, then c_mid is halted in p₁, so hrest must be refl
    by_cases h : c_mid.pc < p₁.length
    · -- c_mid.pc < p₁.length, so we can apply IH
      exact Relation.ReflTransGen.head hstep_seq (ih h)
    · -- c_mid.pc >= p₁.length, so c_mid is halted in p₁
      -- This means c_mid = c' (hrest must be reflexive since c_mid is halted)
      have h_halted : c_mid.isHalted p₁ := Nat.not_lt.mp h
      -- Since c_mid is halted, hrest must be Relation.ReflTransGen.refl
      cases hrest using Relation.ReflTransGen.head_induction_on with
      | refl =>
        -- c_mid = c', so just one step
        exact Relation.ReflTransGen.single hstep_seq
      | head hstep' _ =>
        -- Can't step from halted config
        exact absurd hstep' (Step.halted_no_step h_halted)

/-- Get the instruction at position `offset + i` in `p₁.seq p₂` where `i < p₂.length`. -/
private theorem seq_getInstr_second_eq (p₁ p₂ : Program) (i : ℕ) (_hi : i < p₂.length) :
    (p₁.seq p₂).getInstr (p₁.length + i) = (p₂.getInstr i).map (Instr.shiftJumps p₁.length) := by
  simp only [Program.seq, Program.getInstr]
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Program.shiftJumps, List.getElem?_map, Nat.add_sub_cancel_left]

/-- A step in `p₂` at PC `i` corresponds to a step in `p₁.seq p₂` at PC `p₁.length + i`.
The key insight is that jump targets in p₂ are shifted by p₁.length, so jumps
within the second portion stay within the second portion. -/
theorem seq_step_second {c c' : Config} (hstep : Step p₂ c c') :
    Step (p₁.seq p₂) ⟨p₁.length + c.pc, c.state⟩ ⟨p₁.length + c'.pc, c'.state⟩ := by
  have hpc : c.pc < p₂.length := step_implies_in_bounds hstep
  have hinstr := seq_getInstr_second_eq p₁ p₂ c.pc hpc
  cases hstep with
  | zero h =>
    rw [h, Option.map_some] at hinstr
    simp only [Instr.shiftJumps] at hinstr
    have hstep' := Step.zero (p := p₁.seq p₂) (c := ⟨p₁.length + c.pc, c.state⟩) hinstr
    convert hstep' using 2
  | succ h =>
    rw [h, Option.map_some] at hinstr
    simp only [Instr.shiftJumps] at hinstr
    have hstep' := Step.succ (p := p₁.seq p₂) (c := ⟨p₁.length + c.pc, c.state⟩) hinstr
    convert hstep' using 2
  | trans h =>
    rw [h, Option.map_some] at hinstr
    simp only [Instr.shiftJumps] at hinstr
    have hstep' := Step.trans (p := p₁.seq p₂) (c := ⟨p₁.length + c.pc, c.state⟩) hinstr
    convert hstep' using 2
  | jump_eq h heq =>
    rw [h, Option.map_some] at hinstr
    simp only [Instr.shiftJumps] at hinstr
    have hstep' := Step.jump_eq (p := p₁.seq p₂) (c := ⟨p₁.length + c.pc, c.state⟩) hinstr heq
    convert hstep' using 2
    simp only [Nat.add_comm]
  | jump_ne h hne =>
    rw [h, Option.map_some] at hinstr
    simp only [Instr.shiftJumps] at hinstr
    have hstep' := Step.jump_ne (p := p₁.seq p₂) (c := ⟨p₁.length + c.pc, c.state⟩) hinstr hne
    convert hstep' using 2

/-- Steps in `p₂` lift to steps in `p₁.seq p₂` with PC offset by `p₁.length`. -/
theorem seq_steps_second {c c' : Config} (hsteps : Steps p₂ c c') :
    Steps (p₁.seq p₂) ⟨p₁.length + c.pc, c.state⟩ ⟨p₁.length + c'.pc, c'.state⟩ := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hstep _ ih =>
    exact Relation.ReflTransGen.head (seq_step_second hstep) ih

/-- A step in `p₁.seq p₂` at PC ≥ p₁.length corresponds to a step in `p₂`.
This is the inverse of `seq_step_second`. -/
theorem seq_step_to_p2_step {c c' : Config}
    (hstep : Step (p₁.seq p₂) c c') (hpc : p₁.length ≤ c.pc) (hpc' : c.pc < p₁.length + p₂.length) :
    Step p₂ ⟨c.pc - p₁.length, c.state⟩ ⟨c'.pc - p₁.length, c'.state⟩ := by
  -- Get the instruction at c.pc in p₁.seq p₂
  have hi : c.pc - p₁.length < p₂.length := by omega
  have hinstr_eq := seq_getInstr_second_eq p₁ p₂ (c.pc - p₁.length) hi
  have hpc_eq : p₁.length + (c.pc - p₁.length) = c.pc := by omega
  simp only [hpc_eq] at hinstr_eq
  cases hstep with
  | zero h =>
    rw [hinstr_eq] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr_p2, heq⟩ := h
    match instr with
    | Instr.Z n =>
      injection heq with hn; subst hn
      have hstep' := Step.zero (p := p₂) (c := ⟨c.pc - p₁.length, c.state⟩) hinstr_p2
      simp only at hstep' ⊢
      convert hstep' using 2
      omega
    | Instr.S _ => simp_all [Instr.shiftJumps]
    | Instr.T _ _ => simp_all [Instr.shiftJumps]
    | Instr.J _ _ _ => simp_all [Instr.shiftJumps]
  | succ h =>
    rw [hinstr_eq] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr_p2, heq⟩ := h
    match instr with
    | Instr.Z _ => simp_all [Instr.shiftJumps]
    | Instr.S n =>
      injection heq with hn; subst hn
      have hstep' := Step.succ (p := p₂) (c := ⟨c.pc - p₁.length, c.state⟩) hinstr_p2
      simp only at hstep' ⊢
      convert hstep' using 2
      omega
    | Instr.T _ _ => simp_all [Instr.shiftJumps]
    | Instr.J _ _ _ => simp_all [Instr.shiftJumps]
  | trans h =>
    rw [hinstr_eq] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr_p2, heq⟩ := h
    match instr with
    | Instr.Z _ => simp_all [Instr.shiftJumps]
    | Instr.S _ => simp_all [Instr.shiftJumps]
    | Instr.T m n =>
      injection heq with hm hn; subst hm; subst hn
      have hstep' := Step.trans (p := p₂) (c := ⟨c.pc - p₁.length, c.state⟩) hinstr_p2
      simp only at hstep' ⊢
      convert hstep' using 2
      omega
    | Instr.J _ _ _ => simp_all [Instr.shiftJumps]
  | jump_eq h heq =>
    rw [hinstr_eq] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr_p2, heq'⟩ := h
    match instr with
    | Instr.Z _ => simp_all [Instr.shiftJumps]
    | Instr.S _ => simp_all [Instr.shiftJumps]
    | Instr.T _ _ => simp_all [Instr.shiftJumps]
    | Instr.J m n q =>
      simp only [Instr.shiftJumps] at heq'
      injection heq' with hm hn hq; subst hm; subst hn
      have hstep' := Step.jump_eq (p := p₂) (c := ⟨c.pc - p₁.length, c.state⟩) hinstr_p2 heq
      convert hstep' using 2
      simp only; omega
  | jump_ne h hne =>
    rw [hinstr_eq] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr_p2, heq⟩ := h
    match instr with
    | Instr.Z _ => simp_all [Instr.shiftJumps]
    | Instr.S _ => simp_all [Instr.shiftJumps]
    | Instr.T _ _ => simp_all [Instr.shiftJumps]
    | Instr.J m n q =>
      simp only [Instr.shiftJumps] at heq
      injection heq with hm hn hq; subst hm; subst hn
      have hstep' := Step.jump_ne (p := p₂) (c := ⟨c.pc - p₁.length, c.state⟩) hinstr_p2 hne
      simp only at hstep' ⊢
      convert hstep' using 2
      omega

/-- Sequential composition of halting programs: if p₁ reaches state σ at pc = p₁.length,
and p₂ halts starting from state σ at pc = 0, then p₁.seq p₂ halts.

This directly connects the execution of two programs without requiring state agreement. -/
theorem seq_halts_compose {inputs : List ℕ} {σ : State} {c₂ : Config}
    (h₁_steps : Steps p₁ (Config.init inputs) ⟨p₁.length, σ⟩)
    (h₂_steps : Steps p₂ ⟨0, σ⟩ c₂)
    (h₂_halted : c₂.isHalted p₂) :
    Halts (p₁.seq p₂) inputs := by
  -- Build steps in p₁.seq p₂:
  -- 1. Run p₁ from init to ⟨p₁.length, σ⟩
  have hsteps₁_seq : Steps (p₁.seq p₂) (Config.init inputs) ⟨p₁.length, σ⟩ := by
    by_cases hp₁ : p₁.length = 0
    · -- p₁ is empty: steps from init to ⟨0, σ⟩ must preserve state
      -- Config.init inputs = ⟨0, σ_init⟩ and ⟨p₁.length, σ⟩ = ⟨0, σ⟩
      -- Since p₁ is empty, no steps can be taken, so σ = σ_init
      have h_eq : (Config.init inputs).pc = p₁.length := by simp [Config.init, hp₁]
      -- Check if the steps are reflexive
      have h_halted : (Config.init inputs).isHalted p₁ := by
        simp [Config.isHalted, Config.init, hp₁]
      -- If init is halted, h₁_steps must be refl
      have h_refl : Config.init inputs = ⟨p₁.length, σ⟩ :=
        halts_unique (Relation.ReflTransGen.refl) h_halted h₁_steps (by simp [Config.isHalted, hp₁])
      rw [← h_refl]
    · -- p₁ is non-empty
      apply seq_steps_first h₁_steps
      · simp [Config.init]; omega
      · exact Nat.le_refl _
  -- 2. Run p₂ from ⟨0, σ⟩ to c₂, lifted to p₁.seq p₂ from ⟨p₁.length, σ⟩
  have hsteps₂_seq : Steps (p₁.seq p₂) ⟨p₁.length, σ⟩ ⟨p₁.length + c₂.pc, c₂.state⟩ := by
    have := seq_steps_second (p₁ := p₁) h₂_steps
    simp only [Nat.add_zero] at this
    exact this
  -- Combine the two execution phases
  have hsteps_combined := trans hsteps₁_seq hsteps₂_seq
  -- Show the final config is halted in p₁.seq p₂
  have hhalted_seq : (⟨p₁.length + c₂.pc, c₂.state⟩ : Config).isHalted (p₁.seq p₂) := by
    simp only [Config.isHalted, Program.seq_length]
    -- c₂.isHalted p₂ means p₂.length ≤ c₂.pc
    -- Need: p₁.length + p₂.length ≤ p₁.length + c₂.pc
    have : p₂.length ≤ c₂.pc := h₂_halted
    omega
  exact ⟨⟨p₁.length + c₂.pc, c₂.state⟩, hsteps_combined, hhalted_seq⟩

end Steps

end Urm
