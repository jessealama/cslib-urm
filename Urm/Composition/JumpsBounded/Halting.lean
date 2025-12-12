/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.JumpsBounded.Seq

/-! # JumpsBounded: Halting Properties

This file proves that JumpsBounded programs halt at exactly pc = p.length.

## Main statements

- `Urm.JumpsBounded.halts_at_length`: Halted JumpsBounded programs have pc = p.length
- `Urm.JumpsBounded.halts_reaches_end`: Extract final state from halting execution
-/

namespace Urm

namespace JumpsBounded

variable {p : Program}

/-- Helper: stepping preserves the invariant pc ≤ p.length when jumps are bounded. -/
private theorem step_preserves_pc_bound (hbounded : JumpsBounded p)
    {c c' : Config} (hstep : Step p c c') (_h : c.pc ≤ p.length) : c'.pc ≤ p.length := by
  -- For non-jump steps: c'.pc = c.pc + 1, and c.pc < p.length (since we can step)
  -- For jump steps: c'.pc = q, and q ≤ p.length by boundedness
  cases hstep with
  | zero hinstr =>
    have hpc := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega
  | succ hinstr =>
    have hpc := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega
  | trans hinstr =>
    have hpc := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega
  | jump_eq hinstr _ =>
    have hpc := (List.getElem?_eq_some_iff.mp hinstr).1
    exact hbounded _ hpc _ _ _ hinstr
  | jump_ne hinstr _ =>
    have hpc := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega

/-- Helper: all configs reachable from init have pc ≤ p.length when jumps are bounded. -/
private theorem pc_le_length_of_steps (hbounded : JumpsBounded p)
    {c₀ c : Config} (hsteps : Steps p c₀ c) (h₀ : c₀.pc ≤ p.length) :
    c.pc ≤ p.length := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact h₀
  | head hstep _hrest ih =>
    exact ih (step_preserves_pc_bound hbounded hstep h₀)

/-- If a program has bounded jumps and halts, it halts at exactly pc = p.length. -/
theorem halts_at_length (hbounded : JumpsBounded p)
    {inputs : List ℕ} {c : Config}
    (hsteps : Steps p (Config.init inputs) c) (hhalted : c.isHalted p) :
    c.pc = p.length := by
  have h_ge : p.length ≤ c.pc := hhalted
  have h_le : c.pc ≤ p.length := by
    apply pc_le_length_of_steps hbounded hsteps
    simp [Config.init]
  omega

/-- For a JumpsBounded program that halts, extract the final state and prove
    we reach ⟨p.length, σ⟩. This combines Classical.choose, halts_at_length,
    and the config reconstruction. -/
theorem halts_reaches_end (hbounded : JumpsBounded p) {inputs : List ℕ}
    (hHalts : Halts p inputs) :
    ∃ σ : State, Steps p (Config.init inputs) ⟨p.length, σ⟩ := by
  obtain ⟨c, hsteps, hhalted⟩ := hHalts
  have hat_length := halts_at_length hbounded hsteps hhalted
  refine ⟨c.state, ?_⟩
  cases c with | mk pc state =>
  simp only at hat_length ⊢
  rw [hat_length] at hsteps
  exact hsteps

end JumpsBounded

end Urm
