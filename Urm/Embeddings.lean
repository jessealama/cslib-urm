/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Concat

/-! # Program Embedding Lemmas

This file provides lemmas for lifting execution steps from a subprogram
to a larger program when the subprogram is embedded at an offset.

These lemmas are useful for composition and minimization proofs where
subprograms are concatenated into larger programs.
-/

namespace Urm

open Program

/-- A single Step in p corresponds to a Step in P when p is embedded at offset k in P.
    Requires p to be straight-line (no jumps) so the PC offset is preserved correctly. -/
theorem Step.at_offset {p P : Program} {c c' : Config} (k : ℕ)
    (hsl : p.isStraightLine = true)
    (hembed : ∀ i, i < p.length → P[k + i]? = p[i]?)
    (hstep : Step p c c')
    (hpc_bound : c.pc < p.length) :
    Step P ⟨k + c.pc, c.state⟩ ⟨k + c'.pc, c'.state⟩ := by
  have hinstr : P[k + c.pc]? = p[c.pc]? := hembed c.pc hpc_bound
  cases hstep with
  | zero h =>
    have h' : P[k + c.pc]? = some (Instr.Z _) := hinstr ▸ h
    have hstep' : Step P ⟨k + c.pc, c.state⟩ ⟨k + c.pc + 1, c.state.write _ 0⟩ := Step.zero h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | succ h =>
    have h' : P[k + c.pc]? = some (Instr.S _) := hinstr ▸ h
    have hstep' : Step P ⟨k + c.pc, c.state⟩ ⟨k + c.pc + 1, _⟩ := Step.succ h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | trans h =>
    have h' : P[k + c.pc]? = some (Instr.T _ _) := hinstr ▸ h
    have hstep' : Step P ⟨k + c.pc, c.state⟩ ⟨k + c.pc + 1, _⟩ := Step.trans h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | jump_eq h _ =>
    -- Can't happen: straight-line programs have no jumps
    have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact absurd (hsl _ (heq ▸ List.getElem_mem hlt)) (by simp [Instr.isNonJumping])
  | jump_ne h _ =>
    -- Can't happen: straight-line programs have no jumps
    have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact absurd (hsl _ (heq ▸ List.getElem_mem hlt)) (by simp [Instr.isNonJumping])

/-- Steps in a straight-line p lift to Steps in P at offset k. -/
theorem Steps.straightLine_at_offset {p P : Program} {c c' : Config} (k : ℕ)
    (hsl : p.isStraightLine = true)
    (hembed : ∀ i, i < p.length → P[k + i]? = p[i]?)
    (hsteps : Steps p c c') :
    Steps P ⟨k + c.pc, c.state⟩ ⟨k + c'.pc, c'.state⟩ := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep _ ih =>
    have hpc_bound := Step.pc_lt_length hstep
    have hstep' := Step.at_offset k hsl hembed hstep hpc_bound
    exact Relation.ReflTransGen.head hstep' ih

/-- A step in p lifts to a step in P when p.shiftJumps(offset) is embedded at offset in P. -/
theorem Step.shiftJumps_at_offset {p P : Program} {c c' : Config} (offset : ℕ)
    (hembed : ∀ i, i < p.length → P[offset + i]? = (p.shiftJumps offset)[i]?)
    (hstep : Step p c c')
    (hpc_bound : c.pc < p.length) :
    Step P ⟨offset + c.pc, c.state⟩ ⟨offset + c'.pc, c'.state⟩ := by
  have hinstr_eq : P[offset + c.pc]? = (p.shiftJumps offset)[c.pc]? :=
    hembed c.pc hpc_bound
  match hstep with
  | .zero (n := n) h =>
    have h' : P[offset + c.pc]? = some (Instr.Z n) := by
      rw [hinstr_eq, Program.getElem?_shiftJumps, h]; rfl
    have hstep' : Step P ⟨offset + c.pc, c.state⟩ ⟨offset + c.pc + 1, c.state.write n 0⟩ := Step.zero h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | .succ (n := n) h =>
    have h' : P[offset + c.pc]? = some (Instr.S n) := by
      rw [hinstr_eq, Program.getElem?_shiftJumps, h]; rfl
    have hstep' : Step P ⟨offset + c.pc, c.state⟩ ⟨offset + c.pc + 1, _⟩ := Step.succ h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | .trans (m := m) (n := n) h =>
    have h' : P[offset + c.pc]? = some (Instr.T m n) := by
      rw [hinstr_eq, Program.getElem?_shiftJumps, h]; rfl
    have hstep' : Step P ⟨offset + c.pc, c.state⟩ ⟨offset + c.pc + 1, _⟩ := Step.trans h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | .jump_eq (m := m) (n := n) (q := q) h heq =>
    have h' : P[offset + c.pc]? = some (Instr.J m n (q + offset)) := by
      rw [hinstr_eq, Program.getElem?_shiftJumps, h]; rfl
    have hstep' := @Step.jump_eq P ⟨offset + c.pc, c.state⟩ m n (q + offset) h' heq
    simp only [Nat.add_comm q offset] at hstep'; exact hstep'
  | .jump_ne (m := m) (n := n) (q := q) h hne =>
    have h' : P[offset + c.pc]? = some (Instr.J m n (q + offset)) := by
      rw [hinstr_eq, Program.getElem?_shiftJumps, h]; rfl
    have hstep' : Step P ⟨offset + c.pc, c.state⟩ ⟨offset + c.pc + 1, c.state⟩ := Step.jump_ne h' hne
    simp only [Nat.add_assoc] at hstep'; exact hstep'

/-- Steps in p lift to steps in P when p.shiftJumps(offset) is embedded at offset in P. -/
theorem Steps.shiftJumps_at_offset {p P : Program} {c c' : Config} (offset : ℕ)
    (hembed : ∀ i, i < p.length → P[offset + i]? = (p.shiftJumps offset)[i]?)
    (hsteps : Steps p c c') :
    Steps P ⟨offset + c.pc, c.state⟩ ⟨offset + c'.pc, c'.state⟩ := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep _ ih =>
    have hpc_bound := Step.pc_lt_length hstep
    have hstep' := Step.shiftJumps_at_offset offset hembed hstep hpc_bound
    exact Relation.ReflTransGen.head hstep' ih

end Urm
