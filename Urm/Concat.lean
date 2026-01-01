/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Execution
import Urm.StraightLine

/-! # Program Concatenation

This file defines program concatenation and proves basic properties about how
execution behaves in concatenated programs.

## Main definitions

- `Program.concat`: Concatenate two programs with proper jump adjustment

## Main results

- `Step.concat_left`: Steps in the first part lift to the concatenation
- `Step.concat_right`: Steps in the second part lift to the concatenation
- `Steps.concat_left_prefix`: Multi-step in first part lifts to concatenation
- `Halts.concat_left_lift`: If p1 halts, execution in p1.concat p2 reaches the same state

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Program Combinators -/

namespace Program

/-- Shifting jumps preserves program length. -/
@[simp]
theorem shiftJumps_length (offset : ℕ) (p : Program) :
    (p.shiftJumps offset).length = p.length := by
  simp [shiftJumps]

/-- Shifting jumps by 0 is the identity. -/
theorem shiftJumps_zero (p : Program) : p.shiftJumps 0 = p := by
  simp only [shiftJumps]
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons]
    cases hd <;> simp [Instr.shiftJumps, ih]

/-- Concatenate two programs, adjusting the second program's jump targets.

When concatenating `p1 ++ p2`, jumps within `p2` must be shifted by `p1.length`
to maintain correct targets in the combined program. -/
def concat (p1 p2 : Program) : Program :=
  p1 ++ p2.shiftJumps p1.length

@[simp]
theorem concat_length (p1 p2 : Program) : (p1.concat p2).length = p1.length + p2.length := by
  simp [concat]

theorem concat_nil_left (p : Program) : concat [] p = p := by
  simp [concat, shiftJumps_zero]

theorem concat_nil_right (p : Program) : concat p [] = p := by
  simp [concat, shiftJumps]

/-- Concatenation is associative. -/
theorem concat_assoc (p1 p2 p3 : Program) :
    (p1.concat p2).concat p3 = p1.concat (p2.concat p3) := by
  simp only [concat, List.append_assoc, List.length_append, shiftJumps_length]
  congr 1
  simp only [shiftJumps, List.map_append]
  congr 1
  simp only [List.map_map]
  congr 1
  funext instr
  cases instr with
  | Z n => simp [Instr.shiftJumps]
  | S n => simp [Instr.shiftJumps]
  | T m n => simp [Instr.shiftJumps]
  | J m n q => simp [Instr.shiftJumps]; omega

/-- Get instruction from concatenated program in the first part. -/
theorem getInstr_concat_left {p1 p2 : Program} (i : ℕ) (hi : i < p1.length) :
    (p1.concat p2).getInstr i = p1.getInstr i := by
  simp only [Program.concat, Program.getInstr]
  rw [List.getElem?_append_left hi]

/-- Get instruction from concatenated program in the second part (with shiftJumps). -/
theorem getInstr_concat_right {p1 p2 : Program} (i : ℕ) (hi : p1.length ≤ i)
    (_hi' : i < p1.length + p2.length) :
    (p1.concat p2).getInstr i = (p2.shiftJumps p1.length).getInstr (i - p1.length) := by
  simp only [Program.concat, Program.getInstr]
  rw [List.getElem?_append_right (by omega)]

/-- Get instruction from shifted program. -/
theorem getInstr_shiftJumps (offset : ℕ) (p : Program) (i : ℕ) :
    (p.shiftJumps offset).getInstr i = (p.getInstr i).map (Instr.shiftJumps offset) := by
  simp only [Program.shiftJumps, Program.getInstr, List.getElem?_map]

end Program

/-! ## Concatenation Step Lemmas -/

section ConcatLemmas

variable {p1 p2 : Program}

/-- Stepping in the first part of a concatenated program. -/
theorem Step.concat_left {c c' : Config} (hpc : c.pc < p1.length)
    (hstep : Step p1 c c') : Step (p1.concat p2) c c' := by
  cases hstep with
  | zero h =>
    exact Step.zero (by rw [Program.getInstr_concat_left _ hpc]; exact h)
  | succ h =>
    exact Step.succ (by rw [Program.getInstr_concat_left _ hpc]; exact h)
  | trans h =>
    exact Step.trans (by rw [Program.getInstr_concat_left _ hpc]; exact h)
  | jump_eq h heq =>
    exact Step.jump_eq (by rw [Program.getInstr_concat_left _ hpc]; exact h) heq
  | jump_ne h hne =>
    exact Step.jump_ne (by rw [Program.getInstr_concat_left _ hpc]; exact h) hne

/-- Reverse direction: stepping in concatenated program with pc in first part gives step in p1. -/
theorem Step.of_concat_left {c c' : Config} (hpc : c.pc < p1.length)
    (hstep : Step (p1.concat p2) c c') : Step p1 c c' := by
  have hinstr_eq : (p1.concat p2).getInstr c.pc = p1.getInstr c.pc :=
    Program.getInstr_concat_left c.pc hpc
  cases hstep with
  | zero h => rw [hinstr_eq] at h; exact Step.zero h
  | succ h => rw [hinstr_eq] at h; exact Step.succ h
  | trans h => rw [hinstr_eq] at h; exact Step.trans h
  | jump_eq h heq => rw [hinstr_eq] at h; exact Step.jump_eq h heq
  | jump_ne h hne => rw [hinstr_eq] at h; exact Step.jump_ne h hne

/-- Stepping in the second part of a concatenated program.
If we can step in p2 from pc=k, we can step in p1.concat p2 from pc=k+p1.length. -/
theorem Step.concat_right {c c' : Config}
    (hpc : c.pc < p2.length)
    (hstep : Step p2 c c') :
    Step (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ ⟨c'.pc + p1.length, c'.state⟩ := by
  have hlen : c.pc + p1.length < p1.length + p2.length := by omega
  have hinstr_eq : (p1.concat p2).getInstr (c.pc + p1.length) =
      (p2.shiftJumps p1.length).getInstr c.pc := by
    rw [Program.getInstr_concat_right (c.pc + p1.length) (by omega) hlen]
    simp only [Nat.add_sub_cancel]
  match hstep with
  | .zero (n := n) h =>
    have h' : (p1.concat p2).getInstr (c.pc + p1.length) = some (Instr.Z n) := by
      rw [hinstr_eq, Program.getInstr_shiftJumps, h]; rfl
    convert @Step.zero (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ n h' using 2; simp; omega
  | .succ (n := n) h =>
    have h' : (p1.concat p2).getInstr (c.pc + p1.length) = some (Instr.S n) := by
      rw [hinstr_eq, Program.getInstr_shiftJumps, h]; rfl
    convert @Step.succ (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ n h' using 2; simp; omega
  | .trans (m := m) (n := n) h =>
    have h' : (p1.concat p2).getInstr (c.pc + p1.length) = some (Instr.T m n) := by
      rw [hinstr_eq, Program.getInstr_shiftJumps, h]; rfl
    convert @Step.trans (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ m n h' using 2; simp; omega
  | .jump_eq (m := m) (n := n) (q := q) h heq =>
    have h' : (p1.concat p2).getInstr (c.pc + p1.length) = some (Instr.J m n (q + p1.length)) := by
      rw [hinstr_eq, Program.getInstr_shiftJumps, h]; rfl
    exact @Step.jump_eq (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ m n (q + p1.length) h' heq
  | .jump_ne (m := m) (n := n) (q := q) h hne =>
    have h' : (p1.concat p2).getInstr (c.pc + p1.length) = some (Instr.J m n (q + p1.length)) := by
      rw [hinstr_eq, Program.getInstr_shiftJumps, h]; rfl
    convert @Step.jump_ne (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ m n (q + p1.length) h' hne using 2; simp; omega

/-- Multi-step in the second part of a concatenated program. -/
theorem Steps.concat_right {c c' : Config}
    (hsteps : Steps p2 c c')
    (_hhalted : c'.isHalted p2) :
    Steps (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ ⟨c'.pc + p1.length, c'.state⟩ := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep hrest ih =>
    -- hstep : Step p2 a b
    -- Need: a.pc < p2.length (since a can step)
    have hpc : a.pc < p2.length := by
      by_contra hc
      simp only [not_lt] at hc
      exact Step.halted_no_step hc hstep
    have hstep' := Step.concat_right (p1 := p1) hpc hstep
    exact Relation.ReflTransGen.head hstep' ih

/-- Multi-step in the second part of a concatenated program (interior version).
Unlike concat_right, this version does NOT require the final config to be halted.
The proof works because each stepping config must have pc < p2.length. -/
theorem Steps.concat_right_interior {c c' : Config}
    (hsteps : Steps p2 c c') :
    Steps (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ ⟨c'.pc + p1.length, c'.state⟩ := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep hrest ih =>
    have hpc : a.pc < p2.length := by
      by_contra hc
      simp only [not_lt] at hc
      exact Step.halted_no_step hc hstep
    have hstep' := Step.concat_right (p1 := p1) hpc hstep
    exact Relation.ReflTransGen.head hstep' ih

/-- Multi-step from within p1 (interior version, no halting required).
The proof works because each stepping config must have pc < p1.length. -/
theorem Steps.concat_left_prefix_interior {c c' : Config}
    (hsteps : Steps p1 c c') :
    Steps (p1.concat p2) c c' := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep hrest ih =>
    have hpc : a.pc < p1.length := by
      by_contra hc
      simp only [not_lt] at hc
      exact Step.halted_no_step hc hstep
    have hstep' : Step (p1.concat p2) a b := Step.concat_left hpc hstep
    exact Relation.ReflTransGen.head hstep' ih

/-- Multi-step from within p1 stays in p1 until halting.
If we execute Steps in p1 from c to a halted config c', then the same path exists in p1.concat p2. -/
theorem Steps.concat_left_prefix {c c' : Config}
    (hsteps : Steps p1 c c') (_hhalted : c'.isHalted p1) :
    Steps (p1.concat p2) c c' :=
  Steps.concat_left_prefix_interior hsteps

/-- If p1 halts, we can lift the Steps from p1 to the concatenation. -/
theorem Halts.concat_left_lift (h : Halts p1 inputs) :
    ∃ c, Steps (p1.concat p2) (Config.init inputs) c ∧
         c.isHalted p1 ∧
         c.pc = (Classical.choose h).pc ∧
         c.state = (Classical.choose h).state := by
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec h
  refine ⟨Classical.choose h, ?_, hhalted, rfl, rfl⟩
  exact Steps.concat_left_prefix hsteps hhalted

end ConcatLemmas

end Urm
