/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Execution
import Urm.StraightLine
import Mathlib.Algebra.Group.Defs

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
theorem shift_jumps_length (offset : ℕ) (p : Program) :
    (p.shift_jumps offset).length = p.length := by
  simp [shift_jumps]

/-- Shifting jumps by 0 is the identity. -/
theorem shift_jumps_zero (p : Program) : p.shift_jumps 0 = p := by
  simp only [shift_jumps]
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons]
    cases hd <;> simp [Instr.shift_jumps, ih]

/-- Concatenate two programs, adjusting the second program's jump targets.

When concatenating `p1 ++ p2`, jumps within `p2` must be shifted by `p1.length`
to maintain correct targets in the combined program. -/
def concat (p1 p2 : Program) : Program :=
  p1 ++ p2.shift_jumps p1.length

@[simp]
theorem concat_length (p1 p2 : Program) : (p1.concat p2).length = p1.length + p2.length := by
  simp [concat]

theorem concat_nil_left (p : Program) : concat [] p = p := by
  simp [concat, shift_jumps_zero]

theorem concat_nil_right (p : Program) : concat p [] = p := by
  simp [concat, shift_jumps]

/-- Concatenation is associative. -/
theorem concat_assoc (p1 p2 p3 : Program) :
    (p1.concat p2).concat p3 = p1.concat (p2.concat p3) := by
  simp only [concat, List.append_assoc, List.length_append, shift_jumps_length]
  congr 1
  simp only [shift_jumps, List.map_append, List.map_map]
  congr 1
  apply List.map_eq_map_iff.mpr
  intro instr _
  cases instr <;> simp [Instr.shift_jumps]; omega

/-- Program concatenation forms a semigroup.
Note: This uses `concat` (which shifts jumps), not raw list append. -/
instance : Semigroup Program where
  mul := concat
  mul_assoc := concat_assoc

/-- Program concatenation forms a monoid with empty program as identity. -/
instance : Monoid Program where
  one := []
  one_mul := concat_nil_left
  mul_one := concat_nil_right

/-- Relates `.concat` to `*` for algebraic automation.
Use with `simp only [concat_eq_mul, mul_assoc]` to leverage Monoid associativity. -/
theorem concat_eq_mul (p q : Program) : p.concat q = p * q := rfl

/-- Get instruction from concatenated program in the first part. -/
@[simp]
theorem getElem?_concat_of_lt {p1 p2 : Program} (i : ℕ) (hi : i < p1.length) :
    (p1.concat p2)[i]? = p1[i]? := by
  simp only [Program.concat]
  rw [List.getElem?_append_left hi]

/-- Get instruction from concatenated program in the second part (with shift_jumps). -/
@[simp]
theorem getElem?_concat_of_ge {p1 p2 : Program} (i : ℕ) (hi : p1.length ≤ i) :
    (p1.concat p2)[i]? = (p2.shift_jumps p1.length)[i - p1.length]? := by
  simp only [Program.concat]
  rw [List.getElem?_append_right (by omega)]

/-- Get instruction from shifted program. -/
@[simp]
theorem getElem?_shift_jumps (offset : ℕ) (p : Program) (i : ℕ) :
    (p.shift_jumps offset)[i]? = p[i]?.map (Instr.shift_jumps offset) := by
  simp only [Program.shift_jumps, List.getElem?_map]

end Program

/-! ## Concatenation Step Lemmas -/

section ConcatLemmas

variable {p1 p2 : Program}

/-- Stepping in the first part of a concatenated program. -/
theorem Step.concat_left {c c' : Config} (hpc : c.pc < p1.length)
    (hstep : Step p1 c c') : Step (p1.concat p2) c c' := by
  have hinstr : (p1.concat p2)[c.pc]? = p1[c.pc]? := Program.getElem?_concat_of_lt _ hpc
  cases hstep with
  | zero h => exact Step.zero (hinstr ▸ h)
  | succ h => exact Step.succ (hinstr ▸ h)
  | trans h => exact Step.trans (hinstr ▸ h)
  | jump_eq h heq => exact Step.jump_eq (hinstr ▸ h) heq
  | jump_ne h hne => exact Step.jump_ne (hinstr ▸ h) hne

/-- Reverse direction: stepping in concatenated program with pc in first part gives step in p1. -/
theorem Step.of_concat_left {c c' : Config} (hpc : c.pc < p1.length)
    (hstep : Step (p1.concat p2) c c') : Step p1 c c' := by
  have hinstr_eq : (p1.concat p2)[c.pc]? = p1[c.pc]? :=
    Program.getElem?_concat_of_lt c.pc hpc
  cases hstep with
  | zero h => rw [hinstr_eq] at h; exact Step.zero h
  | succ h => rw [hinstr_eq] at h; exact Step.succ h
  | trans h => rw [hinstr_eq] at h; exact Step.trans h
  | jump_eq h heq => rw [hinstr_eq] at h; exact Step.jump_eq h heq
  | jump_ne h hne => rw [hinstr_eq] at h; exact Step.jump_ne h hne

/-- Stepping in the second part of a concatenated program.
If we can step in p2 from pc=k, we can step in p1.concat p2 from pc=k+p1.length. -/
theorem Step.concat_right {c c' : Config}
    (hstep : Step p2 c c') :
    Step (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ ⟨c'.pc + p1.length, c'.state⟩ := by
  have hinstr_eq : (p1.concat p2)[c.pc + p1.length]? =
      (p2.shift_jumps p1.length)[c.pc]? := by
    rw [Program.getElem?_concat_of_ge (c.pc + p1.length) (by omega)]
    simp only [Nat.add_sub_cancel]
  match hstep with
  | .zero (n := n) h =>
    have h' : (p1.concat p2)[c.pc + p1.length]? = some (Instr.Z n) := by
      rw [hinstr_eq, Program.getElem?_shift_jumps, h]; rfl
    convert @Step.zero (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ n h' using 2; simp; omega
  | .succ (n := n) h =>
    have h' : (p1.concat p2)[c.pc + p1.length]? = some (Instr.S n) := by
      rw [hinstr_eq, Program.getElem?_shift_jumps, h]; rfl
    convert @Step.succ (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ n h' using 2; simp; omega
  | .trans (m := m) (n := n) h =>
    have h' : (p1.concat p2)[c.pc + p1.length]? = some (Instr.T m n) := by
      rw [hinstr_eq, Program.getElem?_shift_jumps, h]; rfl
    convert @Step.trans (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ m n h' using 2; simp; omega
  | .jump_eq (m := m) (n := n) (q := q) h heq =>
    have h' : (p1.concat p2)[c.pc + p1.length]? = some (Instr.J m n (q + p1.length)) := by
      rw [hinstr_eq, Program.getElem?_shift_jumps, h]; rfl
    exact @Step.jump_eq (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ m n (q + p1.length) h' heq
  | .jump_ne (m := m) (n := n) (q := q) h hne =>
    have h' : (p1.concat p2)[c.pc + p1.length]? = some (Instr.J m n (q + p1.length)) := by
      rw [hinstr_eq, Program.getElem?_shift_jumps, h]; rfl
    convert @Step.jump_ne (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ m n (q + p1.length) h' hne using 2; simp; omega

/-- Multi-step in the second part of a concatenated program. -/
theorem Steps.concat_right {c c' : Config}
    (hsteps : Steps p2 c c') :
    Steps (p1.concat p2) ⟨c.pc + p1.length, c.state⟩ ⟨c'.pc + p1.length, c'.state⟩ := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep hrest ih =>
    have hstep' := Step.concat_right (p1 := p1) hstep
    exact Relation.ReflTransGen.head hstep' ih

/-- Multi-step from within p1 (interior version, no halting required).
The proof works because each stepping config must have pc < p1.length. -/
theorem Steps.concat_left_prefix_interior {c c' : Config}
    (hsteps : Steps p1 c c') :
    Steps (p1.concat p2) c c' := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep hrest ih =>
    exact Relation.ReflTransGen.head (Step.concat_left (Step.pc_lt_length hstep) hstep) ih

/-- Multi-step from within p1 stays in p1 until halting.
If we execute Steps in p1 from c to a halted config c', then the same path exists in p1.concat p2. -/
theorem Steps.concat_left_prefix {c c' : Config}
    (hsteps : Steps p1 c c') :
    Steps (p1.concat p2) c c' :=
  Steps.concat_left_prefix_interior hsteps

/-- If p1 halts, we can lift the Steps from p1 to the concatenation. -/
theorem Halts.concat_left_lift (h : Halts p1 inputs) :
    ∃ c, Steps (p1.concat p2) (Config.init inputs) c ∧
         c.is_halted p1 ∧
         c.pc = (Classical.choose h).pc ∧
         c.state = (Classical.choose h).state := by
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec h
  refine ⟨Classical.choose h, ?_, hhalted, rfl, rfl⟩
  exact Steps.concat_left_prefix hsteps

end ConcatLemmas

end Urm
