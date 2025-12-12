/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.JumpsBounded.Basic

/-! # JumpsBounded: Sequential Composition and Shifting

This file proves JumpsBounded is preserved under seq, append, and shifting.

## Main statements

- `Urm.JumpsBounded.seq`: Sequential composition preserves JumpsBounded
- `Urm.JumpsBounded.append`: Append preserves JumpsBounded
- `Urm.JumpsBounded.shiftJumps_bounded_with_offset`: Shifting preserves bounded jumps
-/

namespace Urm

namespace JumpsBounded

variable {p p₁ p₂ : Program}

/-- Sequential composition of JumpsBounded programs is JumpsBounded. -/
theorem seq (h₁ : JumpsBounded p₁) (h₂ : JumpsBounded p₂) : JumpsBounded (p₁.seq p₂) := by
  intro i hi m n q hinstr
  simp only [Program.seq_length] at hi
  by_cases hlt : i < p₁.length
  · -- In first program region
    rw [Program.seq_getInstr_first p₁ p₂ i hlt] at hinstr
    have hbound := h₁ i hlt m n q hinstr
    simp only [Program.seq_length]
    omega
  · -- In second program region
    have hge : p₁.length ≤ i := Nat.not_lt.mp hlt
    rw [Program.seq_getInstr_second p₁ p₂ i hge hi] at hinstr
    simp only [Program.shiftJumps, Program.getInstr, List.getElem?_map] at hinstr
    have hi' : i - p₁.length < p₂.length := by omega
    rw [List.getElem?_eq_getElem hi'] at hinstr
    simp only [Option.map_some, Option.some.injEq] at hinstr
    -- The instruction is shifted, so need to unfold shiftJumps
    generalize h : p₂[i - p₁.length] = instr at hinstr
    cases instr with
    | Z _ => simp only [Instr.shiftJumps, reduceCtorEq] at hinstr
    | S _ => simp only [Instr.shiftJumps, reduceCtorEq] at hinstr
    | T _ _ => simp only [Instr.shiftJumps, reduceCtorEq] at hinstr
    | J jm jn jq =>
      simp only [Instr.shiftJumps, Instr.J.injEq] at hinstr
      obtain ⟨rfl, rfl, rfl⟩ := hinstr
      -- Original instruction at i - p₁.length is J jm jn jq
      have hinstr' : p₂.getInstr (i - p₁.length) = some (Instr.J jm jn jq) := by
        simp only [Program.getInstr]
        rw [List.getElem?_eq_getElem hi']
        simp only [h]
      have hbound := h₂ (i - p₁.length) hi' jm jn jq hinstr'
      simp only [Program.seq_length]
      omega

/-- Appending programs preserves JumpsBounded (for the first program's part). -/
theorem append (h₁ : JumpsBounded p₁) (h₂ : JumpsBounded p₂) : JumpsBounded (p₁ ++ p₂) := by
  intro i hi m n q hinstr
  simp only [List.length_append] at hi ⊢
  by_cases hlt : i < p₁.length
  · -- Instruction from first program
    simp only [Program.getInstr, List.getElem?_append_left hlt] at hinstr
    have hbound := h₁ i hlt m n q hinstr
    omega
  · -- Instruction from second program; note: jumps NOT shifted, so this is bounded by p₂.length
    have hge : p₁.length ≤ i := Nat.not_lt.mp hlt
    have hi' : i - p₁.length < p₂.length := by omega
    simp only [Program.getInstr, List.getElem?_append_right hge] at hinstr
    have hbound := h₂ (i - p₁.length) hi' m n q hinstr
    omega

/-- shiftJumps preserves JumpsBounded when offset is added to length bound.
    Used for sequential composition where p₂.shiftJumps p₁.length is appended to p₁. -/
theorem shiftJumps_bounded_with_offset (h : JumpsBounded p) (offset : ℕ) :
    ∀ i < (p.shiftJumps offset).length, ∀ m n q,
      (p.shiftJumps offset).getInstr i = some (Instr.J m n q) →
      q ≤ p.length + offset := by
  intro i hi m n q hinstr
  simp only [Program.shiftJumps, List.length_map] at hi
  have hi' : i < p.length := hi
  simp only [Program.getInstr, Program.shiftJumps] at hinstr
  rw [List.getElem?_map] at hinstr
  cases hget : p[i]? with
  | none =>
    rw [hget] at hinstr
    simp at hinstr
  | some instr =>
    rw [hget] at hinstr
    simp only [Option.map_some] at hinstr
    cases instr with
    | J m' n' q' =>
      simp only [Instr.shiftJumps, Option.some.injEq] at hinstr
      obtain ⟨rfl, rfl, rfl⟩ := hinstr
      have hbound := h i hi' m n q' (by simp [Program.getInstr, hget])
      omega
    | Z _ => simp [Instr.shiftJumps] at hinstr
    | S _ => simp [Instr.shiftJumps] at hinstr
    | T _ _ => simp [Instr.shiftJumps] at hinstr

end JumpsBounded

end Urm
