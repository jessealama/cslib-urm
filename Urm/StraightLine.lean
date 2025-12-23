/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Execution

/-! # Straight-Line Programs

This file defines straight-line programs (those without jumps) and proves that
they always halt exactly at their length.

## Main definitions

- `Instr.isNonJumping`: predicate for Z, S, T instructions (not J)
- `Program.isStraightLine`: a program contains no jump instructions

## Main results

- `straightLine_halts`: straight-line programs always halt
- `straightLine_halts_at_length`: they halt exactly at program length

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Straight-Line Programs -/

/-- An instruction is "non-jumping" if it's Z, S, or T (not J). -/
def Instr.isNonJumping : Instr → Bool
  | Instr.Z _ => true
  | Instr.S _ => true
  | Instr.T _ _ => true
  | Instr.J _ _ _ => false

/-- A program is "straight-line" if it contains no jump instructions. -/
def Program.isStraightLine (p : Program) : Bool :=
  p.all Instr.isNonJumping

/-- shiftJumps is identity for non-jumping instructions. -/
theorem Instr.shiftJumps_of_isNonJumping {instr : Instr} (h : instr.isNonJumping = true) (offset : ℕ) :
    instr.shiftJumps offset = instr := by
  cases instr with
  | Z n => rfl
  | S n => rfl
  | T m n => rfl
  | J m n q => simp [isNonJumping] at h

/-- shiftJumps is identity for straight-line programs. -/
theorem Program.shiftJumps_of_isStraightLine {p : Program} (h : p.isStraightLine = true) (offset : ℕ) :
    p.shiftJumps offset = p := by
  simp only [Program.shiftJumps]
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons]
    simp only [Program.isStraightLine, List.all_cons, Bool.and_eq_true] at h
    rw [Instr.shiftJumps_of_isNonJumping h.1 offset, ih h.2]

/-- Stepping through a non-jumping instruction increases pc by 1. -/
theorem Step.nonJumping_pc_inc {p : Program} {c c' : Config} {instr : Instr}
    (hstep : Step p c c')
    (hinstr : p.getInstr c.pc = some instr)
    (hnonjump : instr.isNonJumping = true) :
    c'.pc = c.pc + 1 := by
  cases hstep with
  | zero h => simp_all [Program.getInstr]
  | succ h => simp_all [Program.getInstr]
  | trans h => simp_all [Program.getInstr]
  | jump_eq h _ => simp_all [Instr.isNonJumping, Program.getInstr]
  | jump_ne h _ => simp_all [Instr.isNonJumping, Program.getInstr]

/-- A straight-line program halts on any input (pc always increases until it exceeds length). -/
theorem straightLine_halts {p : Program} (hsl : p.isStraightLine = true) (inputs : List ℕ) :
    Halts p inputs := by
  -- We show that in at most p.length steps, pc reaches p.length
  -- Use strong induction on remaining instructions
  suffices h : ∀ (c : Config), c.pc ≤ p.length →
      ∃ c', Steps p c c' ∧ c'.pc ≥ p.length by
    obtain ⟨c', hsteps, hpc⟩ := h (Config.init inputs) (by simp [Config.init])
    exact ⟨c', hsteps, hpc⟩
  intro c hpc_le
  -- Induction on p.length - c.pc (remaining steps)
  generalize hrem : p.length - c.pc = remaining
  induction remaining using Nat.strong_induction_on generalizing c with
  | _ remaining ih =>
    by_cases hhalted : c.pc ≥ p.length
    · -- Already halted
      exact ⟨c, Relation.ReflTransGen.refl, hhalted⟩
    · -- Can take a step
      push_neg at hhalted
      have hpc_lt : c.pc < p.length := hhalted
      have hinstr : ∃ instr, p.getInstr c.pc = some instr := by
        simp only [Program.getInstr]
        exact ⟨p[c.pc], List.getElem?_eq_getElem hpc_lt⟩
      obtain ⟨instr, hinstr⟩ := hinstr
      have hnonjump : instr.isNonJumping = true := by
        simp only [Program.isStraightLine, List.all_eq_true] at hsl
        have hmem : instr ∈ p := by
          simp only [Program.getInstr] at hinstr
          exact List.getElem?_eq_some_iff.mp hinstr |>.2 ▸ List.getElem_mem hpc_lt
        exact hsl instr hmem
      have hstep : ∃ c', Step p c c' ∧ c'.pc = c.pc + 1 := by
        cases instr with
        | Z n => exact ⟨⟨c.pc + 1, c.state.write n 0⟩, Step.zero hinstr, rfl⟩
        | S n => exact ⟨⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩, Step.succ hinstr, rfl⟩
        | T m n =>
          exact ⟨⟨c.pc + 1, c.state.write n (c.state.read m)⟩, Step.trans hinstr, rfl⟩
        | J m n q =>
          simp [Instr.isNonJumping] at hnonjump
      obtain ⟨c', hstep', hpc'⟩ := hstep
      -- Apply IH with smaller remaining count
      have hremaining : p.length - c'.pc < remaining := by omega
      have hpc'_le : c'.pc ≤ p.length := by omega
      obtain ⟨c'', hsteps'', hpc''⟩ := ih (p.length - c'.pc) hremaining c' hpc'_le rfl
      exact ⟨c'', Relation.ReflTransGen.head hstep' hsteps'', hpc''⟩

/-- For straight-line programs, the halted config has pc exactly equal to the program length.

Since straight-line programs can only advance pc by 1, and halting means pc ≥ length,
the pc must be exactly length when halted. -/
theorem straightLine_halts_at_length {p : Program} (hsl : p.isStraightLine = true) (inputs : List ℕ) :
    let h := straightLine_halts hsl inputs
    (Classical.choose h).pc = p.length := by
  have h := straightLine_halts hsl inputs
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec h
  simp only [Config.isHalted] at hhalted
  -- Show pc ≤ p.length by showing pc can never exceed p.length from stepping
  -- Each step of a straight-line program increases pc by exactly 1
  suffices hsuff : ∀ c c' : Config, Steps p c c' → c'.pc ≤ max c.pc p.length by
    have := hsuff (Config.init inputs) (Classical.choose h) hsteps
    simp only [Config.init] at this
    omega
  intro c c' hsteps'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl => omega
  | head hstep _ ih =>
    -- Each step increases pc by 1 for non-jumping instructions
    -- Now handle each case
    cases hstep with
    | zero hinstr =>
      simp only [Program.getInstr] at hinstr
      have hpc_lt := List.getElem?_eq_some_iff.mp hinstr |>.1
      simp only at ih ⊢
      omega
    | succ hinstr =>
      simp only [Program.getInstr] at hinstr
      have hpc_lt := List.getElem?_eq_some_iff.mp hinstr |>.1
      simp only at ih ⊢
      omega
    | trans hinstr =>
      simp only [Program.getInstr] at hinstr
      have hpc_lt := List.getElem?_eq_some_iff.mp hinstr |>.1
      simp only at ih ⊢
      omega
    | jump_eq hinstr _ =>
      -- Jump instructions don't appear in straight-line programs
      simp only [Program.getInstr] at hinstr
      have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
      have hmem : (Instr.J _ _ _) ∈ p := heq ▸ List.getElem_mem hlt
      simp only [Program.isStraightLine, List.all_eq_true] at hsl
      exact absurd (hsl _ hmem) (by simp [Instr.isNonJumping])
    | jump_ne hinstr _ =>
      -- Jump instructions don't appear in straight-line programs
      simp only [Program.getInstr] at hinstr
      have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
      have hmem : (Instr.J _ _ _) ∈ p := heq ▸ List.getElem_mem hlt
      simp only [Program.isStraightLine, List.all_eq_true] at hsl
      exact absurd (hsl _ hmem) (by simp [Instr.isNonJumping])

end Urm
