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

/-- Straight-line programs halt from any starting state, not just Config.init.
This is key for chaining: after running one program, we can run the next
straight-line segment from whatever state we're in. -/
theorem straightLine_halts_from_state {p : Program} (hsl : p.isStraightLine = true) (s : State) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.isHalted p ∧ c.pc = p.length := by
  -- Induction on remaining instructions
  suffices h : ∀ (c : Config), c.pc ≤ p.length →
      ∃ c', Steps p c c' ∧ c'.pc = p.length by
    obtain ⟨c', hsteps, hpc'⟩ := h ⟨0, s⟩ (Nat.zero_le _)
    exact ⟨c', hsteps, Nat.le_of_eq hpc'.symm, hpc'⟩
  intro c hpc_le
  generalize hrem : p.length - c.pc = remaining
  induction remaining using Nat.strong_induction_on generalizing c with
  | _ remaining ih =>
    by_cases hhalted : c.pc ≥ p.length
    · exact ⟨c, Relation.ReflTransGen.refl, by omega⟩
    · push_neg at hhalted
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
        | T m n => exact ⟨⟨c.pc + 1, c.state.write n (c.state.read m)⟩, Step.trans hinstr, rfl⟩
        | J m n q => simp [Instr.isNonJumping] at hnonjump
      obtain ⟨c', hstep', hpc'⟩ := hstep
      have hremaining : p.length - c'.pc < remaining := by omega
      have hpc'_le : c'.pc ≤ p.length := by omega
      obtain ⟨c'', hsteps'', hpc''⟩ := ih (p.length - c'.pc) hremaining c' hpc'_le rfl
      exact ⟨c'', Relation.ReflTransGen.head hstep' hsteps'', hpc''⟩

/-- The final state after running a straight-line program from a given starting state.
This is the relational-semantics version that replaces the functional `executeStraightLine`. -/
noncomputable def straightLineFinalState {p : Program} (hsl : p.isStraightLine = true) (s : State) : State :=
  (Classical.choose (straightLine_halts_from_state hsl s)).state

/-- The final config from straightLineFinalState satisfies the expected properties. -/
theorem straightLineFinalState_spec {p : Program} (hsl : p.isStraightLine = true) (s : State) :
    let c := Classical.choose (straightLine_halts_from_state hsl s)
    Steps p ⟨0, s⟩ c ∧ c.isHalted p ∧ c.pc = p.length :=
  Classical.choose_spec (straightLine_halts_from_state hsl s)

/-- In a straight-line program, we can characterize the state at any intermediate pc.
This gives us the configuration after executing instructions 0..pc-1. -/
theorem straightLine_state_at_pc {p : Program} (hsl : p.isStraightLine = true)
    (s : State) (targetPc : ℕ) (htarget : targetPc ≤ p.length) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = targetPc := by
  induction targetPc with
  | zero => exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, rfl⟩
  | succ n ih =>
    have hn_le : n ≤ p.length := Nat.le_of_succ_le htarget
    obtain ⟨c_n, hsteps_n, hpc_n⟩ := ih hn_le
    have hn_lt : n < p.length := Nat.lt_of_succ_le htarget
    have hinstr : ∃ instr, p.getInstr n = some instr := by
      simp only [Program.getInstr]
      exact ⟨p[n], List.getElem?_eq_getElem hn_lt⟩
    obtain ⟨instr, hinstr⟩ := hinstr
    have hnonjump : instr.isNonJumping = true := by
      simp only [Program.isStraightLine, List.all_eq_true] at hsl
      have hmem : instr ∈ p := by
        simp only [Program.getInstr] at hinstr
        exact List.getElem?_eq_some_iff.mp hinstr |>.2 ▸ List.getElem_mem hn_lt
      exact hsl instr hmem
    -- Convert hinstr to use c_n.pc
    have hinstr' : p.getInstr c_n.pc = some instr := by rw [hpc_n]; exact hinstr
    have hstep : ∃ c', Step p c_n c' ∧ c'.pc = n + 1 := by
      cases instr with
      | Z m =>
        refine ⟨⟨c_n.pc + 1, c_n.state.write m 0⟩, Step.zero hinstr', ?_⟩
        rw [hpc_n]
      | S m =>
        refine ⟨⟨c_n.pc + 1, c_n.state.write m (c_n.state.read m + 1)⟩, Step.succ hinstr', ?_⟩
        rw [hpc_n]
      | T m1 m2 =>
        refine ⟨⟨c_n.pc + 1, c_n.state.write m2 (c_n.state.read m1)⟩, Step.trans hinstr', ?_⟩
        rw [hpc_n]
      | J _ _ _ => simp [Instr.isNonJumping] at hnonjump
    obtain ⟨c', hstep', hpc'⟩ := hstep
    exact ⟨c', Relation.ReflTransGen.tail hsteps_n hstep', hpc'⟩

/-- A single step in a straight-line program modifies at most one register. -/
theorem Step.straightLine_preserves {p : Program} {c c' : Config} {r : ℕ}
    (hsl : p.isStraightLine = true) (hstep : Step p c c')
    (hr : ∀ instr, p.getInstr c.pc = some instr → instr.writesTo ≠ some r) :
    c'.state.read r = c.state.read r := by
  cases hstep with
  | zero hinstr =>
    have := hr _ hinstr
    simp only [Instr.writesTo, ne_eq, Option.some.injEq] at this
    simp only [State.read, State.write]
    exact Function.update_of_ne (Ne.symm this) _ _
  | succ hinstr =>
    have := hr _ hinstr
    simp only [Instr.writesTo, ne_eq, Option.some.injEq] at this
    simp only [State.read, State.write]
    exact Function.update_of_ne (Ne.symm this) _ _
  | trans hinstr =>
    have := hr _ hinstr
    simp only [Instr.writesTo, ne_eq, Option.some.injEq] at this
    simp only [State.read, State.write]
    exact Function.update_of_ne (Ne.symm this) _ _
  | jump_eq hinstr _ =>
    -- Jump in a straight-line program is a contradiction
    simp only [Program.getInstr] at hinstr
    have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
    have hmem : (Instr.J _ _ _) ∈ p := heq ▸ List.getElem_mem hlt
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact absurd (hsl _ hmem) (by simp [Instr.isNonJumping])
  | jump_ne hinstr _ =>
    simp only [Program.getInstr] at hinstr
    have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
    have hmem : (Instr.J _ _ _) ∈ p := heq ▸ List.getElem_mem hlt
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact absurd (hsl _ hmem) (by simp [Instr.isNonJumping])

/-- Multi-step execution preserves registers not written by any instruction. -/
theorem Steps.straightLine_preserves {p : Program} {c c' : Config} {r : ℕ}
    (hsl : p.isStraightLine = true) (hsteps : Steps p c c')
    (hr : ∀ instr, instr ∈ p → instr.writesTo ≠ some r) :
    c'.state.read r = c.state.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
    rw [ih]
    apply Step.straightLine_preserves hsl hstep
    intro instr hinstr
    apply hr
    simp only [Program.getInstr] at hinstr
    exact List.mem_of_getElem? hinstr

/-! ## clearRegistersFrom: Clear registers starting from a given index -/

namespace Program

/-- Clear registers from `start` to `start + count - 1`.
Unlike `clearRegisters` which clears from 0, this allows preserving lower registers. -/
def clearRegistersFrom (start count : ℕ) : Program :=
  (List.range count).map (fun i => Instr.Z (start + i))

@[simp]
theorem clearRegistersFrom_length (start count : ℕ) :
    (clearRegistersFrom start count).length = count := by
  simp [clearRegistersFrom]

theorem clearRegistersFrom_zero (start : ℕ) : clearRegistersFrom start 0 = [] := rfl

theorem clearRegistersFrom_isStraightLine (start count : ℕ) :
    (clearRegistersFrom start count).isStraightLine = true := by
  simp only [clearRegistersFrom, isStraightLine, List.all_map]
  induction count with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.all_append, List.all_cons, List.all_nil,
               and_true, Bool.and_eq_true]
    constructor
    · -- Show all elements in range n satisfy the predicate
      simp only [List.all_eq_true]
      intro i hi
      simp [Instr.isNonJumping]
    · simp [Instr.isNonJumping]

/-- clearRegistersFrom halts on any input. -/
theorem clearRegistersFrom_halts (start count : ℕ) (inputs : List ℕ) :
    Halts (clearRegistersFrom start count) inputs :=
  straightLine_halts (clearRegistersFrom_isStraightLine start count) inputs

end Program

/-! ## Execution Semantics for clearRegistersFrom -/

/-- After executing instruction k (which is Z r) in a straight-line program,
register r becomes 0. -/
theorem straightLine_zero_after_exec {p : Program} (hsl : p.isStraightLine = true)
    (s : State) (k : ℕ) (r : ℕ) (hk : k < p.length) (hwrite : p[k] = Instr.Z r) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k + 1 ∧ c.state.read r = 0 := by
  obtain ⟨c_k, hsteps_k, hpc_k⟩ := straightLine_state_at_pc hsl s k (Nat.le_of_lt hk)
  have hinstr : p.getInstr k = some (Instr.Z r) := by
    simp only [Program.getInstr, List.getElem?_eq_getElem hk, hwrite]
  have hinstr' : p.getInstr c_k.pc = some (Instr.Z r) := by rw [hpc_k]; exact hinstr
  have hstep : Step p c_k ⟨c_k.pc + 1, c_k.state.write r 0⟩ := Step.zero hinstr'
  have hpc_eq : c_k.pc + 1 = k + 1 := by rw [hpc_k]
  refine ⟨⟨c_k.pc + 1, c_k.state.write r 0⟩, Relation.ReflTransGen.tail hsteps_k hstep, hpc_eq, ?_⟩
  simp only [State.read, State.write, Function.update_self]

/-- For a straight-line program, if some instruction writes 0 to register r,
and no later instruction writes to r, then r is 0 in the final state. -/
theorem straightLine_zeros_register {p : Program} (hsl : p.isStraightLine = true)
    (s : State) (r : ℕ) (k : ℕ) (hk : k < p.length)
    (hwrite : p[k] = Instr.Z r)
    (hnowrite : ∀ j (hj : j < p.length), k < j → (p[j]'hj).writesTo ≠ some r) :
    (straightLineFinalState hsl s).read r = 0 := by
  have ⟨hsteps_final, hhalted, hpc_final⟩ := straightLineFinalState_spec hsl s
  obtain ⟨c_after_k, hsteps_to_k, hpc_after_k, hr_zero⟩ :=
    straightLine_zero_after_exec hsl s k r hk hwrite
  let final := Classical.choose (straightLine_halts_from_state hsl s)
  have hsteps_suffix : Steps p c_after_k final :=
    Steps.deterministic_continuation hsteps_to_k hsteps_final hhalted
  -- straightLineFinalState is definitionally the same as Classical.choose
  show (Classical.choose (straightLine_halts_from_state hsl s)).state.read r = 0
  -- Show that the suffix execution preserves r
  -- We need to track that all intermediate pcs are > k
  suffices h : ∀ (a b : Config), a.pc > k → Steps p a b → b.isHalted p →
      b.state.read r = a.state.read r by
    have hpc_gt : c_after_k.pc > k := by omega
    rw [h c_after_k final hpc_gt hsteps_suffix hhalted, hr_zero]
  intro a b hpc_gt hsteps hhalted_b
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head a' c' hstep hrest ih =>
    -- We have a' → c' → ... → b
    -- Need: b.state.read r = a'.state.read r
    have hc'_pc_gt : c'.pc > k := by
      cases hstep with
      | zero h => simp only []; omega
      | succ h => simp only []; omega
      | trans h => simp only []; omega
      | jump_eq h heq =>
        -- This can't happen in a straight-line program
        exfalso
        simp only [Program.isStraightLine, List.all_eq_true] at hsl
        have ha'_pc_lt : a'.pc < p.length := by
          by_contra hc
          simp only [not_lt] at hc
          exact Step.halted_no_step hc (Step.jump_eq h heq)
        simp only [Program.getInstr] at h
        have hmem := List.getElem?_eq_some_iff.mp h
        have hinstr_sl := hsl _ (hmem.2 ▸ List.getElem_mem ha'_pc_lt)
        simp only [Instr.isNonJumping] at hinstr_sl
        exact Bool.false_ne_true hinstr_sl
      | jump_ne h hne => simp only []; omega
    rw [ih hc'_pc_gt]
    -- Show that the step a' → c' preserves register r
    apply Step.straightLine_preserves hsl hstep
    intro instr hinstr
    have ha'_pc_lt : a'.pc < p.length := by
      by_contra hc
      simp only [not_lt] at hc
      exact Step.halted_no_step hc hstep
    simp only [Program.getInstr] at hinstr
    have heq : p[a'.pc] = instr := (List.getElem?_eq_some_iff.mp hinstr).2
    rw [← heq]
    exact hnowrite a'.pc ha'_pc_lt hpc_gt

/-- clearRegistersFrom zeros the specified range. -/
theorem clearRegistersFrom_zeros (start count : ℕ) (s : State) (r : ℕ)
    (hr : start ≤ r ∧ r < start + count) :
    (straightLineFinalState (Program.clearRegistersFrom_isStraightLine start count) s).read r = 0 := by
  have hsl := Program.clearRegistersFrom_isStraightLine start count
  -- The instruction at index (r - start) is Z r
  let k := r - start
  have hk : k < count := by omega
  have hk_lt : k < (Program.clearRegistersFrom start count).length := by
    simp only [Program.clearRegistersFrom_length]; omega
  have hwrite : (Program.clearRegistersFrom start count)[k] = Instr.Z r := by
    simp only [Program.clearRegistersFrom, List.getElem_map, List.getElem_range]
    congr; omega
  have hnowrite : ∀ j (hj : j < (Program.clearRegistersFrom start count).length),
      k < j → ((Program.clearRegistersFrom start count)[j]'hj).writesTo ≠ some r := by
    intro j hj hkj
    simp only [Program.clearRegistersFrom, List.getElem_map, List.getElem_range,
               Instr.writesTo, ne_eq, Option.some.injEq]
    simp only [Program.clearRegistersFrom_length] at hj
    omega
  exact straightLine_zeros_register hsl s r k hk_lt hwrite hnowrite

/-- clearRegistersFrom preserves registers outside its range. -/
theorem clearRegistersFrom_preserves (start count : ℕ) (s : State) (r : ℕ)
    (hr : r < start ∨ start + count ≤ r) :
    (straightLineFinalState (Program.clearRegistersFrom_isStraightLine start count) s).read r = s.read r := by
  -- The program only writes to registers start, start+1, ..., start+count-1
  -- Since r is outside this range, it is preserved
  have hsl := Program.clearRegistersFrom_isStraightLine start count
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  apply Steps.straightLine_preserves hsl hsteps
  intro instr hmem
  -- Each instruction in clearRegistersFrom is Z (start+i) for some i
  simp only [Program.clearRegistersFrom, List.mem_map] at hmem
  obtain ⟨i, hi_range, hinstr_eq⟩ := hmem
  simp only [List.mem_range] at hi_range
  subst hinstr_eq
  simp only [Instr.writesTo, ne_eq, Option.some.injEq]
  cases hr with
  | inl h => omega
  | inr h => omega

/-- After clearRegistersFrom, R[0] is preserved (when start > 0). -/
theorem clearRegistersFrom_preserves_zero (start count : ℕ) (s : State) (hstart : 0 < start) :
    (straightLineFinalState (Program.clearRegistersFrom_isStraightLine start count) s).read 0 = s.read 0 :=
  clearRegistersFrom_preserves start count s 0 (Or.inl hstart)

end Urm
