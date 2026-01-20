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

/-- A non-jumping instruction produces a step that increments PC by 1. -/
theorem Step.of_nonJumping {p : Program} {c : Config} (hlt : c.pc < p.length)
    (hinstr : p[c.pc]? = some p[c.pc]) (hnonjump : (p[c.pc]'hlt).isNonJumping = true) :
    ∃ c', Step p c c' ∧ c'.pc = c.pc + 1 := by
  cases hp : (p[c.pc]'hlt) with
  | Z n => exact ⟨_, Step.zero (hp ▸ hinstr), rfl⟩
  | S n => exact ⟨_, Step.succ (hp ▸ hinstr), rfl⟩
  | T m n => exact ⟨_, Step.trans (hp ▸ hinstr), rfl⟩
  | J _ _ _ => simp [hp, Instr.isNonJumping] at hnonjump

/-- shiftJumps is identity for non-jumping instructions. -/
theorem Instr.shiftJumps_of_isNonJumping {instr : Instr} (h : instr.isNonJumping = true) (offset : ℕ) :
    instr.shiftJumps offset = instr := by
  cases instr with
  | Z _ | S _ | T _ _ => rfl
  | J _ _ _ => simp [isNonJumping] at h

/-- A straight-line program halts on any input (pc always increases until it exceeds length). -/
theorem straightLine_halts {p : Program} (hsl : p.isStraightLine = true) (inputs : List ℕ) :
    Halts p inputs := by
  suffices h : ∀ c : Config, c.pc ≤ p.length → ∃ c', Steps p c c' ∧ c'.pc ≥ p.length by
    obtain ⟨c', hsteps, hpc⟩ := h (Config.init inputs) (by simp [Config.init])
    exact ⟨c', hsteps, hpc⟩
  intro c hpc_le
  generalize hrem : p.length - c.pc = remaining
  induction remaining using Nat.strong_induction_on generalizing c with
  | _ remaining ih =>
    by_cases hhalted : c.pc ≥ p.length
    · exact ⟨c, Relation.ReflTransGen.refl, hhalted⟩
    · push_neg at hhalted
      have hinstr : p[c.pc]? = some p[c.pc] := List.getElem?_eq_getElem hhalted
      simp only [Program.isStraightLine, List.all_eq_true] at hsl
      have hnonjump := hsl p[c.pc] (List.getElem_mem hhalted)
      obtain ⟨c', hstep', hpc'⟩ := Step.of_nonJumping hhalted hinstr hnonjump
      obtain ⟨c'', hsteps'', hpc''⟩ := ih (p.length - c'.pc) (by omega) c' (by omega) rfl
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
    cases hstep with
    | zero hinstr | succ hinstr | trans hinstr =>
      have hpc_lt := List.getElem?_eq_some_iff.mp hinstr |>.1
      simp only at ih ⊢; omega
    | jump_eq hinstr _ | jump_ne hinstr _ =>
      have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
      simp only [Program.isStraightLine, List.all_eq_true] at hsl
      exact absurd (hsl _ (heq ▸ List.getElem_mem hlt)) (by simp [Instr.isNonJumping])

/-- Straight-line programs halt from any starting state, not just Config.init.
This is key for chaining: after running one program, we can run the next
straight-line segment from whatever state we're in. -/
theorem straightLine_halts_from_state {p : Program} (hsl : p.isStraightLine = true) (s : State) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.isHalted p ∧ c.pc = p.length := by
  suffices h : ∀ c : Config, c.pc ≤ p.length → ∃ c', Steps p c c' ∧ c'.pc = p.length by
    obtain ⟨c', hsteps, hpc'⟩ := h ⟨0, s⟩ (Nat.zero_le _)
    exact ⟨c', hsteps, Nat.le_of_eq hpc'.symm, hpc'⟩
  intro c hpc_le
  generalize hrem : p.length - c.pc = remaining
  induction remaining using Nat.strong_induction_on generalizing c with
  | _ remaining ih =>
    by_cases hhalted : c.pc ≥ p.length
    · exact ⟨c, Relation.ReflTransGen.refl, by omega⟩
    · push_neg at hhalted
      have hinstr : p[c.pc]? = some p[c.pc] := List.getElem?_eq_getElem hhalted
      simp only [Program.isStraightLine, List.all_eq_true] at hsl
      have hnonjump := hsl p[c.pc] (List.getElem_mem hhalted)
      obtain ⟨c', hstep', hpc'⟩ := Step.of_nonJumping hhalted hinstr hnonjump
      obtain ⟨c'', hsteps'', hpc''⟩ := ih (p.length - c'.pc) (by omega) c' (by omega) rfl
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
    obtain ⟨c_n, hsteps_n, hpc_n⟩ := ih (Nat.le_of_succ_le htarget)
    have hn_lt : n < p.length := Nat.lt_of_succ_le htarget
    have hpc_lt : c_n.pc < p.length := hpc_n ▸ hn_lt
    have hinstr : p[c_n.pc]? = some p[c_n.pc] := List.getElem?_eq_getElem hpc_lt
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    have hnonjump := hsl p[c_n.pc] (List.getElem_mem hpc_lt)
    obtain ⟨c', hstep', hpc'⟩ := Step.of_nonJumping hpc_lt hinstr hnonjump
    exact ⟨c', Relation.ReflTransGen.tail hsteps_n hstep', hpc_n ▸ hpc'⟩

/-- A single step in a straight-line program modifies at most one register. -/
theorem Step.straightLine_preserves {p : Program} {c c' : Config} {r : ℕ}
    (hsl : p.isStraightLine = true) (hstep : Step p c c')
    (hr : ∀ instr, p[c.pc]? = some instr → instr.writesTo ≠ some r) :
    c'.state.read r = c.state.read r := by
  cases hstep with
  | zero hinstr | succ hinstr | trans hinstr =>
    have := hr _ hinstr
    simp only [Instr.writesTo, ne_eq, Option.some.injEq] at this
    exact Function.update_of_ne (Ne.symm this) _ _
  | jump_eq hinstr _ | jump_ne hinstr _ =>
    have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact absurd (hsl _ (heq ▸ List.getElem_mem hlt)) (by simp [Instr.isNonJumping])

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

theorem clearRegistersFrom_isStraightLine (start count : ℕ) :
    (clearRegistersFrom start count).isStraightLine = true := by
  simp only [clearRegistersFrom, isStraightLine, List.all_map, List.all_eq_true, List.mem_range]
  intro i _; simp [Instr.isNonJumping]

end Program

/-! ## Execution Semantics for clearRegistersFrom -/

/-- After executing instruction k (which is Z r) in a straight-line program,
register r becomes 0. -/
theorem straightLine_zero_after_exec {p : Program} (hsl : p.isStraightLine = true)
    (s : State) (k : ℕ) (r : ℕ) (hk : k < p.length) (hwrite : p[k] = Instr.Z r) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k + 1 ∧ c.state.read r = 0 := by
  obtain ⟨c_k, hsteps_k, hpc_k⟩ := straightLine_state_at_pc hsl s k (Nat.le_of_lt hk)
  have hinstr : p[c_k.pc]? = some (Instr.Z r) := by simp [hpc_k, hk, hwrite]
  refine ⟨_, Relation.ReflTransGen.tail hsteps_k (Step.zero hinstr), hpc_k ▸ rfl, ?_⟩
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
    have ha'_pc_lt := Step.pc_lt_length hstep
    have hc'_pc_gt : c'.pc > k := by
      cases hstep with
      | zero _ | succ _ | trans _ | jump_ne _ _ => simp only []; omega
      | jump_eq h heq =>
        simp only [Program.isStraightLine, List.all_eq_true] at hsl
        exact absurd (hsl _ ((List.getElem?_eq_some_iff.mp h).2 ▸ List.getElem_mem ha'_pc_lt)) (by simp [Instr.isNonJumping])
    rw [ih hc'_pc_gt]
    apply Step.straightLine_preserves hsl hstep
    intro instr hinstr
    exact (List.getElem?_eq_some_iff.mp hinstr).2 ▸ hnowrite a'.pc ha'_pc_lt hpc_gt

/-- clearRegistersFrom zeros the specified range. -/
theorem clearRegistersFrom_zeros (start count : ℕ) (s : State) (r : ℕ)
    (hr : start ≤ r ∧ r < start + count) :
    (straightLineFinalState (Program.clearRegistersFrom_isStraightLine start count) s).read r = 0 := by
  have hsl := Program.clearRegistersFrom_isStraightLine start count
  have hk_lt : r - start < (Program.clearRegistersFrom start count).length := by simp; omega
  have hwrite : (Program.clearRegistersFrom start count)[r - start] = Instr.Z r := by
    simp only [Program.clearRegistersFrom, List.getElem_map, List.getElem_range]; congr; omega
  have hnowrite : ∀ j (hj : j < (Program.clearRegistersFrom start count).length),
      r - start < j → ((Program.clearRegistersFrom start count)[j]'hj).writesTo ≠ some r := by
    intro j hj hkj
    simp only [Program.clearRegistersFrom, List.getElem_map, List.getElem_range, Instr.writesTo,
               ne_eq, Option.some.injEq] at hj ⊢
    omega
  exact straightLine_zeros_register hsl s r (r - start) hk_lt hwrite hnowrite

/-- clearRegistersFrom preserves registers outside its range. -/
theorem clearRegistersFrom_preserves (start count : ℕ) (s : State) (r : ℕ)
    (hr : r < start ∨ start + count ≤ r) :
    (straightLineFinalState (Program.clearRegistersFrom_isStraightLine start count) s).read r = s.read r := by
  have hsl := Program.clearRegistersFrom_isStraightLine start count
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  apply Steps.straightLine_preserves hsl hsteps
  intro instr hmem
  simp only [Program.clearRegistersFrom, List.mem_map, List.mem_range] at hmem
  obtain ⟨i, hi_range, rfl⟩ := hmem
  simp only [Instr.writesTo, ne_eq, Option.some.injEq]
  omega

/-! ## clearRegisters and copyRegisterRange

These are straight-line program building blocks used by both Composition and Minimization. -/

namespace Program

/-- Clear registers 0 to maxReg. -/
def clearRegisters (maxReg : ℕ) : Program := (List.range (maxReg + 1)).map Instr.Z

/-- Copy a range of registers: copies count registers starting at srcStart to dstStart. -/
def copyRegisterRange (srcStart dstStart count : ℕ) : Program :=
  (List.range count).map fun i => Instr.T (srcStart + i) (dstStart + i)

end Program

@[simp]
theorem clearRegisters_length (maxReg : ℕ) :
    (Program.clearRegisters maxReg).length = maxReg + 1 := by simp [Program.clearRegisters]

@[simp]
theorem copyRegisterRange_length (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).length = count := by
  simp [Program.copyRegisterRange]

/-- Tactic for solving length arithmetic goals involving clearRegisters and copyRegisterRange. -/
macro "len_append_omega" : tactic =>
  `(tactic| (simp only [List.length_append, clearRegisters_length, copyRegisterRange_length]; omega))

/-- Tactic for proving register write targets are distinct. -/
macro "writesTo_omega" : tactic =>
  `(tactic| (simp only [Instr.writesTo, ne_eq, Option.some.injEq]; omega))

theorem clearRegisters_isStraightLine (maxReg : ℕ) :
    (Program.clearRegisters maxReg).isStraightLine = true := by
  simp only [Program.clearRegisters, Program.isStraightLine, List.all_map]
  induction maxReg + 1 with
  | zero => simp only [List.range_zero, List.all_nil]
  | succ k ih => simp only [List.range_succ, List.all_append, ih, List.all_cons, List.all_nil,
      Function.comp_apply, Instr.isNonJumping, Bool.and_self]

theorem copyRegisterRange_isStraightLine (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).isStraightLine = true := by
  simp only [Program.copyRegisterRange, Program.isStraightLine, List.all_map, List.all_eq_true]
  intro i _; simp [Instr.isNonJumping]

theorem copyRegisterRange_writesTo (srcStart dstStart count : ℕ)
    (instr : Instr) (hinstr : instr ∈ Program.copyRegisterRange srcStart dstStart count) :
    ∃ i < count, instr.writesTo = some (dstStart + i) := by
  simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hinstr
  obtain ⟨i, hi, hinstr_eq⟩ := hinstr; exact ⟨i, hi, by simp [← hinstr_eq, Instr.writesTo]⟩

theorem copyRegisterRange_preserves_outside (srcStart dstStart count : ℕ)
    (r : ℕ) (hr : r < dstStart ∨ r ≥ dstStart + count) :
    ∀ instr, instr ∈ Program.copyRegisterRange srcStart dstStart count → instr.writesTo ≠ some r := by
  intro instr hinstr; obtain ⟨i, hi, hwrites⟩ := copyRegisterRange_writesTo srcStart dstStart count instr hinstr
  rw [hwrites]; simp only [ne_eq, Option.some.injEq]; omega

/-- clearRegisters preserves registers above maxReg. -/
theorem clearRegisters_preserves_above (maxReg : ℕ) (s : State) (r : ℕ) (hr : r > maxReg) :
    (straightLineFinalState (clearRegisters_isStraightLine maxReg) s).read r = s.read r := by
  have hsl := clearRegisters_isStraightLine maxReg
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  apply Steps.straightLine_preserves hsl hsteps
  intro instr hmem
  simp only [Program.clearRegisters, List.mem_map, List.mem_range] at hmem
  obtain ⟨i, hi, rfl⟩ := hmem
  writesTo_omega

/-! ## straightLine_transfer_result

Helper for reasoning about T instructions in straight-line programs. -/

/-- Helper: after a T instruction executes, we can reach the next pc with the transfer done. -/
private theorem straightLine_transfer_after_exec {p : Program} (_hsl : p.isStraightLine = true)
    (s : State) (k src dst : ℕ) (hk : k < p.length) (hwrite : p[k] = Instr.T src dst)
    (c_k : Config) (hsteps_k : Steps p ⟨0, s⟩ c_k) (hpc_k : c_k.pc = k) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k + 1 ∧ c.state.read dst = c_k.state.read src := by
  have hinstr : p[k]? = some (Instr.T src dst) := by simp only [List.getElem?_eq_getElem hk, hwrite]
  have hinstr' : p[c_k.pc]? = some (Instr.T src dst) := hpc_k ▸ hinstr
  let c_next : Config := ⟨c_k.pc + 1, c_k.state.write dst (c_k.state.read src)⟩
  refine ⟨c_next, Relation.ReflTransGen.tail hsteps_k (Step.trans hinstr'), by simp [c_next, hpc_k], by simp [c_next]⟩

/-- For a straight-line program with a T instruction at position k, the final state has
    the transfer result if no later instruction overwrites the destination. -/
theorem straightLine_transfer_result {p : Program} (hsl : p.isStraightLine = true)
    (s : State) (k src dst : ℕ) (hk : k < p.length) (hwrite : p[k] = Instr.T src dst)
    (hnowrite : ∀ j (hj : j < p.length), k < j → (p[j]'hj).writesTo ≠ some dst) :
    ∃ s_before : State,
      (∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k ∧ c.state = s_before) ∧
      (straightLineFinalState hsl s).read dst = s_before.read src := by
  obtain ⟨c_k, hsteps_k, hpc_k⟩ := straightLine_state_at_pc hsl s k (Nat.le_of_lt hk)
  refine ⟨c_k.state, ⟨c_k, hsteps_k, hpc_k, rfl⟩, ?_⟩
  have ⟨hsteps_final, hhalted, _⟩ := straightLineFinalState_spec hsl s
  obtain ⟨c_after_k, hsteps_to_after_k, _, hval⟩ :=
    straightLine_transfer_after_exec hsl s k src dst hk hwrite c_k hsteps_k hpc_k
  let final := Classical.choose (straightLine_halts_from_state hsl s)
  have hsteps_suffix := Steps.deterministic_continuation hsteps_to_after_k hsteps_final hhalted
  show (Classical.choose (straightLine_halts_from_state hsl s)).state.read dst = c_k.state.read src
  suffices h : ∀ a b, a.pc > k → Steps p a b → b.isHalted p → b.state.read dst = a.state.read dst by
    rw [h c_after_k final (by omega) hsteps_suffix hhalted, hval]
  intro a b hpc_gt hsteps hhalted_b
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head a' c' hstep hrest ih =>
    have ha'_pc_lt := Step.pc_lt_length hstep
    have hc'_pc_gt : c'.pc > k := by
      cases hstep with
      | zero _ | succ _ | trans _ | jump_ne _ _ => simp only []; omega
      | jump_eq h heq' =>
        simp only [Program.isStraightLine, List.all_eq_true] at hsl
        exact absurd (hsl _ ((List.getElem?_eq_some_iff.mp h).2 ▸ List.getElem_mem ha'_pc_lt)) (by simp [Instr.isNonJumping])
    rw [ih hc'_pc_gt]; apply Step.straightLine_preserves hsl hstep; intro instr hinstr
    rw [← (List.getElem?_eq_some_iff.mp hinstr).2]; exact hnowrite a'.pc ha'_pc_lt hpc_gt

end Urm
