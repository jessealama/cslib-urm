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

- `Instr.is_non_jumping`: predicate for Z, S, T instructions (not J)
- `Program.is_straight_line`: a program contains no jump instructions

## Main results

- `straight_line_halts`: straight-line programs always halt
- `straight_line_halts_at_length`: they halt exactly at program length

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Straight-Line Programs -/

/-- An instruction is "non-jumping" if it's Z, S, or T (not J). -/
def Instr.is_non_jumping : Instr → Bool
  | Instr.Z _ => true
  | Instr.S _ => true
  | Instr.T _ _ => true
  | Instr.J _ _ _ => false

/-- A program is "straight-line" if it contains no jump instructions. -/
def Program.is_straight_line (p : Program) : Bool :=
  p.all Instr.is_non_jumping

/-- A non-jumping instruction produces a step that increments PC by 1. -/
theorem Step.of_nonJumping {p : Program} {c : Config} (hlt : c.pc < p.length)
    (hinstr : p[c.pc]? = some p[c.pc]) (hnonjump : (p[c.pc]'hlt).is_non_jumping = true) :
    ∃ c', Step p c c' ∧ c'.pc = c.pc + 1 := by
  cases hp : (p[c.pc]'hlt) with
  | Z n => exact ⟨_, Step.zero (hp ▸ hinstr), rfl⟩
  | S n => exact ⟨_, Step.succ (hp ▸ hinstr), rfl⟩
  | T m n => exact ⟨_, Step.trans (hp ▸ hinstr), rfl⟩
  | J _ _ _ => simp [hp, Instr.is_non_jumping] at hnonjump

/-- shift_jumps is identity for non-jumping instructions. -/
theorem Instr.shift_jumps_of_is_non_jumping {instr : Instr} (h : instr.is_non_jumping = true) (offset : ℕ) :
    instr.shift_jumps offset = instr := by
  cases instr with
  | Z _ | S _ | T _ _ => rfl
  | J _ _ _ => simp [is_non_jumping] at h

/-- A straight-line program halts on any input (pc always increases until it exceeds length). -/
theorem straight_line_halts {p : Program} (hsl : p.is_straight_line = true) (inputs : List ℕ) :
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
      simp only [Program.is_straight_line, List.all_eq_true] at hsl
      have hnonjump := hsl p[c.pc] (List.getElem_mem hhalted)
      obtain ⟨c', hstep', hpc'⟩ := Step.of_nonJumping hhalted hinstr hnonjump
      obtain ⟨c'', hsteps'', hpc''⟩ := ih (p.length - c'.pc) (by omega) c' (by omega) rfl
      exact ⟨c'', Relation.ReflTransGen.head hstep' hsteps'', hpc''⟩

/-- For straight-line programs, the halted config has pc exactly equal to the program length.

Since straight-line programs can only advance pc by 1, and halting means pc ≥ length,
the pc must be exactly length when halted. -/
theorem straight_line_halts_at_length {p : Program} (hsl : p.is_straight_line = true) (inputs : List ℕ) :
    let h := straight_line_halts hsl inputs
    (Classical.choose h).pc = p.length := by
  have h := straight_line_halts hsl inputs
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec h
  simp only [Config.is_halted] at hhalted
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
      simp only [Program.is_straight_line, List.all_eq_true] at hsl
      exact absurd (hsl _ (heq ▸ List.getElem_mem hlt)) (by simp [Instr.is_non_jumping])

/-- Straight-line programs halt from any starting state, not just Config.init.
This is key for chaining: after running one program, we can run the next
straight-line segment from whatever state we're in. -/
theorem straight_line_halts_from_state {p : Program} (hsl : p.is_straight_line = true) (s : State) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.is_halted p ∧ c.pc = p.length := by
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
      simp only [Program.is_straight_line, List.all_eq_true] at hsl
      have hnonjump := hsl p[c.pc] (List.getElem_mem hhalted)
      obtain ⟨c', hstep', hpc'⟩ := Step.of_nonJumping hhalted hinstr hnonjump
      obtain ⟨c'', hsteps'', hpc''⟩ := ih (p.length - c'.pc) (by omega) c' (by omega) rfl
      exact ⟨c'', Relation.ReflTransGen.head hstep' hsteps'', hpc''⟩

/-- The final state after running a straight-line program from a given starting state.
This is the relational-semantics version that replaces the functional `executeStraightLine`. -/
noncomputable def straight_lineFinalState {p : Program} (hsl : p.is_straight_line = true) (s : State) : State :=
  (Classical.choose (straight_line_halts_from_state hsl s)).state

/-- The final config from straight_lineFinalState satisfies the expected properties. -/
theorem straight_lineFinalState_spec {p : Program} (hsl : p.is_straight_line = true) (s : State) :
    let c := Classical.choose (straight_line_halts_from_state hsl s)
    Steps p ⟨0, s⟩ c ∧ c.is_halted p ∧ c.pc = p.length :=
  Classical.choose_spec (straight_line_halts_from_state hsl s)

/-- For a straight-line program, c.state equals straight_lineFinalState if halted from s. -/
theorem straight_lineFinalState_eq_of_halted {p : Program} (hsl : p.is_straight_line = true)
    (s : State) (c : Config) (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.is_halted p) :
    c.state = straight_lineFinalState hsl s :=
  Steps.eq_of_halts hsteps hhalted (straight_lineFinalState_spec hsl s).1
    (straight_lineFinalState_spec hsl s).2.1 ▸ rfl

/-- In a straight-line program, we can characterize the state at any intermediate pc.
This gives us the configuration after executing instructions 0..pc-1. -/
theorem straight_line_state_at_pc {p : Program} (hsl : p.is_straight_line = true)
    (s : State) (targetPc : ℕ) (htarget : targetPc ≤ p.length) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = targetPc := by
  induction targetPc with
  | zero => exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, rfl⟩
  | succ n ih =>
    obtain ⟨c_n, hsteps_n, hpc_n⟩ := ih (Nat.le_of_succ_le htarget)
    have hn_lt : n < p.length := Nat.lt_of_succ_le htarget
    have hpc_lt : c_n.pc < p.length := hpc_n ▸ hn_lt
    have hinstr : p[c_n.pc]? = some p[c_n.pc] := List.getElem?_eq_getElem hpc_lt
    simp only [Program.is_straight_line, List.all_eq_true] at hsl
    have hnonjump := hsl p[c_n.pc] (List.getElem_mem hpc_lt)
    obtain ⟨c', hstep', hpc'⟩ := Step.of_nonJumping hpc_lt hinstr hnonjump
    exact ⟨c', Relation.ReflTransGen.tail hsteps_n hstep', hpc_n ▸ hpc'⟩

/-- A single step in a straight-line program modifies at most one register. -/
theorem Step.straight_line_preserves {p : Program} {c c' : Config} {r : ℕ}
    (hsl : p.is_straight_line = true) (hstep : Step p c c')
    (hr : ∀ instr, p[c.pc]? = some instr → instr.writes_to ≠ some r) :
    c'.state.read r = c.state.read r := by
  cases hstep with
  | zero hinstr | succ hinstr | trans hinstr =>
    have := hr _ hinstr
    simp only [Instr.writes_to, ne_eq, Option.some.injEq] at this
    exact Function.update_of_ne (Ne.symm this) _ _
  | jump_eq hinstr _ | jump_ne hinstr _ =>
    have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
    simp only [Program.is_straight_line, List.all_eq_true] at hsl
    exact absurd (hsl _ (heq ▸ List.getElem_mem hlt)) (by simp [Instr.is_non_jumping])

/-- Multi-step execution preserves registers not written by any instruction. -/
theorem Steps.straight_line_preserves {p : Program} {c c' : Config} {r : ℕ}
    (hsl : p.is_straight_line = true) (hsteps : Steps p c c')
    (hr : ∀ instr, instr ∈ p → instr.writes_to ≠ some r) :
    c'.state.read r = c.state.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
    rw [ih]
    apply Step.straight_line_preserves hsl hstep
    intro instr hinstr
    apply hr
    exact List.mem_of_getElem? hinstr

/-! ## clear_registers_from: Clear registers starting from a given index -/

namespace Program

/-- Clear registers from `start` to `start + count - 1`.
Unlike `clear_registers` which clears from 0, this allows preserving lower registers. -/
def clear_registers_from (start count : ℕ) : Program :=
  (List.range count).map (fun i => Instr.Z (start + i))

@[simp]
theorem clear_registers_from_length (start count : ℕ) :
    (clear_registers_from start count).length = count := by
  simp [clear_registers_from]

@[scoped grind =]
theorem clear_registers_from_is_straight_line (start count : ℕ) :
    (clear_registers_from start count).is_straight_line = true := by
  simp only [clear_registers_from, is_straight_line, List.all_map, List.all_eq_true, List.mem_range]
  intro i _; simp [Instr.is_non_jumping]

end Program

/-! ## Execution Semantics for clear_registers_from -/

/-- After executing instruction k (which is Z r) in a straight-line program,
register r becomes 0. -/
theorem straight_line_zero_after_exec {p : Program} (hsl : p.is_straight_line = true)
    (s : State) (k : ℕ) (r : ℕ) (hk : k < p.length) (hwrite : p[k] = Instr.Z r) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k + 1 ∧ c.state.read r = 0 := by
  obtain ⟨c_k, hsteps_k, hpc_k⟩ := straight_line_state_at_pc hsl s k (Nat.le_of_lt hk)
  have hinstr : p[c_k.pc]? = some (Instr.Z r) := by simp [hpc_k, hk, hwrite]
  refine ⟨_, Relation.ReflTransGen.tail hsteps_k (Step.zero hinstr), hpc_k ▸ rfl, ?_⟩
  simp only [State.read, State.write, Function.update_self]

/-- For a straight-line program, if some instruction writes 0 to register r,
and no later instruction writes to r, then r is 0 in the final state. -/
theorem straight_line_zeros_register {p : Program} (hsl : p.is_straight_line = true)
    (s : State) (r : ℕ) (k : ℕ) (hk : k < p.length)
    (hwrite : p[k] = Instr.Z r)
    (hnowrite : ∀ j (hj : j < p.length), k < j → (p[j]'hj).writes_to ≠ some r) :
    (straight_lineFinalState hsl s).read r = 0 := by
  have ⟨hsteps_final, hhalted, hpc_final⟩ := straight_lineFinalState_spec hsl s
  obtain ⟨c_after_k, hsteps_to_k, hpc_after_k, hr_zero⟩ :=
    straight_line_zero_after_exec hsl s k r hk hwrite
  let final := Classical.choose (straight_line_halts_from_state hsl s)
  have hsteps_suffix : Steps p c_after_k final :=
    Steps.deterministic_continuation hsteps_to_k hsteps_final hhalted
  -- straight_lineFinalState is definitionally the same as Classical.choose
  show (Classical.choose (straight_line_halts_from_state hsl s)).state.read r = 0
  -- Show that the suffix execution preserves r
  -- We need to track that all intermediate pcs are > k
  suffices h : ∀ (a b : Config), a.pc > k → Steps p a b → b.is_halted p →
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
        simp only [Program.is_straight_line, List.all_eq_true] at hsl
        exact absurd (hsl _ ((List.getElem?_eq_some_iff.mp h).2 ▸ List.getElem_mem ha'_pc_lt)) (by simp [Instr.is_non_jumping])
    rw [ih hc'_pc_gt]
    apply Step.straight_line_preserves hsl hstep
    intro instr hinstr
    exact (List.getElem?_eq_some_iff.mp hinstr).2 ▸ hnowrite a'.pc ha'_pc_lt hpc_gt

/-- clear_registers_from zeros the specified range. -/
theorem clear_registers_from_zeros (start count : ℕ) (s : State) (r : ℕ)
    (hr : start ≤ r ∧ r < start + count) :
    (straight_lineFinalState (Program.clear_registers_from_is_straight_line start count) s).read r = 0 := by
  have hsl := Program.clear_registers_from_is_straight_line start count
  have hk_lt : r - start < (Program.clear_registers_from start count).length := by simp; omega
  have hwrite : (Program.clear_registers_from start count)[r - start] = Instr.Z r := by
    simp only [Program.clear_registers_from, List.getElem_map, List.getElem_range]; congr; omega
  have hnowrite : ∀ j (hj : j < (Program.clear_registers_from start count).length),
      r - start < j → ((Program.clear_registers_from start count)[j]'hj).writes_to ≠ some r := by
    intro j hj hkj
    simp only [Program.clear_registers_from, List.getElem_map, List.getElem_range, Instr.writes_to,
               ne_eq, Option.some.injEq] at hj ⊢
    omega
  exact straight_line_zeros_register hsl s r (r - start) hk_lt hwrite hnowrite

/-- clear_registers_from preserves registers outside its range. -/
theorem clear_registers_from_preserves (start count : ℕ) (s : State) (r : ℕ)
    (hr : r < start ∨ start + count ≤ r) :
    (straight_lineFinalState (Program.clear_registers_from_is_straight_line start count) s).read r = s.read r := by
  have hsl := Program.clear_registers_from_is_straight_line start count
  have ⟨hsteps, _, _⟩ := straight_lineFinalState_spec hsl s
  apply Steps.straight_line_preserves hsl hsteps
  intro instr hmem
  simp only [Program.clear_registers_from, List.mem_map, List.mem_range] at hmem
  obtain ⟨i, hi_range, rfl⟩ := hmem
  simp only [Instr.writes_to, ne_eq, Option.some.injEq]
  omega

/-! ## Straight-Line Program Composition

Lemmas for proving composite programs are straight-line.
These simplify proofs in Preservation.lean files across closures. -/

/-- Append preserves straight-line property. -/
@[scoped grind =]
theorem is_straight_line_append {p q : Program}
    (hp : p.is_straight_line = true) (hq : q.is_straight_line = true) :
    (p ++ q).is_straight_line = true := by
  simp only [Program.is_straight_line, List.all_append] at hp hq ⊢
  rw [hp, hq]; rfl

/-- Cons of non-jumping instruction preserves straight-line. -/
@[scoped grind =]
theorem is_straight_line_cons {instr : Instr} {p : Program}
    (hinstr : instr.is_non_jumping = true) (hp : p.is_straight_line = true) :
    Program.is_straight_line (instr :: p) = true := by
  simp only [Program.is_straight_line, List.all_cons] at hp ⊢
  rw [hinstr, hp]; rfl

/-- Singleton non-jumping instruction is straight-line. -/
@[scoped grind =]
theorem is_straight_line_singleton {instr : Instr}
    (h : instr.is_non_jumping = true) :
    Program.is_straight_line [instr] = true := by
  simp only [Program.is_straight_line, List.all_cons, List.all_nil, h, Bool.and_self]

/-- Z instruction is non-jumping. -/
@[simp, scoped grind =] theorem Instr.Z_is_non_jumping (n : ℕ) : (Instr.Z n).is_non_jumping = true := rfl

/-- S instruction is non-jumping. -/
@[simp, scoped grind =] theorem Instr.S_is_non_jumping (n : ℕ) : (Instr.S n).is_non_jumping = true := rfl

/-- T instruction is non-jumping. -/
@[simp, scoped grind =] theorem Instr.T_is_non_jumping (m n : ℕ) : (Instr.T m n).is_non_jumping = true := rfl

/-! ## clear_registers and copy_register_range

These are straight-line program building blocks used by both Composition and Minimization. -/

namespace Program

/-- Clear registers 0 to maxReg. -/
def clear_registers (maxReg : ℕ) : Program := (List.range (maxReg + 1)).map Instr.Z

/-- Copy a range of registers: copies count registers starting at srcStart to dstStart. -/
def copy_register_range (srcStart dstStart count : ℕ) : Program :=
  (List.range count).map fun i => Instr.T (srcStart + i) (dstStart + i)

end Program

@[simp]
theorem clear_registers_length (maxReg : ℕ) :
    (Program.clear_registers maxReg).length = maxReg + 1 := by simp [Program.clear_registers]

@[simp]
theorem copy_register_range_length (srcStart dstStart count : ℕ) :
    (Program.copy_register_range srcStart dstStart count).length = count := by
  simp [Program.copy_register_range]

/-- Tactic for solving length arithmetic goals involving clear_registers and copy_register_range. -/
macro "len_append_omega" : tactic =>
  `(tactic| (simp only [List.length_append, clear_registers_length, copy_register_range_length]; omega))

/-- Tactic for proving register write targets are distinct. -/
macro "writes_to_omega" : tactic =>
  `(tactic| (simp only [Instr.writes_to, ne_eq, Option.some.injEq]; omega))

@[scoped grind =]
theorem clear_registers_is_straight_line (maxReg : ℕ) :
    (Program.clear_registers maxReg).is_straight_line = true := by
  simp only [Program.clear_registers, Program.is_straight_line, List.all_map, List.all_eq_true,
             List.mem_range]
  intro _ _; rfl

@[scoped grind =]
theorem copy_register_range_is_straight_line (srcStart dstStart count : ℕ) :
    (Program.copy_register_range srcStart dstStart count).is_straight_line = true := by
  simp only [Program.copy_register_range, Program.is_straight_line, List.all_map, List.all_eq_true]
  intro i _; simp [Instr.is_non_jumping]

theorem copy_register_range_writes_to (srcStart dstStart count : ℕ)
    (instr : Instr) (hinstr : instr ∈ Program.copy_register_range srcStart dstStart count) :
    ∃ i < count, instr.writes_to = some (dstStart + i) := by
  simp only [Program.copy_register_range, List.mem_map, List.mem_range] at hinstr
  obtain ⟨i, hi, hinstr_eq⟩ := hinstr; exact ⟨i, hi, by simp [← hinstr_eq, Instr.writes_to]⟩

theorem copy_register_range_preserves_outside (srcStart dstStart count : ℕ)
    (r : ℕ) (hr : r < dstStart ∨ r ≥ dstStart + count) :
    ∀ instr, instr ∈ Program.copy_register_range srcStart dstStart count → instr.writes_to ≠ some r := by
  intro instr hinstr; obtain ⟨i, hi, hwrites⟩ := copy_register_range_writes_to srcStart dstStart count instr hinstr
  rw [hwrites]; simp only [ne_eq, Option.some.injEq]; omega

/-- clear_registers preserves registers above maxReg. -/
theorem clear_registers_preserves_above (maxReg : ℕ) (s : State) (r : ℕ) (hr : r > maxReg) :
    (straight_lineFinalState (clear_registers_is_straight_line maxReg) s).read r = s.read r := by
  have hsl := clear_registers_is_straight_line maxReg
  have ⟨hsteps, _, _⟩ := straight_lineFinalState_spec hsl s
  apply Steps.straight_line_preserves hsl hsteps
  intro instr hmem
  simp only [Program.clear_registers, List.mem_map, List.mem_range] at hmem
  obtain ⟨i, hi, rfl⟩ := hmem
  writes_to_omega

/-! ## straight_line_transfer_result

Helper for reasoning about T instructions in straight-line programs. -/

/-- Helper: after a T instruction executes, we can reach the next pc with the transfer done. -/
private theorem straight_line_transfer_after_exec {p : Program} (_hsl : p.is_straight_line = true)
    (s : State) (k src dst : ℕ) (hk : k < p.length) (hwrite : p[k] = Instr.T src dst)
    (c_k : Config) (hsteps_k : Steps p ⟨0, s⟩ c_k) (hpc_k : c_k.pc = k) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k + 1 ∧ c.state.read dst = c_k.state.read src := by
  have hinstr : p[k]? = some (Instr.T src dst) := by simp only [List.getElem?_eq_getElem hk, hwrite]
  have hinstr' : p[c_k.pc]? = some (Instr.T src dst) := hpc_k ▸ hinstr
  let c_next : Config := ⟨c_k.pc + 1, c_k.state.write dst (c_k.state.read src)⟩
  refine ⟨c_next, Relation.ReflTransGen.tail hsteps_k (Step.trans hinstr'), by simp [c_next, hpc_k], by simp [c_next]⟩

/-- For a straight-line program with a T instruction at position k, the final state has
    the transfer result if no later instruction overwrites the destination. -/
theorem straight_line_transfer_result {p : Program} (hsl : p.is_straight_line = true)
    (s : State) (k src dst : ℕ) (hk : k < p.length) (hwrite : p[k] = Instr.T src dst)
    (hnowrite : ∀ j (hj : j < p.length), k < j → (p[j]'hj).writes_to ≠ some dst) :
    ∃ s_before : State,
      (∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k ∧ c.state = s_before) ∧
      (straight_lineFinalState hsl s).read dst = s_before.read src := by
  obtain ⟨c_k, hsteps_k, hpc_k⟩ := straight_line_state_at_pc hsl s k (Nat.le_of_lt hk)
  refine ⟨c_k.state, ⟨c_k, hsteps_k, hpc_k, rfl⟩, ?_⟩
  have ⟨hsteps_final, hhalted, _⟩ := straight_lineFinalState_spec hsl s
  obtain ⟨c_after_k, hsteps_to_after_k, _, hval⟩ :=
    straight_line_transfer_after_exec hsl s k src dst hk hwrite c_k hsteps_k hpc_k
  let final := Classical.choose (straight_line_halts_from_state hsl s)
  have hsteps_suffix := Steps.deterministic_continuation hsteps_to_after_k hsteps_final hhalted
  show (Classical.choose (straight_line_halts_from_state hsl s)).state.read dst = c_k.state.read src
  suffices h : ∀ a b, a.pc > k → Steps p a b → b.is_halted p → b.state.read dst = a.state.read dst by
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
        simp only [Program.is_straight_line, List.all_eq_true] at hsl
        exact absurd (hsl _ ((List.getElem?_eq_some_iff.mp h).2 ▸ List.getElem_mem ha'_pc_lt)) (by simp [Instr.is_non_jumping])
    rw [ih hc'_pc_gt]; apply Step.straight_line_preserves hsl hstep; intro instr hinstr
    rw [← (List.getElem?_eq_some_iff.mp hinstr).2]; exact hnowrite a'.pc ha'_pc_lt hpc_gt

/-! ## High-Level Straight-Line Preservation Helpers

These helpers bundle the common 8-step proof pattern for straight-line program register results
into 2-3 step proofs, reducing boilerplate in Preservation.lean files. -/

/-- For a T instruction at position k: if no later instruction writes to dst,
    and no instruction writes to src, then final dst = initial src.
    Bundles steps 5-8 of the common proof pattern. -/
theorem straight_line_transfer_final {p : Program} (hsl : p.is_straight_line = true)
    (s : State) (c : Config) (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.is_halted p)
    (k src dst : ℕ) (hk : k < p.length)
    (hwrite : p[k] = Instr.T src dst)
    (hnowrite_after : ∀ j (hj : j < p.length), k < j → (p[j]'hj).writes_to ≠ some dst)
    (hnowrite_src : ∀ instr, instr ∈ p → instr.writes_to ≠ some src) :
    c.state.read dst = s.read src := by
  obtain ⟨s_before, ⟨c_k, hsteps_k, _, hs_before_eq⟩, htransfer⟩ :=
    straight_line_transfer_result hsl s k src dst hk hwrite hnowrite_after
  have hs_before_val : s_before.read src = s.read src := by
    rw [← hs_before_eq]
    exact Steps.straight_line_preserves hsl hsteps_k hnowrite_src
  have heq : c.state = straight_lineFinalState hsl s :=
    straight_lineFinalState_eq_of_halted hsl s c hsteps hhalted
  rw [heq, htransfer, hs_before_val]

/-- For a Z instruction at position k: if no later instruction writes to r,
    then final r = 0. Wrapper with Steps/halted interface. -/
theorem straight_line_zero_final {p : Program} (hsl : p.is_straight_line = true)
    (s : State) (c : Config) (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.is_halted p)
    (k r : ℕ) (hk : k < p.length)
    (hwrite : p[k] = Instr.Z r)
    (hnowrite_after : ∀ j (hj : j < p.length), k < j → (p[j]'hj).writes_to ≠ some r) :
    c.state.read r = 0 := by
  have heq : c.state = straight_lineFinalState hsl s :=
    straight_lineFinalState_eq_of_halted hsl s c hsteps hhalted
  rw [heq]
  exact straight_line_zeros_register hsl s r k hk hwrite hnowrite_after

/-- If no instruction writes to r, final r = initial r.
    Direct wrapper with Steps/halted interface. -/
theorem straight_line_preserves_final {p : Program} (hsl : p.is_straight_line = true)
    (s : State) (c : Config) (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.is_halted p)
    (r : ℕ) (hnowrite : ∀ instr, instr ∈ p → instr.writes_to ≠ some r) :
    c.state.read r = s.read r := by
  have heq : c.state = straight_lineFinalState hsl s :=
    straight_lineFinalState_eq_of_halted hsl s c hsteps hhalted
  have ⟨hsteps', _, _⟩ := straight_lineFinalState_spec hsl s
  rw [heq]
  exact Steps.straight_line_preserves hsl hsteps' hnowrite

end Urm
