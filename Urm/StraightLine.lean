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
    (hinstr : p.getInstr c.pc = some p[c.pc]) (hnonjump : (p[c.pc]'hlt).isNonJumping = true) :
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
      have hinstr : p.getInstr c.pc = some p[c.pc] := List.getElem?_eq_getElem hhalted
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
      have hinstr : p.getInstr c.pc = some p[c.pc] := List.getElem?_eq_getElem hhalted
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
    have hinstr : p.getInstr c_n.pc = some p[c_n.pc] := List.getElem?_eq_getElem hpc_lt
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    have hnonjump := hsl p[c_n.pc] (List.getElem_mem hpc_lt)
    obtain ⟨c', hstep', hpc'⟩ := Step.of_nonJumping hpc_lt hinstr hnonjump
    exact ⟨c', Relation.ReflTransGen.tail hsteps_n hstep', hpc_n ▸ hpc'⟩

/-- A single step in a straight-line program modifies at most one register. -/
theorem Step.straightLine_preserves {p : Program} {c c' : Config} {r : ℕ}
    (hsl : p.isStraightLine = true) (hstep : Step p c c')
    (hr : ∀ instr, p.getInstr c.pc = some instr → instr.writesTo ≠ some r) :
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
    simp only [Program.getInstr] at hinstr
    exact List.mem_of_getElem? hinstr

/-- The final state of a straight-line program preserves registers not written by any instruction.
    This is a convenient wrapper around `Steps.straightLine_preserves` for `straightLineFinalState`. -/
theorem straightLineFinalState_preserves {p : Program} {r : ℕ}
    (hsl : p.isStraightLine = true) (s : State)
    (hnowrite : ∀ instr, instr ∈ p → instr.writesTo ≠ some r) :
    (straightLineFinalState hsl s).read r = s.read r := by
  obtain ⟨hsteps, -, -⟩ := straightLineFinalState_spec hsl s
  exact Steps.straightLine_preserves hsl hsteps hnowrite

/-- Partial execution preserves registers not written by instructions 0..k-1.
    For straight-line programs, execution from pc=0 to pc=k only executes instructions 0..k-1. -/
theorem Steps.straightLine_preserves_partial {p : Program} {s : State} {k : ℕ} {r : ℕ}
    (hsl : p.isStraightLine = true)
    (hk : k ≤ p.length)
    (hnowrite : ∀ j (hj : j < k), (p[j]'(Nat.lt_of_lt_of_le hj hk)).writesTo ≠ some r) :
    ∀ c, Steps p ⟨0, s⟩ c → c.pc = k → c.state.read r = s.read r := by
  intro c hsteps hpc
  induction k generalizing c with
  | zero =>
    -- c.pc = 0, so no steps were taken (for straight-line, pc only increases)
    have hc_eq : c = ⟨0, s⟩ := by
      cases Relation.ReflTransGen.cases_tail hsteps with
      | inl heq => exact heq
      | inr h =>
        obtain ⟨c', _, hstep⟩ := h
        -- hstep takes c' to c, so c.pc > c'.pc (for straight-line)
        exfalso
        have hc'_lt := Step.pc_lt_length hstep
        simp only [Program.isStraightLine, List.all_eq_true] at hsl
        have hpc_inc : c.pc > c'.pc := by
          cases hstep with
          | zero | succ | trans => simp
          | jump_eq hinstr | jump_ne hinstr =>
            exact absurd (hsl _ ((List.getElem?_eq_some_iff.mp hinstr).2 ▸ List.getElem_mem hc'_lt))
                         (by simp [Instr.isNonJumping])
        omega
    simp [hc_eq]
  | succ k' ih =>
    have hk'_le : k' ≤ p.length := Nat.le_of_succ_le hk
    have hk'_lt : k' < p.length := Nat.lt_of_succ_le hk
    have hnowrite_k' : ∀ j (hj : j < k'), (p[j]'(Nat.lt_of_lt_of_le hj hk'_le)).writesTo ≠ some r := by
      intro j hj; exact hnowrite j (Nat.lt_succ_of_lt hj)
    -- Use cases_tail to decompose: either c = ⟨0, s⟩ or there's a last step to c
    cases Relation.ReflTransGen.cases_tail hsteps with
    | inl heq =>
      -- c = ⟨0, s⟩, but c.pc = k'+1 ≠ 0, contradiction
      simp_all
    | inr h =>
      obtain ⟨c', hsteps', hstep⟩ := h
      -- hstep takes c' to c, so c'.pc + 1 = c.pc = k'+1, hence c'.pc = k'
      have hc'_lt := Step.pc_lt_length hstep
      have hsl' : ∀ x ∈ p, x.isNonJumping = true := by
        simp only [Program.isStraightLine, List.all_eq_true] at hsl; exact hsl
      have hc'_pc : c'.pc = k' := by
        cases hstep with
        | zero | succ | trans => simp_all
        | jump_eq hinstr | jump_ne hinstr =>
          exact absurd (hsl' _ ((List.getElem?_eq_some_iff.mp hinstr).2 ▸ List.getElem_mem hc'_lt))
                       (by simp [Instr.isNonJumping])
      -- By IH, c'.state.read r = s.read r
      have ih_applied := ih hk'_le hnowrite_k' c' hsteps' hc'_pc
      -- The last step preserves r (since instruction k' doesn't write to r)
      have hstep_preserves : c.state.read r = c'.state.read r := by
        apply Step.straightLine_preserves hsl hstep
        intro instr hinstr
        simp only [Program.getInstr] at hinstr
        have hinstr_eq := List.getElem?_eq_some_iff.mp hinstr
        have : p[c'.pc].writesTo ≠ some r := hc'_pc ▸ hnowrite k' (Nat.lt_succ_self k')
        exact hinstr_eq.2 ▸ this
      rw [hstep_preserves, ih_applied]

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
  have hinstr : p.getInstr c_k.pc = some (Instr.Z r) := by simp [Program.getInstr, hpc_k, hk, hwrite]
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

/-- The maxRegister of clearRegistersFrom.
    For count = 0, returns 0 (empty program).
    For count > 0, returns start + count - 1. -/
theorem clearRegistersFrom_maxRegister (start count : ℕ) :
    (Program.clearRegistersFrom start count).maxRegister =
      if count = 0 then 0 else start + count - 1 := by
  simp only [Program.clearRegistersFrom, Program.maxRegister]
  cases count with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_succ_sub_one]
    -- clearRegistersFrom start (n+1) = [Z start, Z (start+1), ..., Z (start+n)]
    -- The foldl of maxRegister starting from 0 over these instructions is start + n
    -- Use general lemma about foldl max on lists of Z instructions
    have hfoldl_Z : ∀ (xs : List ℕ) (init : ℕ),
        (xs.map Instr.Z).foldl (fun acc i => max acc i.maxRegister) init =
        max init (xs.foldl max 0) := by
      intro xs init
      induction xs generalizing init with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.map_cons, List.foldl_cons, Instr.maxRegister]
        have ih' := ih (max init hd)
        simp only [Instr.maxRegister] at ih'
        rw [ih']
        -- Need: max (max init hd) (foldl max 0 tl) = max init (foldl max (max 0 hd) tl)
        -- Use foldl max (max 0 hd) tl = max hd (foldl max 0 tl) by the shift property
        have hshift : ∀ (ys : List ℕ) (i : ℕ), ys.foldl max i = max i (ys.foldl max 0) := by
          intro ys i
          induction ys generalizing i with
          | nil => simp
          | cons y ys' ih'' => simp only [List.foldl_cons]; rw [ih'', ih'' (max 0 y)]; omega
        rw [hshift tl (max 0 hd)]
        -- max 0 hd = hd for naturals
        have h0 : max 0 hd = hd := Nat.zero_max hd
        rw [h0]
        -- Now: max (max init hd) (foldl max 0 tl) = max init (max hd (foldl max 0 tl))
        omega
    have hrange_max : ∀ m s, ((List.range (m + 1)).map (· + s)).foldl max 0 = s + m := by
      intro m
      induction m with
      | zero => simp [List.range_succ, List.range_zero]
      | succ k ih =>
        intro s
        rw [List.range_succ, List.map_append, List.foldl_append]
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
        have hshift : ∀ (xs : List ℕ) (init : ℕ), xs.foldl max init = max init (xs.foldl max 0) := by
          intro xs init
          induction xs generalizing init with
          | nil => simp
          | cons hd tl ih' =>
            simp only [List.foldl_cons]
            rw [ih', ih' (max 0 hd)]
            omega
        rw [hshift, ih]
        omega
    have heq : (List.range (n + 1)).map (fun i => start + i) = (List.range (n + 1)).map (· + start) := by
      congr 1; ext i; omega
    -- The goal is: foldl f 0 (map (Instr.Z ∘ (· + start)) (range (n+1))) = start + n
    -- Use hfoldl_Z with xs = (range (n+1)).map (· + start)
    have hgoal : ((List.range (n + 1)).map (· + start)).map Instr.Z =
                 (List.range (n + 1)).map (fun i => Instr.Z (start + i)) := by
      rw [← heq, List.map_map]; rfl
    rw [← hgoal, hfoldl_Z, hrange_max]
    simp

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

/-- The maxRegister of clearRegisters is exactly maxReg. -/
theorem clearRegisters_maxRegister (maxReg : ℕ) :
    (Program.clearRegisters maxReg).maxRegister = maxReg := by
  simp only [Program.clearRegisters, Program.maxRegister]
  -- clearRegisters maxReg = [Z 0, Z 1, ..., Z maxReg]
  -- foldl max 0 [0, 1, 2, ..., maxReg]
  -- We prove by induction and using that foldl behaves well
  have haux : ∀ n : ℕ,
      List.foldl (fun acc i => max acc i.maxRegister) 0 (List.map Instr.Z (List.range (n + 1))) = n := by
    intro n
    induction n with
    | zero => simp [List.range, List.range.loop, Instr.maxRegister]
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.foldl_append]
      -- Don't simplify Instr.maxRegister - work with it abstractly
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      -- Goal: max (foldl f 0 [Z 0, ..., Z k]) (Z (k+1)).maxRegister = k + 1
      -- where f = (fun acc i => max acc i.maxRegister)
      have hshift : ∀ (xs : List Instr) (init : ℕ),
          xs.foldl (fun acc i => max acc i.maxRegister) init =
          max init (xs.foldl (fun acc i => max acc i.maxRegister) 0) := by
        intro xs init
        induction xs generalizing init with
        | nil => simp
        | cons hd tl ih' =>
          simp only [List.foldl_cons]
          rw [ih', ih' (max 0 hd.maxRegister)]
          omega
      -- Now apply hshift to the single element list and ih
      rw [hshift, ih]
      simp only [Instr.maxRegister]
      omega
  exact haux maxReg

@[simp]
theorem copyRegisterRange_length (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).length = count := by
  simp [Program.copyRegisterRange]

/-- The maxRegister of copyRegisterRange is bounded by max of endpoint registers.
    For count = 0, returns 0 (empty program). -/
theorem copyRegisterRange_maxRegister (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).maxRegister ≤
    if count = 0 then 0 else max (srcStart + count - 1) (dstStart + count - 1) := by
  simp only [Program.copyRegisterRange, Program.maxRegister]
  cases count with
  | zero => simp
  | succ n =>
    simp only [Nat.add_succ_sub_one]
    -- For count = n + 1, we have instructions T (srcStart + i) (dstStart + i) for i ∈ [0, n]
    -- Each has maxRegister = max (srcStart + i) (dstStart + i)
    -- We need: foldl max 0 [max (s+0) (d+0), ..., max (s+n) (d+n)] ≤ max (s+n) (d+n)
    have hbound : ∀ i, i ≤ n → max (srcStart + i) (dstStart + i) ≤ max (srcStart + n) (dstStart + n) := by
      intro i hi; omega
    -- General lemma: foldl max for instructions bounded by bound
    have hfoldl_bound : ∀ (xs : List Instr) (bound : ℕ),
        (∀ x, x ∈ xs → x.maxRegister ≤ bound) → xs.foldl (fun acc i => max acc i.maxRegister) 0 ≤ bound := by
      intro xs bound hxs
      induction xs with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp] at hxs ⊢
        have ⟨hd_le, tl_le⟩ := hxs
        have ih_bound := ih tl_le
        have hshift : ∀ (ys : List Instr) (init : ℕ),
            ys.foldl (fun acc i => max acc i.maxRegister) init =
            max init (ys.foldl (fun acc i => max acc i.maxRegister) 0) := by
          intro ys init
          induction ys generalizing init with
          | nil => simp
          | cons hd' tl' ih' =>
            simp only [List.foldl_cons]
            rw [ih', ih' (max 0 hd'.maxRegister)]
            omega
        rw [hshift]
        omega
    apply hfoldl_bound
    intro instr hinstr
    simp only [List.mem_map, List.mem_range] at hinstr
    obtain ⟨i, hi, rfl⟩ := hinstr
    simp only [Instr.maxRegister]
    exact hbound i (Nat.lt_succ_iff.mp hi)

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
  have hinstr : p.getInstr k = some (Instr.T src dst) := by simp only [Program.getInstr, List.getElem?_eq_getElem hk, hwrite]
  have hinstr' : p.getInstr c_k.pc = some (Instr.T src dst) := hpc_k ▸ hinstr
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
