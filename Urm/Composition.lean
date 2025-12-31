/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable
import Urm.Shift
import Urm.Concat
import Urm.StandardForm
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-! # Composition Infrastructure

This file provides common infrastructure for composition proofs, including
register isolation lemmas, straight-line program execution, and continuation
lemmas for sequential program execution.

## Main definitions

- `Program.clearRegisters`: Generate zero instructions for registers 0..maxReg
- `Part.sequence`: Sequence a family of partial values into a partial tuple
- `straightLineFinalState`: Final state after running a straight-line program

## Main results

- `Steps.preserves_high_register`: Execution preserves registers above maxRegister
- `Part.sequence_dom`: Domain characterization for Part.sequence
- `straightLine_halts_from_state`: Straight-line programs always halt
- `Halts.concat_continuation`: Chaining halting programs via concatenation

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Program Combinators -/

namespace Program

/-- Clear registers `[0, maxReg]` by setting them to zero. -/
def clearRegisters (maxReg : ℕ) : Program :=
  (List.range (maxReg + 1)).map Instr.Z

/-- Copy `count` consecutive registers from srcStart to dstStart.
    copyRegisterRange 3 10 4 produces [T 3 10, T 4 11, T 5 12, T 6 13] -/
def copyRegisterRange (srcStart dstStart count : ℕ) : Program :=
  (List.range count).map fun i => Instr.T (srcStart + i) (dstStart + i)

/-- Transfer saved results to input registers for running F.
    transferResultsToInputs 10 3 produces [T 10 0, T 11 1, T 12 2] -/
def transferResultsToInputs (resultStart arityF : ℕ) : Program :=
  (List.range arityF).map fun i => Instr.T (resultStart + i) i

end Program

/-! ## copyRegisterRange Properties -/

theorem copyRegisterRange_length (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).length = count := by
  simp [Program.copyRegisterRange]

theorem copyRegisterRange_zero (srcStart dstStart : ℕ) :
    Program.copyRegisterRange srcStart dstStart 0 = [] := by
  simp [Program.copyRegisterRange]

theorem copyRegisterRange_isStraightLine (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).isStraightLine = true := by
  simp only [Program.copyRegisterRange, Program.isStraightLine, List.all_map, List.all_eq_true]
  intro i _
  simp [Instr.isNonJumping]

theorem copyRegisterRange_isStandardForm (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).IsStandardForm :=
  straightLine_isStandardForm (copyRegisterRange_isStraightLine srcStart dstStart count)

/-! ## transferResultsToInputs Properties -/

theorem transferResultsToInputs_length (resultStart arityF : ℕ) :
    (Program.transferResultsToInputs resultStart arityF).length = arityF := by
  simp [Program.transferResultsToInputs]

theorem transferResultsToInputs_zero (resultStart : ℕ) :
    Program.transferResultsToInputs resultStart 0 = [] := by
  simp [Program.transferResultsToInputs]

theorem transferResultsToInputs_isStraightLine (resultStart arityF : ℕ) :
    (Program.transferResultsToInputs resultStart arityF).isStraightLine = true := by
  simp only [Program.transferResultsToInputs, Program.isStraightLine, List.all_map, List.all_eq_true]
  intro i _
  simp [Instr.isNonJumping]

theorem transferResultsToInputs_isStandardForm (resultStart arityF : ℕ) :
    (Program.transferResultsToInputs resultStart arityF).IsStandardForm :=
  straightLine_isStandardForm (transferResultsToInputs_isStraightLine resultStart arityF)

/-! ## Register Isolation Lemmas -/

section RegisterIsolation

variable {p : Program}

/-- Helper: maxRegister bounds instruction maxRegister for valid pc. -/
theorem Program.instr_maxRegister_le {i : ℕ} {instr : Instr}
    (h : p.getInstr i = some instr) : instr.maxRegister ≤ p.maxRegister := by
  simp only [Program.getInstr] at h
  have hi : i < p.length := by
    by_contra hc
    simp only [not_lt] at hc
    simp [List.getElem?_eq_none hc] at h
  induction p generalizing i instr with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [Program.maxRegister, List.foldl_cons]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      -- hd.maxRegister ≤ foldl max (max 0 hd.maxRegister) tl
      have h1 : hd.maxRegister ≤ max 0 hd.maxRegister := Nat.le_max_right _ _
      have h2 : ∀ (init : ℕ) (l : List Instr), init ≤ l.foldl (fun acc i => max acc i.maxRegister) init := by
        intro init l
        induction l generalizing init with
        | nil => exact Nat.le_refl _
        | cons h t iht => exact Nat.le_trans (Nat.le_max_left _ _) (iht _)
      exact Nat.le_trans h1 (h2 _ _)
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hj : j < tl.length := by simp at hi; omega
      have ih' := ih h hj
      simp only [Program.maxRegister] at ih'
      -- ih' : instr.maxRegister ≤ foldl max 0 tl
      -- Need: instr.maxRegister ≤ foldl max (max 0 hd.maxRegister) tl
      have hmono : ∀ (a b : ℕ) (l : List Instr), a ≤ b →
          l.foldl (fun acc i => max acc i.maxRegister) a ≤
          l.foldl (fun acc i => max acc i.maxRegister) b := by
        intro a b l hab
        induction l generalizing a b with
        | nil => exact hab
        | cons h t iht =>
          simp only [List.foldl_cons]
          apply iht
          exact max_le_max hab (Nat.le_refl _)
      exact Nat.le_trans ih' (hmono 0 _ tl (Nat.zero_le _))

/-- A single step preserves registers above the program's maxRegister. -/
theorem Step.preserves_high_register {c c' : Config} (hstep : Step p c c') (r : ℕ)
    (hr : p.maxRegister < r) : c'.state.read r = c.state.read r := by
  cases hstep with
  | zero h =>
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    simp only [State.read, State.write]
    exact Function.update_of_ne (by omega : r ≠ _) _ _
  | succ h =>
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    simp only [State.read, State.write]
    exact Function.update_of_ne (by omega : r ≠ _) _ _
  | trans h =>
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    simp only [State.read, State.write]
    exact Function.update_of_ne (by omega : r ≠ _) _ _
  | jump_eq _ _ => rfl
  | jump_ne _ _ => rfl

/-- Multi-step execution preserves registers above maxRegister. -/
theorem Steps.preserves_high_register {c c' : Config} (hsteps : Steps p c c') (r : ℕ)
    (hr : p.maxRegister < r) : c'.state.read r = c.state.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
    rw [ih]
    exact Step.preserves_high_register hstep r hr

/-- Running a program preserves registers above its maxRegister.

When a program halts, the final state agrees with the initial state on all registers
that are never accessed by any instruction in the program. -/
theorem Halts.preserves_high_registers {p : Program} {inputs : List ℕ}
    (h : Halts p inputs) (r : ℕ) (hr : p.maxRegister < r) :
    (Classical.choose h).state.read r = (Config.init inputs).state.read r := by
  have ⟨hsteps, _⟩ := Classical.choose_spec h
  exact Steps.preserves_high_register hsteps r hr

end RegisterIsolation

/-! ## Part.sequence for Partial Function Families -/

/-- Sequence a finite family of partial values into a partial function.

`Part.sequence f` is defined iff all `f i` are defined, and when defined,
returns a function that gives `(f i).get` for each `i`. -/
def Part.sequence {α : Type*} : {n : ℕ} → (Fin n → Part α) → Part (Fin n → α)
  | 0, _ => Part.some Fin.elim0
  | _ + 1, f => (f 0).bind fun a0 =>
      (Part.sequence (fun i => f i.succ)).map fun rest =>
        Fin.cons a0 rest

theorem Part.sequence_zero {α : Type*} (f : Fin 0 → Part α) :
    Part.sequence f = Part.some Fin.elim0 := rfl

theorem Part.sequence_succ {α : Type*} {n : ℕ} (f : Fin (n + 1) → Part α) :
    Part.sequence f = (f 0).bind fun a0 =>
      (Part.sequence (fun i => f i.succ)).map fun rest =>
        Fin.cons a0 rest := rfl

theorem Part.sequence_dom {α : Type*} {n : ℕ} {f : Fin n → Part α} :
    (Part.sequence f).Dom ↔ ∀ i, (f i).Dom := by
  induction n with
  | zero =>
    simp only [Part.sequence, Part.some_dom]
    exact ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | succ n ih =>
    simp only [Part.sequence, Part.bind_dom, Part.map_Dom]
    constructor
    · intro ⟨hdom0, hrest⟩ i
      match i with
      | ⟨0, _⟩ => exact hdom0
      | ⟨j + 1, hlt⟩ =>
        have := ih.mp hrest
        exact this ⟨j, Nat.lt_of_succ_lt_succ hlt⟩
    · intro hall
      exact ⟨hall 0, ih.mpr (fun i => hall i.succ)⟩

theorem Part.sequence_get {α : Type*} {n : ℕ} {f : Fin n → Part α}
    (hdom : (Part.sequence f).Dom) (i : Fin n) :
    (Part.sequence f).get hdom i = (f i).get (Part.sequence_dom.mp hdom i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    match i with
    | ⟨0, _⟩ =>
      simp only [Part.sequence_succ, Part.bind, Part.map] at hdom ⊢
      rfl
    | ⟨j + 1, hlt⟩ =>
      -- Technical: extract the recursive call from the bind/map structure
      simp only [Part.sequence_succ, Part.bind, Part.map] at hdom ⊢
      exact ih _ ⟨j, Nat.lt_of_succ_lt_succ hlt⟩

/-! ## Standard Form and Concatenation -/

/-- Concatenation of straight-line programs is straight-line. -/
theorem Program.isStraightLine_concat {p1 p2 : Program}
    (h1 : p1.isStraightLine = true) (h2 : p2.isStraightLine = true) :
    (p1.concat p2).isStraightLine = true := by
  simp only [Program.concat, Program.isStraightLine, List.all_append]
  simp only [Program.isStraightLine] at h1 h2
  rw [Bool.and_eq_true]
  constructor
  · exact h1
  · simp only [Program.shiftJumps, List.all_map]
    convert h2 using 2
    funext instr
    cases instr <;> simp [Instr.shiftJumps, Instr.isNonJumping]

/-- Concatenation of straight-line programs is standard form. -/
theorem straightLine_concat_isStandardForm {p1 p2 : Program}
    (h1 : p1.isStraightLine = true) (h2 : p2.isStraightLine = true) :
    (p1.concat p2).IsStandardForm := by
  apply straightLine_isStandardForm
  exact Program.isStraightLine_concat h1 h2

/-- Concatenation of standard form programs is standard form.

If p₁ and p₂ are both standard form, then p₁.concat p₂ is also standard form.
This is a syntactic property: jump targets in p₁ are already bounded by p₁.length ≤ p₁.length + p₂.length,
and jump targets in p₂ are shifted by p₁.length, preserving their bounded property. -/
theorem Program.IsStandardForm.concat {p1 p2 : Program}
    (h1 : p1.IsStandardForm) (h2 : p2.IsStandardForm) :
    (p1.concat p2).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm at *
  rw [List.all_eq_true] at h1 h2 ⊢
  intro instr hinstr
  simp only [Program.concat, Program.shiftJumps] at hinstr
  rw [List.mem_append] at hinstr
  cases hinstr with
  | inl hp1 =>
    -- Instruction from p1: bounded by p1.length ≤ p1.length + p2.length
    have hb := h1 instr hp1
    simp only [Program.concat_length]
    exact Instr.hasBoundedJump_mono hb (Nat.le_add_right _ _)
  | inr hp2 =>
    -- Instruction from p2.shiftJumps: use the shifted bound lemma
    rw [List.mem_map] at hp2
    obtain ⟨instr', hinstr', rfl⟩ := hp2
    have hb := h2 instr' hinstr'
    have hshift := Instr.hasBoundedJump_shiftJumps (len := p2.length) (offset := p1.length) hb
    simp only [Program.concat_length]
    exact hshift

/-- If p1.concat p2 halts and p1 is standard form, then p1 halts.

This is the "prefix halts" property: execution of the concatenation must pass through
a state where p1 has halted (at pc = p1.length) before continuing into p2.

The key insight is that for standard form programs:
1. Execution starts at pc = 0
2. While pc < p1.length, we execute p1's instructions
3. Standard form means when we "exit" p1, it's at pc = p1.length (halted in p1)
4. This config witnesses that p1 halts -/
theorem Halts.prefix_of_concat_sf {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs)
    (h1 : p1.IsStandardForm) :
    Halts p1 inputs := by
  -- Extract the execution path from Config.init to a halted config in H
  -- Find the first config where pc = p1.length
  -- The prefix of the path up to that point is an execution of p1
  -- At pc = p1.length, p1 is halted
  obtain ⟨cH, hsteps, hhalted⟩ := hH
  -- Build p1 steps by extracting prefix of concat execution while pc < p1.length
  -- Key: we need to show there exists a config c with Steps p1 (Config.init inputs) c and c.isHalted p1
  -- Strategy: induction on hsteps, maintaining that we're building parallel p1 steps

  -- Handle empty p1 case first
  by_cases hp1 : p1.length = 0
  · -- Empty p1: Config.init is already halted
    exact ⟨Config.init inputs, Relation.ReflTransGen.refl, by simp [Config.isHalted, hp1]⟩

  -- Non-empty p1: we need to find where pc first reaches p1.length
  -- Use induction on the execution path.
  -- Key insight: at each step, while pc < p1.length, we can convert the step to a p1 step.
  -- When pc reaches p1.length, p1 is halted.

  -- Helper: from any config c with pc ≤ p1.length and steps to a halted config in concat,
  -- we can find a halted config in p1 reachable from c
  suffices h : ∀ c c' : Config,
      Steps (p1.concat p2) c c' → c'.isHalted (p1.concat p2) →
      c.pc ≤ p1.length →
      (∃ c'', Steps p1 c c'' ∧ c''.isHalted p1) by
    have hpc0 : (Config.init inputs).pc ≤ p1.length := by simp [Config.init]
    exact h (Config.init inputs) cH hsteps hhalted hpc0

  intro c c' hsteps'
  -- Use head_induction_on which gives the right IH structure:
  -- motive a := c'.isHalted → a.pc ≤ p1.length → ∃ c'', Steps p1 a c'' ∧ c''.isHalted p1
  -- Given Step a d and Steps d c', the IH applies to d
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- At the end: c = c'. Need to prove the motive for c'.
    -- Given c'.isHalted (concat) and c'.pc ≤ p1.length, show c' is halted in p1.
    intro hhalted' hpc_le
    simp only [Config.isHalted, Program.concat_length] at hhalted'
    have hpc_eq : c'.pc = p1.length := by omega
    exact ⟨c', Relation.ReflTransGen.refl, by simp [Config.isHalted, hpc_eq]⟩
  | @head a d hstep hrest ih =>
    -- hstep : Step (p1.concat p2) a d
    -- hrest : Steps (p1.concat p2) d c'
    -- ih : c'.isHalted (p1.concat p2) → d.pc ≤ p1.length → ∃ c'', Steps p1 d c'' ∧ c''.isHalted p1
    intro hhalted' hpc_le

    -- Check if a is already halted in p1
    by_cases hhalted_p1 : a.isHalted p1
    · exact ⟨a, Relation.ReflTransGen.refl, hhalted_p1⟩

    -- a is not halted in p1, so a.pc < p1.length
    have hpc_lt : a.pc < p1.length := by
      simp only [Config.isHalted, not_le] at hhalted_p1
      exact hhalted_p1

    -- Since a.pc < p1.length, we can convert the step to a p1 step
    have hstep_p1 : Step p1 a d := Step.of_concat_left hpc_lt hstep

    -- d.pc ≤ p1.length by standard form
    have hd_pc_le : d.pc ≤ p1.length := by
      cases hstep_p1 with
      | zero h => simp only; omega
      | succ h => simp only; omega
      | trans h => simp only; omega
      | jump_eq h _ =>
        simp only [Program.getInstr] at h
        have ⟨hpc_valid, hinstr_eq⟩ := List.getElem?_eq_some_iff.mp h
        have hmem : Instr.J _ _ _ ∈ p1 := hinstr_eq ▸ List.getElem_mem hpc_valid
        simp only [Program.IsStandardForm, Program.isStandardForm, List.all_eq_true] at h1
        have hbounded := h1 _ hmem
        simp only [Instr.hasBoundedJump, decide_eq_true_eq] at hbounded
        exact hbounded
      | jump_ne h _ => simp only; omega

    -- Apply IH to get p1 execution from d
    obtain ⟨c'', hsteps_dc'', hhalted_c''⟩ := ih hhalted' hd_pc_le

    -- Chain: a → d in p1, then d →* c'' in p1
    exact ⟨c'', Relation.ReflTransGen.head hstep_p1 hsteps_dc'', hhalted_c''⟩

/-- If p1.concat p2 halts and p1 is standard form, we can recover the intermediate state
after p1 halts (at pc = p1.length). -/
theorem Halts.concat_sf_intermediate_state {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs)
    (h1 : p1.IsStandardForm) :
    ∃ s : State, Steps p1 (Config.init inputs) ⟨p1.length, s⟩ ∧
                 (⟨p1.length, s⟩ : Config).isHalted p1 := by
  have hP1 := Halts.prefix_of_concat_sf hH h1
  have hspec := Classical.choose_spec hP1
  have hpc := h1.halts_at_length inputs (Classical.choose hP1) hspec.1 hspec.2
  use (Classical.choose hP1).state
  constructor
  · -- Need to show Steps p1 (Config.init inputs) ⟨p1.length, c.state⟩
    -- We have hspec.1 : Steps p1 (Config.init inputs) c and hpc : c.pc = p1.length
    have heq : Classical.choose hP1 = ⟨p1.length, (Classical.choose hP1).state⟩ := by
      ext
      · exact hpc
      · rfl
    rw [heq] at hspec
    exact hspec.1
  · simp only [Config.isHalted]
    exact Nat.le_refl _

/-- Generalized prefix extraction: if p1.concat p2 halts starting from ⟨0, s⟩ and p1 is standard form,
then p1 halts from ⟨0, s⟩.

This generalizes `Halts.prefix_of_concat_sf` to arbitrary starting states (not just Config.init). -/
theorem prefix_of_concat_from_zero {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c)
    (hhalted : c.isHalted (p1.concat p2))
    (h1 : p1.IsStandardForm) :
    ∃ c', Steps p1 ⟨0, s⟩ c' ∧ c'.isHalted p1 := by
  -- Handle empty p1 case first
  by_cases hp1 : p1.length = 0
  · -- Empty p1: ⟨0, s⟩ is already halted
    exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, by simp [Config.isHalted, hp1]⟩

  -- Non-empty p1: find where pc first reaches p1.length
  -- Use the same induction as prefix_of_concat_sf
  suffices h : ∀ c0 c' : Config,
      Steps (p1.concat p2) c0 c' → c'.isHalted (p1.concat p2) →
      c0.pc ≤ p1.length →
      (∃ c'', Steps p1 c0 c'' ∧ c''.isHalted p1) by
    have hpc0 : (⟨0, s⟩ : Config).pc ≤ p1.length := by simp
    exact h ⟨0, s⟩ c hsteps hhalted hpc0

  intro c0 c' hsteps'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hhalted' hpc_le
    simp only [Config.isHalted, Program.concat_length] at hhalted'
    have hpc_eq : c'.pc = p1.length := by omega
    exact ⟨c', Relation.ReflTransGen.refl, by simp [Config.isHalted, hpc_eq]⟩
  | @head a d hstep hrest ih =>
    intro hhalted' hpc_le
    by_cases hhalted_p1 : a.isHalted p1
    · exact ⟨a, Relation.ReflTransGen.refl, hhalted_p1⟩
    have hpc_lt : a.pc < p1.length := by
      simp only [Config.isHalted, not_le] at hhalted_p1
      exact hhalted_p1
    have hstep_p1 : Step p1 a d := Step.of_concat_left hpc_lt hstep
    have hd_pc_le : d.pc ≤ p1.length := by
      cases hstep_p1 with
      | zero h => simp only; omega
      | succ h => simp only; omega
      | trans h => simp only; omega
      | jump_eq h _ =>
        simp only [Program.getInstr] at h
        have ⟨hpc_valid, hinstr_eq⟩ := List.getElem?_eq_some_iff.mp h
        have hmem : Instr.J _ _ _ ∈ p1 := hinstr_eq ▸ List.getElem_mem hpc_valid
        simp only [Program.IsStandardForm, Program.isStandardForm, List.all_eq_true] at h1
        have hbounded := h1 _ hmem
        simp only [Instr.hasBoundedJump, decide_eq_true_eq] at hbounded
        exact hbounded
      | jump_ne h _ => simp only; omega
    obtain ⟨c'', hsteps_dc'', hhalted_c''⟩ := ih hhalted' hd_pc_le
    exact ⟨c'', Relation.ReflTransGen.head hstep_p1 hsteps_dc'', hhalted_c''⟩

/-- clearRegisters produces a straight-line program. -/
theorem clearRegisters_isStraightLine (maxReg : ℕ) :
    (Program.clearRegisters maxReg).isStraightLine = true := by
  simp only [Program.clearRegisters, Program.isStraightLine, List.all_map]
  induction maxReg + 1 with
  | zero => simp only [List.range_zero, List.all_nil]
  | succ k ih =>
    simp only [List.range_succ, List.all_append, ih, List.all_cons, List.all_nil,
      Function.comp_apply, Instr.isNonJumping, Bool.and_self]

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

/-! ## Halts lemmas for copyRegisterRange and transferResultsToInputs -/

theorem copyRegisterRange_halts (srcStart dstStart count : ℕ) (s : State) :
    ∃ c, Steps (Program.copyRegisterRange srcStart dstStart count) ⟨0, s⟩ c ∧
         c.isHalted (Program.copyRegisterRange srcStart dstStart count) ∧
         c.pc = count := by
  have hsl := copyRegisterRange_isStraightLine srcStart dstStart count
  obtain ⟨c, hsteps, hhalted, hpc⟩ := straightLine_halts_from_state hsl s
  exact ⟨c, hsteps, hhalted, by rw [hpc, copyRegisterRange_length]⟩

theorem transferResultsToInputs_halts (resultStart arityF : ℕ) (s : State) :
    ∃ c, Steps (Program.transferResultsToInputs resultStart arityF) ⟨0, s⟩ c ∧
         c.isHalted (Program.transferResultsToInputs resultStart arityF) ∧
         c.pc = arityF := by
  have hsl := transferResultsToInputs_isStraightLine resultStart arityF
  obtain ⟨c, hsteps, hhalted, hpc⟩ := straightLine_halts_from_state hsl s
  exact ⟨c, hsteps, hhalted, by rw [hpc, transferResultsToInputs_length]⟩

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

/-! ## Continuation Lemmas for Sequential Execution -/

section Continuation

variable {p1 p2 : Program}

/-- Reverse: stepping in concatenated program with pc in second part gives step in p2.
The config is "de-offset" by p1.length to get the corresponding p2 step. -/
theorem Step.of_concat_right {c c' : Config}
    (hpc_lo : p1.length ≤ c.pc)
    (hpc_hi : c.pc < p1.length + p2.length)
    (hstep : Step (p1.concat p2) c c') :
    Step p2 ⟨c.pc - p1.length, c.state⟩ ⟨c'.pc - p1.length, c'.state⟩ := by
  -- Get the instruction in p2 at the de-offset pc
  have hp2_pc : c.pc - p1.length < p2.length := by omega
  have hinstr : ∃ instr, p2.getInstr (c.pc - p1.length) = some instr := by
    simp only [Program.getInstr]
    exact ⟨p2[c.pc - p1.length], List.getElem?_eq_getElem hp2_pc⟩
  obtain ⟨instr, hinstr⟩ := hinstr
  -- The concat instruction is the shifted version
  have hconcat_instr : (p1.concat p2).getInstr c.pc = some (instr.shiftJumps p1.length) := by
    rw [Program.getInstr_concat_right c.pc hpc_lo hpc_hi, Program.getInstr_shiftJumps, hinstr]
    rfl
  -- Match on the instruction type
  -- Note: we're constructing Step p2 ⟨c.pc - p1.length, c.state⟩ ⟨c'.pc - p1.length, c'.state⟩
  -- and hinstr : p2.getInstr (c.pc - p1.length) = some instr
  set pc2 := c.pc - p1.length with hpc2_def
  cases instr with
  | Z n =>
    have hc' : c' = ⟨c.pc + 1, c.state.write n 0⟩ := by
      cases hstep <;> simp_all [Instr.shiftJumps]
    subst hc'
    have hpc'2 : c.pc + 1 - p1.length = pc2 + 1 := by omega
    rw [hpc'2]
    exact Step.zero hinstr
  | S n =>
    have hc' : c' = ⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩ := by
      cases hstep <;> simp_all [Instr.shiftJumps]
    subst hc'
    have hpc'2 : c.pc + 1 - p1.length = pc2 + 1 := by omega
    rw [hpc'2]
    exact Step.succ hinstr
  | T m n =>
    have hc' : c' = ⟨c.pc + 1, c.state.write n (c.state.read m)⟩ := by
      cases hstep <;> simp_all [Instr.shiftJumps]
    subst hc'
    have hpc'2 : c.pc + 1 - p1.length = pc2 + 1 := by omega
    rw [hpc'2]
    exact Step.trans hinstr
  | J m n q =>
    -- Either we jump (registers equal) or continue (registers different)
    cases hstep with
    | jump_eq h heq =>
      simp only [Instr.shiftJumps] at hconcat_instr
      simp only [hconcat_instr, Option.some.injEq, Instr.J.injEq] at h
      obtain ⟨rfl, rfl, hq⟩ := h
      -- hq : q + p1.length = q✝ (the shifted jump target)
      -- The goal has q✝ - p1.length in the target pc
      simp only [← hq, Nat.add_sub_cancel]
      exact Step.jump_eq hinstr heq
    | jump_ne h hne =>
      simp only [Instr.shiftJumps] at hconcat_instr
      simp only [hconcat_instr, Option.some.injEq, Instr.J.injEq] at h
      obtain ⟨rfl, rfl, _⟩ := h
      have hpc'2 : c.pc + 1 - p1.length = pc2 + 1 := by omega
      rw [hpc'2]
      exact Step.jump_ne hinstr hne
    | _ => simp_all [Instr.shiftJumps]

/-- Extract multi-step p2 execution from concat execution starting at pc = p1.length.
This is the reverse of `Steps.concat_right`: given execution in p1.concat(p2) that
starts at pc = p1.length and halts, we extract the corresponding p2 execution. -/
theorem Steps.of_concat_right {s : State} {c' : Config}
    (hsteps : Steps (p1.concat p2) ⟨p1.length, s⟩ c')
    (hhalted : c'.isHalted (p1.concat p2))
    (_hpc' : c'.pc ≥ p1.length) :
    ∃ c, Steps p2 ⟨0, s⟩ c ∧ c.isHalted p2 ∧ c.state = c'.state := by
  -- Key insight: all steps stay in the p2 range (pc ≥ p1.length)
  -- Generalize to handle arbitrary starting pc in the p2 range
  suffices h : ∀ (start : Config) (c' : Config),
      start.pc ≥ p1.length →
      Steps (p1.concat p2) start c' →
      c'.isHalted (p1.concat p2) →
      ∃ c, Steps p2 ⟨start.pc - p1.length, start.state⟩ c ∧ c.isHalted p2 ∧ c.state = c'.state by
    have := h ⟨p1.length, s⟩ c' (Nat.le_refl _) hsteps hhalted
    simp only [Nat.sub_self] at this
    exact this
  intro start c'' hstart hsteps' hhalted'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- In the refl case, start = c'' (both become c'')
    use ⟨c''.pc - p1.length, c''.state⟩, Relation.ReflTransGen.refl
    constructor
    · simp only [Config.isHalted] at hhalted' ⊢
      simp only [Program.concat, List.length_append, Program.shiftJumps, List.length_map] at hhalted'
      omega
    · rfl
  | @head a b hstep hrest ih =>
    have ha_in_range : a.pc < p1.length + p2.length := by
      by_contra hc
      simp only [not_lt] at hc
      have hhalted_a : a.isHalted (p1.concat p2) := by
        simp only [Config.isHalted, Program.concat, List.length_append,
                   Program.shiftJumps, List.length_map]
        omega
      exact Step.halted_no_step hhalted_a hstep
    have hstep_p2 := Step.of_concat_right hstart ha_in_range hstep
    have hb_pc_ge : b.pc ≥ p1.length := by
      have ha_ge := hstart  -- a.pc ≥ p1.length
      cases hstep with
      | zero h => simp only []; omega
      | succ h => simp only []; omega
      | trans h => simp only []; omega
      | jump_eq h heq =>
        -- The instruction is in p2's range, so its jump target is shifted by p1.length
        -- h : (p1.concat p2).getInstr a.pc = some (J m n q)
        -- Since a.pc ≥ p1.length, this instruction comes from p2.shiftJumps p1.length
        -- So the target q is of the form original_target + p1.length
        have hconcat := Program.getInstr_concat_right a.pc hstart ha_in_range
        rw [hconcat, Program.getInstr_shiftJumps] at h
        -- h : Option.map (Instr.shiftJumps p1.length) (p2.getInstr (a.pc - p1.length)) = some (J m n q)
        -- The original instruction in p2 has target q' and the shifted one has q = q' + p1.length
        cases hp2 : p2.getInstr (a.pc - p1.length) with
        | none => simp only [hp2, Option.map_none] at h; nomatch h
        | some instr =>
          simp only [hp2, Option.map_some] at h
          cases instr with
          | J m' n' q' =>
            simp only [Instr.shiftJumps, Option.some.injEq, Instr.J.injEq] at h
            -- h gives us that the jump target is q' + p1.length = q✝
            -- Goal is: b.pc ≥ p1.length, where b.pc = q✝ (the jump target)
            obtain ⟨_, _, hq_eq⟩ := h
            simp only [← hq_eq]
            omega
          | Z _ => simp only [Instr.shiftJumps, Option.some.injEq] at h; nomatch h
          | S _ => simp only [Instr.shiftJumps, Option.some.injEq] at h; nomatch h
          | T _ _ => simp only [Instr.shiftJumps, Option.some.injEq] at h; nomatch h
      | jump_ne h hne => simp only []; omega
    -- ih takes hb_pc_ge and gives us ∃ c, Steps p2 ⟨b.pc - p1.length, b.state⟩ c ∧ ...
    obtain ⟨c, hrest_p2, hhalted_c, hstate_eq⟩ := ih hb_pc_ge
    exact ⟨c, Relation.ReflTransGen.head hstep_p2 hrest_p2, hhalted_c, hstate_eq⟩

/-- Generalized suffix extraction: if p1.concat p2 halts starting from ⟨0, s⟩ and p1 is standard form,
then p1 halts at ⟨p1.length, s'⟩ for some s', and p2 halts starting from ⟨0, s'⟩.

This generalizes the suffix part of `Halts.suffix_of_concat_sf` to arbitrary starting states. -/
theorem suffix_of_concat_from_zero {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c)
    (hhalted : c.isHalted (p1.concat p2))
    (h1 : p1.IsStandardForm) :
    ∃ s', Steps p1 ⟨0, s⟩ ⟨p1.length, s'⟩ ∧
          (∃ c', Steps p2 ⟨0, s'⟩ c' ∧ c'.isHalted p2) := by
  -- First extract that p1 halts
  obtain ⟨c1, hsteps_p1, hhalted_p1⟩ := prefix_of_concat_from_zero hsteps hhalted h1

  -- By standard form, c1.pc = p1.length
  have hc1_pc : c1.pc = p1.length := by
    simp only [Config.isHalted] at hhalted_p1
    by_contra hne
    have hgt : c1.pc > p1.length := Nat.lt_of_le_of_ne hhalted_p1 (Ne.symm hne)
    have hinv : ∀ c0 c' : Config, Steps p1 c0 c' → c0.pc ≤ p1.length → c'.pc ≤ p1.length := by
      intro c0 c' hsteps' hpc0
      induction hsteps' using Relation.ReflTransGen.head_induction_on with
      | refl => exact hpc0
      | @head a b hstep _ ih =>
        have hb_le : b.pc ≤ p1.length := by
          by_cases ha_halted : a.isHalted p1
          · exact Step.halted_no_step ha_halted hstep |>.elim
          simp only [Config.isHalted, not_le] at ha_halted
          cases hstep with
          | zero h =>
            simp only [Program.getInstr] at h
            have ⟨hpc_lt, _⟩ := List.getElem?_eq_some_iff.mp h
            grind
          | succ h =>
            simp only [Program.getInstr] at h
            have ⟨hpc_lt, _⟩ := List.getElem?_eq_some_iff.mp h
            grind
          | trans h =>
            simp only [Program.getInstr] at h
            have ⟨hpc_lt, _⟩ := List.getElem?_eq_some_iff.mp h
            grind
          | jump_eq h _ =>
            simp only [Program.getInstr] at h
            have ⟨hpc_valid, hinstr_eq⟩ := List.getElem?_eq_some_iff.mp h
            have hmem : Instr.J _ _ _ ∈ p1 := hinstr_eq ▸ List.getElem_mem hpc_valid
            simp only [Program.IsStandardForm, Program.isStandardForm, List.all_eq_true] at h1
            have hbounded := h1 _ hmem
            simp only [Instr.hasBoundedJump, decide_eq_true_eq] at hbounded
            exact hbounded
          | jump_ne h _ =>
            simp only [Program.getInstr] at h
            have ⟨hpc_lt, _⟩ := List.getElem?_eq_some_iff.mp h
            grind
        exact ih hb_le
    have hstart : (⟨0, s⟩ : Config).pc ≤ p1.length := by simp
    have hc1_le := hinv ⟨0, s⟩ c1 hsteps_p1 hstart
    omega

  use c1.state
  constructor
  · convert hsteps_p1 using 1
    ext <;> simp [hc1_pc]

  have hsteps_p1_lifted : Steps (p1.concat p2) ⟨0, s⟩ ⟨p1.length, c1.state⟩ := by
    have h := @Steps.concat_left_prefix p1 p2 ⟨0, s⟩ c1 hsteps_p1 hhalted_p1
    convert h using 1
    ext <;> simp [hc1_pc]

  have h_suffix : Steps (p1.concat p2) ⟨p1.length, c1.state⟩ c :=
    Steps.deterministic_continuation hsteps_p1_lifted hsteps hhalted

  have hc_pc : c.pc ≥ p1.length := by
    simp only [Config.isHalted, Program.concat_length] at hhalted
    omega
  obtain ⟨c', hsteps_p2, hhalted_p2, _⟩ := Steps.of_concat_right h_suffix hhalted hc_pc
  exact ⟨c', hsteps_p2, hhalted_p2⟩

/-- If p1.concat p2 halts and p1 is standard form, then p2 halts from the intermediate state.

After p1 halts at pc = p1.length, the remaining execution is exactly p2 starting
from the state left by p1. -/
theorem Halts.suffix_of_concat_sf {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs)
    (h1 : p1.IsStandardForm) :
    ∃ s : State, Halts p1 inputs ∧
                 (∀ hP1 : Halts p1 inputs, s = (Classical.choose hP1).state) ∧
                 (∃ c, Steps p2 ⟨0, s⟩ c ∧ c.isHalted p2) := by
  -- Get the intermediate state from p1's halting
  have hP1 := Halts.prefix_of_concat_sf hH h1
  have hc1_spec := Classical.choose_spec hP1
  have hc1_pc := h1.halts_at_length inputs (Classical.choose hP1) hc1_spec.1 hc1_spec.2
  use (Classical.choose hP1).state
  refine ⟨hP1, ?_, ?_⟩
  · intro hP1'
    -- By determinism, both choose the same config
    have huniq := Steps.halts_unique hc1_spec.1 hc1_spec.2
                    (Classical.choose_spec hP1').1 (Classical.choose_spec hP1').2
    rw [huniq]
  · -- The execution of H from Config.init to final config passes through c1
    -- The suffix from c1 to final is the execution of p2 from c1.state
    let c1 := Classical.choose hP1
    let s1 := c1.state
    -- Get the halted config of H
    obtain ⟨cH, hH_steps, hH_halted⟩ := hH
    -- Get the p1 execution lifted to H
    have h_to_c1 : Steps (p1.concat p2) (Config.init inputs) c1 :=
      Steps.concat_left_prefix hc1_spec.1 hc1_spec.2
    -- By deterministic_continuation, the path from c1 to cH exists
    have h_suffix : Steps (p1.concat p2) c1 cH :=
      Steps.deterministic_continuation h_to_c1 hH_steps hH_halted
    -- Rewrite c1 as ⟨p1.length, s1⟩
    have h_suffix_start : c1 = ⟨p1.length, s1⟩ := by
      ext
      · exact hc1_pc
      · rfl
    rw [h_suffix_start] at h_suffix
    -- Show cH.pc ≥ p1.length (needed for Steps.of_concat_right)
    have hcH_pc : cH.pc ≥ p1.length := by
      simp only [Config.isHalted, Program.concat_length] at hH_halted
      omega
    -- Extract p2 execution using Steps.of_concat_right
    -- s1 = c1.state = (Classical.choose hP1).state by definition
    have hs1_eq : s1 = (Classical.choose hP1).state := rfl
    rw [← hs1_eq]
    obtain ⟨c, hsteps_p2, hhalted_p2, _⟩ := Steps.of_concat_right h_suffix hH_halted hcH_pc
    exact ⟨c, hsteps_p2, hhalted_p2⟩

/-- If p1 halts (by falling through) and p2 halts when started from p1's final state,
then p1.concat p2 halts.

This is the key continuation lemma: we can chain halting programs.
The hypothesis h1_pc ensures p1 halted by falling through (pc = p1.length),
not by jumping beyond the program. -/
theorem Halts.concat_continuation {inputs : List ℕ}
    (h1 : Halts p1 inputs)
    (h1_pc : (Classical.choose h1).pc = p1.length)
    (h2 : ∃ c, Steps p2 ⟨0, (Classical.choose h1).state⟩ c ∧ c.isHalted p2) :
    Halts (p1.concat p2) inputs := by
  -- Get the halted config from p1
  obtain ⟨hsteps1, hhalted1⟩ := Classical.choose_spec h1
  let c1 := Classical.choose h1
  -- Get the halted config from p2
  obtain ⟨c2, hsteps2, hhalted2⟩ := h2
  -- Lift p1's execution to the concatenation
  have hsteps1' := Steps.concat_left_prefix (p2 := p2) hsteps1 hhalted1
  -- Now continue from where p1 halted
  -- After p1 halts: we're at ⟨c1.pc, c1.state⟩ = ⟨p1.length, c1.state⟩
  -- p2 starts at ⟨0, c1.state⟩, so we need ⟨0 + p1.length, c1.state⟩ = ⟨p1.length, c1.state⟩
  have hsteps2' := Steps.concat_right (p1 := p1) hsteps2 hhalted2
  -- The start of p2's lifted execution: ⟨0 + p1.length, c1.state⟩
  -- This matches where p1 halted: ⟨p1.length, c1.state⟩ (using h1_pc)
  have hstart_eq : (⟨0 + p1.length, c1.state⟩ : Config) = ⟨c1.pc, c1.state⟩ := by
    simp only [Nat.zero_add]
    rw [← h1_pc]
  -- Rewrite hsteps2' to start from c1
  rw [hstart_eq] at hsteps2'
  -- The concatenation is transitive: first do p1's steps, then p2's
  have hsteps_total := Relation.ReflTransGen.trans hsteps1' hsteps2'
  -- Final config: c2 shifted
  refine ⟨⟨c2.pc + p1.length, c2.state⟩, hsteps_total, ?_⟩
  -- Show the final config is halted in p1.concat p2
  simp only [Config.isHalted, Program.concat, List.length_append, Program.shiftJumps,
             List.length_map, Config.isHalted] at hhalted2 ⊢
  omega

/-- If p1 halts (as a standard form program) and p2 is straight-line, then p1.concat p2 halts.

This is a convenient corollary of `concat_continuation` for the common case where
the second program is straight-line (transfers, clears, etc.). Standard form ensures
p1 halts by falling through (pc = p1.length). -/
theorem Halts.concat_straightLine {p1 p2 : Program} {inputs : List ℕ}
    (h1 : Halts p1 inputs)
    (h1_sf : p1.IsStandardForm)
    (h2_sl : p2.isStraightLine = true) :
    Halts (p1.concat p2) inputs := by
  -- Standard form ensures p1 halted by falling through
  have h1_pc : (Classical.choose h1).pc = p1.length := by
    have hspec := Classical.choose_spec h1
    exact h1_sf.halts_at_length inputs (Classical.choose h1) hspec.1 hspec.2
  -- Straight-line p2 halts from any state
  have h2 : ∃ c, Steps p2 ⟨0, (Classical.choose h1).state⟩ c ∧ c.isHalted p2 := by
    obtain ⟨c, hsteps, hhalted, _⟩ := straightLine_halts_from_state h2_sl (Classical.choose h1).state
    exact ⟨c, hsteps, hhalted⟩
  exact Halts.concat_continuation h1 h1_pc h2

end Continuation

end Urm
