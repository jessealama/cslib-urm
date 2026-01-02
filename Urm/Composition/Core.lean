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

theorem copyRegisterRange_isStraightLine (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).isStraightLine = true := by
  simp only [Program.copyRegisterRange, Program.isStraightLine, List.all_map, List.all_eq_true]
  intro i _
  simp [Instr.isNonJumping]

/-! ## transferResultsToInputs Properties -/

theorem transferResultsToInputs_length (resultStart arityF : ℕ) :
    (Program.transferResultsToInputs resultStart arityF).length = arityF := by
  simp [Program.transferResultsToInputs]

theorem transferResultsToInputs_isStraightLine (resultStart arityF : ℕ) :
    (Program.transferResultsToInputs resultStart arityF).isStraightLine = true := by
  simp only [Program.transferResultsToInputs, Program.isStraightLine, List.all_map, List.all_eq_true]
  intro i _
  simp [Instr.isNonJumping]

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
  | zero h | succ h | trans h =>
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    simp only [State.read, State.write]
    exact Function.update_of_ne (by omega) _ _
  | jump_eq _ _ | jump_ne _ _ => rfl

/-- Multi-step execution preserves registers above maxRegister. -/
theorem Steps.preserves_high_register {c c' : Config} (hsteps : Steps p c c') (r : ℕ)
    (hr : p.maxRegister < r) : c'.state.read r = c.state.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
    rw [ih]
    exact Step.preserves_high_register hstep r hr

end RegisterIsolation

/-! ## Agreeing State Lemmas -/

/-- If p halts from a state s that agrees with Config.init inputs on relevant registers,
then Halts p inputs. This is the key lemma for extracting halting from execution traces. -/
theorem Halts.of_agreeing_state {p : Program} {inputs : List ℕ} {s : State} {c : Config}
    (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.isHalted p)
    (hagree : ∀ r, r ≤ p.maxRegister → s.read r = (State.fromInputs inputs).read r) :
    Halts p inputs := by
  have hagree' : s.agreeOn (State.fromInputs inputs) 0 p.maxRegister := fun r _ hhi => hagree r hhi
  have hpc_eq : (⟨0, s⟩ : Config).pc = (Config.init inputs).pc := rfl
  obtain ⟨c', hsteps', hpc', _⟩ := Steps.agreeOn hsteps hpc_eq hagree'
  exact ⟨c', hsteps', by simp only [Config.isHalted] at hhalted ⊢; omega⟩

/-! ## Part.sequence for Partial Function Families -/

/-- Sequence a finite family of partial values into a partial function.

`Part.sequence f` is defined iff all `f i` are defined, and when defined,
returns a function that gives `(f i).get` for each `i`. -/
def Part.sequence {α : Type*} : {n : ℕ} → (Fin n → Part α) → Part (Fin n → α)
  | 0, _ => Part.some Fin.elim0
  | _ + 1, f => (f 0).bind fun a0 =>
      (Part.sequence (fun i => f i.succ)).map fun rest =>
        Fin.cons a0 rest

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
  simp only [Program.concat, Program.isStraightLine, List.all_append, Program.shiftJumps,
    List.all_map] at h1 h2 ⊢
  rw [Bool.and_eq_true]
  exact ⟨h1, by convert h2 using 2; funext instr; cases instr <;> simp [Instr.shiftJumps, Instr.isNonJumping]⟩

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

/-- Generalized prefix extraction: if p1.concat p2 halts starting from ⟨0, s⟩ and p1 is standard form,
then p1 halts from ⟨0, s⟩. -/
theorem prefix_of_concat_from_zero {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c)
    (hhalted : c.isHalted (p1.concat p2))
    (h1 : p1.IsStandardForm) :
    ∃ c', Steps p1 ⟨0, s⟩ c' ∧ c'.isHalted p1 := by
  by_cases hp1 : p1.length = 0
  · exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, by simp [Config.isHalted, hp1]⟩
  suffices h : ∀ c0 c' : Config,
      Steps (p1.concat p2) c0 c' → c'.isHalted (p1.concat p2) →
      c0.pc ≤ p1.length →
      (∃ c'', Steps p1 c0 c'' ∧ c''.isHalted p1) by
    exact h ⟨0, s⟩ c hsteps hhalted (by simp)
  intro c0 c' hsteps'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hhalted' hpc_le
    simp only [Config.isHalted, Program.concat_length] at hhalted'
    exact ⟨c', Relation.ReflTransGen.refl, by simp [Config.isHalted]; omega⟩
  | @head a d hstep hrest ih =>
    intro hhalted' hpc_le
    by_cases hhalted_p1 : a.isHalted p1
    · exact ⟨a, Relation.ReflTransGen.refl, hhalted_p1⟩
    have hpc_lt : a.pc < p1.length := by simp only [Config.isHalted, not_le] at hhalted_p1; exact hhalted_p1
    have hstep_p1 : Step p1 a d := Step.of_concat_left hpc_lt hstep
    obtain ⟨c'', hsteps_dc'', hhalted_c''⟩ := ih hhalted' (Step.pc_le_length_of_step h1 hstep_p1)
    exact ⟨c'', Relation.ReflTransGen.head hstep_p1 hsteps_dc'', hhalted_c''⟩

/-- If p1.concat p2 halts and p1 is standard form, then p1 halts.

This is the "prefix halts" property: execution of the concatenation must pass through
a state where p1 has halted (at pc = p1.length) before continuing into p2. -/
theorem Halts.prefix_of_concat_sf {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs)
    (h1 : p1.IsStandardForm) :
    Halts p1 inputs := by
  obtain ⟨cH, hsteps, hhalted⟩ := hH
  exact prefix_of_concat_from_zero hsteps hhalted h1

/-- clearRegisters produces a straight-line program. -/
theorem clearRegisters_isStraightLine (maxReg : ℕ) :
    (Program.clearRegisters maxReg).isStraightLine = true := by
  simp only [Program.clearRegisters, Program.isStraightLine, List.all_map]
  induction maxReg + 1 with
  | zero => simp only [List.range_zero, List.all_nil]
  | succ k ih =>
    simp only [List.range_succ, List.all_append, ih, List.all_cons, List.all_nil,
      Function.comp_apply, Instr.isNonJumping, Bool.and_self]

/-! ## Register Write Tracking for copyRegisterRange and transferResultsToInputs -/

/-- Each instruction in copyRegisterRange writes to a register in [dstStart, dstStart + count). -/
theorem copyRegisterRange_writesTo (srcStart dstStart count : ℕ)
    (instr : Instr) (hinstr : instr ∈ Program.copyRegisterRange srcStart dstStart count) :
    ∃ i < count, instr.writesTo = some (dstStart + i) := by
  simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hinstr
  obtain ⟨i, hi, hinstr_eq⟩ := hinstr
  use i, hi
  simp [← hinstr_eq, Instr.writesTo]

/-- copyRegisterRange only writes to registers in [dstStart, dstStart + count). -/
theorem copyRegisterRange_preserves_outside (srcStart dstStart count : ℕ)
    (r : ℕ) (hr : r < dstStart ∨ r ≥ dstStart + count) :
    ∀ instr, instr ∈ Program.copyRegisterRange srcStart dstStart count → instr.writesTo ≠ some r := by
  intro instr hinstr
  obtain ⟨i, hi, hwrites⟩ := copyRegisterRange_writesTo srcStart dstStart count instr hinstr
  rw [hwrites]
  simp only [ne_eq, Option.some.injEq]
  omega

/-- Each instruction in transferResultsToInputs writes to a register in [0, arityF). -/
theorem transferResultsToInputs_writesTo (resultStart arityF : ℕ)
    (instr : Instr) (hinstr : instr ∈ Program.transferResultsToInputs resultStart arityF) :
    ∃ i < arityF, instr.writesTo = some i := by
  simp only [Program.transferResultsToInputs, List.mem_map, List.mem_range] at hinstr
  obtain ⟨i, hi, hinstr_eq⟩ := hinstr
  use i, hi
  simp [← hinstr_eq, Instr.writesTo]

/-- transferResultsToInputs only writes to registers in [0, arityF). -/
theorem transferResultsToInputs_preserves_outside (resultStart arityF : ℕ)
    (r : ℕ) (hr : r ≥ arityF) :
    ∀ instr, instr ∈ Program.transferResultsToInputs resultStart arityF → instr.writesTo ≠ some r := by
  intro instr hinstr
  obtain ⟨i, hi, hwrites⟩ := transferResultsToInputs_writesTo resultStart arityF instr hinstr
  rw [hwrites]
  simp only [ne_eq, Option.some.injEq]
  omega

/-- After executing instruction k (which is T src dst) in a straight-line program,
register dst contains the value that was in src at that point. -/
theorem straightLine_transfer_after_exec {p : Program} (_hsl : p.isStraightLine = true)
    (s : State) (k src dst : ℕ) (hk : k < p.length) (hwrite : p[k] = Instr.T src dst)
    (c_k : Config) (hsteps_k : Steps p ⟨0, s⟩ c_k) (hpc_k : c_k.pc = k) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k + 1 ∧ c.state.read dst = c_k.state.read src := by
  have hinstr : p.getInstr k = some (Instr.T src dst) := by
    simp only [Program.getInstr, List.getElem?_eq_getElem hk, hwrite]
  have hinstr' : p.getInstr c_k.pc = some (Instr.T src dst) := by rw [hpc_k]; exact hinstr
  let c_next : Config := ⟨c_k.pc + 1, c_k.state.write dst (c_k.state.read src)⟩
  have hstep : Step p c_k c_next := Step.trans hinstr'
  have hpc_next : c_next.pc = k + 1 := by simp only [c_next, hpc_k]
  refine ⟨c_next, Relation.ReflTransGen.tail hsteps_k hstep, hpc_next, ?_⟩
  simp only [c_next, State.write_read_same]

/-- In a straight-line program with T instructions, track what gets written to a register.
When instruction at index k is T src dst, and no later instruction writes to dst,
the final state has dst = (state before k).read src. -/
theorem straightLine_transfer_result {p : Program} (hsl : p.isStraightLine = true)
    (s : State) (k src dst : ℕ) (hk : k < p.length)
    (hwrite : p[k] = Instr.T src dst)
    (hnowrite : ∀ j (hj : j < p.length), k < j → (p[j]'hj).writesTo ≠ some dst) :
    ∃ s_before : State,
      (∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k ∧ c.state = s_before) ∧
      (straightLineFinalState hsl s).read dst = s_before.read src := by
  obtain ⟨c_k, hsteps_k, hpc_k⟩ := straightLine_state_at_pc hsl s k (Nat.le_of_lt hk)
  use c_k.state
  constructor
  · exact ⟨c_k, hsteps_k, hpc_k, rfl⟩
  · have ⟨hsteps_final, hhalted, _⟩ := straightLineFinalState_spec hsl s
    obtain ⟨c_after_k, hsteps_to_after_k, hpc_after_k, hval⟩ :=
      straightLine_transfer_after_exec hsl s k src dst hk hwrite c_k hsteps_k hpc_k
    let final := Classical.choose (straightLine_halts_from_state hsl s)
    have hsteps_suffix : Steps p c_after_k final :=
      Steps.deterministic_continuation hsteps_to_after_k hsteps_final hhalted
    show (Classical.choose (straightLine_halts_from_state hsl s)).state.read dst = c_k.state.read src
    -- Show that the suffix execution preserves dst
    suffices h : ∀ (a b : Config), a.pc > k → Steps p a b → b.isHalted p →
        b.state.read dst = a.state.read dst by
      have hpc_gt : c_after_k.pc > k := by omega
      rw [h c_after_k final hpc_gt hsteps_suffix hhalted, hval]
    intro a b hpc_gt hsteps hhalted_b
    induction hsteps using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | @head a' c' hstep hrest ih =>
      have hc'_pc_gt : c'.pc > k := by
        cases hstep with
        | zero h => simp only []; omega
        | succ h => simp only []; omega
        | trans h => simp only []; omega
        | jump_eq h heq' =>
          exfalso
          simp only [Program.isStraightLine, List.all_eq_true] at hsl
          have ha'_pc_lt : a'.pc < p.length := by
            by_contra hc; simp only [not_lt] at hc
            exact Step.halted_no_step hc (Step.jump_eq h heq')
          simp only [Program.getInstr] at h
          have hmem := List.getElem?_eq_some_iff.mp h
          have hinstr_sl := hsl _ (hmem.2 ▸ List.getElem_mem ha'_pc_lt)
          simp only [Instr.isNonJumping] at hinstr_sl
          exact Bool.false_ne_true hinstr_sl
        | jump_ne h _ => simp only []; omega
      rw [ih hc'_pc_gt]
      apply Step.straightLine_preserves hsl hstep
      intro instr hinstr
      have ha'_pc_lt : a'.pc < p.length := by
        by_contra hc; simp only [not_lt] at hc
        exact Step.halted_no_step hc hstep
      simp only [Program.getInstr] at hinstr
      have heq' : p[a'.pc] = instr := (List.getElem?_eq_some_iff.mp hinstr).2
      rw [← heq']
      exact hnowrite a'.pc ha'_pc_lt hpc_gt

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
      have ha_ge := hstart
      cases hstep with
      | zero _ | succ _ | trans _ | jump_ne _ _ => simp only []; omega
      | jump_eq h _ =>
        have hconcat := Program.getInstr_concat_right a.pc hstart ha_in_range
        rw [hconcat, Program.getInstr_shiftJumps] at h
        cases hp2 : p2.getInstr (a.pc - p1.length) with
        | none => simp only [hp2, Option.map_none] at h; nomatch h
        | some instr =>
          simp only [hp2, Option.map_some] at h
          cases instr with
          | J _ _ q' =>
            simp only [Instr.shiftJumps, Option.some.injEq, Instr.J.injEq] at h
            obtain ⟨_, _, hq_eq⟩ := h; simp only [← hq_eq]; omega
          | _ => simp only [Instr.shiftJumps, Option.some.injEq] at h; nomatch h
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
    have hc1_le := h1.pc_le_length hsteps_p1 (by simp : (⟨0, s⟩ : Config).pc ≤ p1.length)
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

end Continuation

end Urm
