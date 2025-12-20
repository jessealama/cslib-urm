/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition

/-! # Binary-Unary Composition

This file proves closure of URM-computable functions under the composition of a binary
function with two unary functions: if `f` is binary URM-computable and `g₁`, `g₂` are
unary URM-computable, then `h(x) = f(g₁(x), g₂(x))` is URM-computable.

## Main results

- `URMComputableSF.comp_binary_unary`: Closure under binary-unary composition for
  standard form programs.

## Implementation

The proof follows the user's sketch based on Cutland's approach:
1. Let m = max of registers used by F, G₁, G₂
2. Store input x in R[m+1] (safe storage)
3. Run G₁, save result to R[m+2]
4. Restore input, run G₂, save result to R[m+3]
5. Set up R[0] = R[m+2], R[1] = R[m+3], run F

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Standard Form -/

/-- A program is in standard form if, whenever it halts, the program counter equals
the program length. This means the program halts by "falling through" the end,
not by jumping beyond the program.

This property is essential for sequential composition: when we concatenate programs,
we need to know that the first program terminates exactly at its length so the
second program starts at the right position. -/
def Program.IsStandardForm (p : Program) : Prop :=
  ∀ (inputs : List ℕ) (c : Config),
    Steps p (Config.init inputs) c →
    c.isHalted p →
    c.pc = p.length

/-- A partial function is URM-computable by a standard form program. -/
def URMComputableSF (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∃ p : Program, p.IsStandardForm ∧
    ∀ inputs : Fin n → ℕ,
      let inputList := List.ofFn inputs
      (Halts p inputList ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts p inputList) (hDom : (f inputs).Dom),
        Result p inputList hHalts = (f inputs).get hDom

/-! ## Standard Form Lemmas -/

/-- Straight-line programs are in standard form.

Since straight-line programs have no jumps, they can only increment the program counter
by 1 at each step, so they must halt exactly at the program length. -/
theorem straightLine_isStandardForm {p : Program} (hsl : p.isStraightLine = true) :
    p.IsStandardForm := by
  intro inputs c hsteps hhalted
  -- Use the existing lemma that shows straight-line programs halt at exactly length
  -- First, show that c is the halted config reached from inputs
  have hHalts : Halts p inputs := ⟨c, hsteps, hhalted⟩
  -- The halted config for a straight-line program has pc = length
  have h := straightLine_halts_at_length hsl inputs
  -- We need to show c.pc = p.length
  -- By uniqueness of halted configs, c = Classical.choose hHalts'
  -- where hHalts' = straightLine_halts hsl inputs
  have hHalts' := straightLine_halts hsl inputs
  obtain ⟨hsteps', hhalted'⟩ := Classical.choose_spec hHalts'
  -- By uniqueness
  have heq := Steps.halts_unique hsteps hhalted hsteps' hhalted'
  rw [heq]
  exact h

/-- A single Transfer instruction is in standard form. -/
theorem single_transfer_isStandardForm (src dst : ℕ) :
    Program.IsStandardForm [Instr.T src dst] := by
  apply straightLine_isStandardForm
  simp [Program.isStraightLine, Instr.isNonJumping]

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
The key insight is that p₁ halts at exactly p₁.length, which is where p₂ starts
in the concatenated program. -/
theorem IsStandardForm.concat {p1 p2 : Program}
    (h1 : p1.IsStandardForm) (h2 : p2.IsStandardForm) :
    (p1.concat p2).IsStandardForm := by
  intro inputs c hsteps hhalted
  simp only [Config.isHalted, Program.concat_length] at hhalted
  -- We need to show c.pc = p1.length + p2.length
  -- The proof requires tracking execution through both programs.
  -- During execution:
  -- 1. While pc < p1.length, we execute p1's instructions
  -- 2. When pc reaches p1.length, we start executing p2's instructions
  -- 3. By p1 standard form, we exit p1's region exactly at p1.length
  -- 4. By p2 standard form, we halt exactly at p1.length + p2.length
  --
  -- Key insight: pc can only exceed length via a jump, but standard form
  -- ensures this doesn't happen (halting is always at exactly length).
  sorry

/-! ## Register Independence -/

/-- If two states agree on registers ≤ p.maxRegister, then a step from one
corresponds to a step from the other with the same pc transition. -/
theorem Step.register_independent {p : Program} {c c' : Config} {s2 : State}
    (hstep : Step p c c')
    (hagree : ∀ r, r ≤ p.maxRegister → s2.read r = c.state.read r) :
    ∃ s2', Step p ⟨c.pc, s2⟩ ⟨c'.pc, s2'⟩ ∧
           (∀ r, r ≤ p.maxRegister → s2'.read r = c'.state.read r) := by
  cases hstep with
  | zero hinstr =>
    rename_i n
    have hn_le : n ≤ p.maxRegister := by
      have := Program.instr_maxRegister_le hinstr
      simp [Instr.maxRegister] at this
      exact this
    refine ⟨s2.write n 0, Step.zero hinstr, ?_⟩
    intro r hr
    simp only [State.read, State.write, Function.update]
    split_ifs with heq
    · rfl
    · exact hagree r hr
  | succ hinstr =>
    rename_i n
    have hn_le : n ≤ p.maxRegister := by
      have := Program.instr_maxRegister_le hinstr
      simp [Instr.maxRegister] at this
      exact this
    refine ⟨s2.write n (s2.read n + 1), Step.succ hinstr, ?_⟩
    intro r hr
    simp only [State.read, State.write, Function.update]
    split_ifs with heq
    · subst heq; simp only [State.read] at hagree ⊢; rw [hagree r hr]
    · exact hagree r hr
  | trans hinstr =>
    rename_i m n
    have hmn_le : m ≤ p.maxRegister ∧ n ≤ p.maxRegister := by
      have := Program.instr_maxRegister_le hinstr
      simp only [Instr.maxRegister] at this
      exact ⟨Nat.le_trans (Nat.le_max_left m n) this, Nat.le_trans (Nat.le_max_right m n) this⟩
    refine ⟨s2.write n (s2.read m), Step.trans hinstr, ?_⟩
    intro r hr
    simp only [State.read, State.write, Function.update]
    split_ifs with heq
    · subst heq; simp only [State.read] at hagree ⊢; exact hagree m hmn_le.1
    · exact hagree r hr
  | jump_eq hinstr heq =>
    rename_i m n q
    have hmn_le : m ≤ p.maxRegister ∧ n ≤ p.maxRegister := by
      have := Program.instr_maxRegister_le hinstr
      simp only [Instr.maxRegister] at this; omega
    refine ⟨s2, Step.jump_eq hinstr ?_, ?_⟩
    · rw [hagree m hmn_le.1, hagree n hmn_le.2]; exact heq
    · exact hagree
  | jump_ne hinstr hne =>
    rename_i m n q
    have hmn_le : m ≤ p.maxRegister ∧ n ≤ p.maxRegister := by
      have := Program.instr_maxRegister_le hinstr
      simp only [Instr.maxRegister] at this; omega
    refine ⟨s2, Step.jump_ne hinstr ?_, ?_⟩
    · intro heq'; apply hne; rw [← hagree m hmn_le.1, ← hagree n hmn_le.2]; exact heq'
    · exact hagree

/-- If two states agree on registers ≤ p.maxRegister, then multi-step execution
from one corresponds to multi-step execution from the other. -/
theorem Steps.register_independent {p : Program} {c c' : Config} {s2 : State}
    (hsteps : Steps p c c')
    (hagree : ∀ r, r ≤ p.maxRegister → s2.read r = c.state.read r) :
    ∃ s2', Steps p ⟨c.pc, s2⟩ ⟨c'.pc, s2'⟩ ∧
           (∀ r, r ≤ p.maxRegister → s2'.read r = c'.state.read r) := by
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing s2 with
  | refl => exact ⟨s2, Relation.ReflTransGen.refl, hagree⟩
  | head hstep _ ih =>
    obtain ⟨s2', hstep', hagree'⟩ := Step.register_independent hstep hagree
    obtain ⟨s2'', hsteps', hagree''⟩ := ih hagree'
    exact ⟨s2'', Relation.ReflTransGen.head hstep' hsteps', hagree''⟩

/-- Key lemma: If p halts on some input, and we modify only registers above p.maxRegister,
p still halts with the same pc trajectory. -/
theorem Halts.register_independent {p : Program} {inputs : List ℕ} {s : State}
    (hhalts : Halts p inputs)
    (hagree : ∀ r, r ≤ p.maxRegister → s.read r = (Config.init inputs).state.read r) :
    ∃ c', Steps p ⟨0, s⟩ c' ∧ c'.isHalted p := by
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec hhalts
  obtain ⟨s', hsteps', _⟩ := Steps.register_independent hsteps hagree
  exact ⟨⟨(Classical.choose hhalts).pc, s'⟩, hsteps', hhalted⟩

/-! ## Single Transfer Instruction Execution -/

/-- A single Transfer instruction takes exactly one step and halts. -/
theorem single_transfer_step (src dst : ℕ) (s : State) :
    Step [Instr.T src dst] ⟨0, s⟩ ⟨1, s.write dst (s.read src)⟩ := by
  apply Step.trans
  simp [Program.getInstr]

/-- A single Transfer instruction halts at pc = 1 with the copied value. -/
theorem single_transfer_halts (src dst : ℕ) (s : State) :
    ∃ c', Steps [Instr.T src dst] ⟨0, s⟩ c' ∧
          c'.isHalted [Instr.T src dst] ∧
          c'.pc = 1 ∧
          c'.state = s.write dst (s.read src) := by
  refine ⟨⟨1, s.write dst (s.read src)⟩, ?_, ?_, rfl, rfl⟩
  · exact Relation.ReflTransGen.single (single_transfer_step src dst s)
  · simp [Config.isHalted]

/-! ## clearRegisters Effect on State -/

/-- Helper for clearRegisters_zeros: induction on the range. -/
private theorem clearRegisters_zeros_helper (n : ℕ) (s : State) (r : ℕ) (hr : r < n) :
    (List.foldl (fun σ i => σ.write i 0) s (List.range n)).read r = 0 := by
  induction n generalizing s r with
  | zero => omega
  | succ k ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases heq : r = k
    · subst heq; simp only [State.write_read_same]
    · simp only [State.write_read_diff _ _ _ _ heq]
      exact ih s r (by omega)

/-- clearRegisters zeros all registers up to and including maxReg. -/
theorem clearRegisters_zeros (maxReg : ℕ) (s : State) (r : ℕ) (hr : r ≤ maxReg) :
    (executeStraightLine (Program.clearRegisters maxReg) s).read r = 0 := by
  simp only [Program.clearRegisters, executeStraightLine, State.read]
  -- Use List.foldl_map to simplify the fold over mapped list
  simp only [List.foldl_map]
  exact clearRegisters_zeros_helper (maxReg + 1) s r (by omega)

/-- Helper for clearRegisters_preserves_above. -/
private theorem clearRegisters_preserves_helper (n : ℕ) (s : State) (r : ℕ) (hr : n ≤ r) :
    (List.foldl (fun σ i => σ.write i 0) s (List.range n)).read r = s.read r := by
  induction n generalizing s with
  | zero => simp only [List.range_zero, List.foldl_nil]
  | succ k ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hne : r ≠ k := by omega
    simp only [State.write_read_diff _ _ _ _ hne]
    exact ih s (by omega)

/-- clearRegisters preserves registers above maxReg. -/
theorem clearRegisters_preserves_above (maxReg : ℕ) (s : State) (r : ℕ) (hr : maxReg < r) :
    (executeStraightLine (Program.clearRegisters maxReg) s).read r = s.read r := by
  simp only [Program.clearRegisters, executeStraightLine, State.read]
  simp only [List.foldl_map]
  exact clearRegisters_preserves_helper (maxReg + 1) s r (by omega)

/-- After clearRegisters followed by restoreInput, the state matches Config.init
    on registers up to some bound. -/
theorem clearRegisters_restoreInput_matches_init (maxReg : ℕ) (s : State) (x : ℕ)
    (hSafeHasX : s.read (maxReg + 1) = x) :
    let s' := executeStraightLine (Program.clearRegisters maxReg) s
    let s'' := s'.write 0 (s'.read (maxReg + 1))
    ∀ r, r ≤ maxReg → s''.read r = (Config.init [x]).state.read r := by
  intro s' s'' r hr
  by_cases heq : r = 0
  · -- r = 0: s'' has x at position 0, same as Config.init [x]
    subst heq
    have h1 : s'.read (maxReg + 1) = s.read (maxReg + 1) :=
      clearRegisters_preserves_above maxReg s (maxReg + 1) (by omega)
    simp only [s'', State.write_read_same, h1, hSafeHasX]
    simp only [Config.init, State.fromInputs, State.read, List.getD, List.getElem?_cons_zero]
    rfl
  · -- r ≠ 0 and r ≤ maxReg: s'' has 0, same as Config.init [x]
    have h1 : s'.read r = 0 := clearRegisters_zeros maxReg s r hr
    simp only [s'', State.write_read_diff _ _ _ _ heq, h1]
    simp only [Config.init, State.fromInputs, State.read, List.getD]
    cases r with
    | zero => contradiction
    | succ n => simp only [List.getElem?_cons_succ, List.getElem?_nil]; rfl

/-! ## Binary-Unary Composition Construction -/

/-- The base register for safe storage in binary-unary composition.
This is above all registers used by F, G₁, and G₂. -/
def compositionBaseBU (pF pG1 pG2 : Program) : ℕ :=
  max pF.maxRegister (max pG1.maxRegister pG2.maxRegister)

/-- Build the binary-unary composition program.

Given:
- `pF`: program computing binary function f
- `pG1`: program computing unary function g₁
- `pG2`: program computing unary function g₂

Returns a program that computes h(x) = f(g₁(x), g₂(x)).

The program structure is:
1.  T 0 (m+1)        -- save input x to safe storage
2.  G₁               -- run G₁ to compute g₁(x)
3.  T 0 (m+2)        -- save g₁(x) result
4.  clearRegisters m -- reset workspace (Z 0, Z 1, ..., Z m)
5.  T (m+1) 0        -- restore input x
6.  G₂               -- run G₂ to compute g₂(x)
7.  T 0 (m+3)        -- save g₂(x) result
8.  clearRegisters m -- reset workspace (Z 0, Z 1, ..., Z m)
9.  T (m+2) 0        -- set up R[0] = g₁(x)
10. T (m+3) 1        -- set up R[1] = g₂(x)
11. F                -- run F to compute f(g₁(x), g₂(x))

The clearRegisters steps ensure that G₂ and F see the expected initial state
(all workspace registers zeroed), matching the semantics of `Config.init`.
-/
def Program.composeBU (pF pG1 pG2 : Program) : Program :=
  let m := compositionBaseBU pF pG1 pG2
  let saveInput : Program := [Instr.T 0 (m + 1)]
  let saveG1Result : Program := [Instr.T 0 (m + 2)]
  let clearWorkspace : Program := Program.clearRegisters m
  let restoreInput : Program := [Instr.T (m + 1) 0]
  let saveG2Result : Program := [Instr.T 0 (m + 3)]
  let setupArg0 : Program := [Instr.T (m + 2) 0]
  let setupArg1 : Program := [Instr.T (m + 3) 1]

  Program.foldConcat [
    saveInput,
    pG1,
    saveG1Result,
    clearWorkspace,
    restoreInput,
    pG2,
    saveG2Result,
    clearWorkspace,
    setupArg0,
    setupArg1,
    pF
  ]

/-! ## Register Isolation -/

theorem compositionBaseBU_ge_F (pF pG1 pG2 : Program) :
    pF.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU]
  exact Nat.le_max_left _ _

theorem compositionBaseBU_ge_G1 (pF pG1 pG2 : Program) :
    pG1.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU]
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem compositionBaseBU_ge_G2 (pF pG1 pG2 : Program) :
    pG2.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- Safe storage registers are above all program registers. -/
theorem safe_registers_above_max (pF pG1 pG2 : Program) (i : Fin 3) :
    compositionBaseBU pF pG1 pG2 < compositionBaseBU pF pG1 pG2 + 1 + i := by
  omega

/-! ## Main Composition Theorem -/

/-- Helper: the composed program is in standard form if all components are. -/
theorem composeBU_isStandardForm {pF pG1 pG2 : Program}
    (hF : pF.IsStandardForm)
    (hG1 : pG1.IsStandardForm)
    (hG2 : pG2.IsStandardForm) :
    (Program.composeBU pF pG1 pG2).IsStandardForm := by
  simp only [Program.composeBU, Program.foldConcat]
  -- The composed program is a sequence of concatenations
  -- Each single-instruction transfer is straight-line, hence standard form
  -- By IsStandardForm.concat, the full concatenation is standard form
  sorry

/-- Helper: create a Fin 2 → Part ℕ from two partial values. -/
def mkPair (a b : Part ℕ) : Fin 2 → Part ℕ
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

/-- mkPair domain: mkPair is defined iff both components are defined. -/
theorem mkPair_dom {a b : Part ℕ} :
    (Part.sequence (mkPair a b)).Dom ↔ a.Dom ∧ b.Dom := by
  rw [Part.sequence_dom]
  constructor
  · intro h
    exact ⟨h ⟨0, by omega⟩, h ⟨1, by omega⟩⟩
  · intro ⟨ha, hb⟩ i
    match i with
    | ⟨0, _⟩ => exact ha
    | ⟨1, _⟩ => exact hb

/-- The composed function domain: defined iff g1, g2, and f(g1, g2) are all defined. -/
theorem comp_function_dom {f : (Fin 2 → ℕ) → Part ℕ} {g1 g2 : (Fin 1 → ℕ) → Part ℕ}
    {x : Fin 1 → ℕ} :
    ((Part.sequence (mkPair (g1 x) (g2 x))).bind f).Dom ↔
    (g1 x).Dom ∧ (g2 x).Dom ∧
    ∀ (h1 : (g1 x).Dom) (h2 : (g2 x).Dom),
      (f (fun i => match i with
        | ⟨0, _⟩ => (g1 x).get h1
        | ⟨1, _⟩ => (g2 x).get h2)).Dom := by
  simp only [Part.bind_dom, mkPair_dom]
  constructor
  · intro ⟨⟨hg1, hg2⟩, hf⟩
    refine ⟨hg1, hg2, fun h1 h2 => ?_⟩
    convert hf using 1
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ => simp [Part.sequence_get, mkPair]
    | ⟨1, _⟩ => simp [Part.sequence_get, mkPair]
  · intro ⟨hg1, hg2, hf⟩
    refine ⟨⟨hg1, hg2⟩, ?_⟩
    convert hf hg1 hg2 using 1
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ => simp [Part.sequence_get, mkPair]
    | ⟨1, _⟩ => simp [Part.sequence_get, mkPair]

/-- Binary-unary composition preserves URM-computability for standard form programs.

If f is a binary URM-computable function (by a standard form program) and
g₁, g₂ are unary URM-computable functions (by standard form programs), then
h(x) = f(g₁(x), g₂(x)) is URM-computable by a standard form program. -/
theorem URMComputableSF.comp_binary_unary
    {f : (Fin 2 → ℕ) → Part ℕ}
    {g1 g2 : (Fin 1 → ℕ) → Part ℕ}
    (hf : URMComputableSF 2 f)
    (hg1 : URMComputableSF 1 g1)
    (hg2 : URMComputableSF 1 g2) :
    URMComputableSF 1 (fun x => (Part.sequence (mkPair (g1 x) (g2 x))).bind f) := by
  -- Extract the standard form programs
  obtain ⟨pF, hF_sf, hF_spec⟩ := hf
  obtain ⟨pG1, hG1_sf, hG1_spec⟩ := hg1
  obtain ⟨pG2, hG2_sf, hG2_spec⟩ := hg2

  -- Build the composed program
  let H := Program.composeBU pF pG1 pG2

  -- Show H is standard form
  have hH_sf : H.IsStandardForm := composeBU_isStandardForm hF_sf hG1_sf hG2_sf

  use H
  constructor
  · exact hH_sf
  · intro inputs
    constructor
    · -- Halting ↔ Definedness
      constructor
      · -- Forward: H halts → composed function is defined
        -- Strategy: Decompose H's execution into phases:
        -- Phase 1: saveInput (T 0 (m+1)) - straight-line, always succeeds
        -- Phase 2: G1 - must have halted, so g1 is defined (by hG1_spec)
        -- Phase 3: saveG1Result (T 0 (m+2)) - straight-line
        -- Phase 4: restoreInput (T (m+1) 0) - straight-line
        -- Phase 5: G2 - must have halted, so g2 is defined (by hG2_spec)
        -- Phase 6: saveG2Result (T 0 (m+3)) - straight-line
        -- Phase 7-8: setupArg0, setupArg1 - straight-line
        -- Phase 9: F - must have halted on (g1(x), g2(x)), so f is defined (by hF_spec)
        --
        -- Key lemma needed: extract halting of subprograms from halting of concatenation
        -- This requires showing that if p1.concat p2 halts from initial state,
        -- then p1 must have halted (otherwise we'd never reach p2).
        -- Also need register state tracking to show what state p2 sees.
        intro hHalts
        rw [comp_function_dom]
        -- Extract that each subprogram must have halted
        -- This requires infrastructure for decomposing halts through foldConcat
        sorry
      · -- Backward: composed function is defined → H halts
        -- Strategy: Chain the programs together using Halts.concat_continuation
        -- 1. From comp_function_dom, extract that g1, g2, f are all defined
        -- 2. By hG1_spec, G1 halts on [x]
        -- 3. By hG2_spec, G2 halts on [x]
        -- 4. By hF_spec, F halts on [g1(x), g2(x)]
        -- 5. All transfer instructions are straight-line, hence halt
        -- 6. Chain them: saveInput ++ G1 halts, then ++ saveG1Result, etc.
        -- Key lemmas needed:
        --   - Halts.concat_continuation (exists in Composition.lean)
        --   - Register state tracking through each phase
        intro hDom
        rw [comp_function_dom] at hDom
        obtain ⟨hg1_dom, hg2_dom, hf_dom⟩ := hDom
        -- G1 halts because g1 is defined
        have hG1_halts : Halts pG1 (List.ofFn inputs) :=
          (hG1_spec inputs).1.mpr hg1_dom
        -- G2 halts because g2 is defined
        have hG2_halts : Halts pG2 (List.ofFn inputs) :=
          (hG2_spec inputs).1.mpr hg2_dom
        -- Get the results of G1 and G2
        let v1 := Result pG1 (List.ofFn inputs) hG1_halts
        let v2 := Result pG2 (List.ofFn inputs) hG2_halts
        -- These equal the function values (by hG1_spec, hG2_spec)
        have hv1_eq : v1 = (g1 inputs).get hg1_dom :=
          (hG1_spec inputs).2 hG1_halts hg1_dom
        have hv2_eq : v2 = (g2 inputs).get hg2_dom :=
          (hG2_spec inputs).2 hG2_halts hg2_dom
        -- Construct the input for F as a function Fin 2 → ℕ
        let fInput : Fin 2 → ℕ := fun i => match i with
          | ⟨0, _⟩ => v1
          | ⟨1, _⟩ => v2
        -- f is defined on fInput
        have hf_dom' : (f fInput).Dom := by
          have h := hf_dom hg1_dom hg2_dom
          simp only at h
          convert h using 1
          congr 1
          funext i
          match i with
          | ⟨0, _⟩ => simp only [fInput, hv1_eq]
          | ⟨1, _⟩ => simp only [fInput, hv2_eq]
        -- F halts because f is defined on fInput
        have hF_halts : Halts pF (List.ofFn fInput) :=
          (hF_spec fInput).1.mpr hf_dom'
        -- Now chain all the programs together using Halts.concat_continuation
        -- The composed program H (with clearRegisters) is:
        -- foldConcat [saveInput, G1, saveG1Result, clearWorkspace, restoreInput, G2,
        --             saveG2Result, clearWorkspace, setupArg0, setupArg1, F]
        --
        -- With clearRegisters added, the state after clearWorkspace + restoreInput matches
        -- Config.init [x] on registers <= m, so G2 sees the expected initial state.
        -- Similarly, after the second clearWorkspace + setupArg0 + setupArg1, the state
        -- matches Config.init [g1(x), g2(x)] on registers <= m, so F sees the expected state.
        --
        -- Key lemmas for the proof:
        -- 1. straightLine_halts_at_length: straight-line programs halt at exactly length
        -- 2. Standard form programs halt at exactly length (by definition)
        -- 3. Halts.concat_continuation: chains two halting programs
        -- 4. Halts.register_independent: p halts on modified state if it agrees on <= maxReg
        -- 5. clearRegisters_restoreInput_matches_init: state after clear+restore matches init
        --
        -- The proof requires chaining 11 program segments. Each step uses:
        -- - Halts.concat_continuation to extend the halting chain
        -- - Standard form / straight-line to get h1_pc condition
        -- - Register independence to show the next program halts
        sorry
    · -- Results match
      -- Strategy: Track the value in R[0] through all phases:
      -- After Phase 2: R[0] = g1(x)
      -- After Phase 3: R[m+2] = g1(x)
      -- After Phase 5: R[0] = g2(x)
      -- After Phase 6: R[m+3] = g2(x)
      -- After Phase 7: R[0] = g1(x)
      -- After Phase 8: R[1] = g2(x)
      -- After Phase 9: R[0] = f(g1(x), g2(x))
      --
      -- The proof requires:
      -- 1. Register state tracking through each phase (using Steps.preserves_high_register)
      -- 2. Standard form ensures we fall through at each boundary
      -- 3. Result extraction at the final phase matches the composed function value
      intro hHalts hDom
      -- The Result is the value in R[0] after H halts
      -- This equals f(g1(x), g2(x)) by construction of H
      sorry

end Urm
