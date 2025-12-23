/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.CompositionHelpers

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

/-- clearRegisters is the same as clearRegistersFrom 0 (maxReg + 1). -/
theorem clearRegisters_eq_clearRegistersFrom (maxReg : ℕ) :
    Program.clearRegisters maxReg = Program.clearRegistersFrom 0 (maxReg + 1) := by
  simp only [Program.clearRegisters, Program.clearRegistersFrom]
  congr 1
  funext i
  simp only [Nat.zero_add]

/-- clearRegisters zeros all registers up to and including maxReg.
Uses the relational semantics via straightLineFinalState. -/
theorem clearRegisters_zeros (maxReg : ℕ) (s : State) (r : ℕ) (hr : r ≤ maxReg) :
    (straightLineFinalState (clearRegisters_isStraightLine maxReg) s).read r = 0 := by
  -- clearRegisters maxReg = clearRegistersFrom 0 (maxReg + 1)
  have heq := clearRegisters_eq_clearRegistersFrom maxReg
  -- The straight-line property is preserved
  have hsl := clearRegisters_isStraightLine maxReg
  -- The final states are the same
  have hstate_eq : straightLineFinalState hsl s =
      straightLineFinalState (Program.clearRegistersFrom_isStraightLine 0 (maxReg + 1)) s := by
    -- Both halted configs must be equal by uniqueness
    have ⟨hsteps1, hhalted1, hpc1⟩ := straightLineFinalState_spec hsl s
    have ⟨hsteps2, hhalted2, hpc2⟩ :=
      straightLineFinalState_spec (Program.clearRegistersFrom_isStraightLine 0 (maxReg + 1)) s
    -- Rewrite hsteps1 to use clearRegistersFrom
    have hsteps1' : Steps (Program.clearRegistersFrom 0 (maxReg + 1)) ⟨0, s⟩
        (Classical.choose (straightLine_halts_from_state hsl s)) := by
      simp only [← heq]; exact hsteps1
    have hlen_eq : (Program.clearRegisters maxReg).length =
        (Program.clearRegistersFrom 0 (maxReg + 1)).length := by
      simp only [heq]
    have hhalted1' : (Classical.choose (straightLine_halts_from_state hsl s)).isHalted
        (Program.clearRegistersFrom 0 (maxReg + 1)) := by
      simp only [Config.isHalted] at hhalted1 ⊢
      rw [← hlen_eq]
      exact hhalted1
    -- By uniqueness of halted configs
    have huniq := Steps.halts_unique hsteps1' hhalted1' hsteps2 hhalted2
    simp only [straightLineFinalState]
    rw [huniq]
  rw [hstate_eq]
  -- Now use clearRegistersFrom_zeros
  have hr_range : 0 ≤ r ∧ r < 0 + (maxReg + 1) := ⟨Nat.zero_le r, by omega⟩
  exact clearRegistersFrom_zeros 0 (maxReg + 1) s r hr_range

/-- clearRegisters preserves registers above maxReg.
Uses the relational semantics via straightLineFinalState. -/
theorem clearRegisters_preserves_above (maxReg : ℕ) (s : State) (r : ℕ) (hr : maxReg < r) :
    (straightLineFinalState (clearRegisters_isStraightLine maxReg) s).read r = s.read r := by
  -- The program only writes to registers 0, 1, ..., maxReg
  -- Since r > maxReg, it is preserved
  have hsl := clearRegisters_isStraightLine maxReg
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  apply Steps.straightLine_preserves hsl hsteps
  intro instr hmem
  -- Each instruction in clearRegisters is Z i for some i ≤ maxReg
  simp only [Program.clearRegisters, List.mem_map] at hmem
  obtain ⟨i, hi_range, hinstr_eq⟩ := hmem
  simp only [List.mem_range] at hi_range
  subst hinstr_eq
  simp only [Instr.writesTo, ne_eq, Option.some.injEq]
  omega

/-- For a straight-line program, if c is the halted configuration from state s,
then c.state equals straightLineFinalState. This is a common pattern for
proving state equality after straight-line execution. -/
theorem straightLineFinalState_eq_of_halted {p : Program} (hsl : p.isStraightLine = true) (s : State)
    (c : Config) (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.isHalted p) :
    c.state = straightLineFinalState hsl s := by
  have hspec := straightLineFinalState_spec hsl s
  exact Steps.halts_unique hsteps hhalted hspec.1 hspec.2.1 ▸ rfl

/-! ## Binary-Unary Composition Construction -/

/-- The base register for safe storage in binary-unary composition.
This is at least 1 (to avoid collision with R[1] used for binary input) and
above all registers used by F, G₁, and G₂. -/
def compositionBaseBU (pF pG1 pG2 : Program) : ℕ :=
  max 1 (max pF.maxRegister (max pG1.maxRegister pG2.maxRegister))

/-- Build the binary-unary composition program.

Given:
- `pF`: program computing binary function f
- `pG1`: program computing unary function g₁
- `pG2`: program computing unary function g₂

Returns a program that computes h(x) = f(g₁(x), g₂(x)).

The program is organized into three phases:

**Phase 1**: Compute g₁(x) and save result
- T 0 (m+1)   -- save input x to safe storage
- G₁          -- run G₁ to compute g₁(x)
- T 0 (m+2)   -- save g₁(x) result

**Phase 2**: Compute g₂(x) and save result
- clear[0..m] -- reset workspace
- T (m+1) 0   -- restore input x
- G₂          -- run G₂ to compute g₂(x)
- T 0 (m+3)   -- save g₂(x) result

**Phase 3**: Set up arguments and run F
- clear[0..m] -- reset workspace
- T (m+2) 0   -- set up R[0] = g₁(x)
- T (m+3) 1   -- set up R[1] = g₂(x)
- F           -- run F to compute f(g₁(x), g₂(x))

The clearRegisters steps ensure that G₂ and F see the expected initial state
(all workspace registers zeroed), matching the semantics of `Config.init`.
-/
def Program.composeBU (pF pG1 pG2 : Program) : Program :=
  let m := compositionBaseBU pF pG1 pG2
  -- Phase 1: Compute g₁(x) and save result
  let phase1 := Program.concat [Instr.T 0 (m + 1)]
                  (Program.concat pG1 [Instr.T 0 (m + 2)])
  -- Phase 2: Compute g₂(x) and save result
  let phase2 := Program.concat (Program.clearRegisters m)
                  (Program.concat [Instr.T (m + 1) 0]
                    (Program.concat pG2 [Instr.T 0 (m + 3)]))
  -- Phase 3: Set up arguments and run F
  let phase3 := Program.concat (Program.clearRegisters m)
                  (Program.concat [Instr.T (m + 2) 0, Instr.T (m + 3) 1] pF)
  -- Combine all phases
  Program.concat phase1 (Program.concat phase2 phase3)

/-! ## Register Isolation -/

theorem compositionBaseBU_ge_1 (pF pG1 pG2 : Program) :
    1 ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU]
  exact Nat.le_max_left _ _

theorem compositionBaseBU_ge_F (pF pG1 pG2 : Program) :
    pF.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU]
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem compositionBaseBU_ge_G1 (pF pG1 pG2 : Program) :
    pG1.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU]
  exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)

theorem compositionBaseBU_ge_G2 (pF pG1 pG2 : Program) :
    pG2.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU]
  exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)

/-! ## Main Composition Theorem -/

/-- A single transfer instruction is straight-line. -/
private theorem single_transfer_isStraightLine (src dst : ℕ) :
    Program.isStraightLine [Instr.T src dst] = true := rfl

/-- A two-instruction transfer sequence is straight-line. -/
private theorem double_transfer_isStraightLine (s1 d1 s2 d2 : ℕ) :
    Program.isStraightLine [Instr.T s1 d1, Instr.T s2 d2] = true := rfl

/-! ## T01 Execution Helpers

The T01 instruction `[Instr.T 0 (m + 1)]` copies R[0] to R[m+1] at the start of
the composed program. These lemmas encapsulate the common execution pattern
that appears in all the composition theorems. -/

/-- After executing T01 = [T 0 (m+1)] from initial state, the result state
equals the initial state with R[m+1] set to the input value. -/
theorem T01_state_eq (m : ℕ) (inputs : Fin 1 → ℕ) :
    let hT01_sl := single_transfer_isStraightLine 0 (m + 1)
    let hT01_halts := straightLine_halts hT01_sl (List.ofFn inputs)
    (Classical.choose hT01_halts).state = (State.fromInputs (List.ofFn inputs)).write (m + 1)
        ((State.fromInputs (List.ofFn inputs)).read 0) := by
  intro hT01_sl hT01_halts
  have hex := single_transfer_halts 0 (m + 1) (State.fromInputs (List.ofFn inputs))
  obtain ⟨c', hsteps', hhalted', _, hstate'⟩ := hex
  have hspec := Classical.choose_spec hT01_halts
  have heq := Steps.halts_unique hspec.1 hspec.2 hsteps' hhalted'
  show (Classical.choose hT01_halts).state = _
  rw [heq, hstate']

/-- T01 preserves all registers except m+1. In particular, for r ≤ m,
the state after T01 agrees with the initial state. -/
theorem T01_preserves_below (m : ℕ) (inputs : Fin 1 → ℕ) (r : ℕ) (hr : r ≤ m) :
    let hT01_sl := single_transfer_isStraightLine 0 (m + 1)
    let hT01_halts := straightLine_halts hT01_sl (List.ofFn inputs)
    (Classical.choose hT01_halts).state.read r = (State.fromInputs (List.ofFn inputs)).read r := by
  intro hT01_sl hT01_halts
  have hT01_state := T01_state_eq m inputs
  simp only at hT01_state
  conv_lhs => rw [hT01_state]
  have hr_ne : r ≠ m + 1 := by omega
  exact State.write_read_diff _ _ _ _ hr_ne

/-- T01 stores the input value in R[m+1]. -/
theorem T01_stores_input (m : ℕ) (inputs : Fin 1 → ℕ) :
    let hT01_sl := single_transfer_isStraightLine 0 (m + 1)
    let hT01_halts := straightLine_halts hT01_sl (List.ofFn inputs)
    (Classical.choose hT01_halts).state.read (m + 1) = inputs ⟨0, by omega⟩ := by
  intro hT01_sl hT01_halts
  have hT01_state := T01_state_eq m inputs
  simp only at hT01_state
  conv_lhs => rw [hT01_state]
  rw [State.write_read_same]
  simp only [State.fromInputs, State.read]
  rfl

/-- After T01, the state agrees with the initial inputs on registers ≤ maxReg,
provided maxReg ≤ m. This is the key lemma for using Halts.of_agreeing_state. -/
theorem T01_agreeOn_for_subprogram (m : ℕ) (inputs : Fin 1 → ℕ) (maxReg : ℕ) (h : maxReg ≤ m) :
    let hT01_sl := single_transfer_isStraightLine 0 (m + 1)
    let hT01_halts := straightLine_halts hT01_sl (List.ofFn inputs)
    ∀ r, r ≤ maxReg → (Classical.choose hT01_halts).state.read r =
        (State.fromInputs (List.ofFn inputs)).read r := by
  intro hT01_sl hT01_halts r hr
  exact T01_preserves_below m inputs r (Nat.le_trans hr h)

/-- For any halting proof of T01, the result state agrees with initial inputs on registers ≤ m.
This version works with any `hT01_halts` obtained from different sources (suffix extraction, etc.). -/
theorem T01_preserves_below_any (m : ℕ) (inputs : Fin 1 → ℕ)
    (hT01_halts : Halts [Instr.T 0 (m + 1)] (List.ofFn inputs))
    (r : ℕ) (hr : r ≤ m) :
    (Classical.choose hT01_halts).state.read r = (State.fromInputs (List.ofFn inputs)).read r := by
  -- Bridge to the canonical halting proof via uniqueness
  have hT01_sl := single_transfer_isStraightLine 0 (m + 1)
  have hT01_halts' := straightLine_halts hT01_sl (List.ofFn inputs)
  have hspec := Classical.choose_spec hT01_halts
  have hspec' := Classical.choose_spec hT01_halts'
  have huniq := Steps.halts_unique hspec.1 hspec.2 hspec'.1 hspec'.2
  rw [huniq]
  exact T01_preserves_below m inputs r hr

/-- For any halting proof of T01, register m+1 contains the input value.
This version works with any `hT01_halts` obtained from different sources. -/
theorem T01_stores_input_any (m : ℕ) (inputs : Fin 1 → ℕ)
    (hT01_halts : Halts [Instr.T 0 (m + 1)] (List.ofFn inputs)) :
    (Classical.choose hT01_halts).state.read (m + 1) = inputs ⟨0, by omega⟩ := by
  have hT01_sl := single_transfer_isStraightLine 0 (m + 1)
  have hT01_halts' := straightLine_halts hT01_sl (List.ofFn inputs)
  have hspec := Classical.choose_spec hT01_halts
  have hspec' := Classical.choose_spec hT01_halts'
  have huniq := Steps.halts_unique hspec.1 hspec.2 hspec'.1 hspec'.2
  rw [huniq]
  exact T01_stores_input m inputs

/-- Helper: the composed program is in standard form if all components are. -/
theorem composeBU_isStandardForm {pF pG1 pG2 : Program}
    (hF : pF.IsStandardForm)
    (hG1 : pG1.IsStandardForm)
    (hG2 : pG2.IsStandardForm) :
    (Program.composeBU pF pG1 pG2).IsStandardForm := by
  simp only [Program.composeBU]
  set m := compositionBaseBU pF pG1 pG2 with hm
  -- All single-instruction programs (T instructions) are straight-line, hence standard form
  -- clearRegisters is also straight-line, hence standard form
  have hT1 : Program.IsStandardForm [Instr.T 0 (m + 1)] :=
    straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 1))
  have hT2 : Program.IsStandardForm [Instr.T 0 (m + 2)] :=
    straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 2))
  have hClear : Program.IsStandardForm (Program.clearRegisters m) :=
    straightLine_isStandardForm (clearRegisters_isStraightLine m)
  have hT3 : Program.IsStandardForm [Instr.T (m + 1) 0] :=
    straightLine_isStandardForm (single_transfer_isStraightLine (m + 1) 0)
  have hT4 : Program.IsStandardForm [Instr.T 0 (m + 3)] :=
    straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 3))
  have hSetup : Program.IsStandardForm [Instr.T (m + 2) 0, Instr.T (m + 3) 1] :=
    straightLine_isStandardForm (double_transfer_isStraightLine (m + 2) 0 (m + 3) 1)
  -- Build up phase standard forms using IsStandardForm.concat
  have hPhase1 := hT1.concat (hG1.concat hT2)
  have hPhase2 := hClear.concat (hT3.concat (hG2.concat hT4))
  have hPhase3 := hClear.concat (hSetup.concat hF)
  -- Combine all phases
  exact hPhase1.concat (hPhase2.concat hPhase3)

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


/-- Extract g1 domain from composed program halting.

When the binary-unary composition `composeBU pF pG1 pG2` halts on inputs,
g1 must be defined on those inputs. This is because phase1 of the composed
program runs pG1 and must halt for the overall program to halt. -/
theorem comp_binary_unary_halts_imp_g1_dom
    {g1 : (Fin 1 → ℕ) → Part ℕ}
    {pF pG1 pG2 : Program}
    (hG1_sf : pG1.IsStandardForm)
    (hG1_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG1 (List.ofFn inputs) ↔ (g1 inputs).Dom) ∧
      ∀ (hH : Halts pG1 (List.ofFn inputs)) (hD : (g1 inputs).Dom),
        Result pG1 (List.ofFn inputs) hH = (g1 inputs).get hD)
    (inputs : Fin 1 → ℕ)
    (hHalts : Halts (Program.composeBU pF pG1 pG2) (List.ofFn inputs)) :
    (g1 inputs).Dom := by
  -- Set up program structure
  set m := compositionBaseBU pF pG1 pG2 with hm_def
  let T01 : Program := [Instr.T 0 (m + 1)]
  let T02 : Program := [Instr.T 0 (m + 2)]
  let clearProg := Program.clearRegisters m
  let T10 : Program := [Instr.T (m + 1) 0]
  let T03 : Program := [Instr.T 0 (m + 3)]
  let Tsetup : Program := [Instr.T (m + 2) 0, Instr.T (m + 3) 1]

  let phase1 := T01.concat (pG1.concat T02)
  let phase2 := clearProg.concat (T10.concat (pG2.concat T03))
  let phase3 := clearProg.concat (Tsetup.concat pF)

  -- Standard form properties
  have hT01_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 1))
  have hT02_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 2))

  have hPhase1_sf : phase1.IsStandardForm := hT01_sf.concat (hG1_sf.concat hT02_sf)

  -- H = phase1.concat (phase2.concat phase3)
  let H := Program.composeBU pF pG1 pG2
  have hH_eq : H = phase1.concat (phase2.concat phase3) := rfl

  -- Convert hHalts to use H
  have hHalts' : Halts H (List.ofFn inputs) := hHalts

  -- Extract phase1 halting
  have hPhase1_halts : Halts phase1 (List.ofFn inputs) := by
    rw [hH_eq] at hHalts'
    exact Halts.prefix_of_concat_sf hHalts' hPhase1_sf

  -- Extract pG1 halting from phase1
  -- phase1 = T01.concat (pG1.concat T02)
  -- Use suffix_of_concat_sf to get execution of pG1.concat T02 from state after T01
  have hSuffix1 := Halts.suffix_of_concat_sf hPhase1_halts hT01_sf
  obtain ⟨sT01, hT01_halts, hsT01_eq, cG1T02, hG1T02_steps, hG1T02_halted⟩ := hSuffix1

  -- Extract pG1 halting from pG1.concat T02
  have hG1T02_sf : (pG1.concat T02).IsStandardForm := hG1_sf.concat hT02_sf

  -- Use Urm.prefix_of_concat_from_zero to extract pG1 halting
  have hG1_from_sT01 : ∃ c', Steps pG1 ⟨0, sT01⟩ c' ∧ c'.isHalted pG1 :=
    Urm.prefix_of_concat_from_zero hG1T02_steps hG1T02_halted hG1_sf
  obtain ⟨cG1', hG1_steps, hG1_halted⟩ := hG1_from_sT01

  -- Show sT01 agrees with State.fromInputs on registers 0..pG1.maxRegister
  have hm_ge_G1 : pG1.maxRegister ≤ m := compositionBaseBU_ge_G1 pF pG1 pG2

  -- Use helper: T01 preserves registers below m+1
  have hagreeG1 : ∀ r, r ≤ pG1.maxRegister → sT01.read r = (State.fromInputs (List.ofFn inputs)).read r := by
    intro r hr
    rw [hsT01_eq hT01_halts]
    exact T01_preserves_below_any m inputs hT01_halts r (Nat.le_trans hr hm_ge_G1)

  -- Use Halts.of_agreeing_state to conclude Halts pG1 (List.ofFn inputs)
  have hG1_halts : Halts pG1 (List.ofFn inputs) :=
    Halts.of_agreeing_state hG1_steps hG1_halted hagreeG1

  -- By hG1_spec, Halts pG1 (List.ofFn inputs) → (g1 inputs).Dom
  exact (hG1_spec inputs).1.mp hG1_halts

set_option maxHeartbeats 400000 in
/-- Extract g2 domain from composed program halting.

When the binary-unary composition `composeBU pF pG1 pG2` halts on inputs,
g2 must be defined on those inputs. This is because phase2 of the composed
program runs pG2 (after phase1 completes) and must halt for the overall program to halt.

This proof is more complex than g1 because we must track that R[m+1] preserves
the original input through phase1, so that phase2 can restore it to R[0] for pG2. -/
theorem comp_binary_unary_halts_imp_g2_dom
    {g1 g2 : (Fin 1 → ℕ) → Part ℕ}
    {pF pG1 pG2 : Program}
    (hG1_sf : pG1.IsStandardForm) (hG2_sf : pG2.IsStandardForm)
    (hG1_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG1 (List.ofFn inputs) ↔ (g1 inputs).Dom) ∧
      ∀ (hH : Halts pG1 (List.ofFn inputs)) (hD : (g1 inputs).Dom),
        Result pG1 (List.ofFn inputs) hH = (g1 inputs).get hD)
    (hG2_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG2 (List.ofFn inputs) ↔ (g2 inputs).Dom) ∧
      ∀ (hH : Halts pG2 (List.ofFn inputs)) (hD : (g2 inputs).Dom),
        Result pG2 (List.ofFn inputs) hH = (g2 inputs).get hD)
    (inputs : Fin 1 → ℕ)
    (hHalts : Halts (Program.composeBU pF pG1 pG2) (List.ofFn inputs)) :
    (g2 inputs).Dom := by
  -- Derive g1 halting (needed for tracking phase1's preservation of R[m+1])
  have hg1_dom : (g1 inputs).Dom := comp_binary_unary_halts_imp_g1_dom hG1_sf hG1_spec inputs hHalts
  have hG1_halts : Halts pG1 (List.ofFn inputs) := (hG1_spec inputs).1.mpr hg1_dom

  -- Set up program structure
  set m := compositionBaseBU pF pG1 pG2 with hm_def
  let T01 : Program := [Instr.T 0 (m + 1)]
  let T02 : Program := [Instr.T 0 (m + 2)]
  let clearProg := Program.clearRegisters m
  let T10 : Program := [Instr.T (m + 1) 0]
  let T03 : Program := [Instr.T 0 (m + 3)]
  let Tsetup : Program := [Instr.T (m + 2) 0, Instr.T (m + 3) 1]

  let phase1 := T01.concat (pG1.concat T02)
  let phase2 := clearProg.concat (T10.concat (pG2.concat T03))
  let phase3 := clearProg.concat (Tsetup.concat pF)

  -- Standard form properties
  have hT01_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 1))
  have hT02_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 2))
  have hT10_sf := straightLine_isStandardForm (single_transfer_isStraightLine (m + 1) 0)
  have hT03_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 3))
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine m)

  have hPhase1_sf : phase1.IsStandardForm := hT01_sf.concat (hG1_sf.concat hT02_sf)
  have hPhase2_sf : phase2.IsStandardForm := hClear_sf.concat (hT10_sf.concat (hG2_sf.concat hT03_sf))

  -- H = phase1.concat (phase2.concat phase3)
  let H := Program.composeBU pF pG1 pG2
  have hH_eq : H = phase1.concat (phase2.concat phase3) := rfl

  -- Convert hHalts to use H
  have hHalts' : Halts H (List.ofFn inputs) := hHalts

  -- Extract phase1 halting
  have hPhase1_halts : Halts phase1 (List.ofFn inputs) := by
    rw [hH_eq] at hHalts'
    exact Halts.prefix_of_concat_sf hHalts' hPhase1_sf

  -- Extract phase2 halting from H
  have hSuffix12 := Halts.suffix_of_concat_sf hHalts' hPhase1_sf
  obtain ⟨sPhase1, _, hsPhase1_eq, cPhase23, hPhase23_steps, hPhase23_halted⟩ := hSuffix12

  -- phase2.concat phase3 halts from sPhase1
  -- Extract phase2 halting
  have hPhase2_from := prefix_of_concat_from_zero hPhase23_steps hPhase23_halted hPhase2_sf
  obtain ⟨cPhase2', hPhase2_steps, hPhase2_halted⟩ := hPhase2_from

  -- phase2 = clearProg.concat (T10.concat (pG2.concat T03))
  -- We need to extract pG2 halting from this
  -- After clearProg, registers 0..m-1 are 0, and T10 restores R[0] from R[m+1]
  -- This sets up the correct state for pG2

  -- Step 1: Extract T10.concat (pG2.concat T03) execution from phase2
  have hT10rest_sf : (T10.concat (pG2.concat T03)).IsStandardForm :=
    hT10_sf.concat (hG2_sf.concat hT03_sf)
  have hClear_sl := clearRegisters_isStraightLine m
  obtain ⟨sClear, hClear_steps, hClear_p2_halts⟩ :=
    suffix_of_concat_from_zero hPhase2_steps hPhase2_halted hClear_sf
  obtain ⟨cT10rest, hT10rest_steps, hT10rest_halted⟩ := hClear_p2_halts

  -- Step 2: Extract pG2.concat T03 execution from T10.concat (pG2.concat T03)
  have hG2T03_sf : (pG2.concat T03).IsStandardForm := hG2_sf.concat hT03_sf
  obtain ⟨sT10, hT10_steps, hG2T03_halts⟩ :=
    suffix_of_concat_from_zero hT10rest_steps hT10rest_halted hT10_sf
  obtain ⟨cG2T03, hG2T03_steps, hG2T03_halted⟩ := hG2T03_halts

  -- Step 3: Extract pG2 halting from pG2.concat T03
  have hG2_from_sT10 : ∃ c', Steps pG2 ⟨0, sT10⟩ c' ∧ c'.isHalted pG2 :=
    prefix_of_concat_from_zero hG2T03_steps hG2T03_halted hG2_sf

  obtain ⟨cG2', hG2_steps', hG2_halted'⟩ := hG2_from_sT10

  -- Step 4: Show state agreement
  have hm_ge_G2 : pG2.maxRegister ≤ m := compositionBaseBU_ge_G2 pF pG1 pG2

  have hagreeG2 : ∀ r, r ≤ pG2.maxRegister →
      sT10.read r = (State.fromInputs (List.ofFn inputs)).read r := by
    intro r hr
    by_cases hr0 : r = 0
    · -- r = 0: sT10.read 0 = inputs[0] and State.fromInputs gives inputs[0]
      subst hr0
      -- Step 1: sT10.read 0 = sClear.read (m + 1) via T10 semantics
      have hT10_char := single_transfer_halts (m + 1) 0 sClear
      obtain ⟨cT10', hT10_steps', hT10_halted', _, hT10_state'⟩ := hT10_char
      have hT10_halted : (⟨T10.length, sT10⟩ : Config).isHalted T10 := Nat.le_refl _
      have hconfigs_eq := Steps.halts_unique hT10_steps hT10_halted hT10_steps' hT10_halted'
      have hsT10_eq : sT10 = sClear.write 0 (sClear.read (m + 1)) := by
        have : sT10 = cT10'.state := congrArg Config.state hconfigs_eq
        rw [this, hT10_state']
      have hsT10_r0 : sT10.read 0 = sClear.read (m + 1) := by
        rw [hsT10_eq, State.write_read_same]

      -- Step 2: sClear.read (m + 1) = sPhase1.read (m + 1) via clearRegisters_preserves_above
      have hClear_halted : (⟨clearProg.length, sClear⟩ : Config).isHalted clearProg := Nat.le_refl _
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sPhase1 :=
        straightLineFinalState_eq_of_halted hClear_sl sPhase1 ⟨clearProg.length, sClear⟩ hClear_steps hClear_halted
      have hsClear_preserves : sClear.read (m + 1) = sPhase1.read (m + 1) := by
        rw [hsClear_eq]
        exact clearRegisters_preserves_above m sPhase1 (m + 1) (by omega : m < m + 1)

      -- Step 3: sPhase1.read (m + 1) = inputs ⟨0, _⟩
      have hsPhase1_state : sPhase1 = (Classical.choose hPhase1_halts).state :=
        hsPhase1_eq hPhase1_halts

      -- Now prove (Classical.choose hPhase1_halts).state.read (m + 1) = inputs ⟨0, _⟩
      let cPhase1' := Classical.choose hPhase1_halts
      have hPhase1'_spec := Classical.choose_spec hPhase1_halts
      have hPhase1'_steps : Steps phase1 (Config.init (List.ofFn inputs)) cPhase1' := hPhase1'_spec.1
      have hPhase1'_halted : cPhase1'.isHalted phase1 := hPhase1'_spec.2

      have hPhase1_preserves_input : cPhase1'.state.read (m + 1) = inputs ⟨0, by omega⟩ := by
        -- Get the state after T01
        have hT01_sl := single_transfer_isStraightLine 0 (m + 1)
        have hT01_halts := straightLine_halts hT01_sl (List.ofFn inputs)
        let sT01' := (Classical.choose hT01_halts).state

        -- Use T01 helpers
        have hT01_state : sT01' = (State.fromInputs (List.ofFn inputs)).write (m + 1)
            ((State.fromInputs (List.ofFn inputs)).read 0) := T01_state_eq m inputs
        have hsT01'_m1 : sT01'.read (m + 1) = inputs ⟨0, by omega⟩ := T01_stores_input m inputs

        -- pG1 preserves R[m+1]
        have hm_ge_G1' : pG1.maxRegister ≤ m := compositionBaseBU_ge_G1 pF pG1 pG2
        have hagreeG1' : ∀ r, r ≤ pG1.maxRegister →
            sT01'.read r = (State.fromInputs (List.ofFn inputs)).read r := fun r' hr' =>
          T01_preserves_below m inputs r' (Nat.le_trans hr' hm_ge_G1')
        have hagreeG1'' : sT01'.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG1.maxRegister := by
          intro r' _ hhi
          exact hagreeG1' r' hhi

        -- Get cG1 execution from agreeing state using helper
        let eG1 := Halts.executeFromAgreeingState hG1_halts hG1_sf hagreeG1''
        let cG1' := eG1.config
        have hG1_steps'' := eG1.steps
        have hG1_halted'' := eG1.halted
        have hG1_pc'' := eG1.pc_eq

        -- pG1 preserves R[m+1]
        have hG1_preserves' : cG1'.state.read (m + 1) = sT01'.read (m + 1) :=
          eG1.preserves_high_register (m + 1) (by omega : pG1.maxRegister < m + 1)

        -- T02 execution from cG1'.state
        have hT02_halts'' := single_transfer_halts 0 (m + 2) cG1'.state
        obtain ⟨cT02', hT02_steps'', hT02_halted'', hT02_pc'', hT02_state''⟩ := hT02_halts''

        -- T02 preserves R[m+1] (it only writes to m+2)
        have hT02_preserves' : cT02'.state.read (m + 1) = cG1'.state.read (m + 1) := by
          rw [hT02_state'']
          exact State.write_read_diff _ _ _ _ (by omega : m + 1 ≠ m + 2)

        -- Relate cPhase1' to the explicitly constructed final config
        have hG1T02_steps' : Steps (pG1.concat T02) ⟨0, sT01'⟩ ⟨cT02'.pc + pG1.length, cT02'.state⟩ := by
          have hG1T02_steps_prefix := Steps.concat_left_prefix (p2 := T02) hG1_steps'' hG1_halted''
          have hT02_steps''' := Steps.concat_right (p1 := pG1) hT02_steps'' hT02_halted''
          have hstart_eq : (⟨0 + pG1.length, cG1'.state⟩ : Config) = ⟨cG1'.pc, cG1'.state⟩ := by
            simp only [Nat.zero_add]; ext; exact hG1_pc''.symm; rfl
          rw [hstart_eq] at hT02_steps'''
          exact Relation.ReflTransGen.trans hG1T02_steps_prefix hT02_steps'''
        have hG1T02_halted' : (⟨cT02'.pc + pG1.length, cT02'.state⟩ : Config).isHalted (pG1.concat T02) := by
          simp only [Config.isHalted, Program.concat_length, T02, List.length_singleton] at hT02_halted'' ⊢
          rw [hT02_pc'']
          omega

        -- The final config of phase1 from Config.init
        have hPhase1_final_steps' : Steps phase1 (Config.init (List.ofFn inputs))
            ⟨(cT02'.pc + pG1.length) + T01.length, cT02'.state⟩ := by
          have hT01_steps' := (Classical.choose_spec hT01_halts).1
          have hT01_halted' := (Classical.choose_spec hT01_halts).2
          have hT01_steps'' := Steps.concat_left_prefix (p2 := pG1.concat T02) hT01_steps' hT01_halted'
          have hG1T02_steps'' := Steps.concat_right (p1 := T01) hG1T02_steps' hG1T02_halted'
          have hstart_eq' : (⟨0 + T01.length, sT01'⟩ : Config) = ⟨(Classical.choose hT01_halts).pc, sT01'⟩ := by
            simp only [Nat.zero_add]
            congr 1
            have hspec' := Classical.choose_spec hT01_halts
            have hpc' := hT01_sf.halts_at_length (List.ofFn inputs) _ hspec'.1 hspec'.2
            simp only [T01, List.length_singleton] at hpc' ⊢
            exact hpc'.symm
          rw [hstart_eq'] at hG1T02_steps''
          exact Relation.ReflTransGen.trans hT01_steps'' hG1T02_steps''
        have hPhase1_final_halted' : (⟨(cT02'.pc + pG1.length) + T01.length, cT02'.state⟩ : Config).isHalted phase1 := by
          simp only [Config.isHalted, phase1, Program.concat_length, T01, T02, List.length_singleton]
          rw [hT02_pc'']
          omega

        -- By uniqueness, cPhase1'.state = cT02'.state
        have hPhase1_state_eq' : cPhase1'.state = cT02'.state := by
          have heq := Steps.halts_unique hPhase1'_steps hPhase1'_halted hPhase1_final_steps' hPhase1_final_halted'
          simp only [heq]

        -- Combine all the equalities
        rw [hPhase1_state_eq', hT02_preserves', hG1_preserves', hsT01'_m1]

      -- Step 4: (State.fromInputs (List.ofFn inputs)).read 0 = inputs ⟨0, _⟩
      have hRHS : (State.fromInputs (List.ofFn inputs)).read 0 = inputs ⟨0, by omega⟩ := by
        simp only [State.fromInputs, State.read]
        rfl

      -- Combine: sT10.read 0 = sClear.read (m+1) = sPhase1.read (m+1) = inputs[0] = RHS
      rw [hsT10_r0, hsClear_preserves, hsPhase1_state, hPhase1_preserves_input, ← hRHS]
    · -- r > 0: clearProg cleared R[r] to 0, T10 only writes R[0]
      have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
      have hinputs_len : (List.ofFn inputs).length = 1 := by simp
      simp only [State.fromInputs, State.read]
      have hgetD_zero : (List.ofFn inputs).getD r 0 = 0 := by
        simp only [List.getD_eq_getElem?_getD]
        have hout : r ≥ (List.ofFn inputs).length := by simp; exact hr_pos
        rw [List.getElem?_eq_none hout]
        rfl
      rw [hgetD_zero]
      -- Now prove sT10.read r = 0
      have hT10_char := single_transfer_halts (m + 1) 0 sClear
      obtain ⟨cT10', hT10_steps', hT10_halted', _, hT10_state'⟩ := hT10_char
      have hT10_halted : (⟨T10.length, sT10⟩ : Config).isHalted T10 :=
        Nat.le_refl _
      have hconfigs_eq := Steps.halts_unique hT10_steps hT10_halted hT10_steps' hT10_halted'
      have hsT10_eq : sT10 = sClear.write 0 (sClear.read (m + 1)) := by
        have : sT10 = cT10'.state := congrArg Config.state hconfigs_eq
        rw [this, hT10_state']
      have hT10_preserves_r : sT10 r = sClear r := by
        rw [hsT10_eq]; exact State.write_read_diff _ _ _ _ hr0
      have hClear_halted : (⟨clearProg.length, sClear⟩ : Config).isHalted clearProg := Nat.le_refl _
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sPhase1 :=
        straightLineFinalState_eq_of_halted hClear_sl sPhase1 ⟨clearProg.length, sClear⟩ hClear_steps hClear_halted
      have hClear_zeros_r : sClear r = 0 := by
        rw [hsClear_eq]
        exact clearRegisters_zeros m sPhase1 r (Nat.le_trans hr hm_ge_G2)
      rw [hT10_preserves_r, hClear_zeros_r]

  have hG2_halts' : Halts pG2 (List.ofFn inputs) :=
    Halts.of_agreeing_state hG2_steps' hG2_halted' hagreeG2
  exact (hG2_spec inputs).1.mp hG2_halts'

set_option maxHeartbeats 600000 in
/-- Extract f domain from composed program halting, given g1 and g2 are defined.

When the binary-unary composition `composeBU pF pG1 pG2` halts on inputs and both
g1 and g2 are defined, f must be defined on the composed outputs. This is because
phase3 runs pF with inputs derived from g1 and g2's outputs.

This is the most complex part of the halts→dom direction because we must track:
- R[m+2] holds g1(input) (saved by T02 in phase1)
- R[m+3] holds g2(input) (saved by T03 in phase2)
- Tsetup correctly loads these into R[0] and R[1] for pF -/
theorem comp_binary_unary_halts_imp_f_dom
    {f : (Fin 2 → ℕ) → Part ℕ} {g1 g2 : (Fin 1 → ℕ) → Part ℕ}
    {pF pG1 pG2 : Program}
    (hF_sf : pF.IsStandardForm) (hG1_sf : pG1.IsStandardForm) (hG2_sf : pG2.IsStandardForm)
    (hF_spec : ∀ inputs : Fin 2 → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hH : Halts pF (List.ofFn inputs)) (hD : (f inputs).Dom),
        Result pF (List.ofFn inputs) hH = (f inputs).get hD)
    (hG1_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG1 (List.ofFn inputs) ↔ (g1 inputs).Dom) ∧
      ∀ (hH : Halts pG1 (List.ofFn inputs)) (hD : (g1 inputs).Dom),
        Result pG1 (List.ofFn inputs) hH = (g1 inputs).get hD)
    (hG2_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG2 (List.ofFn inputs) ↔ (g2 inputs).Dom) ∧
      ∀ (hH : Halts pG2 (List.ofFn inputs)) (hD : (g2 inputs).Dom),
        Result pG2 (List.ofFn inputs) hH = (g2 inputs).get hD)
    (inputs : Fin 1 → ℕ)
    (hHalts : Halts (Program.composeBU pF pG1 pG2) (List.ofFn inputs))
    (hg1_dom : (g1 inputs).Dom)
    (hg2_dom : (g2 inputs).Dom) :
    (f fun i => match i with
      | ⟨0, _⟩ => (g1 inputs).get hg1_dom
      | ⟨1, _⟩ => (g2 inputs).get hg2_dom).Dom := by
  -- Derive halting facts
  have hG1_halts : Halts pG1 (List.ofFn inputs) := (hG1_spec inputs).1.mpr hg1_dom

  -- Set up program structure
  set m := compositionBaseBU pF pG1 pG2 with hm_def
  let T01 : Program := [Instr.T 0 (m + 1)]
  let T02 : Program := [Instr.T 0 (m + 2)]
  let clearProg := Program.clearRegisters m
  let T10 : Program := [Instr.T (m + 1) 0]
  let T03 : Program := [Instr.T 0 (m + 3)]
  let Tsetup : Program := [Instr.T (m + 2) 0, Instr.T (m + 3) 1]

  let phase1 := T01.concat (pG1.concat T02)
  let phase2 := clearProg.concat (T10.concat (pG2.concat T03))
  let phase3 := clearProg.concat (Tsetup.concat pF)

  -- Standard form properties
  have hT01_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 1))
  have hT02_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 2))
  have hT10_sf := straightLine_isStandardForm (single_transfer_isStraightLine (m + 1) 0)
  have hT03_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 3))
  have hTsetup_sf := straightLine_isStandardForm (double_transfer_isStraightLine (m + 2) 0 (m + 3) 1)
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine m)

  have hPhase1_sf : phase1.IsStandardForm := hT01_sf.concat (hG1_sf.concat hT02_sf)
  have hPhase2_sf : phase2.IsStandardForm := hClear_sf.concat (hT10_sf.concat (hG2_sf.concat hT03_sf))
  have hPhase3_sf : phase3.IsStandardForm := hClear_sf.concat (hTsetup_sf.concat hF_sf)

  -- H = phase1.concat (phase2.concat phase3)
  let H := Program.composeBU pF pG1 pG2
  have hH_eq : H = phase1.concat (phase2.concat phase3) := rfl

  -- Convert hHalts to use H
  have hHalts' : Halts H (List.ofFn inputs) := hHalts

  -- Extract phase1 halting
  have hPhase1_halts : Halts phase1 (List.ofFn inputs) := by
    rw [hH_eq] at hHalts'
    exact Halts.prefix_of_concat_sf hHalts' hPhase1_sf

  -- Extract suffix after phase1
  have hSuffix12 := Halts.suffix_of_concat_sf hHalts' hPhase1_sf
  obtain ⟨sPhase1, _, hsPhase1_eq, cPhase23, hPhase23_steps, hPhase23_halted⟩ := hSuffix12

  -- T01 execution facts (using helpers)
  have hT01_sl := single_transfer_isStraightLine 0 (m + 1)
  have hT01_halts' := straightLine_halts hT01_sl (List.ofFn inputs)
  let sT01 := (Classical.choose hT01_halts').state
  have hT01_state : sT01 = (State.fromInputs (List.ofFn inputs)).write (m + 1)
      ((State.fromInputs (List.ofFn inputs)).read 0) := T01_state_eq m inputs
  have hsT01_m1 : sT01.read (m + 1) = inputs ⟨0, by omega⟩ := T01_stores_input m inputs
  have hT01_steps := (Classical.choose_spec hT01_halts').1
  have hT01_halted := (Classical.choose_spec hT01_halts').2
  have hT01_pc : (Classical.choose hT01_halts').pc = T01.length := by
    have hpc := hT01_sf.halts_at_length (List.ofFn inputs) _ hT01_steps hT01_halted
    simp only [T01, List.length_singleton] at hpc ⊢
    exact hpc

  -- Prove that sPhase1 preserved input[0] in register m+1 (hoisted to avoid duplication)
  have hsPhase1_m1 : sPhase1.read (m + 1) = inputs ⟨0, by omega⟩ := by
    rw [hsPhase1_eq hPhase1_halts]
    let cPhase1' := Classical.choose hPhase1_halts
    have hPhase1'_spec := Classical.choose_spec hPhase1_halts
    have hPhase1'_steps : Steps phase1 (Config.init (List.ofFn inputs)) cPhase1' := hPhase1'_spec.1
    have hPhase1'_halted : cPhase1'.isHalted phase1 := hPhase1'_spec.2

    have hm_ge_G1 : pG1.maxRegister ≤ m := compositionBaseBU_ge_G1 pF pG1 pG2
    have hagreeG1' : ∀ r', r' ≤ pG1.maxRegister →
        sT01.read r' = (State.fromInputs (List.ofFn inputs)).read r' := fun r' hr' =>
      T01_preserves_below m inputs r' (Nat.le_trans hr' hm_ge_G1)
    have hagreeG1'' : sT01.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG1.maxRegister := fun _ _ hhi =>
      hagreeG1' _ hhi

    let eG1 := Halts.executeFromAgreeingState hG1_halts hG1_sf hagreeG1''
    let cG1' := eG1.config
    have hG1_steps' := eG1.steps
    have hG1_halted' := eG1.halted

    have hG1_preserves : cG1'.state.read (m + 1) = sT01.read (m + 1) :=
      eG1.preserves_high_register (m + 1) (by omega : pG1.maxRegister < m + 1)

    have hT02_halts' := single_transfer_halts 0 (m + 2) cG1'.state
    obtain ⟨cT02', hT02_steps', hT02_halted', hT02_pc', hT02_state'⟩ := hT02_halts'

    have hT02_preserves : cT02'.state.read (m + 1) = cG1'.state.read (m + 1) := by
      rw [hT02_state']
      exact State.write_read_diff _ _ _ _ (by omega : m + 1 ≠ m + 2)

    have hG1T02_steps : Steps (pG1.concat T02) ⟨0, sT01⟩ ⟨cT02'.pc + pG1.length, cT02'.state⟩ := by
      have hG1T02_steps_prefix := Steps.concat_left_prefix (p2 := T02) hG1_steps' hG1_halted'
      have hT02_steps'' := Steps.concat_right (p1 := pG1) hT02_steps' hT02_halted'
      have hstart_eq : (⟨0 + pG1.length, cG1'.state⟩ : Config) = ⟨cG1'.pc, cG1'.state⟩ := by
        simp only [Nat.zero_add]; ext; exact eG1.pc_eq.symm; rfl
      rw [hstart_eq] at hT02_steps''
      exact Relation.ReflTransGen.trans hG1T02_steps_prefix hT02_steps''
    have hG1T02_halted : (⟨cT02'.pc + pG1.length, cT02'.state⟩ : Config).isHalted (pG1.concat T02) := by
      simp only [Config.isHalted, Program.concat_length, T02, List.length_singleton] at hT02_halted' ⊢
      rw [hT02_pc']
      omega

    have hPhase1_final_steps : Steps phase1 (Config.init (List.ofFn inputs))
        ⟨(cT02'.pc + pG1.length) + T01.length, cT02'.state⟩ := by
      have hT01_steps' := Steps.concat_left_prefix (p2 := pG1.concat T02) hT01_steps hT01_halted
      have hG1T02_steps' := Steps.concat_right (p1 := T01) hG1T02_steps hG1T02_halted
      have hstart_eq' : (⟨0 + T01.length, sT01⟩ : Config) = ⟨(Classical.choose hT01_halts').pc, sT01⟩ := by
        simp only [Nat.zero_add, hT01_pc]
      rw [hstart_eq'] at hG1T02_steps'
      exact Relation.ReflTransGen.trans hT01_steps' hG1T02_steps'
    have hPhase1_final_halted : (⟨(cT02'.pc + pG1.length) + T01.length, cT02'.state⟩ : Config).isHalted phase1 := by
      simp only [Config.isHalted, phase1, Program.concat_length, T01, T02, List.length_singleton]
      rw [hT02_pc']
      omega

    have hPhase1_state_eq : cPhase1'.state = cT02'.state := by
      have heq := Steps.halts_unique hPhase1'_steps hPhase1'_halted hPhase1_final_steps hPhase1_final_halted
      simp only [heq]

    rw [hPhase1_state_eq, hT02_preserves, hG1_preserves, hsT01_m1]

  -- Extract phase3 halting from phase2.concat phase3
  have hPhase3_from := suffix_of_concat_from_zero hPhase23_steps hPhase23_halted hPhase2_sf
  obtain ⟨sPhase2, hPhase2_steps_from_s1, hPhase3_halts⟩ := hPhase3_from
  obtain ⟨cPhase3, hPhase3_steps, hPhase3_halted⟩ := hPhase3_halts

  -- Phase2 halts from sPhase1 (hoisted to avoid duplication in by_cases branches)
  have hsPhase2_from_sPhase1 := prefix_of_concat_from_zero hPhase23_steps hPhase23_halted hPhase2_sf
  obtain ⟨cPhase2_from_s1, hPhase2_steps_s1, hPhase2_halted_s1⟩ := hsPhase2_from_sPhase1

  -- Extract Tsetup.concat pF halting from phase3
  have hTsetupF_sf : (Tsetup.concat pF).IsStandardForm := hTsetup_sf.concat hF_sf
  have hClear_sl := clearRegisters_isStraightLine m
  obtain ⟨sClear', hClear_steps_phase3, hTsetupF_halts⟩ :=
    suffix_of_concat_from_zero hPhase3_steps hPhase3_halted hClear_sf
  obtain ⟨cTsetupF, hTsetupF_steps, hTsetupF_halted⟩ := hTsetupF_halts

  -- Characterize sClear' (hoisted to avoid duplication)
  have hClear_halted : (⟨clearProg.length, sClear'⟩ : Config).isHalted clearProg := Nat.le_refl _
  have hsClear'_eq : sClear' = straightLineFinalState hClear_sl sPhase2 :=
    straightLineFinalState_eq_of_halted hClear_sl sPhase2 ⟨clearProg.length, sClear'⟩ hClear_steps_phase3 hClear_halted

  -- Extract pF halting from Tsetup.concat pF
  obtain ⟨sTsetup, hTsetup_steps_from_clear, hF_halts⟩ :=
    suffix_of_concat_from_zero hTsetupF_steps hTsetupF_halted hTsetup_sf
  obtain ⟨cF', hF_steps', hF_halted'⟩ := hF_halts

  -- The key step: show sTsetup agrees with State.fromInputs for the composed inputs
  let fInput : Fin 2 → ℕ := fun i => match i with
    | ⟨0, _⟩ => (g1 inputs).get hg1_dom
    | ⟨1, _⟩ => (g2 inputs).get hg2_dom

  have hm_ge_F : pF.maxRegister ≤ m := compositionBaseBU_ge_F pF pG1 pG2

  have hagreeF : ∀ r, r ≤ pF.maxRegister →
      sTsetup.read r = (State.fromInputs (List.ofFn fInput)).read r := by
    intro r hr
    -- First, characterize sTsetup using Tsetup's semantics
    have hTsetup_exec : ∃ c, Steps Tsetup ⟨0, sClear'⟩ c ∧ c.isHalted Tsetup ∧ c.pc = 2 ∧
        c.state = (sClear'.write 0 (sClear'.read (m + 2))).write 1 (sClear'.read (m + 3)) := by
      have h1 := single_transfer_step (m + 2) 0 sClear'
      let s1 := sClear'.write 0 (sClear'.read (m + 2))
      have h2' : Step Tsetup ⟨1, s1⟩ ⟨2, s1.write 1 (s1.read (m + 3))⟩ := by
        apply Step.trans
        simp [Program.getInstr, Tsetup]
      have hsteps : Steps Tsetup ⟨0, sClear'⟩ ⟨2, s1.write 1 (s1.read (m + 3))⟩ := by
        have h1' : Step Tsetup ⟨0, sClear'⟩ ⟨1, s1⟩ := by
          apply Step.trans
          simp [Program.getInstr, Tsetup]
        exact Relation.ReflTransGen.head h1' (Relation.ReflTransGen.single h2')
      have hhalted : (⟨2, s1.write 1 (s1.read (m + 3))⟩ : Config).isHalted Tsetup := by
        simp [Config.isHalted, Tsetup]
      have hs1_read : s1.read (m + 3) = sClear'.read (m + 3) := by
        simp only [s1, State.write_read_diff _ _ _ _ (by omega : m + 3 ≠ 0)]
      refine ⟨⟨2, s1.write 1 (s1.read (m + 3))⟩, hsteps, hhalted, rfl, ?_⟩
      rw [hs1_read]
    obtain ⟨cTsetup', hTsetup_steps', hTsetup_halted', _, hTsetup_state'⟩ := hTsetup_exec

    have hsTsetup_halted : (⟨Tsetup.length, sTsetup⟩ : Config).isHalted Tsetup := Nat.le_refl _
    have hconfigs_eq := Steps.halts_unique hTsetup_steps_from_clear hsTsetup_halted
                                           hTsetup_steps' hTsetup_halted'
    have hsTsetup_eq : sTsetup = (sClear'.write 0 (sClear'.read (m + 2))).write 1 (sClear'.read (m + 3)) := by
      have : sTsetup = cTsetup'.state := congrArg Config.state hconfigs_eq
      rw [this, hTsetup_state']

    -- Hoisted: clearProg halts from sPhase1 (used in both r=0 and r=1 cases)
    have hClear_halts_s1 := straightLine_halts_from_state hClear_sl sPhase1
    obtain ⟨cClear_s1, hClear_steps_s1, hClear_halted_s1, hClear_pc_s1⟩ := hClear_halts_s1
    have hClear_state_eq_s1 := straightLineFinalState_eq_of_halted hClear_sl sPhase1 cClear_s1 hClear_steps_s1 hClear_halted_s1

    -- Hoisted: T10 execution from cClear_s1.state (used in both r=0 and r=1 cases)
    have hT10_halts_s1 := single_transfer_halts (m + 1) 0 cClear_s1.state
    obtain ⟨cT10_s1, hT10_steps_s1, hT10_halted_s1, hT10_pc_s1, hT10_state_s1⟩ := hT10_halts_s1
    have hT10_r0_s1 : cT10_s1.state.read 0 = sPhase1.read (m + 1) := by
      rw [hT10_state_s1, State.write_read_same]
      have hClear_preserves_m1 : cClear_s1.state.read (m + 1) = sPhase1.read (m + 1) := by
        rw [hClear_state_eq_s1]; exact clearRegisters_preserves_above m sPhase1 (m + 1) (by omega)
      exact hClear_preserves_m1
    have hT10_r0_eq : cT10_s1.state.read 0 = inputs ⟨0, by omega⟩ := by
      rw [hT10_r0_s1, hsPhase1_m1]

    -- Hoisted: hagreeG2' (used in both r=0 and r=1 cases)
    have hm_ge_G2' : pG2.maxRegister ≤ m := compositionBaseBU_ge_G2 pF pG1 pG2
    have hagreeG2' : cT10_s1.state.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG2.maxRegister := by
      intro r' _ hhi
      by_cases hr0' : r' = 0
      · rw [hr0', hT10_r0_eq]; simp [State.fromInputs, State.read]
      · have hT10_preserves_r' : cT10_s1.state.read r' = cClear_s1.state.read r' := by
          rw [hT10_state_s1]; exact State.write_read_diff _ _ _ _ (by omega : r' ≠ 0)
        have hClear_zeros_r' : cClear_s1.state.read r' = 0 := by
          rw [hClear_state_eq_s1]; exact clearRegisters_zeros m sPhase1 r' (by omega : r' ≤ m)
        rw [hT10_preserves_r', hClear_zeros_r']
        simp only [State.fromInputs, State.read]
        have hr_ge' : r' ≥ (List.ofFn inputs).length := by simp only [List.length_ofFn]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr_ge', Option.getD_none]

    -- Hoisted: G2 execution from cT10_s1.state (used in both r=0 and r=1 cases)
    have hG2_halts_s1 : Halts pG2 (List.ofFn inputs) := (hG2_spec inputs).1.mpr hg2_dom
    let eG2_s1 := Halts.executeFromAgreeingState hG2_halts_s1 hG2_sf hagreeG2'
    let cG2_s1 := eG2_s1.config
    have hG2_steps_s1 := eG2_s1.steps
    have hG2_halted_s1 := eG2_s1.halted
    have hG2_pc_s1 := eG2_s1.pc_eq

    -- Hoisted: T03 execution from cG2_s1.state (used in both r=0 and r=1 cases)
    have hT03_halts_s1 := single_transfer_halts 0 (m + 3) cG2_s1.state
    obtain ⟨cT03_s1, hT03_steps_s1, hT03_halted_s1, hT03_pc_s1, hT03_state_s1⟩ := hT03_halts_s1

    -- Hoisted: Phase2 step construction (used in both r=0 and r=1 cases)
    have hG2T03_steps_s1 : Steps (pG2.concat T03) ⟨0, cT10_s1.state⟩ ⟨cT03_s1.pc + pG2.length, cT03_s1.state⟩ := by
      have hG2T03_prefix := Steps.concat_left_prefix (p2 := T03) hG2_steps_s1 hG2_halted_s1
      have hT03_steps'' := Steps.concat_right (p1 := pG2) hT03_steps_s1 hT03_halted_s1
      have hstart_eq : (⟨0 + pG2.length, cG2_s1.state⟩ : Config) = ⟨cG2_s1.pc, cG2_s1.state⟩ := by
        simp only [Nat.zero_add]; ext; exact hG2_pc_s1.symm; rfl
      rw [hstart_eq] at hT03_steps''
      exact Relation.ReflTransGen.trans hG2T03_prefix hT03_steps''
    have hG2T03_halted_s1 : (⟨cT03_s1.pc + pG2.length, cT03_s1.state⟩ : Config).isHalted (pG2.concat T03) := by
      simp only [Config.isHalted, Program.concat_length, T03, List.length_singleton] at hT03_halted_s1 ⊢
      rw [hT03_pc_s1]; omega
    have hT10G2T03_steps_s1 : Steps (T10.concat (pG2.concat T03)) ⟨0, cClear_s1.state⟩
        ⟨(cT03_s1.pc + pG2.length) + T10.length, cT03_s1.state⟩ := by
      have hT10_prefix := Steps.concat_left_prefix (p2 := pG2.concat T03) hT10_steps_s1 hT10_halted_s1
      have hG2T03_steps'' := Steps.concat_right (p1 := T10) hG2T03_steps_s1 hG2T03_halted_s1
      have hstart_eq : (⟨0 + T10.length, cT10_s1.state⟩ : Config) = ⟨cT10_s1.pc, cT10_s1.state⟩ := by
        simp only [Nat.zero_add, T10, List.length_singleton] at hT10_pc_s1 ⊢
        ext
        · exact hT10_pc_s1.symm
        · rfl
      rw [hstart_eq] at hG2T03_steps''
      exact Relation.ReflTransGen.trans hT10_prefix hG2T03_steps''
    have hT10G2T03_halted_s1 : (⟨(cT03_s1.pc + pG2.length) + T10.length, cT03_s1.state⟩ : Config).isHalted (T10.concat (pG2.concat T03)) := by
      simp only [Config.isHalted, Program.concat_length, T10, T03, List.length_singleton] at hT03_halted_s1 ⊢
      rw [hT03_pc_s1]; omega
    have hPhase2_explicit_steps_s1 : Steps phase2 ⟨0, sPhase1⟩ ⟨((cT03_s1.pc + pG2.length) + T10.length) + clearProg.length, cT03_s1.state⟩ := by
      have hClear_prefix := Steps.concat_left_prefix (p2 := T10.concat (pG2.concat T03)) hClear_steps_s1 hClear_halted_s1
      have hT10G2T03_steps'' := Steps.concat_right (p1 := clearProg) hT10G2T03_steps_s1 hT10G2T03_halted_s1
      have hstart_eq : (⟨0 + clearProg.length, cClear_s1.state⟩ : Config) = ⟨cClear_s1.pc, cClear_s1.state⟩ := by
        simp only [Nat.zero_add]
        ext
        · exact hClear_pc_s1.symm
        · rfl
      rw [hstart_eq] at hT10G2T03_steps''
      exact Relation.ReflTransGen.trans hClear_prefix hT10G2T03_steps''
    have hPhase2_explicit_halted_s1 : (⟨((cT03_s1.pc + pG2.length) + T10.length) + clearProg.length, cT03_s1.state⟩ : Config).isHalted phase2 := by
      simp only [Config.isHalted, phase2, Program.concat_length, T10, T03, List.length_singleton] at hT03_halted_s1 ⊢
      rw [hT03_pc_s1]; omega
    have hPhase2_state_match_s1 : cPhase2_from_s1.state = cT03_s1.state := by
      have hconfigs := Steps.halts_unique hPhase2_steps_s1 hPhase2_halted_s1 hPhase2_explicit_steps_s1 hPhase2_explicit_halted_s1
      rw [hconfigs]

    by_cases hr0 : r = 0
    · -- Case r = 0: sTsetup.read 0 = fInput 0 = g1(inputs[0])
      subst hr0
      have hsTsetup_r0 : sTsetup.read 0 = sClear'.read (m + 2) := by
        rw [hsTsetup_eq]
        simp only [State.read, State.write]
        simp [Function.update]

      have hsClear'_preserves_m2 : sClear'.read (m + 2) = sPhase2.read (m + 2) := by
        rw [hsClear'_eq]
        exact clearRegisters_preserves_above m sPhase2 (m + 2) (by omega)

      -- sPhase2.read (m+2) = g1(inputs[0])
      have hsPhase2_halted : (⟨phase2.length, sPhase2⟩ : Config).isHalted phase2 := by simp [Config.isHalted]
      have hconfigs := Steps.halts_unique hPhase2_steps_from_s1 hsPhase2_halted hPhase2_steps_s1 hPhase2_halted_s1
      have hsPhase2_eq : sPhase2 = cPhase2_from_s1.state := congrArg Config.state hconfigs

      have hPhase2_preserves_m2 : cPhase2_from_s1.state.read (m + 2) = sPhase1.read (m + 2) := by
        have hClear_preserves : cClear_s1.state.read (m + 2) = sPhase1.read (m + 2) := by
          rw [hClear_state_eq_s1]
          exact clearRegisters_preserves_above m sPhase1 (m + 2) (by omega)

        have hT10_preserves : cT10_s1.state.read (m + 2) = cClear_s1.state.read (m + 2) := by
          rw [hT10_state_s1]
          exact State.write_read_diff _ _ _ _ (by omega : m + 2 ≠ 0)

        have hG2_preserves' : cG2_s1.state.read (m + 2) = cT10_s1.state.read (m + 2) :=
          eG2_s1.preserves_high_register (m + 2) (by omega : pG2.maxRegister < m + 2)

        have hT03_preserves' : cT03_s1.state.read (m + 2) = cG2_s1.state.read (m + 2) := by
          rw [hT03_state_s1]
          exact State.write_read_diff _ _ _ _ (by omega : m + 2 ≠ m + 3)

        have hChain : cT03_s1.state.read (m + 2) = sPhase1.read (m + 2) := by
          rw [hT03_preserves', hG2_preserves', hT10_preserves, hClear_preserves]

        rw [hPhase2_state_match_s1, hChain]

      have hsPhase1_v1 : sPhase1.read (m + 2) = (g1 inputs).get hg1_dom := by
        rw [hsPhase1_eq hPhase1_halts]
        let cPhase1''' := Classical.choose hPhase1_halts
        have hPhase1'''_spec := Classical.choose_spec hPhase1_halts
        have hPhase1'''_steps : Steps phase1 (Config.init (List.ofFn inputs)) cPhase1''' := hPhase1'''_spec.1
        have hPhase1'''_halted : cPhase1'''.isHalted phase1 := hPhase1'''_spec.2

        have hm_ge_G1''' : pG1.maxRegister ≤ m := compositionBaseBU_ge_G1 pF pG1 pG2
        have hagreeG1'''' : ∀ r', r' ≤ pG1.maxRegister →
            sT01.read r' = (State.fromInputs (List.ofFn inputs)).read r' := by
          intro r' hr'
          rw [hT01_state]
          have hr_ne : r' ≠ m + 1 := by omega
          exact State.write_read_diff _ _ _ _ hr_ne
        have hagreeG1''''' : sT01.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG1.maxRegister := by
          intro r' _ hhi
          exact hagreeG1'''' r' hhi

        let eG1'' := Halts.executeFromAgreeingState hG1_halts hG1_sf hagreeG1'''''
        let cG1''' := eG1''.config
        have hG1_steps'''' := eG1''.steps
        have hG1_halted'''' := eG1''.halted
        have hG1_pc''' := eG1''.pc_eq

        have hcG1'''_r0 : cG1'''.state.read 0 = (g1 inputs).get hg1_dom := by
          have h0_le : 0 ≤ pG1.maxRegister := Nat.zero_le _
          have hagree_at_0 := State.agreeOn_read eG1''.state_agrees (Nat.zero_le 0) h0_le
          rw [hagree_at_0]
          have hres : (Classical.choose eG1''.originalHalts).state.read 0 = Result pG1 (List.ofFn inputs) hG1_halts := by
            simp only [Result, State.output, State.read]
          rw [hres]
          exact (hG1_spec inputs).2 hG1_halts hg1_dom

        have hT02_halts'''' := single_transfer_halts 0 (m + 2) cG1'''.state
        obtain ⟨cT02''', hT02_steps'''', hT02_halted'''', hT02_pc'''', hT02_state''''⟩ := hT02_halts''''

        have hT02_m2 : cT02'''.state.read (m + 2) = cG1'''.state.read 0 := by
          rw [hT02_state'''', State.write_read_same]

        have hG1T02_steps''' : Steps (pG1.concat T02) ⟨0, sT01⟩ ⟨cT02'''.pc + pG1.length, cT02'''.state⟩ := by
          have hG1T02_steps_prefix := Steps.concat_left_prefix (p2 := T02) hG1_steps'''' hG1_halted''''
          have hT02_steps''''' := Steps.concat_right (p1 := pG1) hT02_steps'''' hT02_halted''''
          have hstart_eq : (⟨0 + pG1.length, cG1'''.state⟩ : Config) = ⟨cG1'''.pc, cG1'''.state⟩ := by
            simp only [Nat.zero_add]; ext; exact hG1_pc'''.symm; rfl
          rw [hstart_eq] at hT02_steps'''''
          exact Relation.ReflTransGen.trans hG1T02_steps_prefix hT02_steps'''''
        have hG1T02_halted''' : (⟨cT02'''.pc + pG1.length, cT02'''.state⟩ : Config).isHalted (pG1.concat T02) := by
          simp only [Config.isHalted, Program.concat_length, T02, List.length_singleton] at hT02_halted'''' ⊢
          rw [hT02_pc'''']
          omega

        have hPhase1_final_steps''' : Steps phase1 (Config.init (List.ofFn inputs))
            ⟨(cT02'''.pc + pG1.length) + T01.length, cT02'''.state⟩ := by
          have hT01_steps' := Steps.concat_left_prefix (p2 := pG1.concat T02) hT01_steps hT01_halted
          have hG1T02_steps'''' := Steps.concat_right (p1 := T01) hG1T02_steps''' hG1T02_halted'''
          have hstart_eq' : (⟨0 + T01.length, sT01⟩ : Config) = ⟨(Classical.choose hT01_halts').pc, sT01⟩ := by
            simp only [Nat.zero_add, hT01_pc]
          rw [hstart_eq'] at hG1T02_steps''''
          exact Relation.ReflTransGen.trans hT01_steps' hG1T02_steps''''
        have hPhase1_final_halted''' : (⟨(cT02'''.pc + pG1.length) + T01.length, cT02'''.state⟩ : Config).isHalted phase1 := by
          simp only [Config.isHalted, phase1, Program.concat_length, T01, T02, List.length_singleton]
          rw [hT02_pc'''']
          omega

        have hPhase1_state_eq''' : cPhase1'''.state = cT02'''.state := by
          have heq := Steps.halts_unique hPhase1'''_steps hPhase1'''_halted hPhase1_final_steps''' hPhase1_final_halted'''
          simp only [heq]

        rw [hPhase1_state_eq''', hT02_m2, hcG1'''_r0]

      have hsPhase2_v1 : sPhase2.read (m + 2) = (g1 inputs).get hg1_dom := by
        rw [hsPhase2_eq, hPhase2_preserves_m2, hsPhase1_v1]

      rw [hsTsetup_r0, hsClear'_preserves_m2, hsPhase2_v1]

      simp only [State.fromInputs, State.read, fInput]
      simp only [List.ofFn, List.getD]
      rfl

    · by_cases hr1 : r = 1
      · -- Case r = 1: sTsetup.read 1 = fInput 1 = g2(inputs[0])
        subst hr1
        have hsTsetup_r1 : sTsetup.read 1 = sClear'.read (m + 3) := by
          rw [hsTsetup_eq, State.write_read_same]

        have hsClear'_preserves_m3 : sClear'.read (m + 3) = sPhase2.read (m + 3) := by
          rw [hsClear'_eq]
          exact clearRegisters_preserves_above m sPhase2 (m + 3) (by omega)

        have hsPhase2_v2 : sPhase2.read (m + 3) = (g2 inputs).get hg2_dom := by
          have hsPhase2_eq : sPhase2 = cPhase2_from_s1.state := by
            have h1 : (⟨phase2.length, sPhase2⟩ : Config).isHalted phase2 := Nat.le_refl _
            have huniq := Steps.halts_unique hPhase2_steps_from_s1 h1 hPhase2_steps_s1 hPhase2_halted_s1
            exact congrArg Config.state huniq

          have hcG2_s1_r0 : cG2_s1.state.read 0 = (g2 inputs).get hg2_dom := by
            have h0_le : 0 ≤ pG2.maxRegister := Nat.zero_le _
            have hagree_at_0 := State.agreeOn_read eG2_s1.state_agrees (Nat.zero_le 0) h0_le
            rw [hagree_at_0]
            have hres : (Classical.choose eG2_s1.originalHalts).state.read 0 = Result pG2 (List.ofFn inputs) hG2_halts_s1 := by
              simp only [Result, State.output, State.read]
            rw [hres]
            exact (hG2_spec inputs).2 hG2_halts_s1 hg2_dom

          have hT03_m3 : cT03_s1.state.read (m + 3) = cG2_s1.state.read 0 := by
            rw [hT03_state_s1, State.write_read_same]

          rw [hsPhase2_eq, hPhase2_state_match_s1, hT03_m3, hcG2_s1_r0]

        rw [hsTsetup_r1, hsClear'_preserves_m3, hsPhase2_v2]

        simp only [State.fromInputs, State.read, fInput]
        simp only [List.ofFn, List.getD]
        rfl

      · -- Case r > 1: sTsetup.read r = 0
        have hsTsetup_r : sTsetup.read r = sClear'.read r := by
          rw [hsTsetup_eq]
          have hr_ne_0 : r ≠ 0 := hr0
          have hr_ne_1 : r ≠ 1 := hr1
          simp only [State.read, State.write]
          simp [Function.update, hr_ne_0, hr_ne_1]

        have hsClear'_zero : sClear'.read r = 0 := by
          rw [hsClear'_eq]
          exact clearRegisters_zeros m sPhase2 r (Nat.le_trans hr hm_ge_F)

        rw [hsTsetup_r, hsClear'_zero]

        simp only [State.fromInputs, State.read]
        have hr_ge : r ≥ (List.ofFn fInput).length := by
          simp only [List.length_ofFn]
          omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr_ge, Option.getD_none]

  have hF_halts' : Halts pF (List.ofFn fInput) :=
    Halts.of_agreeing_state hF_steps' hF_halted' hagreeF
  exact (hF_spec fInput).1.mp hF_halts'

set_option maxHeartbeats 800000 in
/-- Forward direction: if the composed program halts, the composed function is defined.

This lemma extracts the forward implication (Halts → Dom) from the main composition theorem.
Takes programs and their specs as explicit parameters. -/
theorem comp_binary_unary_halts_imp_dom
    {f : (Fin 2 → ℕ) → Part ℕ} {g1 g2 : (Fin 1 → ℕ) → Part ℕ}
    {pF pG1 pG2 : Program}
    (hF_sf : pF.IsStandardForm) (hG1_sf : pG1.IsStandardForm) (hG2_sf : pG2.IsStandardForm)
    (hF_spec : ∀ inputs : Fin 2 → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hH : Halts pF (List.ofFn inputs)) (hD : (f inputs).Dom),
        Result pF (List.ofFn inputs) hH = (f inputs).get hD)
    (hG1_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG1 (List.ofFn inputs) ↔ (g1 inputs).Dom) ∧
      ∀ (hH : Halts pG1 (List.ofFn inputs)) (hD : (g1 inputs).Dom),
        Result pG1 (List.ofFn inputs) hH = (g1 inputs).get hD)
    (hG2_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG2 (List.ofFn inputs) ↔ (g2 inputs).Dom) ∧
      ∀ (hH : Halts pG2 (List.ofFn inputs)) (hD : (g2 inputs).Dom),
        Result pG2 (List.ofFn inputs) hH = (g2 inputs).get hD)
    (inputs : Fin 1 → ℕ)
    (hHalts : Halts (Program.composeBU pF pG1 pG2) (List.ofFn inputs)) :
    ((Part.sequence (mkPair (g1 inputs) (g2 inputs))).bind f).Dom := by
  rw [comp_function_dom]
  -- Set up program structure
  set m := compositionBaseBU pF pG1 pG2 with hm_def
  let T01 : Program := [Instr.T 0 (m + 1)]
  let T02 : Program := [Instr.T 0 (m + 2)]
  let clearProg := Program.clearRegisters m
  let T10 : Program := [Instr.T (m + 1) 0]
  let T03 : Program := [Instr.T 0 (m + 3)]
  let Tsetup : Program := [Instr.T (m + 2) 0, Instr.T (m + 3) 1]

  let phase1 := T01.concat (pG1.concat T02)
  let phase2 := clearProg.concat (T10.concat (pG2.concat T03))
  let phase3 := clearProg.concat (Tsetup.concat pF)

  -- Standard form properties
  have hT01_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 1))
  have hT02_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 2))
  have hT10_sf := straightLine_isStandardForm (single_transfer_isStraightLine (m + 1) 0)
  have hT03_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 3))
  have hTsetup_sf := straightLine_isStandardForm (double_transfer_isStraightLine (m + 2) 0 (m + 3) 1)
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine m)

  have hPhase1_sf : phase1.IsStandardForm := hT01_sf.concat (hG1_sf.concat hT02_sf)
  have hPhase2_sf : phase2.IsStandardForm := hClear_sf.concat (hT10_sf.concat (hG2_sf.concat hT03_sf))
  have hPhase3_sf : phase3.IsStandardForm := hClear_sf.concat (hTsetup_sf.concat hF_sf)

  -- H = phase1.concat (phase2.concat phase3)
  let H := Program.composeBU pF pG1 pG2
  have hH_eq : H = phase1.concat (phase2.concat phase3) := rfl

  -- Convert hHalts to use H
  have hHalts' : Halts H (List.ofFn inputs) := hHalts

  -- Extract phase1 halting
  have hPhase1_halts : Halts phase1 (List.ofFn inputs) := by
    rw [hH_eq] at hHalts'
    exact Halts.prefix_of_concat_sf hHalts' hPhase1_sf

  -- g1 domain follows from composed program halting
  have hg1_dom : (g1 inputs).Dom := comp_binary_unary_halts_imp_g1_dom hG1_sf hG1_spec inputs hHalts
  have hG1_halts : Halts pG1 (List.ofFn inputs) := (hG1_spec inputs).1.mpr hg1_dom

  -- Extract suffix after phase1 for use by f proof
  have hSuffix12 := Halts.suffix_of_concat_sf hHalts' hPhase1_sf
  obtain ⟨sPhase1, _, hsPhase1_eq, cPhase23, hPhase23_steps, hPhase23_halted⟩ := hSuffix12

  -- g2 domain follows from composed program halting
  have hg2_dom : (g2 inputs).Dom := comp_binary_unary_halts_imp_g2_dom hG1_sf hG2_sf hG1_spec hG2_spec inputs hHalts

  have hf_dom : ∀ (h1 : (g1 inputs).Dom) (h2 : (g2 inputs).Dom),
      (f fun i => match i with
        | ⟨0, _⟩ => (g1 inputs).get h1
        | ⟨1, _⟩ => (g2 inputs).get h2).Dom :=
    fun h1 h2 => comp_binary_unary_halts_imp_f_dom hF_sf hG1_sf hG2_sf hF_spec hG1_spec hG2_spec inputs hHalts h1 h2

  exact ⟨hg1_dom, hg2_dom, hf_dom⟩

set_option maxHeartbeats 800000 in
/-- Backward direction: if the composed function is defined, the composed program halts.

This lemma extracts the backward implication (Dom → Halts) from the main composition theorem.
Takes programs and their specs as explicit parameters. -/
theorem comp_binary_unary_dom_imp_halts
    {f : (Fin 2 → ℕ) → Part ℕ} {g1 g2 : (Fin 1 → ℕ) → Part ℕ}
    {pF pG1 pG2 : Program}
    (hF_sf : pF.IsStandardForm) (hG1_sf : pG1.IsStandardForm) (hG2_sf : pG2.IsStandardForm)
    (hF_spec : ∀ inputs : Fin 2 → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hH : Halts pF (List.ofFn inputs)) (hD : (f inputs).Dom),
        Result pF (List.ofFn inputs) hH = (f inputs).get hD)
    (hG1_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG1 (List.ofFn inputs) ↔ (g1 inputs).Dom) ∧
      ∀ (hH : Halts pG1 (List.ofFn inputs)) (hD : (g1 inputs).Dom),
        Result pG1 (List.ofFn inputs) hH = (g1 inputs).get hD)
    (hG2_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG2 (List.ofFn inputs) ↔ (g2 inputs).Dom) ∧
      ∀ (hH : Halts pG2 (List.ofFn inputs)) (hD : (g2 inputs).Dom),
        Result pG2 (List.ofFn inputs) hH = (g2 inputs).get hD)
    (inputs : Fin 1 → ℕ)
    (hDom : ((Part.sequence (mkPair (g1 inputs) (g2 inputs))).bind f).Dom) :
    Halts (Program.composeBU pF pG1 pG2) (List.ofFn inputs) := by
  -- Define H for convenience (will convert at the end)
  let H := Program.composeBU pF pG1 pG2
  rw [comp_function_dom] at hDom
  obtain ⟨hg1_dom, hg2_dom, hf_dom⟩ := hDom

  -- G1, G2, F all halt because their respective functions are defined
  have hG1_halts : Halts pG1 (List.ofFn inputs) := (hG1_spec inputs).1.mpr hg1_dom
  have hG2_halts : Halts pG2 (List.ofFn inputs) := (hG2_spec inputs).1.mpr hg2_dom
  let v1 := Result pG1 (List.ofFn inputs) hG1_halts
  let v2 := Result pG2 (List.ofFn inputs) hG2_halts
  have hv1_eq : v1 = (g1 inputs).get hg1_dom := (hG1_spec inputs).2 hG1_halts hg1_dom
  have hv2_eq : v2 = (g2 inputs).get hg2_dom := (hG2_spec inputs).2 hG2_halts hg2_dom

  let fInput : Fin 2 → ℕ := fun i => match i with
    | ⟨0, _⟩ => v1
    | ⟨1, _⟩ => v2
  have hf_dom' : (f fInput).Dom := by
    have h := hf_dom hg1_dom hg2_dom
    convert h using 2
    funext i
    match i with
    | ⟨0, _⟩ => exact hv1_eq
    | ⟨1, _⟩ => exact hv2_eq
  have hF_halts : Halts pF (List.ofFn fInput) := (hF_spec fInput).1.mpr hf_dom'
  set m := compositionBaseBU pF pG1 pG2 with hm_def
  let T01 : Program := [Instr.T 0 (m + 1)]
  let T02 : Program := [Instr.T 0 (m + 2)]
  let clearProg := Program.clearRegisters m
  let T10 : Program := [Instr.T (m + 1) 0]
  let T03 : Program := [Instr.T 0 (m + 3)]
  let Tsetup : Program := [Instr.T (m + 2) 0, Instr.T (m + 3) 1]

  -- Standard form properties
  have hT01_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 1))
  have hT02_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 2))
  have hT10_sf := straightLine_isStandardForm (single_transfer_isStraightLine (m + 1) 0)
  have hT03_sf := straightLine_isStandardForm (single_transfer_isStraightLine 0 (m + 3))
  have hTsetup_sf := straightLine_isStandardForm (double_transfer_isStraightLine (m + 2) 0 (m + 3) 1)
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine m)

  -- Define the three phases
  let phase1 := T01.concat (pG1.concat T02)
  let phase2 := clearProg.concat (T10.concat (pG2.concat T03))
  let phase3 := clearProg.concat (Tsetup.concat pF)

  have hPhase1_sf : phase1.IsStandardForm := hT01_sf.concat (hG1_sf.concat hT02_sf)
  have hPhase2_sf : phase2.IsStandardForm := hClear_sf.concat (hT10_sf.concat (hG2_sf.concat hT03_sf))
  have hPhase3_sf : phase3.IsStandardForm := hClear_sf.concat (hTsetup_sf.concat hF_sf)

  -- The key structural lemma: each phase halts when started from appropriate state
  -- Phase 1 halts from Config.init
  have hPhase1_halts : Halts phase1 (List.ofFn inputs) := by
    -- phase1 = T01.concat (pG1.concat T02)
    -- Chain: T01 → G1 → T02 using concat_continuation twice
    have hT01_sl := single_transfer_isStraightLine 0 (m + 1)
    have hT02_sl := single_transfer_isStraightLine 0 (m + 2)
    have hT01_halts := straightLine_halts hT01_sl (List.ofFn inputs)
    have hT01_pc := straightLine_halts_at_length hT01_sl (List.ofFn inputs)
    let sT01 := (Classical.choose hT01_halts).state
    -- sT01 = (State.fromInputs inputs).write (m+1) (inputs[0])
    -- T01 writes to register m+1, and m+1 > m ≥ pG1.maxRegister
    -- So sT01 agrees with State.fromInputs on registers 0..pG1.maxRegister
    have hm_ge_G1 : pG1.maxRegister ≤ m := compositionBaseBU_ge_G1 pF pG1 pG2
    have hagreeG1 : ∀ r, r ≤ pG1.maxRegister → sT01.read r = (State.fromInputs (List.ofFn inputs)).read r := fun r hr =>
      T01_preserves_below m inputs r (Nat.le_trans hr hm_ge_G1)
    have hagreeG1' : sT01.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG1.maxRegister := fun _ _ hhi =>
      hagreeG1 _ hhi
    -- Get cG1 execution from agreeing state using helper
    let eG1 := Halts.executeFromAgreeingState hG1_halts hG1_sf hagreeG1'
    let cG1 := eG1.config
    have hG1_steps' := eG1.steps
    have hG1_halted' := eG1.halted
    have hG1_pc' := eG1.pc_eq
    -- T02 halts from cG1.state (straight-line halts from any state)
    obtain ⟨cT02, hT02_steps', hT02_halted', hT02_pc'⟩ :=
      straightLine_halts_from_state hT02_sl cG1.state
    -- Chain G1 and T02
    have hG1T02_halts' : ∃ c, Steps (pG1.concat T02) ⟨0, sT01⟩ c ∧ c.isHalted (pG1.concat T02) := by
      have hG1T02_steps := Steps.concat_left_prefix (p2 := T02) hG1_steps' hG1_halted'
      have hT02_steps'' := Steps.concat_right (p1 := pG1) hT02_steps' hT02_halted'
      have hstart_eq : (⟨0 + pG1.length, cG1.state⟩ : Config) = ⟨cG1.pc, cG1.state⟩ := by
        simp only [Nat.zero_add]; ext; exact hG1_pc'.symm; rfl
      rw [hstart_eq] at hT02_steps''
      have hsteps_total := Relation.ReflTransGen.trans hG1T02_steps hT02_steps''
      refine ⟨⟨cT02.pc + pG1.length, cT02.state⟩, hsteps_total, ?_⟩
      simp only [Config.isHalted, Program.concat_length, T02, List.length_singleton] at hT02_halted' ⊢
      rw [hT02_pc']
      simp only [List.length_singleton]
      omega
    -- Chain T01 with G1++T02
    exact Halts.concat_continuation hT01_halts hT01_pc hG1T02_halts'

  -- Phase 2 halts from cPhase1.state (registers set up appropriately)
  -- Key requirement: s.read (m + 1) = inputs ⟨0, _⟩ (original input preserved)
  have hPhase2_halts_from : ∀ s : State,
      s.read (m + 1) = inputs ⟨0, by omega⟩ →
      (∃ c, Steps phase2 ⟨0, s⟩ c ∧ c.isHalted phase2) := by
    intro s hs_input
    -- phase2 = clearProg.concat (T10.concat (pG2.concat T03))
    -- The proof chains: clearProg → T10 → G2 → T03

    -- Step 1: clearProg halts and preserves R[m+1]
    have hClear_sl := clearRegisters_isStraightLine m
    have hClear_halts := straightLine_halts_from_state hClear_sl s
    obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc⟩ := hClear_halts
    -- cClear.state preserves R[m+1]
    have hClear_preserves : cClear.state.read (m + 1) = s.read (m + 1) := by
      have hClear_state_eq := straightLineFinalState_eq_of_halted hClear_sl s cClear hClear_steps hClear_halted
      rw [hClear_state_eq]
      exact clearRegisters_preserves_above m s (m + 1) (by omega)

    -- Step 2: T10 halts from cClear.state and sets R[0] = R[m+1]
    have hT10_sl := single_transfer_isStraightLine (m + 1) 0
    have hT10_halts := single_transfer_halts (m + 1) 0 cClear.state
    obtain ⟨cT10, hT10_steps, hT10_halted, hT10_pc, hT10_state⟩ := hT10_halts

    -- After T10: R[0] = original R[m+1] = inputs[0]
    have hT10_r0 : cT10.state.read 0 = inputs ⟨0, by omega⟩ := by
      rw [hT10_state, State.write_read_same, hClear_preserves, hs_input]

    -- Step 3: pG2 halts from cT10.state because it agrees with initial state
    -- First show agreement on registers 0..pG2.maxRegister
    have hm_ge_G2 : pG2.maxRegister ≤ m := compositionBaseBU_ge_G2 pF pG1 pG2
    have hagreeG2 : cT10.state.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG2.maxRegister := by
      intro r _ hhi
      -- For r = 0: cT10.state.read 0 = inputs[0] by hT10_r0
      -- For r > 0 with r ≤ pG2.maxRegister ≤ m:
      --   cT10.state.read r = cClear.state.read r (T10 only writes to 0)
      --   cClear.state.read r = 0 (clearRegisters zeros r ≤ m)
      --   State.fromInputs.read r = 0 for r ≥ 1 (only 1 input)
      by_cases hr0 : r = 0
      · rw [hr0, hT10_r0]
        simp only [State.fromInputs, State.read]
        rfl
      · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        -- cT10.state.read r = cClear.state.read r
        have hT10_preserves_r : cT10.state.read r = cClear.state.read r := by
          rw [hT10_state]
          exact State.write_read_diff _ _ _ _ (by omega : r ≠ 0)
        -- cClear.state.read r = 0 for r ≤ m
        have hClear_zeros_r : cClear.state.read r = 0 := by
          have hClear_state_eq := straightLineFinalState_eq_of_halted hClear_sl s cClear hClear_steps hClear_halted
          rw [hClear_state_eq]
          exact clearRegisters_zeros m s r (by omega : r ≤ m)
        rw [hT10_preserves_r, hClear_zeros_r]
        -- State.fromInputs.read r = 0 for r ≥ 1 with 1 input
        simp only [State.fromInputs, State.read]
        -- For r ≥ 1 and List.ofFn inputs has length 1, getD returns default 0
        have hr_ge : r ≥ (List.ofFn inputs).length := by simp only [List.length_ofFn]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr_ge, Option.getD_none]

    -- Get pG2 execution from agreeing state using helper
    let eG2 := Halts.executeFromAgreeingState hG2_halts hG2_sf hagreeG2
    let cG2 := eG2.config
    have hG2_steps := eG2.steps
    have hG2_halted := eG2.halted
    have hG2_pc := eG2.pc_eq

    -- Step 4: T03 halts from cG2.state
    have hT03_sl := single_transfer_isStraightLine 0 (m + 3)
    have hT03_halts := single_transfer_halts 0 (m + 3) cG2.state
    obtain ⟨cT03, hT03_steps, hT03_halted, hT03_pc, _⟩ := hT03_halts

    -- Now chain all phases using concat_continuation
    -- phase2 = clearProg.concat (T10.concat (pG2.concat T03))

    -- First: pG2.concat T03 halts from cT10.state
    have hG2T03_steps : Steps (pG2.concat T03) ⟨0, cT10.state⟩ ⟨cT03.pc + pG2.length, cT03.state⟩ := by
      have hG2T03_prefix := Steps.concat_left_prefix (p2 := T03) hG2_steps hG2_halted
      have hT03_steps' := Steps.concat_right (p1 := pG2) hT03_steps hT03_halted
      have hstart_eq : (⟨0 + pG2.length, cG2.state⟩ : Config) = ⟨cG2.pc, cG2.state⟩ := by
        simp only [Nat.zero_add]; ext; exact hG2_pc.symm; rfl
      rw [hstart_eq] at hT03_steps'
      exact Relation.ReflTransGen.trans hG2T03_prefix hT03_steps'
    have hG2T03_halted : (⟨cT03.pc + pG2.length, cT03.state⟩ : Config).isHalted (pG2.concat T03) := by
      simp only [Config.isHalted, Program.concat_length, T03, List.length_singleton] at hT03_halted ⊢
      rw [hT03_pc]
      omega

    -- Second: T10.concat (pG2.concat T03) halts from cClear.state
    have hT10G2T03_steps : Steps (T10.concat (pG2.concat T03)) ⟨0, cClear.state⟩
        ⟨(cT03.pc + pG2.length) + T10.length, cT03.state⟩ := by
      have hT10_prefix := Steps.concat_left_prefix (p2 := pG2.concat T03) hT10_steps hT10_halted
      have hG2T03_steps' := Steps.concat_right (p1 := T10) hG2T03_steps hG2T03_halted
      have hstart_eq : (⟨0 + T10.length, cT10.state⟩ : Config) = ⟨cT10.pc, cT10.state⟩ := by
        simp only [Nat.zero_add]
        congr 1
        simp only [T10, List.length_singleton] at hT10_pc ⊢
        exact hT10_pc.symm
      rw [hstart_eq] at hG2T03_steps'
      exact Relation.ReflTransGen.trans hT10_prefix hG2T03_steps'
    have hT10G2T03_halted : (⟨(cT03.pc + pG2.length) + T10.length, cT03.state⟩ : Config).isHalted
        (T10.concat (pG2.concat T03)) := by
      simp only [Config.isHalted, Program.concat_length, T10, T03, List.length_singleton] at hT03_halted ⊢
      rw [hT03_pc]
      omega

    -- Third: phase2 = clearProg.concat (T10.concat (pG2.concat T03)) halts from s
    have hPhase2_steps : Steps phase2 ⟨0, s⟩
        ⟨((cT03.pc + pG2.length) + T10.length) + clearProg.length, cT03.state⟩ := by
      have hClear_prefix := Steps.concat_left_prefix (p2 := T10.concat (pG2.concat T03)) hClear_steps hClear_halted
      have hT10G2T03_steps' := Steps.concat_right (p1 := clearProg) hT10G2T03_steps hT10G2T03_halted
      have hstart_eq : (⟨0 + clearProg.length, cClear.state⟩ : Config) = ⟨cClear.pc, cClear.state⟩ := by
        simp only [Nat.zero_add]
        congr 1
        exact hClear_pc.symm
      rw [hstart_eq] at hT10G2T03_steps'
      exact Relation.ReflTransGen.trans hClear_prefix hT10G2T03_steps'
    have hPhase2_halted : (⟨((cT03.pc + pG2.length) + T10.length) + clearProg.length, cT03.state⟩ : Config).isHalted phase2 := by
      simp only [Config.isHalted, phase2, Program.concat_length, T10, T03,
        List.length_singleton] at hT03_halted ⊢
      rw [hT03_pc]
      omega

    exact ⟨_, hPhase2_steps, hPhase2_halted⟩

  -- Phase 3 halts from cPhase2.state (registers set up appropriately)
  -- Key requirements: s.read (m + 2) = v1, s.read (m + 3) = v2
  have hPhase3_halts_from : ∀ s : State,
      s.read (m + 2) = v1 → s.read (m + 3) = v2 →
      (∃ c, Steps phase3 ⟨0, s⟩ c ∧ c.isHalted phase3) := by
    intro s hs_v1 hs_v2
    -- phase3 = clearProg.concat (Tsetup.concat pF)
    -- The proof chains: clearProg → Tsetup → pF

    -- Step 1: clearProg halts and preserves R[m+2], R[m+3]
    have hClear_sl := clearRegisters_isStraightLine m
    have hClear_halts := straightLine_halts_from_state hClear_sl s
    obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc⟩ := hClear_halts
    -- cClear.state preserves R[m+2] and R[m+3]
    have hClear_state_eq := straightLineFinalState_eq_of_halted hClear_sl s cClear hClear_steps hClear_halted
    have hClear_preserves_v1 : cClear.state.read (m + 2) = v1 := by
      rw [hClear_state_eq, clearRegisters_preserves_above m s (m + 2) (by omega), hs_v1]
    have hClear_preserves_v2 : cClear.state.read (m + 3) = v2 := by
      rw [hClear_state_eq, clearRegisters_preserves_above m s (m + 3) (by omega), hs_v2]

    -- Step 2: Tsetup halts from cClear.state and sets R[0] = v1, R[1] = v2
    -- Tsetup = [T (m+2) 0, T (m+3) 1]
    -- We'll chain two single transfers

    -- First transfer: T (m+2) 0
    have hT1_halts := single_transfer_halts (m + 2) 0 cClear.state
    obtain ⟨cT1, hT1_steps, hT1_halted, hT1_pc, hT1_state⟩ := hT1_halts

    -- Second transfer: T (m+3) 1
    have hT2_halts := single_transfer_halts (m + 3) 1 cT1.state
    obtain ⟨cT2, hT2_steps, hT2_halted, hT2_pc, hT2_state⟩ := hT2_halts

    -- Chain them to get Tsetup execution
    -- Tsetup = [T (m+2) 0, T (m+3) 1]
    -- We execute the two instructions directly
    have hTsetup_steps : Steps Tsetup ⟨0, cClear.state⟩ ⟨2, cT2.state⟩ := by
      -- First step: T (m+2) 0
      have hstep1 : Step Tsetup ⟨0, cClear.state⟩ ⟨1, cClear.state.write 0 (cClear.state.read (m + 2))⟩ := by
        apply Step.trans
        simp only [Program.getInstr, Tsetup, List.getElem?_cons_zero]
      -- Second step: T (m+3) 1 (from cT1.state)
      have hstep2 : Step Tsetup ⟨1, cT1.state⟩ ⟨2, cT1.state.write 1 (cT1.state.read (m + 3))⟩ := by
        apply Step.trans
        simp only [Program.getInstr, Tsetup, List.getElem?_cons_succ, List.getElem?_cons_zero]
      -- The final state matches cT2.state
      have hstate2_match : cT1.state.write 1 (cT1.state.read (m + 3)) = cT2.state := hT2_state.symm
      rw [hstate2_match] at hstep2
      -- hstep1 goes to cT1.state by hT1_state
      have hstate1_match : cClear.state.write 0 (cClear.state.read (m + 2)) = cT1.state := hT1_state.symm
      rw [hstate1_match] at hstep1
      exact Relation.ReflTransGen.head hstep1 (Relation.ReflTransGen.single hstep2)
    have hTsetup_halted : (⟨2, cT2.state⟩ : Config).isHalted Tsetup := by
      simp only [Config.isHalted, Tsetup, List.length_cons, List.length_nil]
      omega
    have hTsetup_pc : (⟨2, cT2.state⟩ : Config).pc = Tsetup.length := by
      simp only [Tsetup, List.length_cons, List.length_nil]

    -- Use the final config as cTsetup
    let cTsetup := (⟨2, cT2.state⟩ : Config)

    -- After Tsetup: R[0] = v1, R[1] = v2
    have hTsetup_r0 : cTsetup.state.read 0 = v1 := by
      -- cTsetup.state = cT2.state = cT1.state.write 1 (cT1.state.read (m+3))
      -- cT1.state = cClear.state.write 0 (cClear.state.read (m+2))
      -- cT2.state.read 0 = cT1.state.read 0 (since T2 only writes to 1)
      -- cT1.state.read 0 = cClear.state.read (m+2) = v1
      show cT2.state.read 0 = v1
      rw [hT2_state, State.write_read_diff _ _ _ _ (by omega : 0 ≠ 1)]
      rw [hT1_state, State.write_read_same, hClear_preserves_v1]
    have hTsetup_r1 : cTsetup.state.read 1 = v2 := by
      show cT2.state.read 1 = v2
      rw [hT2_state, State.write_read_same]
      -- cT1.state.read (m+3) = cClear.state.read (m+3) (since T1 only writes to 0)
      rw [hT1_state, State.write_read_diff _ _ _ _ (by omega : m + 3 ≠ 0)]
      exact hClear_preserves_v2

    -- Step 3: pF halts from cTsetup.state because it agrees with fInput
    have hm_ge_F : pF.maxRegister ≤ m := compositionBaseBU_ge_F pF pG1 pG2
    have hagreeF : cTsetup.state.agreeOn (State.fromInputs (List.ofFn fInput)) 0 pF.maxRegister := by
      intro r _ hhi
      -- r ≤ pF.maxRegister ≤ m
      by_cases hr0 : r = 0
      · -- R[0] = v1 = fInput 0
        rw [hr0, hTsetup_r0]
        simp only [State.fromInputs, State.read, fInput]
        rfl
      · by_cases hr1 : r = 1
        · -- R[1] = v2 = fInput 1
          rw [hr1, hTsetup_r1]
          simp only [State.fromInputs, State.read, fInput]
          rfl
        · -- r > 1: cTsetup.state.read r = 0 (from clearProg)
          --        fromInputs.read r = 0 (only 2 inputs)
          have hTsetup_preserves_r : cTsetup.state.read r = cClear.state.read r := by
            -- cTsetup.state = cT2.state = cT1.state.write 1 (cT1.state.read (m+3))
            -- cT1.state = cClear.state.write 0 (cClear.state.read (m+2))
            show cT2.state.read r = cClear.state.read r
            rw [hT2_state, State.write_read_diff _ _ _ _ (by omega : r ≠ 1)]
            rw [hT1_state, State.write_read_diff _ _ _ _ (by omega : r ≠ 0)]
          have hClear_zeros_r : cClear.state.read r = 0 := by
            rw [hClear_state_eq]
            exact clearRegisters_zeros m s r (by omega : r ≤ m)
          rw [hTsetup_preserves_r, hClear_zeros_r]
          -- fromInputs.read r = 0 for r ≥ 2
          simp only [State.fromInputs, State.read]
          have hr_ge : r ≥ (List.ofFn fInput).length := by simp only [List.length_ofFn]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr_ge, Option.getD_none]

    -- Get pF execution from agreeing state using helper
    let eF := Halts.executeFromAgreeingState hF_halts hF_sf hagreeF
    let cF := eF.config
    have hF_steps := eF.steps
    have hF_halted := eF.halted
    have hF_pc := eF.pc_eq

    -- Now chain all phases using concat_continuation
    -- phase3 = clearProg.concat (Tsetup.concat pF)

    -- First: Tsetup.concat pF halts from cClear.state
    have hTsetupF_steps : Steps (Tsetup.concat pF) ⟨0, cClear.state⟩ ⟨cF.pc + Tsetup.length, cF.state⟩ := by
      have hTsetup_prefix := Steps.concat_left_prefix (p2 := pF) hTsetup_steps hTsetup_halted
      have hF_steps' := Steps.concat_right (p1 := Tsetup) hF_steps hF_halted
      have hstart_eq : (⟨0 + Tsetup.length, cTsetup.state⟩ : Config) = ⟨cTsetup.pc, cTsetup.state⟩ := by
        simp only [Nat.zero_add, cTsetup, Tsetup, List.length_cons, List.length_nil]
      rw [hstart_eq] at hF_steps'
      exact Relation.ReflTransGen.trans hTsetup_prefix hF_steps'
    have hTsetupF_halted : (⟨cF.pc + Tsetup.length, cF.state⟩ : Config).isHalted (Tsetup.concat pF) := by
      simp only [Config.isHalted, Program.concat_length, Tsetup, List.length_cons] at hF_halted ⊢
      rw [hF_pc]
      omega

    -- Second: phase3 = clearProg.concat (Tsetup.concat pF) halts from s
    have hPhase3_steps : Steps phase3 ⟨0, s⟩
        ⟨(cF.pc + Tsetup.length) + clearProg.length, cF.state⟩ := by
      have hClear_prefix := Steps.concat_left_prefix (p2 := Tsetup.concat pF) hClear_steps hClear_halted
      have hTsetupF_steps' := Steps.concat_right (p1 := clearProg) hTsetupF_steps hTsetupF_halted
      have hstart_eq : (⟨0 + clearProg.length, cClear.state⟩ : Config) = ⟨cClear.pc, cClear.state⟩ := by
        simp only [Nat.zero_add]
        congr 1
        exact hClear_pc.symm
      rw [hstart_eq] at hTsetupF_steps'
      exact Relation.ReflTransGen.trans hClear_prefix hTsetupF_steps'
    have hPhase3_halted : (⟨(cF.pc + Tsetup.length) + clearProg.length, cF.state⟩ : Config).isHalted phase3 := by
      simp only [Config.isHalted, phase3, Program.concat_length, Tsetup,
        List.length_cons] at hF_halted ⊢
      rw [hF_pc]
      omega

    exact ⟨_, hPhase3_steps, hPhase3_halted⟩

  -- Chain all phases
  let cPhase1 := Classical.choose hPhase1_halts
  have hPhase1_spec := Classical.choose_spec hPhase1_halts
  have hPhase1_steps : Steps phase1 (Config.init (List.ofFn inputs)) cPhase1 := hPhase1_spec.1
  have hPhase1_halted : cPhase1.isHalted phase1 := hPhase1_spec.2
  have hPhase1_pc : cPhase1.pc = phase1.length :=
    hPhase1_sf.halts_at_length (List.ofFn inputs) cPhase1 hPhase1_steps hPhase1_halted

  -- Prove that cPhase1 preserves inputs[0] in R[m+1]
  have hPhase1_preserves_input : cPhase1.state.read (m + 1) = inputs ⟨0, by omega⟩ := by
    -- Phase1 = T01.concat (pG1.concat T02)
    -- T01 sets R[m+1] = inputs[0]
    -- pG1 preserves R[m+1] (since pG1.maxRegister ≤ m < m+1)
    -- T02 preserves R[m+1] (since it only writes to m+2)

    -- Step 1: Get the state after T01
    have hT01_sl := single_transfer_isStraightLine 0 (m + 1)
    have hT01_halts := straightLine_halts hT01_sl (List.ofFn inputs)
    have hT01_pc := straightLine_halts_at_length hT01_sl (List.ofFn inputs)
    let sT01 := (Classical.choose hT01_halts).state

    -- Step 2: sT01.read (m+1) = inputs[0] (using helpers)
    have hT01_state : sT01 = (State.fromInputs (List.ofFn inputs)).write (m + 1)
        ((State.fromInputs (List.ofFn inputs)).read 0) := T01_state_eq m inputs
    have hsT01_m1 : sT01.read (m + 1) = inputs ⟨0, by omega⟩ := T01_stores_input m inputs

    -- Step 3: pG1.concat T02 from sT01 preserves R[m+1] (using helpers)
    have hm_ge_G1 : pG1.maxRegister ≤ m := compositionBaseBU_ge_G1 pF pG1 pG2
    have hagreeG1 : ∀ r, r ≤ pG1.maxRegister → sT01.read r = (State.fromInputs (List.ofFn inputs)).read r := fun r hr =>
      T01_preserves_below m inputs r (Nat.le_trans hr hm_ge_G1)
    have hagreeG1' : sT01.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG1.maxRegister := fun _ _ hhi =>
      hagreeG1 _ hhi
    -- Get cG1 execution from agreeing state using helper
    let eG1 := Halts.executeFromAgreeingState hG1_halts hG1_sf hagreeG1'
    let cG1 := eG1.config
    have hG1_steps' := eG1.steps
    have hG1_halted' := eG1.halted
    have hG1_pc' := eG1.pc_eq

    -- cG1 output equals v1 (via agreement with original execution)
    have hcG1_r0_eq : cG1.state.read 0 = v1 := by
      have h0_le : 0 ≤ pG1.maxRegister := Nat.zero_le _
      have hagree_at_0 := State.agreeOn_read eG1.state_agrees (Nat.zero_le 0) h0_le
      rw [hagree_at_0]
      rfl

    -- pG1 preserves R[m+1]
    have hG1_preserves : cG1.state.read (m + 1) = sT01.read (m + 1) :=
      Steps.preserves_high_register hG1_steps' (m + 1) (by omega : pG1.maxRegister < m + 1)

    -- Step 4: T02 execution from cG1.state
    have hT02_sl := single_transfer_isStraightLine 0 (m + 2)
    have hT02_halts' := single_transfer_halts 0 (m + 2) cG1.state
    obtain ⟨cT02, hT02_steps', hT02_halted', hT02_pc', hT02_state'⟩ := hT02_halts'

    -- T02 preserves R[m+1] (it only writes to m+2)
    have hT02_preserves : cT02.state.read (m + 1) = cG1.state.read (m + 1) := by
      rw [hT02_state']
      exact State.write_read_diff _ _ _ _ (by omega : m + 1 ≠ m + 2)

    -- Step 5: Relate cPhase1 to the explicitly constructed final config
    -- phase1 = T01.concat (pG1.concat T02)
    -- The final config of pG1.concat T02 from sT01 is ⟨cT02.pc + pG1.length, cT02.state⟩
    have hG1T02_steps : Steps (pG1.concat T02) ⟨0, sT01⟩ ⟨cT02.pc + pG1.length, cT02.state⟩ := by
      have hG1T02_steps_prefix := Steps.concat_left_prefix (p2 := T02) hG1_steps' hG1_halted'
      have hT02_steps'' := Steps.concat_right (p1 := pG1) hT02_steps' hT02_halted'
      have hstart_eq : (⟨0 + pG1.length, cG1.state⟩ : Config) = ⟨cG1.pc, cG1.state⟩ := by
        simp only [Nat.zero_add]; ext; exact hG1_pc'.symm; rfl
      rw [hstart_eq] at hT02_steps''
      exact Relation.ReflTransGen.trans hG1T02_steps_prefix hT02_steps''
    have hG1T02_halted : (⟨cT02.pc + pG1.length, cT02.state⟩ : Config).isHalted (pG1.concat T02) := by
      simp only [Config.isHalted, Program.concat_length, T02, List.length_singleton] at hT02_halted' ⊢
      rw [hT02_pc']
      omega

    -- The final config of phase1 from Config.init is ⟨something, cT02.state⟩
    have hPhase1_final_steps : Steps phase1 (Config.init (List.ofFn inputs))
        ⟨(cT02.pc + pG1.length) + T01.length, cT02.state⟩ := by
      have hT01_steps := (Classical.choose_spec hT01_halts).1
      have hT01_halted := (Classical.choose_spec hT01_halts).2
      have hT01_steps' := Steps.concat_left_prefix (p2 := pG1.concat T02) hT01_steps hT01_halted
      have hG1T02_steps' := Steps.concat_right (p1 := T01) hG1T02_steps hG1T02_halted
      have hstart_eq : (⟨0 + T01.length, sT01⟩ : Config) = ⟨(Classical.choose hT01_halts).pc, sT01⟩ := by
        simp only [Nat.zero_add]
        congr 1
        have hspec := Classical.choose_spec hT01_halts
        have hpc := hT01_sf.halts_at_length (List.ofFn inputs) _ hspec.1 hspec.2
        simp only [T01, List.length_singleton] at hpc ⊢
        exact hpc.symm
      rw [hstart_eq] at hG1T02_steps'
      exact Relation.ReflTransGen.trans hT01_steps' hG1T02_steps'
    have hPhase1_final_halted : (⟨(cT02.pc + pG1.length) + T01.length, cT02.state⟩ : Config).isHalted phase1 := by
      simp only [Config.isHalted, phase1, Program.concat_length, T01, T02, List.length_singleton]
      rw [hT02_pc']
      omega

    -- By uniqueness, cPhase1 = ⟨..., cT02.state⟩
    have hPhase1_state_eq : cPhase1.state = cT02.state := by
      have heq := Steps.halts_unique hPhase1_steps hPhase1_halted hPhase1_final_steps hPhase1_final_halted
      simp only [heq]

    -- Combine all the equalities
    rw [hPhase1_state_eq, hT02_preserves, hG1_preserves, hsT01_m1]

  -- Phase1 writes v1 to register m+2 (trace through T01 -> pG1 -> T02)
  have hPhase1_v1 : cPhase1.state.read (m + 2) = v1 := by
    -- Trace phase1 = T01.concat (pG1.concat T02) to show T02 writes v1 to m+2
    -- Step 1: Get the state after T01
    have hT01_sl := single_transfer_isStraightLine 0 (m + 1)
    have hT01_halts' := straightLine_halts hT01_sl (List.ofFn inputs)
    let sT01 := (Classical.choose hT01_halts').state

    -- Step 2: Run pG1 from sT01 using agreement with original execution (using helpers)
    have hm_ge_G1 : pG1.maxRegister ≤ m := compositionBaseBU_ge_G1 pF pG1 pG2
    have hagreeG1' : sT01.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG1.maxRegister := fun _ _ hhi =>
      T01_preserves_below m inputs _ (Nat.le_trans hhi hm_ge_G1)
    -- Get cG1 execution from agreeing state using helper
    let eG1' := Halts.executeFromAgreeingState hG1_halts hG1_sf hagreeG1'
    let cG1' := eG1'.config
    have hG1_steps' := eG1'.steps
    have hG1_halted' := eG1'.halted

    -- cG1'.state.read 0 = v1 (via agreement with original execution)
    have hcG1'_r0_eq : cG1'.state.read 0 = v1 := by
      have h0_le : 0 ≤ pG1.maxRegister := Nat.zero_le _
      have hagree_at_0 := State.agreeOn_read eG1'.state_agrees (Nat.zero_le 0) h0_le
      rw [hagree_at_0]
      rfl

    -- Step 3: T02 writes cG1'.state.read 0 to m+2
    have hT02_halts' := single_transfer_halts 0 (m + 2) cG1'.state
    obtain ⟨cT02', hT02_steps', hT02_halted', hT02_pc', hT02_state'⟩ := hT02_halts'

    -- Step 4: Build the full phase1 execution
    have hG1T02_steps : Steps (pG1.concat T02) ⟨0, sT01⟩ ⟨cT02'.pc + pG1.length, cT02'.state⟩ := by
      have hG1T02_steps_prefix := Steps.concat_left_prefix (p2 := T02) hG1_steps' hG1_halted'
      have hT02_steps'' := Steps.concat_right (p1 := pG1) hT02_steps' hT02_halted'
      have hstart_eq : (⟨0 + pG1.length, cG1'.state⟩ : Config) = ⟨cG1'.pc, cG1'.state⟩ := by
        simp only [Nat.zero_add]; ext; exact eG1'.pc_eq.symm; rfl
      rw [hstart_eq] at hT02_steps''
      exact Relation.ReflTransGen.trans hG1T02_steps_prefix hT02_steps''
    have hG1T02_halted : (⟨cT02'.pc + pG1.length, cT02'.state⟩ : Config).isHalted (pG1.concat T02) := by
      simp only [Config.isHalted, Program.concat_length, T02, List.length_singleton] at hT02_halted' ⊢
      rw [hT02_pc']
      omega

    have hPhase1_final_steps : Steps phase1 (Config.init (List.ofFn inputs))
        ⟨(cT02'.pc + pG1.length) + T01.length, cT02'.state⟩ := by
      have hT01_steps := (Classical.choose_spec hT01_halts').1
      have hT01_halted := (Classical.choose_spec hT01_halts').2
      have hT01_steps' := Steps.concat_left_prefix (p2 := pG1.concat T02) hT01_steps hT01_halted
      have hG1T02_steps' := Steps.concat_right (p1 := T01) hG1T02_steps hG1T02_halted
      have hstart_eq : (⟨0 + T01.length, sT01⟩ : Config) = ⟨(Classical.choose hT01_halts').pc, sT01⟩ := by
        simp only [Nat.zero_add]
        congr 1
        have hspec := Classical.choose_spec hT01_halts'
        have hpc := hT01_sf.halts_at_length (List.ofFn inputs) _ hspec.1 hspec.2
        simp only [T01, List.length_singleton] at hpc ⊢
        exact hpc.symm
      rw [hstart_eq] at hG1T02_steps'
      exact Relation.ReflTransGen.trans hT01_steps' hG1T02_steps'
    have hPhase1_final_halted : (⟨(cT02'.pc + pG1.length) + T01.length, cT02'.state⟩ : Config).isHalted phase1 := by
      simp only [Config.isHalted, phase1, Program.concat_length, T01, T02, List.length_singleton]
      rw [hT02_pc']
      omega

    -- By uniqueness, cPhase1.state = cT02'.state
    have hPhase1_state_eq' : cPhase1.state = cT02'.state := by
      have heq := Steps.halts_unique hPhase1_steps hPhase1_halted hPhase1_final_steps hPhase1_final_halted
      simp only [heq]

    -- Final computation
    rw [hPhase1_state_eq', hT02_state', State.write_read_same, hcG1'_r0_eq]

  have hPhase12_halts : Halts (phase1.concat phase2) (List.ofFn inputs) :=
    Halts.concat_continuation hPhase1_halts hPhase1_pc (hPhase2_halts_from cPhase1.state hPhase1_preserves_input)

  let cPhase12 := Classical.choose hPhase12_halts
  have hPhase12_spec := Classical.choose_spec hPhase12_halts
  have hPhase12_steps : Steps (phase1.concat phase2) (Config.init (List.ofFn inputs)) cPhase12 :=
    hPhase12_spec.1
  have hPhase12_halted : cPhase12.isHalted (phase1.concat phase2) := hPhase12_spec.2
  have hPhase12_pc : cPhase12.pc = (phase1.concat phase2).length :=
    (hPhase1_sf.concat hPhase2_sf).halts_at_length (List.ofFn inputs) cPhase12 hPhase12_steps hPhase12_halted

  -- Prove that cPhase12.state has the required values for phase3
  -- cPhase12.state.read (m + 2) = v1 (from phase1: T02 writes G1's result)
  -- cPhase12.state.read (m + 3) = v2 (from phase2: T03 writes G2's result)

  have hPhase12_v1 : cPhase12.state.read (m + 2) = v1 := by
    -- Strategy: phase1 writes v1 to m+2, phase2 preserves m+2
    -- Step 1: Extract intermediate state after phase1 using suffix_of_concat_from_zero
    obtain ⟨s1, hPhase1_steps_s1, hPhase2_halts_s1⟩ :=
      suffix_of_concat_from_zero hPhase12_steps hPhase12_halted hPhase1_sf

    -- Step 2: Show s1 = cPhase1.state by determinism
    have hs1_eq : s1 = cPhase1.state := by
      have hPhase1_spec := Classical.choose_spec hPhase1_halts
      have hpc := hPhase1_sf.halts_at_length _ _ hPhase1_spec.1 hPhase1_spec.2
      have hPhase1_at_len : Steps phase1 (Config.init (List.ofFn inputs)) ⟨phase1.length, cPhase1.state⟩ := by
        have heq : cPhase1 = ⟨phase1.length, cPhase1.state⟩ := by
          ext
          · exact hpc
          · rfl
        rw [← heq]
        exact hPhase1_spec.1
      have h1 : (⟨phase1.length, s1⟩ : Config).isHalted phase1 := by simp [Config.isHalted]
      have h2 : (⟨phase1.length, cPhase1.state⟩ : Config).isHalted phase1 := by simp [Config.isHalted]
      have hconfigs_eq := Steps.halts_unique hPhase1_steps_s1 h1 hPhase1_at_len h2
      exact congrArg Config.state hconfigs_eq

    -- Step 3: Get phase2's final config from suffix extraction
    obtain ⟨cPhase2_final, hPhase2_steps_final, hPhase2_halted_final⟩ := hPhase2_halts_s1

    -- Step 4: Relate cPhase12.state to cPhase2_final.state via determinism
    -- The execution hPhase12_steps decomposes as phase1 followed by phase2
    have hPhase12_state_eq : cPhase12.state = cPhase2_final.state := by
      -- Lift phase1 execution to concatenation
      have hPhase1_lifted := Steps.concat_left_prefix (p2 := phase2) hPhase1_steps_s1 (by simp [Config.isHalted])
      -- Lift phase2 execution to concatenation
      have hPhase2_lifted := Steps.concat_right (p1 := phase1) hPhase2_steps_final hPhase2_halted_final
      -- Adjust starting point
      simp only [Nat.zero_add] at hPhase2_lifted
      -- Chain the executions
      have hsteps_total := Relation.ReflTransGen.trans hPhase1_lifted hPhase2_lifted
      -- Final config is ⟨cPhase2_final.pc + phase1.length, cPhase2_final.state⟩
      have hfinal_halted : (⟨cPhase2_final.pc + phase1.length, cPhase2_final.state⟩ : Config).isHalted (phase1.concat phase2) := by
        simp only [Config.isHalted, Program.concat_length] at hPhase2_halted_final ⊢
        omega
      have hconfigs_eq := Steps.halts_unique hPhase12_steps hPhase12_halted hsteps_total hfinal_halted
      simp only [hconfigs_eq]

    -- Step 5: Show phase2 preserves m+2 by tracing through sub-programs
    -- Goal after rw [hPhase12_state_eq]: cPhase2_final.state.read (m + 2) = v1
    rw [hPhase12_state_eq]
    -- Need to show cPhase2_final.state.read (m+2) = s1.read (m+2) = v1
    -- First show s1.read (m+2) = v1
    have hs1_v1 : s1.read (m + 2) = v1 := by rw [hs1_eq]; exact hPhase1_v1

    -- To trace phase2, we need s1.read (m+1) = inputs[0]
    have hs1_input : s1.read (m + 1) = inputs ⟨0, by omega⟩ := by
      rw [hs1_eq]; exact hPhase1_preserves_input

    -- Re-trace phase2 construction to get explicit final state
    -- Step 5a: clearProg halts and preserves m+2
    have hClear_sl := clearRegisters_isStraightLine m
    have hClear_halts := straightLine_halts_from_state hClear_sl s1
    obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc⟩ := hClear_halts
    have hClear_state_eq := straightLineFinalState_eq_of_halted hClear_sl s1 cClear hClear_steps hClear_halted
    have hClear_preserves_m2 : cClear.state.read (m + 2) = s1.read (m + 2) := by
      rw [hClear_state_eq]; exact clearRegisters_preserves_above m s1 (m + 2) (by omega)

    -- Step 5b: T10 halts and preserves m+2 (writes to 0)
    have hT10_halts := single_transfer_halts (m + 1) 0 cClear.state
    obtain ⟨cT10, hT10_steps, hT10_halted, hT10_pc, hT10_state⟩ := hT10_halts
    have hT10_preserves_m2 : cT10.state.read (m + 2) = cClear.state.read (m + 2) := by
      rw [hT10_state]; exact State.write_read_diff _ _ _ _ (by omega : m + 2 ≠ 0)

    -- Step 5c: pG2 halts and preserves m+2 (maxRegister ≤ m < m+2)
    have hm_ge_G2 : pG2.maxRegister ≤ m := compositionBaseBU_ge_G2 pF pG1 pG2
    have hT10_r0 : cT10.state.read 0 = inputs ⟨0, by omega⟩ := by
      rw [hT10_state, State.write_read_same]
      have hClear_preserves_m1 : cClear.state.read (m + 1) = s1.read (m + 1) := by
        rw [hClear_state_eq]; exact clearRegisters_preserves_above m s1 (m + 1) (by omega)
      rw [hClear_preserves_m1, hs1_input]
    have hagreeG2 : cT10.state.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG2.maxRegister := by
      intro r _ hhi
      by_cases hr0 : r = 0
      · rw [hr0, hT10_r0]; simp [State.fromInputs, State.read]
      · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        have hT10_preserves_r : cT10.state.read r = cClear.state.read r := by
          rw [hT10_state]; exact State.write_read_diff _ _ _ _ (by omega : r ≠ 0)
        have hClear_zeros_r : cClear.state.read r = 0 := by
          rw [hClear_state_eq]; exact clearRegisters_zeros m s1 r (by omega : r ≤ m)
        rw [hT10_preserves_r, hClear_zeros_r]
        simp only [State.fromInputs, State.read]
        have hr_ge : r ≥ (List.ofFn inputs).length := by simp only [List.length_ofFn]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr_ge, Option.getD_none]
    -- Get cG2 execution from agreeing state using helper
    let eG2 := Halts.executeFromAgreeingState hG2_halts hG2_sf hagreeG2
    let cG2 := eG2.config
    have hG2_steps := eG2.steps
    have hG2_halted := eG2.halted
    have hG2_pc := eG2.pc_eq
    have hG2_preserves_m2 : cG2.state.read (m + 2) = cT10.state.read (m + 2) :=
      Steps.preserves_high_register hG2_steps (m + 2) (by omega : pG2.maxRegister < m + 2)

    -- Step 5d: T03 halts and preserves m+2 (writes to m+3)
    have hT03_halts := single_transfer_halts 0 (m + 3) cG2.state
    obtain ⟨cT03, hT03_steps, hT03_halted, hT03_pc, hT03_state⟩ := hT03_halts
    have hT03_preserves_m2 : cT03.state.read (m + 2) = cG2.state.read (m + 2) := by
      rw [hT03_state]
      exact State.write_read_diff _ _ _ _ (by omega : m + 2 ≠ m + 3)

    -- Chain all preservation proofs
    have hPhase2_chain : cT03.state.read (m + 2) = s1.read (m + 2) := by
      rw [hT03_preserves_m2, hG2_preserves_m2, hT10_preserves_m2, hClear_preserves_m2]

    -- Now show cPhase2_final.state = cT03.state by determinism
    -- First build the full phase2 execution ending at cT03
    have hPhase2_explicit_steps : Steps phase2 ⟨0, s1⟩ ⟨((cT03.pc + pG2.length) + T10.length) + clearProg.length, cT03.state⟩ := by
      have hG2T03_steps : Steps (pG2.concat T03) ⟨0, cT10.state⟩ ⟨cT03.pc + pG2.length, cT03.state⟩ := by
        have hG2T03_prefix := Steps.concat_left_prefix (p2 := T03) hG2_steps hG2_halted
        have hT03_steps' := Steps.concat_right (p1 := pG2) hT03_steps hT03_halted
        have hstart_eq : (⟨0 + pG2.length, cG2.state⟩ : Config) = ⟨cG2.pc, cG2.state⟩ := by
          simp only [Nat.zero_add]; ext; exact hG2_pc.symm; rfl
        rw [hstart_eq] at hT03_steps'
        exact Relation.ReflTransGen.trans hG2T03_prefix hT03_steps'
      have hG2T03_halted : (⟨cT03.pc + pG2.length, cT03.state⟩ : Config).isHalted (pG2.concat T03) := by
        simp only [Config.isHalted, Program.concat_length, T03, List.length_singleton] at hT03_halted ⊢
        rw [hT03_pc]; omega
      have hT10G2T03_steps : Steps (T10.concat (pG2.concat T03)) ⟨0, cClear.state⟩
          ⟨(cT03.pc + pG2.length) + T10.length, cT03.state⟩ := by
        have hT10_prefix := Steps.concat_left_prefix (p2 := pG2.concat T03) hT10_steps hT10_halted
        have hG2T03_steps' := Steps.concat_right (p1 := T10) hG2T03_steps hG2T03_halted
        have hstart_eq : (⟨0 + T10.length, cT10.state⟩ : Config) = ⟨cT10.pc, cT10.state⟩ := by
          simp only [Nat.zero_add, T10, List.length_singleton] at hT10_pc ⊢
          ext
          · exact hT10_pc.symm
          · rfl
        rw [hstart_eq] at hG2T03_steps'
        exact Relation.ReflTransGen.trans hT10_prefix hG2T03_steps'
      have hT10G2T03_halted : (⟨(cT03.pc + pG2.length) + T10.length, cT03.state⟩ : Config).isHalted (T10.concat (pG2.concat T03)) := by
        simp only [Config.isHalted, Program.concat_length, T10, T03, List.length_singleton] at hT03_halted ⊢
        rw [hT03_pc]; omega
      have hClear_prefix := Steps.concat_left_prefix (p2 := T10.concat (pG2.concat T03)) hClear_steps hClear_halted
      have hT10G2T03_steps' := Steps.concat_right (p1 := clearProg) hT10G2T03_steps hT10G2T03_halted
      have hstart_eq : (⟨0 + clearProg.length, cClear.state⟩ : Config) = ⟨cClear.pc, cClear.state⟩ := by
        simp only [Nat.zero_add]
        ext
        · exact hClear_pc.symm
        · rfl
      rw [hstart_eq] at hT10G2T03_steps'
      exact Relation.ReflTransGen.trans hClear_prefix hT10G2T03_steps'
    have hPhase2_explicit_halted : (⟨((cT03.pc + pG2.length) + T10.length) + clearProg.length, cT03.state⟩ : Config).isHalted phase2 := by
      simp only [Config.isHalted, phase2, Program.concat_length, T10, T03, List.length_singleton] at hT03_halted ⊢
      rw [hT03_pc]; omega

    -- By determinism, cPhase2_final.state = cT03.state
    have hPhase2_state_match : cPhase2_final.state = cT03.state := by
      have hconfigs_eq := Steps.halts_unique hPhase2_steps_final hPhase2_halted_final hPhase2_explicit_steps hPhase2_explicit_halted
      rw [hconfigs_eq]

    rw [hPhase2_state_match, hPhase2_chain, hs1_v1]

  have hPhase12_v2 : cPhase12.state.read (m + 3) = v2 := by
    -- Strategy: phase2's T03 writes cG2.state.read 0 to m+3, and cG2.state.read 0 = v2

    -- Step 1: Extract intermediate state after phase1 using suffix_of_concat_from_zero
    obtain ⟨s1', hPhase1_steps_s1', hPhase2_halts_s1'⟩ :=
      suffix_of_concat_from_zero hPhase12_steps hPhase12_halted hPhase1_sf

    -- Step 2: Show s1' = cPhase1.state by determinism
    have hs1'_eq : s1' = cPhase1.state := by
      have hPhase1_spec' := Classical.choose_spec hPhase1_halts
      have hpc := hPhase1_sf.halts_at_length _ _ hPhase1_spec'.1 hPhase1_spec'.2
      have hPhase1_at_len : Steps phase1 (Config.init (List.ofFn inputs)) ⟨phase1.length, cPhase1.state⟩ := by
        have heq : cPhase1 = ⟨phase1.length, cPhase1.state⟩ := by
          ext
          · exact hpc
          · rfl
        rw [← heq]
        exact hPhase1_spec'.1
      have h1 : (⟨phase1.length, s1'⟩ : Config).isHalted phase1 := by simp [Config.isHalted]
      have h2 : (⟨phase1.length, cPhase1.state⟩ : Config).isHalted phase1 := by simp [Config.isHalted]
      have hconfigs_eq := Steps.halts_unique hPhase1_steps_s1' h1 hPhase1_at_len h2
      exact congrArg Config.state hconfigs_eq

    -- Step 3: Get phase2's final config from suffix extraction
    obtain ⟨cPhase2_final', hPhase2_steps_final', hPhase2_halted_final'⟩ := hPhase2_halts_s1'

    -- Step 4: Relate cPhase12.state to cPhase2_final'.state via determinism
    have hPhase12_state_eq' : cPhase12.state = cPhase2_final'.state := by
      have hPhase1_lifted := Steps.concat_left_prefix (p2 := phase2) hPhase1_steps_s1' (by simp [Config.isHalted])
      have hPhase2_lifted := Steps.concat_right (p1 := phase1) hPhase2_steps_final' hPhase2_halted_final'
      simp only [Nat.zero_add] at hPhase2_lifted
      have hsteps_total := Relation.ReflTransGen.trans hPhase1_lifted hPhase2_lifted
      have hfinal_halted : (⟨cPhase2_final'.pc + phase1.length, cPhase2_final'.state⟩ : Config).isHalted (phase1.concat phase2) := by
        simp only [Config.isHalted, Program.concat_length] at hPhase2_halted_final' ⊢
        omega
      have hconfigs_eq := Steps.halts_unique hPhase12_steps hPhase12_halted hsteps_total hfinal_halted
      simp only [hconfigs_eq]

    rw [hPhase12_state_eq']

    -- Step 5: Trace through phase2 to show T03 writes v2 to m+3
    have hs1'_input : s1'.read (m + 1) = inputs ⟨0, by omega⟩ := by
      rw [hs1'_eq]; exact hPhase1_preserves_input

    -- Re-trace phase2 construction to get explicit final state with T03's value
    -- Step 5a: clearProg
    have hClear_sl' := clearRegisters_isStraightLine m
    have hClear_halts' := straightLine_halts_from_state hClear_sl' s1'
    obtain ⟨cClear', hClear_steps', hClear_halted', hClear_pc'⟩ := hClear_halts'
    have hClear_state_eq' := straightLineFinalState_eq_of_halted hClear_sl' s1' cClear' hClear_steps' hClear_halted'
    have hClear_preserves_m1' : cClear'.state.read (m + 1) = s1'.read (m + 1) := by
      rw [hClear_state_eq']; exact clearRegisters_preserves_above m s1' (m + 1) (by omega)

    -- Step 5b: T10
    have hT10_halts' := single_transfer_halts (m + 1) 0 cClear'.state
    obtain ⟨cT10', hT10_steps', hT10_halted', hT10_pc', hT10_state'⟩ := hT10_halts'
    have hT10'_r0 : cT10'.state.read 0 = inputs ⟨0, by omega⟩ := by
      rw [hT10_state', State.write_read_same, hClear_preserves_m1', hs1'_input]

    -- Step 5c: pG2 from cT10'.state
    have hm_ge_G2' : pG2.maxRegister ≤ m := compositionBaseBU_ge_G2 pF pG1 pG2
    have hagreeG2' : cT10'.state.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG2.maxRegister := by
      intro r _ hhi
      by_cases hr0 : r = 0
      · rw [hr0, hT10'_r0]; simp [State.fromInputs, State.read]
      · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        have hT10_preserves_r : cT10'.state.read r = cClear'.state.read r := by
          rw [hT10_state']; exact State.write_read_diff _ _ _ _ (by omega : r ≠ 0)
        have hClear_zeros_r : cClear'.state.read r = 0 := by
          rw [hClear_state_eq']; exact clearRegisters_zeros m s1' r (by omega : r ≤ m)
        rw [hT10_preserves_r, hClear_zeros_r]
        simp only [State.fromInputs, State.read]
        have hr_ge : r ≥ (List.ofFn inputs).length := by simp only [List.length_ofFn]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr_ge, Option.getD_none]
    -- Get cG2 execution from agreeing state using helper
    let eG2' := Halts.executeFromAgreeingState hG2_halts hG2_sf hagreeG2'
    let cG2' := eG2'.config
    have hG2_steps' := eG2'.steps
    have hG2_halted' := eG2'.halted
    have hG2_pc' := eG2'.pc_eq

    -- cG2'.state.read 0 = v2 (via agreement)
    have hcG2'_r0_eq : cG2'.state.read 0 = v2 := by
      have h0_le : 0 ≤ pG2.maxRegister := Nat.zero_le _
      have hagree_at_0 := State.agreeOn_read eG2'.state_agrees (Nat.zero_le 0) h0_le
      rw [hagree_at_0]
      rfl  -- v2 = Result pG2 ... = (Classical.choose hG2_halts).state.output

    -- Step 5d: T03 writes cG2'.state.read 0 to m+3
    have hT03_halts' := single_transfer_halts 0 (m + 3) cG2'.state
    obtain ⟨cT03', hT03_steps', hT03_halted', hT03_pc', hT03_state'⟩ := hT03_halts'
    have hT03'_m3 : cT03'.state.read (m + 3) = v2 := by
      rw [hT03_state', State.write_read_same, hcG2'_r0_eq]

    -- Now show cPhase2_final'.state = cT03'.state by determinism
    have hPhase2_explicit_steps' : Steps phase2 ⟨0, s1'⟩ ⟨((cT03'.pc + pG2.length) + T10.length) + clearProg.length, cT03'.state⟩ := by
      have hG2T03_steps : Steps (pG2.concat T03) ⟨0, cT10'.state⟩ ⟨cT03'.pc + pG2.length, cT03'.state⟩ := by
        have hG2T03_prefix := Steps.concat_left_prefix (p2 := T03) hG2_steps' hG2_halted'
        have hT03_steps'' := Steps.concat_right (p1 := pG2) hT03_steps' hT03_halted'
        have hstart_eq : (⟨0 + pG2.length, cG2'.state⟩ : Config) = ⟨cG2'.pc, cG2'.state⟩ := by
          simp only [Nat.zero_add]
          ext
          · exact hG2_pc'.symm
          · rfl
        rw [hstart_eq] at hT03_steps''
        exact Relation.ReflTransGen.trans hG2T03_prefix hT03_steps''
      have hG2T03_halted : (⟨cT03'.pc + pG2.length, cT03'.state⟩ : Config).isHalted (pG2.concat T03) := by
        simp only [Config.isHalted, Program.concat_length, T03, List.length_singleton] at hT03_halted' ⊢
        rw [hT03_pc']; omega
      have hT10G2T03_steps : Steps (T10.concat (pG2.concat T03)) ⟨0, cClear'.state⟩
          ⟨(cT03'.pc + pG2.length) + T10.length, cT03'.state⟩ := by
        have hT10_prefix := Steps.concat_left_prefix (p2 := pG2.concat T03) hT10_steps' hT10_halted'
        have hG2T03_steps' := Steps.concat_right (p1 := T10) hG2T03_steps hG2T03_halted
        have hstart_eq : (⟨0 + T10.length, cT10'.state⟩ : Config) = ⟨cT10'.pc, cT10'.state⟩ := by
          simp only [Nat.zero_add, T10, List.length_singleton] at hT10_pc' ⊢
          ext
          · exact hT10_pc'.symm
          · rfl
        rw [hstart_eq] at hG2T03_steps'
        exact Relation.ReflTransGen.trans hT10_prefix hG2T03_steps'
      have hT10G2T03_halted : (⟨(cT03'.pc + pG2.length) + T10.length, cT03'.state⟩ : Config).isHalted (T10.concat (pG2.concat T03)) := by
        simp only [Config.isHalted, Program.concat_length, T10, T03, List.length_singleton] at hT03_halted' ⊢
        rw [hT03_pc']; omega
      have hClear_prefix := Steps.concat_left_prefix (p2 := T10.concat (pG2.concat T03)) hClear_steps' hClear_halted'
      have hT10G2T03_steps' := Steps.concat_right (p1 := clearProg) hT10G2T03_steps hT10G2T03_halted
      have hstart_eq : (⟨0 + clearProg.length, cClear'.state⟩ : Config) = ⟨cClear'.pc, cClear'.state⟩ := by
        simp only [Nat.zero_add]
        ext
        · exact hClear_pc'.symm
        · rfl
      rw [hstart_eq] at hT10G2T03_steps'
      exact Relation.ReflTransGen.trans hClear_prefix hT10G2T03_steps'
    have hPhase2_explicit_halted' : (⟨((cT03'.pc + pG2.length) + T10.length) + clearProg.length, cT03'.state⟩ : Config).isHalted phase2 := by
      simp only [Config.isHalted, phase2, Program.concat_length, T10, T03, List.length_singleton] at hT03_halted' ⊢
      rw [hT03_pc']; omega

    have hPhase2_state_match' : cPhase2_final'.state = cT03'.state := by
      have hconfigs_eq := Steps.halts_unique hPhase2_steps_final' hPhase2_halted_final' hPhase2_explicit_steps' hPhase2_explicit_halted'
      rw [hconfigs_eq]

    rw [hPhase2_state_match', hT03'_m3]

  have hH_halts : Halts (phase1.concat (phase2.concat phase3)) (List.ofFn inputs) := by
    rw [(Program.concat_assoc phase1 phase2 phase3).symm]
    exact Halts.concat_continuation hPhase12_halts hPhase12_pc (hPhase3_halts_from cPhase12.state hPhase12_v1 hPhase12_v2)

  -- H = phase1.concat (phase2.concat phase3) by definition
  -- Show Program.composeBU pF pG1 pG2 = phase1.concat (phase2.concat phase3)
  have hH_eq : Program.composeBU pF pG1 pG2 = phase1.concat (phase2.concat phase3) := by
    simp only [Program.composeBU, Program.concat]
    rfl
  rw [hH_eq]
  exact hH_halts

set_option maxHeartbeats 800000 in
/-- Result correctness: the result of the composed program equals the composed function value.

This lemma extracts the result equality from the main composition theorem.
Takes programs and their specs as explicit parameters. -/
theorem comp_binary_unary_result
    {f : (Fin 2 → ℕ) → Part ℕ} {g1 g2 : (Fin 1 → ℕ) → Part ℕ}
    {pF pG1 pG2 : Program}
    (hF_sf : pF.IsStandardForm) (hG1_sf : pG1.IsStandardForm) (hG2_sf : pG2.IsStandardForm)
    (hF_spec : ∀ inputs : Fin 2 → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hH : Halts pF (List.ofFn inputs)) (hD : (f inputs).Dom),
        Result pF (List.ofFn inputs) hH = (f inputs).get hD)
    (hG1_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG1 (List.ofFn inputs) ↔ (g1 inputs).Dom) ∧
      ∀ (hH : Halts pG1 (List.ofFn inputs)) (hD : (g1 inputs).Dom),
        Result pG1 (List.ofFn inputs) hH = (g1 inputs).get hD)
    (hG2_spec : ∀ inputs : Fin 1 → ℕ,
      (Halts pG2 (List.ofFn inputs) ↔ (g2 inputs).Dom) ∧
      ∀ (hH : Halts pG2 (List.ofFn inputs)) (hD : (g2 inputs).Dom),
        Result pG2 (List.ofFn inputs) hH = (g2 inputs).get hD)
    (inputs : Fin 1 → ℕ)
    (hHalts : Halts (Program.composeBU pF pG1 pG2) (List.ofFn inputs))
    (hDom : ((Part.sequence (mkPair (g1 inputs) (g2 inputs))).bind f).Dom) :
    Result (Program.composeBU pF pG1 pG2) (List.ofFn inputs) hHalts =
    ((Part.sequence (mkPair (g1 inputs) (g2 inputs))).bind f).get hDom := by
  -- Define H for convenience
  let H := Program.composeBU pF pG1 pG2
  -- Step 1: Extract domain conditions from hDom
  rw [comp_function_dom] at hDom
  obtain ⟨hg1_dom, hg2_dom, hf_dom_raw⟩ := hDom

  -- Step 2: Get intermediate values
  have hG1_halts : Halts pG1 (List.ofFn inputs) := (hG1_spec inputs).1.mpr hg1_dom
  have hG2_halts : Halts pG2 (List.ofFn inputs) := (hG2_spec inputs).1.mpr hg2_dom
  let v1 := (g1 inputs).get hg1_dom
  let v2 := (g2 inputs).get hg2_dom

  -- Step 3: F halts on (v1, v2)
  let fInput : Fin 2 → ℕ := fun i => match i with
    | ⟨0, _⟩ => v1
    | ⟨1, _⟩ => v2
  have hf_dom : (f fInput).Dom := by
    convert hf_dom_raw hg1_dom hg2_dom using 2
  have hF_halts : Halts pF (List.ofFn fInput) := (hF_spec fInput).1.mpr hf_dom

  -- Step 4: Get result values from each program
  have hG1_result : Result pG1 (List.ofFn inputs) hG1_halts = v1 :=
    (hG1_spec inputs).2 hG1_halts hg1_dom
  have hG2_result : Result pG2 (List.ofFn inputs) hG2_halts = v2 :=
    (hG2_spec inputs).2 hG2_halts hg2_dom
  have hF_result : Result pF (List.ofFn fInput) hF_halts = (f fInput).get hf_dom :=
    (hF_spec fInput).2 hF_halts hf_dom

  -- Step 5: Simplify the bind expression using Part.Dom.bind
  have hSeqDom : (Part.sequence (mkPair (g1 inputs) (g2 inputs))).Dom := by
    rw [mkPair_dom]
    exact ⟨hg1_dom, hg2_dom⟩

  -- The sequence get equals fInput
  have hSeq_get_eq : (Part.sequence (mkPair (g1 inputs) (g2 inputs))).get hSeqDom = fInput := by
    funext i
    simp only [Part.sequence_get, mkPair]
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

  -- Use Part.Dom.bind to simplify the bind
  have hbind_simp : (Part.sequence (mkPair (g1 inputs) (g2 inputs))).bind f = f fInput := by
    rw [Part.Dom.bind hSeqDom, hSeq_get_eq]

  -- Now we need to show Result H = (f fInput).get hf_dom
  -- Convert the goal to use hbind_simp
  have hgoal_conv : ((Part.sequence (mkPair (g1 inputs) (g2 inputs))).bind f).get
      (comp_function_dom.mpr ⟨hg1_dom, hg2_dom, hf_dom_raw⟩) = (f fInput).get hf_dom := by
    simp only [hbind_simp]

  rw [hgoal_conv]

  -- Step 6: Now we need Result H inputs hHalts = (f fInput).get hf_dom
  -- This is ← hF_result, composed with showing H's final R[0] = F's final R[0]
  rw [← hF_result]

  -- Step 7: Build the execution trace for H to show Result H = Result pF
  -- The key insight is that H's final state has the same R[0] as pF's final state

  -- Get H's final config
  let cH := Classical.choose hHalts
  have hH_spec := Classical.choose_spec hHalts
  have hH_steps : Steps H (Config.init (List.ofFn inputs)) cH := hH_spec.1
  have hH_halted : cH.isHalted H := hH_spec.2

  -- Get pF's final config and its output
  let cF := Classical.choose hF_halts
  have hF_spec := Classical.choose_spec hF_halts
  have hF_steps : Steps pF (Config.init (List.ofFn fInput)) cF := hF_spec.1
  have hF_halted : cF.isHalted pF := hF_spec.2
  have hF_pc : cF.pc = pF.length := hF_sf.halts_at_length (List.ofFn fInput) cF hF_steps hF_halted

  -- H's final output equals pF's output: phase3 runs pF from state agreeing with [v1, v2]
  have hResult_eq : cH.state.output = cF.state.output := by
    -- Redefine the phase structure (not in scope from backward direction)
    set m := compositionBaseBU pF pG1 pG2 with hm_def
    let T01 : Program := [Instr.T 0 (m + 1)]
    let T02 : Program := [Instr.T 0 (m + 2)]
    let clearProg := Program.clearRegisters m
    let T10 : Program := [Instr.T (m + 1) 0]
    let T03 : Program := [Instr.T 0 (m + 3)]
    let Tsetup : Program := [Instr.T (m + 2) 0, Instr.T (m + 3) 1]

    let phase1 := T01.concat (pG1.concat T02)
    let phase2 := clearProg.concat (T10.concat (pG2.concat T03))
    let phase3 := clearProg.concat (Tsetup.concat pF)

    -- Standard form and straight-line properties
    have hT01_sl := single_transfer_isStraightLine 0 (m + 1)
    have hT02_sl := single_transfer_isStraightLine 0 (m + 2)
    have hT10_sl := single_transfer_isStraightLine (m + 1) 0
    have hT03_sl := single_transfer_isStraightLine 0 (m + 3)
    have hTsetup_sl := double_transfer_isStraightLine (m + 2) 0 (m + 3) 1
    have hClear_sl := clearRegisters_isStraightLine m

    have hPhase1_sf : phase1.IsStandardForm :=
      (straightLine_isStandardForm hT01_sl).concat
        (hG1_sf.concat (straightLine_isStandardForm hT02_sl))
    have hPhase2_sf : phase2.IsStandardForm :=
      (straightLine_isStandardForm hClear_sl).concat
        ((straightLine_isStandardForm hT10_sl).concat
          (hG2_sf.concat (straightLine_isStandardForm hT03_sl)))
    have hPhase3_sf : phase3.IsStandardForm :=
      (straightLine_isStandardForm hClear_sl).concat
        ((straightLine_isStandardForm hTsetup_sl).concat hF_sf)

    -- H = phase1.concat (phase2.concat phase3)
    have hH_eq : H = phase1.concat (phase2.concat phase3) := rfl

    -- We'll build the execution trace to show cH.state = some state with R[0] = cF.state.output
    -- The strategy: use Halts.from_agreeing_state to get pF's final config from the setup state

    -- Key register bounds
    have hm_ge_F : pF.maxRegister ≤ m := compositionBaseBU_ge_F pF pG1 pG2
    have hm_ge_G1 : pG1.maxRegister ≤ m := compositionBaseBU_ge_G1 pF pG1 pG2
    have hm_ge_G2 : pG2.maxRegister ≤ m := compositionBaseBU_ge_G2 pF pG1 pG2

    -- === APPROACH ===
    -- 1. Build the state sSetup that pF sees after phase1 + phase2 + clear + Tsetup
    -- 2. Show sSetup agrees with Config.init [v1, v2] on pF-relevant registers
    -- 3. Use Halts.from_agreeing_state to get pF execution and output from sSetup
    -- 4. Build cH_built using that pF execution
    -- 5. Build full execution trace to cH_built
    -- 6. Apply Steps.halts_unique to show cH = cH_built

    -- === SETUP STATE CONSTRUCTION ===
    -- After clear + Tsetup in phase3:
    -- - R[0] = v1 (transferred from R[m+2])
    -- - R[1] = v2 (transferred from R[m+3])
    -- - R[2..m] = 0 (cleared)
    -- - R[m+1] = x, R[m+2] = v1, R[m+3] = v2 (preserved above m)

    -- We need to show this agrees with Config.init [v1, v2] on registers ≤ pF.maxRegister

    -- Config.init [v1, v2] has:
    -- - R[0] = v1
    -- - R[1] = v2
    -- - R[r] = 0 for r ≥ 2
    -- Since pF.maxRegister ≤ m, and our setup has R[0]=v1, R[1]=v2, R[2..m]=0,
    -- the states agree on registers ≤ pF.maxRegister.

    -- Build state agreement lemma
    have hagree_pF : ∀ sSetup : State,
        (sSetup.read 0 = v1) →
        (sSetup.read 1 = v2) →
        (∀ r, 2 ≤ r → r ≤ m → sSetup.read r = 0) →
        (∀ r, r ≤ pF.maxRegister →
          sSetup.read r = (State.fromInputs [v1, v2]).read r) := by
      intro sSetup hr0 hr1 hzeros r hr
      by_cases h0 : r = 0
      · subst h0
        simp only [State.fromInputs, State.read, List.getD_cons_zero]
        exact hr0
      · by_cases h1 : r = 1
        · subst h1
          simp only [State.fromInputs, State.read, List.getD]
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
          exact hr1
        · -- r ≥ 2 and r ≤ pF.maxRegister ≤ m
          have hr_ge_2 : 2 ≤ r := by omega
          have hr_le_m : r ≤ m := Nat.le_trans hr hm_ge_F
          have hsSetup_zero := hzeros r hr_ge_2 hr_le_m
          -- Config.init [v1, v2] also has 0 at position r ≥ 2
          have hinit_zero : (State.fromInputs [v1, v2]).read r = 0 := by
            apply State.fromInputs_out_of_range
            simp only [List.length_cons, List.length_nil]
            omega
          rw [hsSetup_zero, hinit_zero]

    -- Use Halts.from_agreeing_state to get pF execution
    -- Given a state sSetup satisfying the conditions, pF produces the correct output
    have hPf_from_setup : ∀ sSetup : State,
        (sSetup.read 0 = v1) →
        (sSetup.read 1 = v2) →
        (∀ r, 2 ≤ r → r ≤ m → sSetup.read r = 0) →
        ∃ cPf', Steps pF ⟨0, sSetup⟩ cPf' ∧
                cPf'.isHalted pF ∧
                cPf'.state.output = cF.state.output := by
      intro sSetup hr0 hr1 hzeros
      have hagree := hagree_pF sSetup hr0 hr1 hzeros
      have hfInput_eq : List.ofFn fInput = [v1, v2] := by
        simp only [List.ofFn_succ, List.ofFn_zero, fInput]
        rfl
      have hF_halts' : Halts pF [v1, v2] := by
        rw [← hfInput_eq]; exact hF_halts
      obtain ⟨cPf', hsteps', hhalted', houtput'⟩ := Halts.from_agreeing_state hF_halts' hagree
      refine ⟨cPf', hsteps', hhalted', ?_⟩
      -- The output equality follows from uniqueness of halted configs
      -- Get the halted config for hF_halts' and show it equals cF
      let cF' := Classical.choose hF_halts'
      have hF'_spec := Classical.choose_spec hF_halts'
      have hF'_steps : Steps pF (Config.init [v1, v2]) cF' := hF'_spec.1
      have hF'_halted : cF'.isHalted pF := hF'_spec.2
      -- Show init configs are equal
      have hinit_eq : Config.init [v1, v2] = Config.init (List.ofFn fInput) := by
        rw [hfInput_eq]
      -- Transport hF_steps to start from [v1, v2]
      have hF_steps' : Steps pF (Config.init [v1, v2]) cF := by
        rw [hinit_eq]; exact hF_steps
      -- By uniqueness, cF' = cF
      have hcF_eq : cF' = cF := Steps.halts_unique hF'_steps hF'_halted hF_steps' hF_halted
      -- houtput' says cPf'.state.output = Result pF [v1, v2] hF_halts'
      -- Result pF [v1, v2] hF_halts' = cF'.state.output by definition
      -- So cPf'.state.output = cF'.state.output = cF.state.output
      rw [houtput']
      simp only [Result]
      -- Now goal is (Classical.choose hF_halts').state.output = cF.state.output
      -- which is cF'.state.output = cF.state.output
      show cF'.state.output = cF.state.output
      rw [hcF_eq]

    -- === BUILD EXECUTION TRACE ===
    -- We need to trace through all phases and build the expected final config

    -- Get input value (x)
    let x := inputs ⟨0, by omega⟩

    -- === PHASE 1 TRACE ===
    -- Phase 1: T01 ++ G1 ++ T02
    -- T01: R[m+1] := R[0] (save input)
    -- G1: compute, R[0] = v1
    -- T02: R[m+2] := R[0] (save v1)

    -- G1 halts from Config.init
    let cG1 := Classical.choose hG1_halts
    have hG1_spec' := Classical.choose_spec hG1_halts
    have hG1_steps : Steps pG1 (Config.init (List.ofFn inputs)) cG1 := hG1_spec'.1
    have hG1_halted : cG1.isHalted pG1 := hG1_spec'.2
    have hG1_pc : cG1.pc = pG1.length := hG1_sf.halts_at_length (List.ofFn inputs) cG1 hG1_steps hG1_halted

    -- G1's output is v1
    have hG1_output : cG1.state.output = v1 := hG1_result

    -- === PHASE 2 TRACE ===
    -- G2 halts from Config.init
    let cG2 := Classical.choose hG2_halts
    have hG2_spec' := Classical.choose_spec hG2_halts
    have hG2_steps : Steps pG2 (Config.init (List.ofFn inputs)) cG2 := hG2_spec'.1
    have hG2_halted : cG2.isHalted pG2 := hG2_spec'.2
    have hG2_pc : cG2.pc = pG2.length := hG2_sf.halts_at_length (List.ofFn inputs) cG2 hG2_steps hG2_halted

    -- G2's output is v2
    have hG2_output : cG2.state.output = v2 := hG2_result

    -- === FINAL STATE CONSTRUCTION ===
    -- The key insight: we need to show what state pF runs from in H.
    -- After phase1 + phase2 + (clear + Tsetup) of phase3:
    -- - R[0] = v1 (from R[m+2] via T(m+2, 0))
    -- - R[1] = v2 (from R[m+3] via T(m+3, 1))
    -- - R[2..m] = 0 (from clearRegisters)
    --
    -- This state satisfies the conditions for hPf_from_setup.

    -- Define the setup state explicitly
    -- sSetup = state after clear + Tsetup where:
    -- - registers 0..m are cleared, then
    -- - R[0] is set to v1 (from some source register holding v1)
    -- - R[1] is set to v2 (from some source register holding v2)

    -- For now, we define sSetup abstractly via the execution
    -- The key is that clearRegisters zeros R[0..m], then transfers set R[0]=v1, R[1]=v2

    -- === SIMPLIFIED APPROACH ===
    -- Rather than building the full trace explicitly, we use the structure:
    -- 1. H halts (given)
    -- 2. H's final phase is phase3 = clear ++ Tsetup ++ pF
    -- 3. After clear ++ Tsetup, pF runs from a state matching Config.init [v1, v2]
    -- 4. By hPf_from_setup, pF's output matches cF's output

    -- The full explicit trace would require building:
    -- - State after T01: s1 with R[m+1] = x
    -- - State after G1 from s1: s2 with R[0] = v1 (via register_independent)
    -- - State after T02: s3 with R[m+2] = v1
    -- - State after clear in phase2: s4 with R[0..m] = 0, R[m+1] = x, R[m+2] = v1
    -- - State after T10: s5 with R[0] = x
    -- - State after G2 from s5: s6 with R[0] = v2 (via register_independent)
    -- - State after T03: s7 with R[m+3] = v2
    -- - State after clear in phase3: s8 with R[0..m] = 0, R[m+2] = v1, R[m+3] = v2
    -- - State after Tsetup: sSetup with R[0] = v1, R[1] = v2, R[2..m] = 0

    -- This requires using:
    -- - single_transfer_halts for T instructions
    -- - straightLine_halts_from_state for clear
    -- - Halts.from_agreeing_state / register_independent for G1, G2
    -- - Tracking register values through each step

    -- For the current proof, we admit this trace construction and use the result
    -- The full implementation would follow the pattern above

    -- State conditions that must hold after phase1 + phase2 + (clear + Tsetup):
    have hsSetup_conditions : ∃ sSetup : State,
        sSetup.read 0 = v1 ∧
        sSetup.read 1 = v2 ∧
        (∀ r, 2 ≤ r → r ≤ m → sSetup.read r = 0) ∧
        -- And there's a trace from H's init through phase1+phase2+(clear+Tsetup) to ⟨setup_pc, sSetup⟩
        ∃ setup_pc : ℕ,
          setup_pc = phase1.length + phase2.length + clearProg.length + Tsetup.length ∧
          ∃ hsteps_to_setup : Steps H (Config.init (List.ofFn inputs)) ⟨setup_pc, sSetup⟩, True := by
      -- Construct sSetup by tracing through phases; after clear+Tsetup: R[0]=v1, R[1]=v2

      -- We construct sSetup explicitly:
      let sSetup : State := fun r =>
        if r = 0 then v1
        else if r = 1 then v2
        else if r ≤ m then 0
        else if r = m + 1 then x
        else if r = m + 2 then v1
        else if r = m + 3 then v2
        else 0

      have hr0 : sSetup.read 0 = v1 := by simp [sSetup, State.read]
      have hr1 : sSetup.read 1 = v2 := by simp [sSetup, State.read]
      have hzeros : ∀ r, 2 ≤ r → r ≤ m → sSetup.read r = 0 := by
        intro r hr2 hrm
        simp only [sSetup, State.read]
        simp only [if_neg (by omega : r ≠ 0), if_neg (by omega : r ≠ 1), if_pos hrm]

      refine ⟨sSetup, hr0, hr1, hzeros, ?_⟩

      -- Now we need to build the trace to sSetup
      -- We'll build it step by step through each phase

      -- === T INSTRUCTION EXECUTIONS ===

      -- Initial state
      let s0 := (Config.init (List.ofFn inputs)).state

      -- T01: copies R[0] to R[m+1]
      have hT01_exec := single_transfer_halts 0 (m + 1) s0
      obtain ⟨cT01, hT01_steps, hT01_halted, hT01_pc, hT01_state⟩ := hT01_exec
      -- After T01: state is s0.write (m+1) (s0.read 0) = s0.write (m+1) x
      have hT01_state_r0 : cT01.state.read 0 = s0.read 0 := by
        rw [hT01_state]
        exact State.write_read_diff s0 0 (m + 1) (s0.read 0) (by omega)
      have hT01_state_saved : cT01.state.read (m + 1) = s0.read 0 := by
        rw [hT01_state]; exact State.write_read_same s0 (m + 1) (s0.read 0)

      -- After G1 runs (we'll need G1's halting for this - skip for now and focus on T instructions)

      -- T02: copies R[0] to R[m+2] (after G1, R[0] = v1)
      -- We'll parameterize by the state after G1
      have hT02_exec : ∀ s : State,
          ∃ c, Steps T02 ⟨0, s⟩ c ∧ c.isHalted T02 ∧ c.pc = 1 ∧
               c.state = s.write (m + 2) (s.read 0) := by
        intro s
        exact single_transfer_halts 0 (m + 2) s

      -- T10: copies R[m+1] to R[0] (restores input)
      have hT10_exec : ∀ s : State,
          ∃ c, Steps T10 ⟨0, s⟩ c ∧ c.isHalted T10 ∧ c.pc = 1 ∧
               c.state = s.write 0 (s.read (m + 1)) := by
        intro s
        exact single_transfer_halts (m + 1) 0 s

      -- T03: copies R[0] to R[m+3] (after G2, R[0] = v2)
      have hT03_exec : ∀ s : State,
          ∃ c, Steps T03 ⟨0, s⟩ c ∧ c.isHalted T03 ∧ c.pc = 1 ∧
               c.state = s.write (m + 3) (s.read 0) := by
        intro s
        exact single_transfer_halts 0 (m + 3) s

      -- Tsetup: two transfers [T (m+2) 0, T (m+3) 1]
      -- First transfer: R[0] := R[m+2]
      -- Second transfer: R[1] := R[m+3]
      have hTsetup_exec : ∀ s : State,
          ∃ c, Steps Tsetup ⟨0, s⟩ c ∧ c.isHalted Tsetup ∧ c.pc = 2 ∧
               c.state = (s.write 0 (s.read (m + 2))).write 1 (s.read (m + 3)) := by
        intro s
        -- First transfer
        have h1 := single_transfer_step (m + 2) 0 s
        let s1 := s.write 0 (s.read (m + 2))
        -- Second transfer
        have h2 := single_transfer_step (m + 3) 1 s1
        -- The second step needs adjustment for Tsetup context
        have h2' : Step Tsetup ⟨1, s1⟩ ⟨2, s1.write 1 (s1.read (m + 3))⟩ := by
          apply Step.trans
          simp [Program.getInstr, Tsetup]
        -- Combine steps
        have hsteps : Steps Tsetup ⟨0, s⟩ ⟨2, s1.write 1 (s1.read (m + 3))⟩ := by
          have h1' : Step Tsetup ⟨0, s⟩ ⟨1, s1⟩ := by
            apply Step.trans
            simp [Program.getInstr, Tsetup]
          exact Relation.ReflTransGen.head h1' (Relation.ReflTransGen.single h2')
        have hhalted : (⟨2, s1.write 1 (s1.read (m + 3))⟩ : Config).isHalted Tsetup := by
          simp [Config.isHalted, Tsetup]
        -- Simplify s1.read (m + 3) = s.read (m + 3) since we only wrote to position 0
        have hs1_read : s1.read (m + 3) = s.read (m + 3) := by
          simp only [s1, State.write_read_diff _ _ _ _ (by omega : m + 3 ≠ 0)]
        refine ⟨⟨2, s1.write 1 (s1.read (m + 3))⟩, hsteps, hhalted, rfl, ?_⟩
        rw [hs1_read]

      -- === CLEAR PROGRAM EXECUTIONS ===
      -- clearProg halts from any state
      have hClear_exec : ∀ s : State,
          ∃ c, Steps clearProg ⟨0, s⟩ c ∧ c.isHalted clearProg ∧
               c.pc = clearProg.length ∧
               (∀ r, r ≤ m → c.state.read r = 0) ∧
               (∀ r, m < r → c.state.read r = s.read r) := by
        intro s
        have hClear_halts := straightLine_halts_from_state hClear_sl s
        obtain ⟨c, hsteps, hhalted, hpc⟩ := hClear_halts
        have hstate_eq := straightLineFinalState_eq_of_halted hClear_sl s c hsteps hhalted
        refine ⟨c, hsteps, hhalted, hpc, ?_, ?_⟩
        · intro r hr; rw [hstate_eq]; exact clearRegisters_zeros m s r hr
        · intro r hr; rw [hstate_eq]; exact clearRegisters_preserves_above m s r hr

      -- === REMAINING TRACE CONSTRUCTION ===
      -- Build the full trace: T01 → G1 → T02 → clearProg → T10 → G2 → T03 → clearProg → Tsetup

      -- PHASE 1: T01 → G1 → T02

      -- G1 from agreeing state (cT01.state agrees with init on R[0..maxRegister])
      have hagreeG1 : cT01.state.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG1.maxRegister := by
        intro r _ hhi
        rw [hT01_state]
        have hr_ne : r ≠ m + 1 := by omega
        exact State.write_read_diff s0 r (m + 1) (s0.read 0) hr_ne

      let eG1 := Halts.executeFromAgreeingState hG1_halts hG1_sf hagreeG1
      let cG1' := eG1.config
      have hG1_steps' := eG1.steps
      have hG1_halted' := eG1.halted
      have hG1_pc' := eG1.pc_eq

      -- cG1'.state.read 0 = v1
      have hcG1'_r0 : cG1'.state.read 0 = v1 := by
        have h0_le : 0 ≤ pG1.maxRegister := Nat.zero_le _
        have hagree_at_0 := State.agreeOn_read eG1.state_agrees (Nat.zero_le 0) h0_le
        rw [hagree_at_0]
        have hres : (Classical.choose eG1.originalHalts).state.read 0 = Result pG1 (List.ofFn inputs) hG1_halts := by
          simp only [Result, State.output, State.read]
        rw [hres]
        exact (hG1_spec inputs).2 hG1_halts hg1_dom

      -- cG1'.state.read (m+1) = x (preserved from T01)
      have hcG1'_m1 : cG1'.state.read (m + 1) = x := by
        have hm1_gt : pG1.maxRegister < m + 1 := by omega
        have hpreserved := eG1.preserves_high_register (m + 1) hm1_gt
        rw [hpreserved, hT01_state]
        exact State.write_read_same s0 (m + 1) (s0.read 0)

      -- T02 execution from cG1'.state
      obtain ⟨cT02, hT02_steps, hT02_halted, hT02_pc, hT02_state⟩ := hT02_exec cG1'.state

      -- After T02: R[m+2] = v1, R[m+1] = x
      have hcT02_m2 : cT02.state.read (m + 2) = v1 := by
        rw [hT02_state, State.write_read_same, hcG1'_r0]
      have hcT02_m1 : cT02.state.read (m + 1) = x := by
        rw [hT02_state]
        have h_ne : m + 1 ≠ m + 2 := by omega
        rw [State.write_read_diff cG1'.state (m + 1) (m + 2) _ h_ne, hcG1'_m1]

      -- Build phase1 execution: T01 → G1 → T02
      -- First: T01.concat (pG1.concat T02) from init to final
      have hG1T02_steps : Steps (pG1.concat T02) ⟨0, cT01.state⟩ ⟨cT02.pc + pG1.length, cT02.state⟩ := by
        have hG1_steps_prefix := Steps.concat_left_prefix (p2 := T02) hG1_steps' hG1_halted'
        have hT02_steps' := Steps.concat_right (p1 := pG1) hT02_steps hT02_halted
        have hstart_eq : (⟨0 + pG1.length, cG1'.state⟩ : Config) = ⟨cG1'.pc, cG1'.state⟩ := by
          simp only [Nat.zero_add]; ext; exact hG1_pc'.symm; rfl
        rw [hstart_eq] at hT02_steps'
        exact Relation.ReflTransGen.trans hG1_steps_prefix hT02_steps'

      have hG1T02_halted : (⟨cT02.pc + pG1.length, cT02.state⟩ : Config).isHalted (pG1.concat T02) := by
        simp only [Config.isHalted, Program.concat_length, T02, List.length_singleton]
        rw [hT02_pc]; omega

      have hT01_steps_in_phase1 := Steps.concat_left_prefix (p2 := pG1.concat T02) hT01_steps hT01_halted

      have hG1T02_steps_in_phase1 := Steps.concat_right (p1 := T01) hG1T02_steps hG1T02_halted

      have hstart_eq1 : (⟨0 + T01.length, cT01.state⟩ : Config) = ⟨cT01.pc, cT01.state⟩ := by
        simp only [Nat.zero_add, T01, List.length_singleton]; ext; exact hT01_pc.symm; rfl
      rw [hstart_eq1] at hG1T02_steps_in_phase1

      have hPhase1_steps : Steps phase1 (Config.init (List.ofFn inputs))
          ⟨(cT02.pc + pG1.length) + T01.length, cT02.state⟩ :=
        Relation.ReflTransGen.trans hT01_steps_in_phase1 hG1T02_steps_in_phase1

      have hPhase1_halted : (⟨(cT02.pc + pG1.length) + T01.length, cT02.state⟩ : Config).isHalted phase1 := by
        simp only [Config.isHalted, phase1, Program.concat_length, T01, T02, List.length_singleton]
        rw [hT02_pc]; omega

      -- Simplify phase1 PC
      have hPhase1_pc_eq : (cT02.pc + pG1.length) + T01.length = phase1.length := by
        simp only [phase1, Program.concat_length, T01, T02, List.length_singleton]
        rw [hT02_pc]; omega

      -- PHASE 2: clearProg → T10 → G2 → T03

      -- Execute clearProg from cT02.state
      obtain ⟨cClear1, hClear1_steps, hClear1_halted, hClear1_pc, hClear1_zeros, hClear1_preserves⟩ :=
        hClear_exec cT02.state

      -- After clear: R[0..m] = 0, R[m+1] = x, R[m+2] = v1
      have hClear1_m1 : cClear1.state.read (m + 1) = x := by
        rw [hClear1_preserves (m + 1) (by omega), hcT02_m1]
      have hClear1_m2 : cClear1.state.read (m + 2) = v1 := by
        rw [hClear1_preserves (m + 2) (by omega), hcT02_m2]

      -- T10: restore input to R[0]
      obtain ⟨cT10, hT10_steps, hT10_halted, hT10_pc, hT10_state⟩ := hT10_exec cClear1.state

      -- After T10: R[0] = x
      have hcT10_r0 : cT10.state.read 0 = x := by
        rw [hT10_state, State.write_read_same, hClear1_m1]

      -- After T10: R[m+1] = x, R[m+2] = v1 (preserved)
      have hcT10_m1 : cT10.state.read (m + 1) = x := by
        rw [hT10_state]
        rw [State.write_read_diff cClear1.state (m + 1) 0 _ (by omega), hClear1_m1]
      have hcT10_m2 : cT10.state.read (m + 2) = v1 := by
        rw [hT10_state]
        rw [State.write_read_diff cClear1.state (m + 2) 0 _ (by omega), hClear1_m2]

      -- G2 from agreeing state (cT10.state agrees with init on R[0..maxRegister])
      have hagreeG2 : cT10.state.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG2.maxRegister := by
        intro r _ hhi
        by_cases hr0 : r = 0
        · rw [hr0, hcT10_r0]
          simp only [State.fromInputs, State.read, x, List.ofFn, List.getD]
          rfl
        · rw [hT10_state, State.write_read_diff cClear1.state r 0 _ hr0]
          have hr_le_m : r ≤ m := by omega
          rw [hClear1_zeros r hr_le_m]
          simp only [State.fromInputs, State.read]
          have hr_ge : r ≥ (List.ofFn inputs).length := by simp only [List.length_ofFn]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr_ge, Option.getD_none]

      let eG2 := Halts.executeFromAgreeingState hG2_halts hG2_sf hagreeG2
      let cG2' := eG2.config
      have hG2_steps' := eG2.steps
      have hG2_halted' := eG2.halted
      have hG2_pc' := eG2.pc_eq

      -- cG2'.state.read 0 = v2
      have hcG2'_r0 : cG2'.state.read 0 = v2 := by
        have h0_le : 0 ≤ pG2.maxRegister := Nat.zero_le _
        have hagree_at_0 := State.agreeOn_read eG2.state_agrees (Nat.zero_le 0) h0_le
        rw [hagree_at_0]
        have hres : (Classical.choose eG2.originalHalts).state.read 0 = Result pG2 (List.ofFn inputs) hG2_halts := by
          simp only [Result, State.output, State.read]
        rw [hres]
        exact (hG2_spec inputs).2 hG2_halts hg2_dom

      -- Preserved values after G2
      have hcG2'_m1 : cG2'.state.read (m + 1) = x := by
        have hm1_gt : pG2.maxRegister < m + 1 := by omega
        rw [eG2.preserves_high_register (m + 1) hm1_gt, hcT10_m1]
      have hcG2'_m2 : cG2'.state.read (m + 2) = v1 := by
        have hm2_gt : pG2.maxRegister < m + 2 := by omega
        rw [eG2.preserves_high_register (m + 2) hm2_gt, hcT10_m2]

      -- T03 execution
      obtain ⟨cT03, hT03_steps, hT03_halted, hT03_pc, hT03_state⟩ := hT03_exec cG2'.state

      -- After T03: R[m+3] = v2, R[m+1] = x, R[m+2] = v1
      have hcT03_m3 : cT03.state.read (m + 3) = v2 := by
        rw [hT03_state, State.write_read_same, hcG2'_r0]
      have hcT03_m1 : cT03.state.read (m + 1) = x := by
        rw [hT03_state, State.write_read_diff cG2'.state (m + 1) (m + 3) _ (by omega), hcG2'_m1]
      have hcT03_m2 : cT03.state.read (m + 2) = v1 := by
        rw [hT03_state, State.write_read_diff cG2'.state (m + 2) (m + 3) _ (by omega), hcG2'_m2]

      -- Build phase2 trace: clearProg → T10 → G2 → T03
      have hT10G2T03_steps : Steps (T10.concat (pG2.concat T03)) ⟨0, cClear1.state⟩
          ⟨(cT03.pc + pG2.length) + T10.length, cT03.state⟩ := by
        -- T10
        have hT10_prefix := Steps.concat_left_prefix (p2 := pG2.concat T03) hT10_steps hT10_halted
        -- G2 → T03
        have hG2T03_steps : Steps (pG2.concat T03) ⟨0, cT10.state⟩ ⟨cT03.pc + pG2.length, cT03.state⟩ := by
          have hG2_prefix := Steps.concat_left_prefix (p2 := T03) hG2_steps' hG2_halted'
          have hT03_lifted := Steps.concat_right (p1 := pG2) hT03_steps hT03_halted
          have hstart : (⟨0 + pG2.length, cG2'.state⟩ : Config) = ⟨cG2'.pc, cG2'.state⟩ := by
            simp only [Nat.zero_add]; ext; exact hG2_pc'.symm; rfl
          rw [hstart] at hT03_lifted
          exact Relation.ReflTransGen.trans hG2_prefix hT03_lifted
        have hG2T03_halted : (⟨cT03.pc + pG2.length, cT03.state⟩ : Config).isHalted (pG2.concat T03) := by
          simp only [Config.isHalted, Program.concat_length, T03, List.length_singleton]
          rw [hT03_pc]; omega
        have hG2T03_lifted := Steps.concat_right (p1 := T10) hG2T03_steps hG2T03_halted
        have hstart2 : (⟨0 + T10.length, cT10.state⟩ : Config) = ⟨cT10.pc, cT10.state⟩ := by
          simp only [Nat.zero_add, T10, List.length_singleton]; ext; exact hT10_pc.symm; rfl
        rw [hstart2] at hG2T03_lifted
        exact Relation.ReflTransGen.trans hT10_prefix hG2T03_lifted

      have hT10G2T03_halted : (⟨(cT03.pc + pG2.length) + T10.length, cT03.state⟩ : Config).isHalted
          (T10.concat (pG2.concat T03)) := by
        simp only [Config.isHalted, Program.concat_length, T10, T03, List.length_singleton]
        rw [hT03_pc]; omega

      -- clearProg prefix then T10G2T03
      have hClear1_prefix := Steps.concat_left_prefix (p2 := T10.concat (pG2.concat T03))
          hClear1_steps hClear1_halted
      have hT10G2T03_lifted := Steps.concat_right (p1 := clearProg) hT10G2T03_steps hT10G2T03_halted
      have hstart3 : (⟨0 + clearProg.length, cClear1.state⟩ : Config) = ⟨cClear1.pc, cClear1.state⟩ := by
        simp only [Nat.zero_add]; ext; exact hClear1_pc.symm; rfl
      rw [hstart3] at hT10G2T03_lifted

      have hPhase2_steps : Steps phase2 ⟨0, cT02.state⟩
          ⟨((cT03.pc + pG2.length) + T10.length) + clearProg.length, cT03.state⟩ :=
        Relation.ReflTransGen.trans hClear1_prefix hT10G2T03_lifted

      have hPhase2_halted : (⟨((cT03.pc + pG2.length) + T10.length) + clearProg.length, cT03.state⟩ : Config).isHalted phase2 := by
        simp only [Config.isHalted, phase2, Program.concat_length, T10, T03, List.length_singleton]
        rw [hT03_pc]; omega

      have hPhase2_pc_eq : ((cT03.pc + pG2.length) + T10.length) + clearProg.length = phase2.length := by
        simp only [phase2, Program.concat_length, T10, T03, List.length_singleton]
        rw [hT03_pc]; omega

      -- PHASE 3 PREFIX: clearProg → Tsetup

      -- Execute clearProg from cT03.state
      obtain ⟨cClear2, hClear2_steps, hClear2_halted, hClear2_pc, hClear2_zeros, hClear2_preserves⟩ :=
        hClear_exec cT03.state

      -- After clear: R[0..m] = 0, R[m+1] = x, R[m+2] = v1, R[m+3] = v2
      have hClear2_m1 : cClear2.state.read (m + 1) = x := by
        rw [hClear2_preserves (m + 1) (by omega), hcT03_m1]
      have hClear2_m2 : cClear2.state.read (m + 2) = v1 := by
        rw [hClear2_preserves (m + 2) (by omega), hcT03_m2]
      have hClear2_m3 : cClear2.state.read (m + 3) = v2 := by
        rw [hClear2_preserves (m + 3) (by omega), hcT03_m3]

      -- Tsetup execution
      obtain ⟨cTsetup, hTsetup_steps, hTsetup_halted, hTsetup_pc, hTsetup_state⟩ :=
        hTsetup_exec cClear2.state

      -- After Tsetup: R[0] = v1, R[1] = v2
      have hcTsetup_r0 : cTsetup.state.read 0 = v1 := by
        rw [hTsetup_state, State.write_read_diff _ 0 1 _ (by omega), State.write_read_same, hClear2_m2]
      have hcTsetup_r1 : cTsetup.state.read 1 = v2 := by
        rw [hTsetup_state, State.write_read_same, hClear2_m3]

      -- After Tsetup: R[2..m] = 0 (from clear, preserved by Tsetup)
      have hcTsetup_zeros : ∀ r, 2 ≤ r → r ≤ m → cTsetup.state.read r = 0 := by
        intro r hr2 hrm
        rw [hTsetup_state]
        rw [State.write_read_diff _ r 1 _ (by omega)]
        rw [State.write_read_diff _ r 0 _ (by omega)]
        exact hClear2_zeros r hrm

      -- m ≥ 1 follows from the definition of compositionBaseBU which uses max 1 (...)
      -- This ensures R[m+1] ≠ R[1], avoiding collision with binary input register
      have hm_ge_1 : 1 ≤ m := compositionBaseBU_ge_1 pF pG1 pG2

      -- After Tsetup: R[m+1] = x, R[m+2] = v1, R[m+3] = v2 (preserved)
      have hcTsetup_m1 : cTsetup.state.read (m + 1) = x := by
        rw [hTsetup_state]
        rw [State.write_read_diff _ (m + 1) 1 _ (by omega)]
        rw [State.write_read_diff _ (m + 1) 0 _ (by omega)]
        exact hClear2_m1
      have hcTsetup_m2 : cTsetup.state.read (m + 2) = v1 := by
        rw [hTsetup_state]
        rw [State.write_read_diff _ (m + 2) 1 _ (by omega)]
        rw [State.write_read_diff _ (m + 2) 0 _ (by omega)]
        exact hClear2_m2
      have hcTsetup_m3 : cTsetup.state.read (m + 3) = v2 := by
        rw [hTsetup_state]
        rw [State.write_read_diff _ (m + 3) 1 _ (by omega)]
        rw [State.write_read_diff _ (m + 3) 0 _ (by omega)]
        exact hClear2_m3

      -- Build phase3 prefix: clearProg → Tsetup
      have hClearTsetup_steps : Steps (clearProg.concat (Tsetup.concat pF)) ⟨0, cT03.state⟩
          ⟨clearProg.length + Tsetup.length, cTsetup.state⟩ := by
        -- First build execution in clearProg.concat Tsetup
        -- Lift Tsetup to clearProg.concat Tsetup
        have hTsetup_lifted := Steps.concat_right (p1 := clearProg) hTsetup_steps hTsetup_halted
        have hstart4 : (⟨0 + clearProg.length, cClear2.state⟩ : Config) = ⟨cClear2.pc, cClear2.state⟩ := by
          simp only [Nat.zero_add]; ext; exact hClear2_pc.symm; rfl
        rw [hstart4] at hTsetup_lifted
        -- Lift clearProg to clearProg.concat Tsetup
        have hClear2_prefix_CT : Steps (clearProg.concat Tsetup) ⟨0, cT03.state⟩ ⟨cClear2.pc, cClear2.state⟩ :=
          Steps.concat_left_prefix hClear2_steps hClear2_halted
        -- Chain them in clearProg.concat Tsetup
        have hCT_steps := Relation.ReflTransGen.trans hClear2_prefix_CT hTsetup_lifted
        -- Convert pc: cTsetup.pc + clearProg.length = clearProg.length + Tsetup.length
        have hpc_eq : cTsetup.pc + clearProg.length = clearProg.length + Tsetup.length := by
          simp only [Tsetup, List.length_cons, List.length_nil]
          rw [hTsetup_pc]; omega
        -- Show halted in clearProg.concat Tsetup
        have hCT_halted : (⟨clearProg.length + Tsetup.length, cTsetup.state⟩ : Config).isHalted (clearProg.concat Tsetup) := by
          simp only [Config.isHalted, Program.concat_length, Tsetup, List.length_cons, List.length_nil]
          omega
        -- Now lift to phase3 = (clearProg.concat Tsetup).concat pF (using associativity)
        have hassoc : clearProg.concat (Tsetup.concat pF) = (clearProg.concat Tsetup).concat pF :=
          (Program.concat_assoc clearProg Tsetup pF).symm
        rw [hassoc]
        have hCT_steps' : Steps (clearProg.concat Tsetup) ⟨0, cT03.state⟩
            ⟨clearProg.length + Tsetup.length, cTsetup.state⟩ := by
          convert hCT_steps using 2; exact hpc_eq.symm
        exact Steps.concat_left_prefix hCT_steps' hCT_halted

      -- CHAIN ALL PHASES TOGETHER IN H
      -- We'll build the complete execution by embedding each phase's execution in H

      -- Phase 1 lifted to H (halts at phase1.length)
      have hPhase1_in_H := Steps.concat_left_prefix (p2 := phase2.concat phase3) hPhase1_steps hPhase1_halted

      -- For the rest of the proof, we need a "concat_interior" style lemma.
      -- Since Steps.concat_right requires halting in the inner program, and our
      -- intermediate segments don't halt in phase2.concat phase3, we use a different
      -- approach: build the combined phase2+phase3_prefix execution in one piece.

      -- Build phase2 followed by phase3_prefix as one execution in phase2.concat phase3
      have hPhase2_steps' : Steps phase2 ⟨0, cT02.state⟩ ⟨phase2.length, cT03.state⟩ := by
        convert hPhase2_steps using 2; exact hPhase2_pc_eq.symm
      have hPhase2_halted' : (⟨phase2.length, cT03.state⟩ : Config).isHalted phase2 := by
        simp only [Config.isHalted]; omega

      -- Phase2 embedded in phase2.concat phase3 (same configs, just different program context)
      have hPhase2_in_23 : Steps (phase2.concat phase3) ⟨0, cT02.state⟩ ⟨phase2.length, cT03.state⟩ :=
        Steps.concat_left_prefix hPhase2_steps' hPhase2_halted'

      -- Phase3 prefix: clearProg then Tsetup, halts within (clearProg.concat Tsetup)
      have hCT_halted_in_CT : (⟨clearProg.length + Tsetup.length, cTsetup.state⟩ : Config).isHalted
          (clearProg.concat Tsetup) := by
        simp only [Config.isHalted, Program.concat_length, Tsetup, List.length_cons, List.length_nil]
        omega

      -- hClearTsetup_steps is in phase3 = clearProg.concat (Tsetup.concat pF)
      -- We need steps in clearProg.concat Tsetup first
      have hCT_steps_in_CT : Steps (clearProg.concat Tsetup) ⟨0, cT03.state⟩
          ⟨clearProg.length + Tsetup.length, cTsetup.state⟩ := by
        -- Chain clearProg then Tsetup
        have hClear2_in_CT := Steps.concat_left_prefix (p2 := Tsetup) hClear2_steps hClear2_halted
        have hTsetup_in_CT := Steps.concat_right (p1 := clearProg) hTsetup_steps hTsetup_halted
        have hTsetup_start : (⟨0 + clearProg.length, cClear2.state⟩ : Config) =
            ⟨cClear2.pc, cClear2.state⟩ := by simp only [Nat.zero_add]; ext; exact hClear2_pc.symm; rfl
        rw [hTsetup_start] at hTsetup_in_CT
        have hsteps := Relation.ReflTransGen.trans hClear2_in_CT hTsetup_in_CT
        convert hsteps using 2
        simp only [Tsetup, List.length_cons, List.length_nil]; rw [hTsetup_pc]; omega

      -- Lift clearProg.concat Tsetup execution to phase2.concat phase3
      -- Using concat_right with p1 = phase2, p2 = phase3 = clearProg.concat (Tsetup.concat pF)
      -- But we only have execution in clearProg.concat Tsetup, not phase3
      -- So we first embed clearProg.concat Tsetup in phase3 via concat_left_prefix
      have hCT_in_phase3 : Steps phase3 ⟨0, cT03.state⟩
          ⟨clearProg.length + Tsetup.length, cTsetup.state⟩ := by
        have hassoc : phase3 = (clearProg.concat Tsetup).concat pF := by
          simp only [phase3]; exact (Program.concat_assoc clearProg Tsetup pF).symm
        rw [hassoc]
        exact Steps.concat_left_prefix hCT_steps_in_CT hCT_halted_in_CT

      -- Now lift to phase2.concat phase3 using concat_right
      -- Need: execution in phase3 that halts in phase3
      -- Issue: clearProg.length + Tsetup.length is NOT halted in phase3 (doesn't include pF)
      -- So we can't directly use concat_right here.

      -- Alternative: Build the complete execution to setup_pc directly
      -- Phase 1 gets us to phase1.length with cT02.state
      -- Then we need to show execution continues in H

      -- For now, use the combined phase2+phase3_prefix steps we built
      -- The execution in phase2.concat phase3 goes:
      -- - Phase2: 0 → phase2.length (embedded from phase2)
      -- - Phase3_prefix: phase2.length → phase2.length + clearProg.length + Tsetup.length

      -- Chain phase2 and phase3_prefix in phase2.concat phase3
      -- Use concat_right_interior which doesn't require halting at the intermediate point
      have hPhase3_in_23 : Steps (phase2.concat phase3) ⟨phase2.length, cT03.state⟩
          ⟨phase2.length + clearProg.length + Tsetup.length, cTsetup.state⟩ := by
        have hlifted := Steps.concat_right_interior (p1 := phase2) hCT_in_phase3
        simp only [Nat.zero_add] at hlifted
        convert hlifted using 2; omega

      -- Chain phase2 and phase3_prefix
      have hPhase23_steps : Steps (phase2.concat phase3) ⟨0, cT02.state⟩
          ⟨phase2.length + clearProg.length + Tsetup.length, cTsetup.state⟩ :=
        Relation.ReflTransGen.trans hPhase2_in_23 hPhase3_in_23

      -- Lift the combined phase2+phase3_prefix to H
      -- Use concat_right_interior which doesn't require halting
      have hPhase23_in_H := Steps.concat_right_interior (p1 := phase1) hPhase23_steps
      have hstart5 : (⟨0 + phase1.length, cT02.state⟩ : Config) = ⟨phase1.length, cT02.state⟩ := by
        simp only [Nat.zero_add]
      rw [hstart5] at hPhase23_in_H

      -- Align configs for chaining
      have hstart6 : (⟨phase1.length, cT02.state⟩ : Config) =
          ⟨(cT02.pc + pG1.length) + T01.length, cT02.state⟩ := by
        ext; exact hPhase1_pc_eq.symm; rfl
      rw [hstart6] at hPhase23_in_H

      have hPhase123_steps : Steps H (Config.init (List.ofFn inputs))
          ⟨clearProg.length + Tsetup.length + phase2.length + phase1.length, cTsetup.state⟩ := by
        have hsteps := Relation.ReflTransGen.trans hPhase1_in_H hPhase23_in_H
        convert hsteps using 2
        simp only; omega

      -- Show cTsetup.state = sSetup
      have hstate_eq : cTsetup.state = sSetup := by
        funext r
        simp only [sSetup]
        by_cases hr0 : r = 0
        · simp only [hr0, ↓reduceIte]; exact hcTsetup_r0
        · simp only [hr0, ↓reduceIte]
          by_cases hr1 : r = 1
          · simp only [hr1, ↓reduceIte]; exact hcTsetup_r1
          · simp only [hr1, ↓reduceIte]
            by_cases hrm : r ≤ m
            · simp only [hrm, ↓reduceIte]
              have hr2 : 2 ≤ r := by omega
              exact hcTsetup_zeros r hr2 hrm
            · simp only [hrm, ↓reduceIte]
              by_cases hrm1 : r = m + 1
              · simp only [hrm1, ↓reduceIte]; exact hcTsetup_m1
              · simp only [hrm1, ↓reduceIte]
                by_cases hrm2 : r = m + 2
                · simp only [hrm2, ↓reduceIte]; exact hcTsetup_m2
                · simp only [hrm2, ↓reduceIte]
                  by_cases hrm3 : r = m + 3
                  · simp only [hrm3, ↓reduceIte]; exact hcTsetup_m3
                  · simp only [hrm3, ↓reduceIte]
                    -- r > m + 3, so it was 0 initially and preserved
                    rw [hTsetup_state]
                    show ((cClear2.state.write 0 (cClear2.state.read (m + 2))).write 1
                          (cClear2.state.read (m + 3))).read r = 0
                    rw [State.write_read_diff _ r 1 _ (by omega)]
                    rw [State.write_read_diff _ r 0 _ hr0]
                    rw [hClear2_preserves r (by omega)]
                    rw [hT03_state]
                    rw [State.write_read_diff _ r (m + 3) _ hrm3]
                    -- Continue through G2...
                    have hr_gt_G2 : pG2.maxRegister < r := by omega
                    rw [eG2.preserves_high_register r hr_gt_G2]
                    rw [hT10_state]
                    rw [State.write_read_diff _ r 0 _ hr0]
                    rw [hClear1_preserves r (by omega)]
                    rw [hT02_state]
                    rw [State.write_read_diff _ r (m + 2) _ hrm2]
                    -- Continue through G1...
                    have hr_gt_G1 : pG1.maxRegister < r := by omega
                    rw [eG1.preserves_high_register r hr_gt_G1]
                    rw [hT01_state]
                    rw [State.write_read_diff _ r (m + 1) _ hrm1]
                    -- Finally, initial state has 0 for all r > 0
                    -- since inputs is Fin 1 → ℕ, the input list has length 1
                    -- and r > m + 3 ≥ 1, so r is out of bounds
                    simp only [s0, Config.init, State.fromInputs, State.read]
                    have hr_ge_1 : r ≥ 1 := by omega
                    have hlen : (List.ofFn inputs).length = 1 := by simp
                    have hr_out : r ≥ (List.ofFn inputs).length := by simp; omega
                    rw [List.getD_eq_getElem?_getD]
                    simp only [List.getElem?_eq_none hr_out, Option.getD_none]

      -- Final answer
      refine ⟨phase1.length + phase2.length + clearProg.length + Tsetup.length, rfl, ?_⟩
      rw [← hstate_eq]
      refine ⟨?_, trivial⟩
      convert hPhase123_steps using 2
      omega

    obtain ⟨sSetup, hr0, hr1, hzeros, setup_pc, hpc_eq, hsteps_to_setup, _⟩ := hsSetup_conditions

    -- Apply hPf_from_setup to get pF's execution and output
    obtain ⟨cPf', hPf_steps, hPf_halted, hPf_output⟩ := hPf_from_setup sSetup hr0 hr1 hzeros

    -- Build the expected final config
    let cH_built : Config := ⟨cPf'.pc + setup_pc, cPf'.state⟩

    -- Show cH_built is halted in H
    have hH_built_halted : cH_built.isHalted H := by
      simp only [Config.isHalted, cH_built, hH_eq]
      simp only [Program.concat_length]
      simp only [Config.isHalted] at hPf_halted
      simp only [hpc_eq, phase3]
      simp only [Program.concat_length] at hPf_halted ⊢
      omega

    -- Build steps from setup to cH_built
    have hPf_steps_in_H : Steps H ⟨setup_pc, sSetup⟩ cH_built := by
      -- pF execution lifted to H at offset setup_pc
      -- setup_pc = phase1.length + phase2.length + clearProg.length + Tsetup.length
      -- pF starts at setup_pc in H (after all the setup)

      -- Step 1: Lift pF to Tsetup.concat pF
      have h1 := Steps.concat_right (p1 := Tsetup) hPf_steps hPf_halted
      simp only [Nat.zero_add] at h1
      -- h1 : Steps (Tsetup.concat pF) ⟨Tsetup.length, sSetup⟩ ⟨cPf'.pc + Tsetup.length, cPf'.state⟩

      -- Need halted in Tsetup.concat pF for next lift
      have hhalted1 : (⟨cPf'.pc + Tsetup.length, cPf'.state⟩ : Config).isHalted (Tsetup.concat pF) := by
        simp only [Config.isHalted, Program.concat_length]
        simp only [Config.isHalted] at hPf_halted
        omega

      -- Step 2: Lift to clearProg.concat (Tsetup.concat pF)
      have h2 := Steps.concat_right (p1 := clearProg) h1 hhalted1
      -- h2 : Steps (clearProg.concat (Tsetup.concat pF))
      --        ⟨Tsetup.length + clearProg.length, sSetup⟩
      --        ⟨cPf'.pc + Tsetup.length + clearProg.length, cPf'.state⟩

      -- Need halted in phase3 = clearProg.concat (Tsetup.concat pF)
      have hhalted2 : (⟨cPf'.pc + Tsetup.length + clearProg.length, cPf'.state⟩ : Config).isHalted phase3 := by
        simp only [Config.isHalted, phase3, Program.concat_length]
        simp only [Config.isHalted] at hPf_halted
        omega

      -- Step 3: Lift to phase2.concat phase3
      have h3 := Steps.concat_right (p1 := phase2) h2 hhalted2
      -- Adjust the starting pc

      -- Need halted in phase2.concat phase3
      have hhalted3 : (⟨cPf'.pc + Tsetup.length + clearProg.length + phase2.length, cPf'.state⟩ : Config).isHalted (phase2.concat phase3) := by
        simp only [Config.isHalted, phase2, phase3, Program.concat_length]
        simp only [Config.isHalted] at hPf_halted
        omega

      -- Step 4: Lift to H = phase1.concat (phase2.concat phase3)
      have h4 := Steps.concat_right (p1 := phase1) h3 hhalted3

      -- Now simplify and convert to match the goal
      simp only [cH_built]
      simp only [hpc_eq] at h4 ⊢

      -- The setup_pc should match the offset in h4
      -- setup_pc = phase1.length + phase2.length + clearProg.length + Tsetup.length
      -- h4 starts at Tsetup.length + clearProg.length + phase2.length + phase1.length
      -- These should be equal (up to commutativity of addition)

      convert h4 using 2 <;> omega

    -- Combine: steps from init to setup, then to final
    have hH_steps_built : Steps H (Config.init (List.ofFn inputs)) cH_built :=
      Relation.ReflTransGen.trans hsteps_to_setup hPf_steps_in_H

    -- Apply determinism
    have hcH_eq : cH = cH_built := Steps.halts_unique hH_steps hH_halted hH_steps_built hH_built_halted

    -- Conclude
    calc cH.state.output
        = cH_built.state.output := by rw [hcH_eq]
      _ = cPf'.state.output := rfl
      _ = cF.state.output := hPf_output

  calc Result H (List.ofFn inputs) hHalts
      = cH.state.output := rfl
    _ = cF.state.output := hResult_eq
    _ = Result pF (List.ofFn fInput) hF_halts := rfl

-- Increase heartbeats limit for this complex proof
set_option maxHeartbeats 800000 in
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
        intro hHalts
        exact comp_binary_unary_halts_imp_dom hF_sf hG1_sf hG2_sf hF_spec hG1_spec hG2_spec inputs hHalts
      · -- Backward: composed function is defined → H halts
        intro hDom
        exact comp_binary_unary_dom_imp_halts hF_sf hG1_sf hG2_sf hF_spec hG1_spec hG2_spec inputs hDom
    · -- Results match
      intro hHalts hDom
      exact comp_binary_unary_result hF_sf hG1_sf hG2_sf hF_spec hG1_spec hG2_spec inputs hHalts hDom

end Urm
