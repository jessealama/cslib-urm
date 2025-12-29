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

/-- Execution result for clearRegisters: halts, zeros registers 0..maxReg, preserves above. -/
theorem clearRegisters_exec (maxReg : ℕ) (s : State) :
    ∃ c, Steps (Program.clearRegisters maxReg) ⟨0, s⟩ c ∧
         c.isHalted (Program.clearRegisters maxReg) ∧
         c.pc = (Program.clearRegisters maxReg).length ∧
         (∀ r, r ≤ maxReg → c.state.read r = 0) ∧
         (∀ r, maxReg < r → c.state.read r = s.read r) := by
  have hsl := clearRegisters_isStraightLine maxReg
  have hhalts := straightLine_halts_from_state hsl s
  obtain ⟨c, hsteps, hhalted, hpc⟩ := hhalts
  have hstate_eq := straightLineFinalState_eq_of_halted hsl s c hsteps hhalted
  refine ⟨c, hsteps, hhalted, hpc, ?_, ?_⟩
  · intro r hr; rw [hstate_eq]; exact clearRegisters_zeros maxReg s r hr
  · intro r hr; rw [hstate_eq]; exact clearRegisters_preserves_above maxReg s r hr

/-! ## Binary-Unary Composition Construction -/

-- compositionBaseBU is defined in CompositionHelpers

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
  simp only [compositionBaseBU, le_max_iff]; omega

theorem compositionBaseBU_ge_G1 (pF pG1 pG2 : Program) :
    pG1.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU, le_max_iff]; omega

theorem compositionBaseBU_ge_G2 (pF pG1 pG2 : Program) :
    pG2.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU, le_max_iff]; omega

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

/-- Any halting config for T01 equals the canonical one from straightLine_halts. -/
theorem T01_config_unique (m : ℕ) (inputs : Fin 1 → ℕ)
    (hT01_halts : Halts [Instr.T 0 (m + 1)] (List.ofFn inputs)) :
    Classical.choose hT01_halts =
    Classical.choose (straightLine_halts (single_transfer_isStraightLine 0 (m + 1)) (List.ofFn inputs)) := by
  have hspec := Classical.choose_spec hT01_halts
  have hspec' := Classical.choose_spec (straightLine_halts (single_transfer_isStraightLine 0 (m + 1)) (List.ofFn inputs))
  exact Steps.halts_unique hspec.1 hspec.2 hspec'.1 hspec'.2

/-- For any halting proof of T01, the result state agrees with initial inputs on registers ≤ m. -/
theorem T01_preserves_below_any (m : ℕ) (inputs : Fin 1 → ℕ)
    (hT01_halts : Halts [Instr.T 0 (m + 1)] (List.ofFn inputs))
    (r : ℕ) (hr : r ≤ m) :
    (Classical.choose hT01_halts).state.read r = (State.fromInputs (List.ofFn inputs)).read r := by
  rw [T01_config_unique]; exact T01_preserves_below m inputs r hr

/-- For any halting proof of T01, register m+1 contains the input value. -/
theorem T01_stores_input_any (m : ℕ) (inputs : Fin 1 → ℕ)
    (hT01_halts : Halts [Instr.T 0 (m + 1)] (List.ofFn inputs)) :
    (Classical.choose hT01_halts).state.read (m + 1) = inputs ⟨0, by omega⟩ := by
  rw [T01_config_unique]; exact T01_stores_input m inputs

/-- Helper: the composed program is in standard form if all components are. -/
theorem composeBU_isStandardForm {pF pG1 pG2 : Program}
    (hF : pF.IsStandardForm)
    (hG1 : pG1.IsStandardForm)
    (hG2 : pG2.IsStandardForm) :
    (Program.composeBU pF pG1 pG2).IsStandardForm := by
  simp only [Program.composeBU]
  let m := compositionBaseBU pF pG1 pG2
  have hPhase1 := ComposeBUComponents.phase1_sf' m hG1
  have hPhase2 := ComposeBUComponents.phase2_sf' m hG2
  have hPhase3 := ComposeBUComponents.phase3_sf' m hF
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
  -- Set up program structure using ComposeBUComponents
  let bu := ComposeBUComponents.mk' pF pG1 pG2
  let m := bu.m
  have hT01_sf := ComposeBUComponents.T01_sf' m
  have hT02_sf := ComposeBUComponents.T02_sf' m
  have hPhase1_sf := ComposeBUComponents.phase1_sf' m hG1_sf

  -- H = bu.phase1.concat (bu.phase2.concat bu.phase3)
  let H := Program.composeBU pF pG1 pG2
  have hH_eq : H = bu.phase1.concat (bu.phase2.concat bu.phase3) := rfl

  -- Convert hHalts to use H
  have hHalts' : Halts H (List.ofFn inputs) := hHalts

  -- Extract phase1 halting
  have hPhase1_halts : Halts bu.phase1 (List.ofFn inputs) := by
    rw [hH_eq] at hHalts'
    exact Halts.prefix_of_concat_sf hHalts' hPhase1_sf

  -- Extract pG1 halting from phase1
  -- bu.phase1 = bu.T01.concat (pG1.concat bu.T02)
  -- Use suffix_of_concat_sf to get execution of pG1.concat bu.T02 from state after bu.T01
  have hSuffix1 := Halts.suffix_of_concat_sf hPhase1_halts hT01_sf
  obtain ⟨sT01, hT01_halts, hsT01_eq, cG1T02, hG1T02_steps, hG1T02_halted⟩ := hSuffix1

  -- Extract pG1 halting from pG1.concat bu.T02
  have hG1T02_sf : (pG1.concat bu.T02).IsStandardForm := hG1_sf.concat hT02_sf

  -- Use Urm.prefix_of_concat_from_zero to extract pG1 halting
  have hG1_from_sT01 : ∃ c', Steps pG1 ⟨0, sT01⟩ c' ∧ c'.isHalted pG1 :=
    Urm.prefix_of_concat_from_zero hG1T02_steps hG1T02_halted hG1_sf
  obtain ⟨cG1', hG1_steps, hG1_halted⟩ := hG1_from_sT01

  -- Show sT01 agrees with State.fromInputs on registers 0..pG1.maxRegister
  have hm_ge_G1 : pG1.maxRegister ≤ m := ComposeBUComponents.m_ge_G1'

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
  have hg1_dom := comp_binary_unary_halts_imp_g1_dom hG1_sf hG1_spec inputs hHalts
  have hG1_halts := (hG1_spec inputs).1.mpr hg1_dom
  let bu := ComposeBUComponents.mk' pF pG1 pG2; let m := bu.m
  have hClear_sl := clearRegisters_isStraightLine m
  have hPhase1_sf := ComposeBUComponents.phase1_sf' m hG1_sf
  have hPhase2_sf := ComposeBUComponents.phase2_sf' m hG2_sf
  -- Extract phase execution chain
  have hPhase1_halts := Halts.prefix_of_concat_sf hHalts hPhase1_sf
  obtain ⟨sPhase1, _, hsPhase1_eq, _, hPhase23_steps, hPhase23_halted⟩ :=
    Halts.suffix_of_concat_sf hHalts hPhase1_sf
  obtain ⟨_, hPhase2_steps, hPhase2_halted⟩ :=
    prefix_of_concat_from_zero hPhase23_steps hPhase23_halted hPhase2_sf
  -- Extract clear → T10 → G2 chain from phase2
  obtain ⟨sClear, hClear_steps, ⟨_, hT10rest_steps, hT10rest_halted⟩⟩ :=
    suffix_of_concat_from_zero hPhase2_steps hPhase2_halted (ComposeBUComponents.clearProg_sf' m)
  obtain ⟨sT10, hT10_steps, ⟨_, hG2T03_steps, hG2T03_halted⟩⟩ :=
    suffix_of_concat_from_zero hT10rest_steps hT10rest_halted (ComposeBUComponents.T10_sf' m)
  obtain ⟨cG2', hG2_steps', hG2_halted'⟩ :=
    prefix_of_concat_from_zero hG2T03_steps hG2T03_halted hG2_sf
  -- Characterize T10 and Clear states
  obtain ⟨_, hT10_steps', hT10_halted', _, hT10_state'⟩ := single_transfer_halts (m + 1) 0 sClear
  have hsT10_eq : sT10 = sClear.write 0 (sClear.read (m + 1)) := by
    have := congrArg Config.state (Steps.halts_unique hT10_steps (Nat.le_refl _) hT10_steps' hT10_halted')
    simp only [hT10_state'] at this; exact this
  have hsClear_eq : sClear = straightLineFinalState hClear_sl sPhase1 :=
    straightLineFinalState_eq_of_halted hClear_sl sPhase1 ⟨bu.clearProg.length, sClear⟩ hClear_steps (Nat.le_refl _)
  -- Show state agreement for pG2
  have hagreeG2 : ∀ r, r ≤ pG2.maxRegister →
      sT10.read r = (State.fromInputs (List.ofFn inputs)).read r := by
    intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | hr_pos
    · -- r = 0: trace back through T10 → Clear → Phase1 → T01
      -- Step 1: sT10.read 0 = sClear.read (m + 1)
      have hsT10_r0 : sT10.read 0 = sClear.read (m + 1) := by rw [hsT10_eq, State.write_read_same]
      -- Step 2: sClear.read (m + 1) = sPhase1.read (m + 1)
      have hsClear_preserves : sClear.read (m + 1) = sPhase1.read (m + 1) := by
        rw [hsClear_eq]; exact clearRegisters_preserves_above m sPhase1 (m + 1) (by omega)
      -- Step 3: sPhase1.read (m + 1) = cPhase1'.state.read (m + 1)
      have hsPhase1_state : sPhase1 = (Classical.choose hPhase1_halts).state := hsPhase1_eq hPhase1_halts
      -- Step 4: Phase1 preserves R[m+1] = inputs[0] via T01 → G1 → T02 chain
      have hPhase1_preserves_input : (Classical.choose hPhase1_halts).state.read (m + 1) = inputs ⟨0, by omega⟩ := by
        have ⟨hP1_steps, hP1_halted⟩ := Classical.choose_spec hPhase1_halts
        have hT01_halts := straightLine_halts (single_transfer_isStraightLine 0 (m + 1)) (List.ofFn inputs)
        let sT01 := (Classical.choose hT01_halts).state
        have hm_ge_G1 : pG1.maxRegister ≤ m := compositionBaseBU_ge_G1 pF pG1 pG2
        have hagreeG1 : sT01.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG1.maxRegister :=
          fun _ _ hhi => T01_preserves_below m inputs _ (Nat.le_trans hhi hm_ge_G1)
        let eG1 := Halts.executeFromAgreeingState hG1_halts hG1_sf hagreeG1
        obtain ⟨_, hT02_steps, hT02_halted, _, hT02_state⟩ := single_transfer_halts 0 (m + 2) eG1.config.state
        have hT01_spec := Classical.choose_spec hT01_halts
        have hT01_pc := (ComposeBUComponents.T01_sf' m).halts_at_length _ _ hT01_spec.1 hT01_spec.2
        have ⟨hG1T02_steps, hG1T02_halted⟩ := Steps.chain_concat eG1.steps eG1.halted eG1.pc_eq hT02_steps hT02_halted
        have ⟨hP1_steps', hP1_halted'⟩ := Steps.chain_concat hT01_spec.1 hT01_spec.2 hT01_pc hG1T02_steps hG1T02_halted
        rw [congrArg Config.state (Steps.halts_unique hP1_steps hP1_halted hP1_steps' hP1_halted'),
          hT02_state, State.write_read_diff _ _ _ _ (by omega : m + 1 ≠ m + 2),
          eG1.preserves_high_register (m + 1) (Nat.lt_of_le_of_lt hm_ge_G1 (by omega : m < m + 1)),
          T01_stores_input m inputs]
      -- Step 5: RHS simplification
      have hRHS : (State.fromInputs (List.ofFn inputs)).read 0 = inputs ⟨0, by omega⟩ := by
        simp only [State.fromInputs, State.read]; rfl
      rw [hsT10_r0, hsClear_preserves, hsPhase1_state, hPhase1_preserves_input, ← hRHS]
    · -- r > 0: Clear zeroed it, T10 preserved it
      have hRHS_zero : (State.fromInputs (List.ofFn inputs)).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; exact hr_pos)]; rfl
      have hT10_preserves_r : sT10.read r = sClear.read r := by
        rw [hsT10_eq]; exact State.write_read_diff _ _ _ _ (Nat.ne_of_gt hr_pos)
      have hClear_zeros_r : sClear.read r = 0 := by
        rw [hsClear_eq]; exact clearRegisters_zeros m sPhase1 r (Nat.le_trans hr ComposeBUComponents.m_ge_G2')
      rw [hT10_preserves_r, hClear_zeros_r, hRHS_zero]
  exact (hG2_spec inputs).1.mp (Halts.of_agreeing_state hG2_steps' hG2_halted' hagreeG2)

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
  let bu := ComposeBUComponents.mk' pF pG1 pG2; let m := bu.m
  have hPhase1_sf := ComposeBUComponents.phase1_sf' m hG1_sf
  have hPhase2_sf := ComposeBUComponents.phase2_sf' m hG2_sf
  have hG1_halts := (hG1_spec inputs).1.mpr hg1_dom
  have hHalts' : Halts (bu.phase1.concat (bu.phase2.concat bu.phase3)) (List.ofFn inputs) := hHalts
  have hPhase1_halts := Halts.prefix_of_concat_sf hHalts' hPhase1_sf
  obtain ⟨sPhase1, _, hsPhase1_eq, _, hPhase23_steps, hPhase23_halted⟩ :=
    Halts.suffix_of_concat_sf hHalts' hPhase1_sf

  -- Phase1 execution: T01 → G1 → T02
  have hT01_sl := single_transfer_isStraightLine 0 (m + 1)
  have hT01_halts' := straightLine_halts hT01_sl (List.ofFn inputs)
  let sT01 := (Classical.choose hT01_halts').state
  have hT01_steps := (Classical.choose_spec hT01_halts').1
  have hT01_halted := (Classical.choose_spec hT01_halts').2
  have hT01_pc : (Classical.choose hT01_halts').pc = bu.T01.length :=
    (ComposeBUComponents.T01_sf' m).halts_at_length (List.ofFn inputs) _ hT01_steps hT01_halted

  have hm_ge_G1 : pG1.maxRegister ≤ m := ComposeBUComponents.m_ge_G1'
  have hagreeG1 : sT01.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG1.maxRegister :=
    fun _ _ hhi => T01_preserves_below m inputs _ (Nat.le_trans hhi hm_ge_G1)
  let eG1 := Halts.executeFromAgreeingState hG1_halts hG1_sf hagreeG1
  have hG1_preserves_m1 : eG1.config.state.read (m + 1) = sT01.read (m + 1) :=
    eG1.preserves_high_register (m + 1) (Nat.lt_of_le_of_lt hm_ge_G1 (by omega))

  have hcG1'_r0 : eG1.config.state.read 0 = (g1 inputs).get hg1_dom := by
    rw [State.agreeOn_read eG1.state_agrees (Nat.zero_le 0) (Nat.zero_le _)]
    exact (hG1_spec inputs).2 hG1_halts hg1_dom

  obtain ⟨cT02', hT02_steps', hT02_halted', hT02_pc', hT02_state'⟩ :=
    single_transfer_halts 0 (m + 2) eG1.config.state
  have hT02_preserves_m1 : cT02'.state.read (m + 1) = eG1.config.state.read (m + 1) := by
    rw [hT02_state']; exact State.write_read_diff _ _ _ _ (by omega)
  have hT02_m2 : cT02'.state.read (m + 2) = eG1.config.state.read 0 := by
    rw [hT02_state', State.write_read_same]

  have ⟨hG1T02_steps, hG1T02_halted⟩ :=
    Steps.chain_concat eG1.steps eG1.halted eG1.pc_eq hT02_steps' hT02_halted'
  have ⟨hPhase1_final_steps, hPhase1_final_halted⟩ :=
    Steps.chain_concat hT01_steps hT01_halted hT01_pc hG1T02_steps hG1T02_halted

  have hPhase1_state_eq : (Classical.choose hPhase1_halts).state = cT02'.state := by
    have heq := Steps.halts_unique (Classical.choose_spec hPhase1_halts).1
      (Classical.choose_spec hPhase1_halts).2 hPhase1_final_steps hPhase1_final_halted
    simp only [heq]

  have hsPhase1_m1 : sPhase1.read (m + 1) = inputs ⟨0, by omega⟩ := by
    rw [hsPhase1_eq hPhase1_halts, hPhase1_state_eq, hT02_preserves_m1, hG1_preserves_m1, T01_stores_input]
  have hsPhase1_v1 : sPhase1.read (m + 2) = (g1 inputs).get hg1_dom := by
    rw [hsPhase1_eq hPhase1_halts, hPhase1_state_eq, hT02_m2, hcG1'_r0]

  -- Extract phase2, phase3, clear, Tsetup, F halts
  obtain ⟨sPhase2, hPhase2_steps_from_s1, cPhase3, hPhase3_steps, hPhase3_halted⟩ :=
    suffix_of_concat_from_zero hPhase23_steps hPhase23_halted hPhase2_sf
  obtain ⟨cPhase2_from_s1, hPhase2_steps_s1, hPhase2_halted_s1⟩ :=
    prefix_of_concat_from_zero hPhase23_steps hPhase23_halted hPhase2_sf
  have hClear_sl := clearRegisters_isStraightLine m
  obtain ⟨sClear', hClear_steps_phase3, cTsetupF, hTsetupF_steps, hTsetupF_halted⟩ :=
    suffix_of_concat_from_zero hPhase3_steps hPhase3_halted (ComposeBUComponents.clearProg_sf' m)
  have hsClear'_eq : sClear' = straightLineFinalState hClear_sl sPhase2 :=
    straightLineFinalState_eq_of_halted hClear_sl sPhase2 ⟨bu.clearProg.length, sClear'⟩
      hClear_steps_phase3 (Nat.le_refl _)
  obtain ⟨sTsetup, hTsetup_steps_from_clear, cF', hF_steps', hF_halted'⟩ :=
    suffix_of_concat_from_zero hTsetupF_steps hTsetupF_halted (ComposeBUComponents.Tsetup_sf' m)

  let fInput : Fin 2 → ℕ := fun i => match i with
    | ⟨0, _⟩ => (g1 inputs).get hg1_dom
    | ⟨1, _⟩ => (g2 inputs).get hg2_dom
  have hm_ge_F : pF.maxRegister ≤ m := ComposeBUComponents.m_ge_F'

  -- Show sTsetup agrees with State.fromInputs fInput
  have hagreeF : ∀ r, r ≤ pF.maxRegister →
      sTsetup.read r = (State.fromInputs (List.ofFn fInput)).read r := by
    intro r hr
    -- Characterize sTsetup
    obtain ⟨cTsetup', hTsetup_steps', hTsetup_halted', _, hTsetup_state'⟩ :=
      double_transfer_halts (m + 2) 0 (m + 3) 1 sClear'
    have hsTsetup_halted : (⟨bu.Tsetup.length, sTsetup⟩ : Config).isHalted bu.Tsetup := Nat.le_refl _
    have hconfigs_eq := Steps.halts_unique hTsetup_steps_from_clear hsTsetup_halted
                                           hTsetup_steps' hTsetup_halted'
    have hsTsetup_eq : sTsetup = (sClear'.write 0 (sClear'.read (m + 2))).write 1 (sClear'.read (m + 3)) := by
      have : sTsetup = cTsetup'.state := congrArg Config.state hconfigs_eq
      rw [this, hTsetup_state', State.write_read_diff _ _ _ _ (by omega : m + 3 ≠ 0)]

    -- Phase2 execution from sPhase1
    obtain ⟨cClear_s1, hClear_steps_s1, hClear_halted_s1, hClear_pc_s1, hClear_zeros_s1, hClear_preserves_s1⟩ :=
      clearRegisters_exec m sPhase1
    obtain ⟨cT10_s1, hT10_steps_s1, hT10_halted_s1, hT10_pc_s1, hT10_state_s1⟩ :=
      single_transfer_halts (m + 1) 0 cClear_s1.state
    have hT10_r0_eq : cT10_s1.state.read 0 = inputs ⟨0, by omega⟩ := by
      rw [hT10_state_s1, State.write_read_same, hClear_preserves_s1 (m + 1) (by omega), hsPhase1_m1]
    have hm_ge_G2' : pG2.maxRegister ≤ m := compositionBaseBU_ge_G2 pF pG1 pG2
    have hagreeG2' : cT10_s1.state.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG2.maxRegister := by
      have hcT10_zeros : ∀ r, 1 ≤ r → r ≤ m → cT10_s1.state.read r = 0 := fun r _ hrm =>
        by rw [hT10_state_s1, State.write_read_diff _ _ _ _ (by omega), hClear_zeros_s1 r hrm]
      rw [List.ofFn_succ_last]; exact agrees_single_input_after_clear_transfer hm_ge_G2' hT10_r0_eq hcT10_zeros
    have hG2_halts_s1 := (hG2_spec inputs).1.mpr hg2_dom
    let eG2_s1 := Halts.executeFromAgreeingState hG2_halts_s1 hG2_sf hagreeG2'
    obtain ⟨cT03_s1, hT03_steps_s1, hT03_halted_s1, hT03_pc_s1, hT03_state_s1⟩ :=
      single_transfer_halts 0 (m + 3) eG2_s1.config.state
    have ⟨hG2T03_steps, hG2T03_halted⟩ :=
      Steps.chain_concat eG2_s1.steps eG2_s1.halted eG2_s1.pc_eq hT03_steps_s1 hT03_halted_s1
    have ⟨hT10G2T03_steps, hT10G2T03_halted⟩ :=
      Steps.chain_concat hT10_steps_s1 hT10_halted_s1 hT10_pc_s1 hG2T03_steps hG2T03_halted
    have ⟨hPhase2_explicit_steps, hPhase2_explicit_halted⟩ :=
      Steps.chain_concat hClear_steps_s1 hClear_halted_s1 hClear_pc_s1 hT10G2T03_steps hT10G2T03_halted
    have hPhase2_state : cPhase2_from_s1.state = cT03_s1.state := by
      have hconfigs := Steps.halts_unique hPhase2_steps_s1 hPhase2_halted_s1
        hPhase2_explicit_steps hPhase2_explicit_halted
      simp only [hconfigs]
    have hsPhase2_eq : sPhase2 = cPhase2_from_s1.state :=
      congrArg Config.state (Steps.halts_unique hPhase2_steps_from_s1 (Nat.le_refl _)
        hPhase2_steps_s1 hPhase2_halted_s1)

    rcases Nat.eq_zero_or_pos r with rfl | hr_pos
    · -- r = 0
      have hPhase2_preserves_m2 : cT03_s1.state.read (m + 2) = sPhase1.read (m + 2) := by
        rw [hT03_state_s1, State.write_read_diff _ _ _ _ (by omega),
            eG2_s1.preserves_high_register (m + 2) (Nat.lt_of_le_of_lt hm_ge_G2' (by omega)),
            hT10_state_s1, State.write_read_diff _ _ _ _ (by omega),
            hClear_preserves_s1 (m + 2) (by omega)]
      rw [hsTsetup_eq, State.write_read_diff _ _ _ _ (by omega), State.write_read_same,
          hsClear'_eq, clearRegisters_preserves_above m sPhase2 (m + 2) (by omega),
          hsPhase2_eq, hPhase2_state, hPhase2_preserves_m2, hsPhase1_v1]
      simp only [State.fromInputs, State.read, fInput, List.ofFn, List.getD]; rfl
    · by_cases hr1 : r = 1
      · -- r = 1
        subst hr1
        have hcG2_r0 : eG2_s1.config.state.read 0 = (g2 inputs).get hg2_dom := by
          rw [State.agreeOn_read eG2_s1.state_agrees (Nat.zero_le 0) (Nat.zero_le _)]
          exact (hG2_spec inputs).2 hG2_halts_s1 hg2_dom
        rw [hsTsetup_eq, State.write_read_same, hsClear'_eq,
            clearRegisters_preserves_above m sPhase2 (m + 3) (by omega),
            hsPhase2_eq, hPhase2_state, hT03_state_s1, State.write_read_same, hcG2_r0]
        simp only [State.fromInputs, State.read, fInput, List.ofFn, List.getD]; rfl
      · -- r > 1
        rw [hsTsetup_eq, State.write_read_diff _ _ _ _ (by omega), State.write_read_diff _ _ _ _ (by omega),
            hsClear'_eq, clearRegisters_zeros m sPhase2 r (Nat.le_trans hr hm_ge_F)]
        simp only [State.fromInputs, State.read]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]

  exact (hF_spec fInput).1.mp (Halts.of_agreeing_state hF_steps' hF_halted' hagreeF)

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
  -- Set up program structure using ComposeBUComponents
  let bu := ComposeBUComponents.mk' pF pG1 pG2
  let m := bu.m
  have hPhase1_sf := ComposeBUComponents.phase1_sf' m hG1_sf

  -- H = phase1.concat (phase2.concat phase3)
  let H := Program.composeBU pF pG1 pG2
  have hH_eq : H = bu.phase1.concat (bu.phase2.concat bu.phase3) := rfl

  -- Convert hHalts to use H
  have hHalts' : Halts H (List.ofFn inputs) := hHalts

  -- Extract phase1 halting
  have hPhase1_halts : Halts bu.phase1 (List.ofFn inputs) := by
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
  -- Set up program structure using ComposeBUComponents
  let bu := ComposeBUComponents.mk' pF pG1 pG2
  let m := bu.m
  let T01 := bu.T01
  let T02 := bu.T02
  let clearProg := bu.clearProg
  let T10 := bu.T10
  let T03 := bu.T03
  let Tsetup := bu.Tsetup
  let phase1 := bu.phase1
  let phase2 := bu.phase2
  let phase3 := bu.phase3

  -- Standard form properties using helper lemmas
  have hT01_sf := ComposeBUComponents.T01_sf' m
  have hT02_sf := ComposeBUComponents.T02_sf' m
  have hClear_sf := ComposeBUComponents.clearProg_sf' m
  have hPhase1_sf := ComposeBUComponents.phase1_sf' m hG1_sf
  have hPhase2_sf := ComposeBUComponents.phase2_sf' m hG2_sf
  have hPhase3_sf := ComposeBUComponents.phase3_sf' m hF_sf

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
    -- Chain G1 and T02 using chain_concat_halts
    have hG1T02_halts' : ∃ c, Steps (pG1.concat T02) ⟨0, sT01⟩ c ∧ c.isHalted (pG1.concat T02) :=
      Steps.chain_concat_halts hG1_steps' hG1_halted' hG1_pc' ⟨cT02, hT02_steps', hT02_halted'⟩
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

    -- Step 1: clearProg halts, zeros R[0..m], preserves R[m+1..]
    obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves_above⟩ :=
      clearRegisters_exec m s
    have hClear_preserves : cClear.state.read (m + 1) = s.read (m + 1) := hClear_preserves_above (m + 1) (by omega)

    -- Step 2: T10 halts from cClear.state and sets R[0] = R[m+1]
    obtain ⟨cT10, hT10_steps, hT10_halted, hT10_pc, hT10_state⟩ := single_transfer_halts (m + 1) 0 cClear.state
    have hT10_r0 : cT10.state.read 0 = inputs ⟨0, by omega⟩ := by
      rw [hT10_state, State.write_read_same, hClear_preserves, hs_input]

    -- Step 3: pG2 halts from cT10.state because it agrees with initial state
    have hm_ge_G2 : pG2.maxRegister ≤ m := compositionBaseBU_ge_G2 pF pG1 pG2
    have hcT10_zeros : ∀ r, 1 ≤ r → r ≤ m → cT10.state.read r = 0 := by
      intro r _ hrm; rw [hT10_state, State.write_read_diff _ _ _ _ (by omega : r ≠ 0), hClear_zeros r hrm]
    have hlist_eq : List.ofFn inputs = [inputs ⟨0, by omega⟩] := List.ofFn_succ_last
    have hagreeG2 : cT10.state.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG2.maxRegister := by
      rw [hlist_eq]; exact agrees_single_input_after_clear_transfer hm_ge_G2 hT10_r0 hcT10_zeros

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

    -- Chain: pG2.concat T03 → T10.concat (pG2.concat T03) → phase2
    have ⟨hG2T03_steps, hG2T03_halted⟩ := Steps.chain_concat hG2_steps hG2_halted hG2_pc hT03_steps hT03_halted
    have ⟨hT10G2T03_steps, hT10G2T03_halted⟩ := Steps.chain_concat hT10_steps hT10_halted hT10_pc hG2T03_steps hG2T03_halted
    have ⟨hPhase2_steps, hPhase2_halted⟩ := Steps.chain_concat hClear_steps hClear_halted hClear_pc hT10G2T03_steps hT10G2T03_halted

    exact ⟨_, hPhase2_steps, hPhase2_halted⟩

  -- Phase 3 halts from cPhase2.state (registers set up appropriately)
  -- Key requirements: s.read (m + 2) = v1, s.read (m + 3) = v2
  have hPhase3_halts_from : ∀ s : State,
      s.read (m + 2) = v1 → s.read (m + 3) = v2 →
      (∃ c, Steps phase3 ⟨0, s⟩ c ∧ c.isHalted phase3) := by
    intro s hs_v1 hs_v2
    -- phase3 = clearProg.concat (Tsetup.concat pF)
    -- The proof chains: clearProg → Tsetup → pF

    -- Step 1: clearProg halts, zeros R[0..m], preserves R[m+1..]
    obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves_above⟩ :=
      clearRegisters_exec m s
    have hClear_preserves_v1 : cClear.state.read (m + 2) = v1 := by
      rw [hClear_preserves_above (m + 2) (by omega), hs_v1]
    have hClear_preserves_v2 : cClear.state.read (m + 3) = v2 := by
      rw [hClear_preserves_above (m + 3) (by omega), hs_v2]

    -- Step 2: Tsetup halts from cClear.state and sets R[0] = v1, R[1] = v2
    -- Tsetup = [T (m+2) 0, T (m+3) 1]
    obtain ⟨cTsetup, hTsetup_steps, hTsetup_halted, hTsetup_pc, hTsetup_state⟩ :=
      double_transfer_halts (m + 2) 0 (m + 3) 1 cClear.state
    -- Simplify the state formula (m+3 ≠ 0)
    have hTsetup_state' : cTsetup.state =
        (cClear.state.write 0 (cClear.state.read (m + 2))).write 1 (cClear.state.read (m + 3)) := by
      simp only [hTsetup_state, State.write_read_diff _ _ _ _ (by omega : m + 3 ≠ 0)]

    -- After Tsetup: R[0] = v1, R[1] = v2
    have hTsetup_r0 : cTsetup.state.read 0 = v1 := by
      rw [hTsetup_state', State.write_read_diff _ _ _ _ (by omega : 0 ≠ 1),
          State.write_read_same, hClear_preserves_v1]
    have hTsetup_r1 : cTsetup.state.read 1 = v2 := by
      rw [hTsetup_state', State.write_read_same, hClear_preserves_v2]

    -- Step 3: pF halts from cTsetup.state because it agrees with fInput
    have hm_ge_F : pF.maxRegister ≤ m := compositionBaseBU_ge_F pF pG1 pG2
    have hcTsetup_zeros : ∀ r, 2 ≤ r → r ≤ m → cTsetup.state.read r = 0 := by
      intro r _ hrm
      rw [hTsetup_state', State.write_read_diff _ _ _ _ (by omega : r ≠ 1),
          State.write_read_diff _ _ _ _ (by omega : r ≠ 0), hClear_zeros r hrm]
    have hlist_eq : List.ofFn fInput = [v1, v2] := List.ofFn_succ_last
    have hagreeF : cTsetup.state.agreeOn (State.fromInputs (List.ofFn fInput)) 0 pF.maxRegister := by
      rw [hlist_eq]; exact agrees_two_inputs_after_clear_transfer hm_ge_F hTsetup_r0 hTsetup_r1 hcTsetup_zeros

    -- Get pF execution from agreeing state using helper
    let eF := Halts.executeFromAgreeingState hF_halts hF_sf hagreeF
    let cF := eF.config
    have hF_steps := eF.steps
    have hF_halted := eF.halted
    have hF_pc := eF.pc_eq

    -- Chain: Tsetup.concat pF → phase3
    have ⟨hTsetupF_steps, hTsetupF_halted⟩ := Steps.chain_concat hTsetup_steps hTsetup_halted hTsetup_pc hF_steps hF_halted
    have ⟨hPhase3_steps, hPhase3_halted⟩ := Steps.chain_concat hClear_steps hClear_halted hClear_pc hTsetupF_steps hTsetupF_halted

    exact ⟨_, hPhase3_steps, hPhase3_halted⟩

  -- Chain all phases
  let cPhase1 := Classical.choose hPhase1_halts
  have hPhase1_spec := Classical.choose_spec hPhase1_halts
  have hPhase1_steps : Steps phase1 (Config.init (List.ofFn inputs)) cPhase1 := hPhase1_spec.1
  have hPhase1_halted : cPhase1.isHalted phase1 := hPhase1_spec.2
  have hPhase1_pc : cPhase1.pc = phase1.length :=
    hPhase1_sf.halts_at_length (List.ofFn inputs) cPhase1 hPhase1_steps hPhase1_halted

  -- Hoisted: Phase1 trace building (used by hPhase1_preserves_input and hPhase1_v1)
  have hT01_sl' := single_transfer_isStraightLine 0 (m + 1)
  have hT01_halts'' := straightLine_halts hT01_sl' (List.ofFn inputs)
  let cT01' := Classical.choose hT01_halts''
  let sT01' := cT01'.state
  have hT01_steps' := (Classical.choose_spec hT01_halts'').1
  have hT01_halted' := (Classical.choose_spec hT01_halts'').2
  have hT01_pc' : cT01'.pc = T01.length :=
    hT01_sf.halts_at_length (List.ofFn inputs) cT01' hT01_steps' hT01_halted'
  have hsT01'_m1 : sT01'.read (m + 1) = inputs ⟨0, by omega⟩ := T01_stores_input m inputs

  have hm_ge_G1' : pG1.maxRegister ≤ m := compositionBaseBU_ge_G1 pF pG1 pG2
  have hagreeG1'' : sT01'.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG1.maxRegister := fun _ _ hhi =>
    T01_preserves_below m inputs _ (Nat.le_trans hhi hm_ge_G1')

  let eG1'' := Halts.executeFromAgreeingState hG1_halts hG1_sf hagreeG1''
  let cG1'' := eG1''.config
  have hG1''_steps := eG1''.steps
  have hG1''_halted := eG1''.halted
  have hG1''_pc := eG1''.pc_eq

  have hcG1''_r0 : cG1''.state.read 0 = v1 := by
    have h0_le : 0 ≤ pG1.maxRegister := Nat.zero_le _
    have hagree_at_0 := State.agreeOn_read eG1''.state_agrees (Nat.zero_le 0) h0_le
    rw [hagree_at_0]; rfl

  have hG1''_preserves_m1 : cG1''.state.read (m + 1) = sT01'.read (m + 1) :=
    Steps.preserves_high_register hG1''_steps (m + 1) (by omega : pG1.maxRegister < m + 1)

  have hT02''_halts := single_transfer_halts 0 (m + 2) cG1''.state
  obtain ⟨cT02'', hT02''_steps, hT02''_halted, hT02''_pc, hT02''_state⟩ := hT02''_halts

  have hT02''_preserves_m1 : cT02''.state.read (m + 1) = cG1''.state.read (m + 1) := by
    rw [hT02''_state]; exact State.write_read_diff _ _ _ _ (by omega : m + 1 ≠ m + 2)

  have hT02''_m2 : cT02''.state.read (m + 2) = cG1''.state.read 0 := by
    rw [hT02''_state, State.write_read_same]

  have ⟨hG1''T02''_steps, hG1''T02''_halted⟩ :=
    Steps.chain_concat hG1''_steps hG1''_halted hG1''_pc hT02''_steps hT02''_halted

  have ⟨hPhase1''_final_steps, hPhase1''_final_halted⟩ :=
    Steps.chain_concat hT01_steps' hT01_halted' hT01_pc' hG1''T02''_steps hG1''T02''_halted

  have hPhase1''_state_eq : cPhase1.state = cT02''.state := by
    have heq := Steps.halts_unique hPhase1_steps hPhase1_halted hPhase1''_final_steps hPhase1''_final_halted
    simp only [heq]

  -- Now both properties follow from hoisted definitions
  have hPhase1_preserves_input : cPhase1.state.read (m + 1) = inputs ⟨0, by omega⟩ := by
    rw [hPhase1''_state_eq, hT02''_preserves_m1, hG1''_preserves_m1, hsT01'_m1]

  have hPhase1_v1 : cPhase1.state.read (m + 2) = v1 := by
    rw [hPhase1''_state_eq, hT02''_m2, hcG1''_r0]

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

  -- Hoisted: Extract intermediate state after phase1 (used by both v1 and v2 proofs)
  obtain ⟨s1, hPhase1_steps_s1, hPhase2_halts_s1⟩ :=
    suffix_of_concat_from_zero hPhase12_steps hPhase12_halted hPhase1_sf
  have hs1_eq : s1 = cPhase1.state := by
    have hPhase1_spec := Classical.choose_spec hPhase1_halts
    have hpc := hPhase1_sf.halts_at_length _ _ hPhase1_spec.1 hPhase1_spec.2
    have hPhase1_at_len : Steps phase1 (Config.init (List.ofFn inputs)) ⟨phase1.length, cPhase1.state⟩ := by
      have heq : cPhase1 = ⟨phase1.length, cPhase1.state⟩ := by ext; exact hpc; rfl
      rw [← heq]; exact hPhase1_spec.1
    have h1 : (⟨phase1.length, s1⟩ : Config).isHalted phase1 := by simp [Config.isHalted]
    have h2 : (⟨phase1.length, cPhase1.state⟩ : Config).isHalted phase1 := by simp [Config.isHalted]
    have hconfigs_eq := Steps.halts_unique hPhase1_steps_s1 h1 hPhase1_at_len h2
    exact congrArg Config.state hconfigs_eq
  obtain ⟨cPhase2_final, hPhase2_steps_final, hPhase2_halted_final⟩ := hPhase2_halts_s1
  have hPhase12_state_eq : cPhase12.state = cPhase2_final.state := by
    have ⟨hsteps_total, hfinal_halted⟩ := Steps.chain_concat hPhase1_steps_s1
        (by simp [Config.isHalted]) rfl hPhase2_steps_final hPhase2_halted_final
    have hconfigs_eq := Steps.halts_unique hPhase12_steps hPhase12_halted hsteps_total hfinal_halted
    simp only [hconfigs_eq]
  have hs1_input : s1.read (m + 1) = inputs ⟨0, by omega⟩ := by
    rw [hs1_eq]; exact hPhase1_preserves_input

  -- Hoisted: Phase2 trace construction (used by hPhase12_v1 and hPhase12_v2)
  -- Step 5a: clearProg halts, zeros R[0..m], preserves R[m+1..]
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves_above⟩ :=
    clearRegisters_exec m s1
  have hClear_preserves_m1 : cClear.state.read (m + 1) = s1.read (m + 1) := hClear_preserves_above (m + 1) (by omega)

  -- Step 5b: T10 halts and sets R[0] = R[m+1]
  obtain ⟨cT10, hT10_steps, hT10_halted, hT10_pc, hT10_state⟩ := single_transfer_halts (m + 1) 0 cClear.state
  have hT10_r0 : cT10.state.read 0 = inputs ⟨0, by omega⟩ := by
    rw [hT10_state, State.write_read_same, hClear_preserves_m1, hs1_input]

  -- Step 5c: G2 execution
  have hm_ge_G2 : pG2.maxRegister ≤ m := compositionBaseBU_ge_G2 pF pG1 pG2
  have hcT10_zeros : ∀ r, 1 ≤ r → r ≤ m → cT10.state.read r = 0 := by
    intro r _ hrm; rw [hT10_state, State.write_read_diff _ _ _ _ (by omega : r ≠ 0), hClear_zeros r hrm]
  have hlist_eq : List.ofFn inputs = [inputs ⟨0, by omega⟩] := List.ofFn_succ_last
  have hagreeG2 : cT10.state.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG2.maxRegister := by
    rw [hlist_eq]; exact agrees_single_input_after_clear_transfer hm_ge_G2 hT10_r0 hcT10_zeros
  let eG2 := Halts.executeFromAgreeingState hG2_halts hG2_sf hagreeG2
  let cG2 := eG2.config
  have hG2_steps := eG2.steps
  have hG2_halted := eG2.halted
  have hG2_pc := eG2.pc_eq
  have hcG2_r0_eq : cG2.state.read 0 = v2 := by
    have h0_le : 0 ≤ pG2.maxRegister := Nat.zero_le _
    have hagree_at_0 := State.agreeOn_read eG2.state_agrees (Nat.zero_le 0) h0_le
    rw [hagree_at_0]; rfl

  -- Step 5d: T03 execution
  have hT03_halts := single_transfer_halts 0 (m + 3) cG2.state
  obtain ⟨cT03, hT03_steps, hT03_halted, hT03_pc, hT03_state⟩ := hT03_halts

  -- Phase2 explicit steps and halted (using chain_concat)
  have ⟨hG2T03_steps, hG2T03_halted⟩ := Steps.chain_concat hG2_steps hG2_halted hG2_pc hT03_steps hT03_halted
  have ⟨hT10G2T03_steps, hT10G2T03_halted⟩ := Steps.chain_concat hT10_steps hT10_halted hT10_pc hG2T03_steps hG2T03_halted
  have ⟨hPhase2_explicit_steps, hPhase2_explicit_halted⟩ := Steps.chain_concat hClear_steps hClear_halted hClear_pc hT10G2T03_steps hT10G2T03_halted
  have hPhase2_state_match : cPhase2_final.state = cT03.state := by
    have hconfigs_eq := Steps.halts_unique hPhase2_steps_final hPhase2_halted_final hPhase2_explicit_steps hPhase2_explicit_halted
    rw [hconfigs_eq]

  have hPhase12_v1 : cPhase12.state.read (m + 2) = v1 := by
    -- Uses hoisted Phase2 trace: phase2 preserves m+2
    rw [hPhase12_state_eq, hPhase2_state_match]
    have hClear_preserves_m2 : cClear.state.read (m + 2) = s1.read (m + 2) :=
      hClear_preserves_above (m + 2) (by omega)
    have hT10_preserves_m2 : cT10.state.read (m + 2) = cClear.state.read (m + 2) := by
      rw [hT10_state]; exact State.write_read_diff _ _ _ _ (by omega : m + 2 ≠ 0)
    have hG2_preserves_m2 : cG2.state.read (m + 2) = cT10.state.read (m + 2) :=
      Steps.preserves_high_register hG2_steps (m + 2) (by omega : pG2.maxRegister < m + 2)
    have hT03_preserves_m2 : cT03.state.read (m + 2) = cG2.state.read (m + 2) := by
      rw [hT03_state]; exact State.write_read_diff _ _ _ _ (by omega : m + 2 ≠ m + 3)
    have hs1_v1 : s1.read (m + 2) = v1 := by rw [hs1_eq]; exact hPhase1_v1
    rw [hT03_preserves_m2, hG2_preserves_m2, hT10_preserves_m2, hClear_preserves_m2, hs1_v1]

  have hPhase12_v2 : cPhase12.state.read (m + 3) = v2 := by
    -- Uses hoisted Phase2 trace: T03 writes cG2.state.read 0 to m+3
    rw [hPhase12_state_eq, hPhase2_state_match, hT03_state, State.write_read_same, hcG2_r0_eq]

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

      -- Tsetup execution using double_transfer_halts
      have hTsetup_exec : ∀ s : State,
          ∃ c, Steps Tsetup ⟨0, s⟩ c ∧ c.isHalted Tsetup ∧ c.pc = 2 ∧
               c.state = (s.write 0 (s.read (m + 2))).write 1 (s.read (m + 3)) := by
        intro s
        obtain ⟨c, hsteps, hhalted, hpc, hstate⟩ := double_transfer_halts (m + 2) 0 (m + 3) 1 s
        refine ⟨c, hsteps, hhalted, hpc, ?_⟩
        simp only [hstate, State.write_read_diff _ _ _ _ (by omega : m + 3 ≠ 0)]

      -- clearProg execution helper
      let hClear_exec := fun s => clearRegisters_exec m s

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

      -- Build phase1 execution: T01 → G1 → T02 (using chain_concat)
      have ⟨hG1T02_steps, hG1T02_halted⟩ :=
        Steps.chain_concat hG1_steps' hG1_halted' hG1_pc' hT02_steps hT02_halted
      have ⟨hPhase1_steps, hPhase1_halted⟩ :=
        Steps.chain_concat hT01_steps hT01_halted hT01_pc hG1T02_steps hG1T02_halted

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
      have hcT10_zeros : ∀ r, 1 ≤ r → r ≤ m → cT10.state.read r = 0 := by
        intro r _ hrm; rw [hT10_state, State.write_read_diff _ _ _ _ (by omega : r ≠ 0), hClear1_zeros r hrm]
      have hlist_eq : List.ofFn inputs = [inputs ⟨0, by omega⟩] := List.ofFn_succ_last
      have hagreeG2 : cT10.state.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG2.maxRegister := by
        rw [hlist_eq]; exact agrees_single_input_after_clear_transfer hm_ge_G2 hcT10_r0 hcT10_zeros

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

      -- Build phase2 trace: clearProg → T10 → G2 → T03 (using chain_concat)
      have ⟨hG2T03_steps, hG2T03_halted⟩ :=
        Steps.chain_concat hG2_steps' hG2_halted' hG2_pc' hT03_steps hT03_halted
      have ⟨hT10G2T03_steps, hT10G2T03_halted⟩ :=
        Steps.chain_concat hT10_steps hT10_halted hT10_pc hG2T03_steps hG2T03_halted
      have ⟨hPhase2_steps, hPhase2_halted⟩ :=
        Steps.chain_concat hClear1_steps hClear1_halted hClear1_pc hT10G2T03_steps hT10G2T03_halted

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
        rw [hTsetup_state, State.write_read_diff _ r 1 _ (by omega),
            State.write_read_diff _ r 0 _ (by omega), hClear2_zeros r hrm]

      -- m ≥ 1 follows from the definition of compositionBaseBU which uses max 1 (...)
      -- This ensures R[m+1] ≠ R[1], avoiding collision with binary input register
      have hm_ge_1 : 1 ≤ m := compositionBaseBU_ge_1 pF pG1 pG2

      -- After Tsetup: R[m+1] = x, R[m+2] = v1, R[m+3] = v2 (preserved)
      have hcTsetup_m1 : cTsetup.state.read (m + 1) = x := by
        rw [hTsetup_state, State.write_read_diff _ (m + 1) 1 _ (by omega),
            State.write_read_diff _ (m + 1) 0 _ (by omega), hClear2_m1]
      have hcTsetup_m2 : cTsetup.state.read (m + 2) = v1 := by
        rw [hTsetup_state, State.write_read_diff _ (m + 2) 1 _ (by omega),
            State.write_read_diff _ (m + 2) 0 _ (by omega), hClear2_m2]
      have hcTsetup_m3 : cTsetup.state.read (m + 3) = v2 := by
        rw [hTsetup_state, State.write_read_diff _ (m + 3) 1 _ (by omega),
            State.write_read_diff _ (m + 3) 0 _ (by omega), hClear2_m3]

      -- Build phase3 prefix: clearProg → Tsetup
      have hClearTsetup_steps : Steps (clearProg.concat (Tsetup.concat pF)) ⟨0, cT03.state⟩
          ⟨clearProg.length + Tsetup.length, cTsetup.state⟩ := by
        -- Chain clearProg and Tsetup
        have ⟨hCT_steps, hCT_halted⟩ := Steps.chain_concat hClear2_steps hClear2_halted hClear2_pc hTsetup_steps hTsetup_halted
        have hpc_eq : cTsetup.pc + clearProg.length = clearProg.length + Tsetup.length := by
          simp only [Tsetup, List.length_cons, List.length_nil]; rw [hTsetup_pc]; omega
        have hCT_steps' : Steps (clearProg.concat Tsetup) ⟨0, cT03.state⟩
            ⟨clearProg.length + Tsetup.length, cTsetup.state⟩ := by convert hCT_steps using 2; exact hpc_eq.symm
        have hCT_halted' : (⟨clearProg.length + Tsetup.length, cTsetup.state⟩ : Config).isHalted (clearProg.concat Tsetup) := by
          simp only [Config.isHalted, Program.concat_length, Tsetup, List.length_cons, List.length_nil]; omega
        -- Lift to phase3 = (clearProg.concat Tsetup).concat pF via associativity
        have hassoc : clearProg.concat (Tsetup.concat pF) = (clearProg.concat Tsetup).concat pF :=
          (Program.concat_assoc clearProg Tsetup pF).symm
        rw [hassoc]
        exact Steps.concat_left_prefix hCT_steps' hCT_halted'

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
        have ⟨hsteps, _⟩ := Steps.chain_concat hClear2_steps hClear2_halted hClear2_pc hTsetup_steps hTsetup_halted
        have hpc_eq : cTsetup.pc + clearProg.length = clearProg.length + Tsetup.length := by
          simp only [Tsetup, List.length_cons, List.length_nil]; rw [hTsetup_pc]; omega
        convert hsteps using 2; exact hpc_eq.symm

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
