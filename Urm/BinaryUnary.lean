/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Michael Han
-/
import Urm.UnaryComposition
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Binary-Unary Composition Closure

This file proves that the composition of a binary function `f` with two unary functions
`g₀` and `g₁` preserves computability:

If `f : (Fin 2 → ℕ) → Part ℕ` and `g₀, g₁ : ℕ → Part ℕ` are computable, then
`h(x) = f(g₀(x), g₁(x))` is computable.

This is a stepping stone between the unary-unary case (in `UnaryComposition.lean`)
and the full general case (Cutland's Theorem 3.1).

## Main Results

- `binaryUnaryComposeProgram`: Constructs the composed program H from F, G₀, G₁
- `comp_binary_unary_bounded`: Proves correctness assuming bounded jumps
- `URMComputable.comp_binary_unary`: Full composition closure theorem

## Program Structure

Following Cutland's construction, the composed program has 5 phases:
1. Save input x to safe register (m+1)
2. Run G₀ on x, save g₀(x) to safe register (m+2)
3. Restore x, clear scratch, run G₁ on x
4. Setup binary inputs: R₁ := g₁(x), R₀ := g₀(x)
5. Clear scratch for F, run F

where m = max(1, Pf.maxRegister, Pg0.maxRegister, Pg1.maxRegister).
-/

namespace Urm

/-! ## clearAbove - Generalization of clearScratch

clearAbove zeros registers from `start` through `maxReg`, preserving registers below `start`. -/

/-- Clear registers R_start through R_maxReg. Empty if start > maxReg. -/
def Program.clearAbove (start maxReg : ℕ) : Program :=
  if start > maxReg then []
  else (List.range (maxReg - start + 1)).map fun i => Instr.Z (start + i)

/-- clearAbove is a straight-line program (no jumps). -/
theorem Program.clearAbove_isStraightLine (start maxReg : ℕ) :
    (Program.clearAbove start maxReg).isStraightLine = true := by
  simp only [clearAbove]
  split_ifs with h
  · simp [Program.isStraightLine]
  · simp only [Program.isStraightLine, List.all_map]
    simp only [List.all_eq_true, Function.comp_apply]
    intro i hi
    simp only [List.mem_range] at hi
    simp [Instr.isNonJumping]

/-- clearAbove has bounded jumps (trivially, since it has no jumps). -/
theorem Program.clearAbove_boundedJumps (start maxReg : ℕ) :
    (Program.clearAbove start maxReg).boundedJumps :=
  Program.boundedJumps_of_straightLine (clearAbove_isStraightLine start maxReg)

/-! ## Composed Program Construction -/

/-- The composed program for h(x) = f(g₀(x), g₁(x)).
    Following Cutland's Theorem 3.1 construction with explicit phases. -/
def binaryUnaryComposeProgram (Pf Pg0 Pg1 : Program) : Program :=
  let m := max 1 (max Pf.maxRegister (max Pg0.maxRegister Pg1.maxRegister))
  let saveX := m + 1     -- x stored here (preserved across all runs)
  let saveG0 := m + 2    -- g₀(x) stored here

  -- Phase 1: Save input x to safe register
  let phase1_saveX : Program := [Instr.T 0 saveX]

  -- Phase 2: Run G₀ on x, save result to safe register
  let phase2_runG0AndSave : Program := Program.concat Pg0 [Instr.T 0 saveG0]

  -- Phase 3: Restore x to R₀, clear scratch registers, run G₁
  let phase3_restoreAndG1 : Program :=
    Program.concat (Program.concat [Instr.T saveX 0] (Program.clearAbove 1 m)) Pg1

  -- Phase 4: Setup binary inputs for F
  -- After G₁, R₀ = g₁(x). We need R₀ = g₀(x), R₁ = g₁(x).
  -- Order matters: first copy g₁(x) to R₁, then restore g₀(x) to R₀
  let phase4_setupBinaryInputs : Program := [Instr.T 0 1, Instr.T saveG0 0]

  -- Phase 5: Clear registers R₂..Rₘ for F, then run F
  let phase5_clearAndRunF : Program := Program.concat (Program.clearAbove 2 Pf.maxRegister) Pf

  -- Concatenate all phases
  Program.concat (Program.concat (Program.concat (Program.concat
    phase1_saveX phase2_runG0AndSave) phase3_restoreAndG1)
    phase4_setupBinaryInputs) phase5_clearAndRunF

/-! ## Helper for Binary Inputs -/

/-- Create a binary input function (Fin 2 → ℕ) from two values. -/
def binaryInputs (y₀ y₁ : ℕ) : Fin 2 → ℕ := fun i =>
  if i = 0 then y₀ else y₁

theorem binaryInputs_zero (y₀ y₁ : ℕ) : binaryInputs y₀ y₁ 0 = y₀ := rfl

theorem binaryInputs_one (y₀ y₁ : ℕ) : binaryInputs y₀ y₁ 1 = y₁ := rfl

/-! ## Key Lemmas about Program Properties -/

/-- The m value used in the construction. -/
def binaryUnaryM (Pf Pg0 Pg1 : Program) : ℕ :=
  max 1 (max Pf.maxRegister (max Pg0.maxRegister Pg1.maxRegister))

/-- saveX register index. -/
def binaryUnarySaveX (Pf Pg0 Pg1 : Program) : ℕ := binaryUnaryM Pf Pg0 Pg1 + 1

/-- saveG0 register index. -/
def binaryUnarySaveG0 (Pf Pg0 Pg1 : Program) : ℕ := binaryUnaryM Pf Pg0 Pg1 + 2

/-- m is at least 1. -/
theorem binaryUnaryM_ge_one (Pf Pg0 Pg1 : Program) : binaryUnaryM Pf Pg0 Pg1 ≥ 1 := by
  simp only [binaryUnaryM]
  omega

/-- m is at least Pf.maxRegister. -/
theorem binaryUnaryM_ge_Pf (Pf Pg0 Pg1 : Program) :
    binaryUnaryM Pf Pg0 Pg1 ≥ Pf.maxRegister := by
  simp only [binaryUnaryM]
  omega

/-- m is at least Pg0.maxRegister. -/
theorem binaryUnaryM_ge_Pg0 (Pf Pg0 Pg1 : Program) :
    binaryUnaryM Pf Pg0 Pg1 ≥ Pg0.maxRegister := by
  simp only [binaryUnaryM]
  omega

/-- m is at least Pg1.maxRegister. -/
theorem binaryUnaryM_ge_Pg1 (Pf Pg0 Pg1 : Program) :
    binaryUnaryM Pf Pg0 Pg1 ≥ Pg1.maxRegister := by
  simp only [binaryUnaryM]
  omega

/-! ## State Agreement Properties -/

/-- State for binary function with inputs y₀, y₁. -/
def State.binaryInit (y₀ y₁ : ℕ) : State := fun r =>
  if r = 0 then y₀
  else if r = 1 then y₁
  else 0

theorem State.binaryInit_R0 (y₀ y₁ : ℕ) : (State.binaryInit y₀ y₁).read 0 = y₀ := by
  simp [State.binaryInit, State.read]

theorem State.binaryInit_R1 (y₀ y₁ : ℕ) : (State.binaryInit y₀ y₁).read 1 = y₁ := by
  simp [State.binaryInit, State.read]

theorem State.binaryInit_high (y₀ y₁ : ℕ) (r : ℕ) (hr : r > 1) :
    (State.binaryInit y₀ y₁).read r = 0 := by
  simp only [State.binaryInit, State.read]
  split_ifs with h1 h2
  · omega
  · omega
  · rfl

/-- A state agrees with binaryInit if R₀ and R₁ match, and higher registers are zero. -/
theorem State.agreesLow_binaryInit (σ : State) (y₀ y₁ : ℕ) (maxReg : ℕ)
    (hR0 : σ.read 0 = y₀) (hR1 : σ.read 1 = y₁)
    (hcleared : ∀ r, 2 ≤ r → r ≤ maxReg → σ.read r = 0) :
    σ.agreesLow (State.binaryInit y₀ y₁) maxReg := by
  intro r hr
  rcases Nat.lt_trichotomy r 1 with hr1 | hr1 | hr1
  · -- r = 0
    have : r = 0 := by omega
    simp [this, hR0, State.binaryInit_R0]
  · -- r = 1
    simp [hr1, hR1, State.binaryInit_R1]
  · -- r > 1
    have h2 : 2 ≤ r := by omega
    rw [hcleared r h2 hr, State.binaryInit_high y₀ y₁ r hr1]

/-- State.binaryInit equals State.fromInputs for two-element list. -/
theorem State.binaryInit_eq_fromInputs (y₀ y₁ : ℕ) :
    State.binaryInit y₀ y₁ = State.fromInputs [y₀, y₁] := by
  funext r
  simp only [State.binaryInit, State.fromInputs, List.getD]
  split_ifs with h0 h1
  · simp [h0]
  · simp [h1]
  · have hr : 2 ≤ r := by omega
    simp [List.getElem?_eq_none (by simp; omega : [y₀, y₁].length ≤ r)]

/-- Binary version of Halts.of_agreesLow: if σ agrees with fresh [y₀, y₁] on low registers,
    and P halts on [y₀, y₁], then P halts from σ. -/
theorem Halts.of_agreesLow_binary {p : Program} {y₀ y₁ : ℕ} {σ : State}
    (hagree : σ.agreesLow (State.fromInputs [y₀, y₁]) p.maxRegister)
    (hfresh : Halts p [y₀, y₁]) :
    ∃ c', Steps p ⟨0, σ⟩ c' ∧ c'.isHalted p ∧
          c'.state.read 0 = Result p [y₀, y₁] hfresh := by
  -- Get the fresh execution trace without destructing hfresh (we need it for the goal)
  let c_fresh := Classical.choose hfresh
  have hsteps_fresh : Steps p (Config.init [y₀, y₁]) c_fresh := (Classical.choose_spec hfresh).1
  have hhalted_fresh : c_fresh.isHalted p := (Classical.choose_spec hfresh).2
  -- Build config agreement: Config.init [y₀, y₁] agrees with ⟨0, σ⟩
  have hconfig_agree : (Config.init [y₀, y₁]).agreesLow ⟨0, σ⟩ p := by
    constructor
    · simp [Config.init]
    · exact hagree.symm
  -- Use Steps.preserves_agreesLow to mirror execution
  obtain ⟨c', hsteps', hagree'⟩ := Steps.preserves_agreesLow hconfig_agree hsteps_fresh
  -- c' is halted (same pc as c_fresh)
  have hhalted' : c'.isHalted p := by
    simp only [Config.isHalted, Config.agreesLow] at hagree' ⊢
    exact hagree'.1 ▸ hhalted_fresh
  -- R0 matches
  have hR0_eq : c'.state.read 0 = c_fresh.state.read 0 := by
    have hstate_agree := hagree'.2
    exact hstate_agree.symm.read_eq 0 (by omega)
  refine ⟨c', hsteps', hhalted', ?_⟩
  simp only [Result, State.output, State.read] at hR0_eq ⊢
  exact hR0_eq

/-- Binary version of Halts.to_agreesLow: if σ agrees with fresh [y₀, y₁] and p halts from σ,
    then p halts on [y₀, y₁]. -/
theorem Halts.to_agreesLow_binary {p : Program} {y₀ y₁ : ℕ} {σ : State}
    (hagree : σ.agreesLow (State.fromInputs [y₀, y₁]) p.maxRegister)
    (hσ : ∃ c, Steps p ⟨0, σ⟩ c ∧ c.isHalted p) :
    Halts p [y₀, y₁] := by
  obtain ⟨c, hsteps, hhalted⟩ := hσ
  -- Build config agreement: ⟨0, σ⟩ agrees with Config.init [y₀, y₁]
  have hconfig_agree : (⟨0, σ⟩ : Config).agreesLow (Config.init [y₀, y₁]) p := by
    constructor
    · simp [Config.init]
    · exact hagree
  -- Use Steps.preserves_agreesLow to mirror execution
  obtain ⟨c', hsteps', hagree'⟩ := Steps.preserves_agreesLow hconfig_agree hsteps
  -- c' is halted (same pc as c)
  have hhalted' : c'.isHalted p := by
    simp only [Config.isHalted, Config.agreesLow] at hagree' hhalted ⊢
    exact hagree'.1 ▸ hhalted
  exact ⟨c', hsteps', hhalted'⟩

/-! ## Main Theorems -/

/-- Specification for a binary program computing f. -/
structure BinaryProgramSpec (f : (Fin 2 → ℕ) → Part ℕ) (P : Program) : Prop where
  /-- P computes f on standard binary inputs -/
  halts_iff : ∀ y₀ y₁ : ℕ, Halts P [y₀, y₁] ↔ (f (binaryInputs y₀ y₁)).Dom
  /-- When f terminates, P returns the correct result -/
  result_eq : ∀ y₀ y₁ : ℕ, ∀ (hH : Halts P [y₀, y₁]) (hf : (f (binaryInputs y₀ y₁)).Dom),
    Result P [y₀, y₁] hH = (f (binaryInputs y₀ y₁)).get hf

/-- The composed function h(x) = f(g₀(x), g₁(x)). -/
def composeBinaryUnary (f : (Fin 2 → ℕ) → Part ℕ) (g₀ g₁ : ℕ → Part ℕ) : ℕ → Part ℕ :=
  fun x => (g₀ x).bind fun y₀ => (g₁ x).bind fun y₁ => f (binaryInputs y₀ y₁)

/-- Correctness of the composed program assuming bounded jumps.
    This is the main technical theorem. -/
theorem comp_binary_unary_bounded
    {f : (Fin 2 → ℕ) → Part ℕ} {g₀ g₁ : ℕ → Part ℕ}
    {Pf : Program} {Pg0 Pg1 : Program}
    (hPf : BinaryProgramSpec f Pf) (hPf_bounded : Pf.boundedJumps)
    (hPg0 : ProgramComputesUnary Pg0 g₀) (hPg0_bounded : Pg0.boundedJumps)
    (hPg1 : ProgramComputesUnary Pg1 g₁) (hPg1_bounded : Pg1.boundedJumps) :
    ProgramComputesUnary (binaryUnaryComposeProgram Pf Pg0 Pg1)
      (composeBinaryUnary f g₀ g₁) := by
  intro x
  refine ⟨?halts_iff, ?result_eq⟩
  case halts_iff =>
    -- H halts ↔ h(x) defined
    constructor
    · -- Forward: H halts → h(x) defined
      intro hH_halts
      -- Need to extract that g₀, g₁, and f all terminate
      sorry
    · -- Backward: h(x) defined → H halts
      intro h_dom
      simp only [composeBinaryUnary, Part.bind_dom] at h_dom
      -- Extract that g₀(x), g₁(x), and f are all defined
      obtain ⟨hg0_dom, hg1_dom, hf_dom⟩ := h_dom
      -- Define the output values
      let y₀ := (g₀ x).get hg0_dom
      let y₁ := (g₁ x).get hg1_dom
      -- Individual program halting
      have hPg0_halts : Halts Pg0 [x] := (hPg0 x).1.mpr hg0_dom
      have hPg1_halts : Halts Pg1 [x] := (hPg1 x).1.mpr hg1_dom
      have hPf_halts : Halts Pf [y₀, y₁] := (hPf.halts_iff y₀ y₁).mpr hf_dom
      -- Results from Pg0, Pg1
      have hPg0_result : Result Pg0 [x] hPg0_halts = y₀ :=
        (hPg0 x).2 hPg0_halts hg0_dom
      have hPg1_result : Result Pg1 [x] hPg1_halts = y₁ :=
        (hPg1 x).2 hPg1_halts hg1_dom
      -- Key bounds for m and safe registers
      let m := binaryUnaryM Pf Pg0 Pg1
      let saveX := binaryUnarySaveX Pf Pg0 Pg1
      let saveG0 := binaryUnarySaveG0 Pf Pg0 Pg1
      -- m ≥ all program maxRegisters
      have hm_ge_Pf := binaryUnaryM_ge_Pf Pf Pg0 Pg1
      have hm_ge_Pg0 := binaryUnaryM_ge_Pg0 Pf Pg0 Pg1
      have hm_ge_Pg1 := binaryUnaryM_ge_Pg1 Pf Pg0 Pg1
      have hm_ge_1 := binaryUnaryM_ge_one Pf Pg0 Pg1
      -- The composition chains all 5 phases
      -- Phase 1: Save x to saveX (straight-line)
      -- Phase 2: Run Pg0, save result to saveG0
      -- Phase 3: Restore x, clear scratch, run Pg1
      -- Phase 4: Setup binary inputs (R₀ := y₀, R₁ := y₁)
      -- Phase 5: Clear scratch for Pf, run Pf
      -- The full proof requires:
      -- 1. Track state through each phase
      -- 2. Show state agreement at each boundary
      -- 3. Chain using Halts.concat_continuation and steps_concat_continuation
      -- This is complex - leaving sorry for now
      sorry
  case result_eq =>
    intro hH_halts h_dom
    -- When both halt and function defined, results match
    sorry

/-- Full composition closure theorem for binary-unary composition. -/
theorem URMComputable.comp_binary_unary
    {f : (Fin 2 → ℕ) → Part ℕ} {g₀ g₁ : ℕ → Part ℕ}
    (hf : URMComputable 2 f)
    (hg0 : UnaryURMComputable g₀)
    (hg1 : UnaryURMComputable g₁) :
    UnaryURMComputable (composeBinaryUnary f g₀ g₁) := by
  -- Get witness programs
  obtain ⟨Pf, hPf⟩ := hf
  obtain ⟨Pg0, hPg0⟩ := hg0
  obtain ⟨Pg1, hPg1⟩ := hg1
  -- Use standardization to get bounded versions
  -- TODO: Once exists_boundedJumps is proven, use it here
  -- For now, we assume the witnesses already have bounded jumps
  have hPf_bounded : Pf.boundedJumps := by
    -- This follows from standardization theorem
    sorry
  have hPg0_bounded : Pg0.boundedJumps := by sorry
  have hPg1_bounded : Pg1.boundedJumps := by sorry
  -- Convert hPf to BinaryProgramSpec
  have hPf_spec : BinaryProgramSpec f Pf := by
    constructor
    · intro y₀ y₁
      exact (hPf (binaryInputs y₀ y₁)).1
    · intro y₀ y₁ hH hf_dom
      exact (hPf (binaryInputs y₀ y₁)).2 hH hf_dom
  -- Apply the bounded version
  exact ⟨binaryUnaryComposeProgram Pf Pg0 Pg1,
         comp_binary_unary_bounded hPf_spec hPf_bounded hPg0 hPg0_bounded hPg1 hPg1_bounded⟩

end Urm
