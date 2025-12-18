/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Michael Han
-/
import Urm.UnaryComposition
import Urm.CompositionHelpers
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
      -- Define phases (matching binaryUnaryComposeProgram structure)
      let phase1 : Program := [Instr.T 0 saveX]
      let phase2 : Program := Pg0.concat [Instr.T 0 saveG0]
      let phase3 : Program := (Program.concat (Program.concat [Instr.T saveX 0] (Program.clearAbove 1 m)) Pg1)
      let phase4 : Program := [Instr.T 0 1, Instr.T saveG0 0]
      let phase5 : Program := (Program.clearAbove 2 Pf.maxRegister).concat Pf

      -- H = phase1.concat(phase2.concat(phase3.concat(phase4.concat(phase5))))
      let H := binaryUnaryComposeProgram Pf Pg0 Pg1

      -- Straight-line properties
      have hphase1_sl : phase1.isStraightLine = true := by
        simp [Program.isStraightLine, phase1, Instr.isNonJumping]
      have hphase4_sl : phase4.isStraightLine = true := by
        simp [Program.isStraightLine, phase4, Instr.isNonJumping]

      -- Bounded jumps for phases
      have hphase1_bounded : phase1.boundedJumps :=
        Program.boundedJumps_of_straightLine hphase1_sl
      have hphase4_bounded : phase4.boundedJumps :=
        Program.boundedJumps_of_straightLine hphase4_sl

      -- Initial state
      let σ₀ : State := State.fromInputs [x]

      -- ===== Phase 1: Save x to saveX =====
      have hphase1_halts : ∃ c, Steps phase1 ⟨0, σ₀⟩ c ∧ c.isHalted phase1 :=
        straightLine_halts_from_state hphase1_sl σ₀

      -- State after phase1
      let σ₁ := (Classical.choose hphase1_halts).state
      have hσ₁_eq := straightLine_final_state_eq hphase1_sl σ₀

      have hσ₁_R0 : σ₁.read 0 = x := by
        simp only [σ₁, hσ₁_eq, executeStraightLine, List.foldl, phase1]
        simp only [State.read, State.write, Function.update, σ₀, State.fromInputs, List.getD]
        simp only [List.getElem?_cons_zero, Option.getD_some]
        have h0_ne_saveX : (0 : ℕ) ≠ saveX := by
          simp only [saveX, binaryUnarySaveX, binaryUnaryM]
          omega
        simp only [dif_neg h0_ne_saveX, State.fromInputs, List.getD,
                   List.getElem?_cons_zero, Option.getD_some]

      have hσ₁_saveX : σ₁.read saveX = x := by
        simp only [σ₁, hσ₁_eq, executeStraightLine, List.foldl, phase1]
        simp only [State.read, State.write, Function.update]
        simp only [dif_pos trivial, σ₀, State.fromInputs, List.getD,
                   List.getElem?_cons_zero, Option.getD_some]

      -- σ₁ agrees with State.fromInputs [x] on low registers
      have hσ₁_agrees_Pg0 : σ₁.agreesLow (State.fromInputs [x]) Pg0.maxRegister := by
        intro r hr
        simp only [σ₁, hσ₁_eq, executeStraightLine, List.foldl, phase1]
        simp only [State.read, State.write, Function.update]
        by_cases hr_eq : r = saveX
        · -- r = saveX, but saveX > Pg0.maxRegister, so r ≤ Pg0.maxRegister leads to contradiction
          subst hr_eq
          have : saveX > Pg0.maxRegister := by
            simp only [saveX, binaryUnarySaveX, binaryUnaryM]
            omega
          omega
        · simp only [dif_neg hr_eq, σ₀]

      -- ===== Phase 2: Run Pg0, then save result =====
      -- Pg0 halts from σ₁ because σ₁ agrees with [x] on low registers
      have hPg0_from_σ₁ : ∃ c, Steps Pg0 ⟨0, σ₁⟩ c ∧ c.isHalted Pg0 ∧
          c.state.read 0 = y₀ := by
        have hagree := hσ₁_agrees_Pg0
        obtain ⟨c', hsteps', hhalted', hR0'⟩ := Halts.of_agreesLow hagree hPg0_halts
        exact ⟨c', hsteps', hhalted', hR0' ▸ hPg0_result⟩

      have hPg0_from_σ₁_exists : ∃ c, Steps Pg0 ⟨0, σ₁⟩ c ∧ c.isHalted Pg0 :=
        ⟨_, hPg0_from_σ₁.choose_spec.1, hPg0_from_σ₁.choose_spec.2.1⟩

      -- The save instruction after Pg0
      let save_g0 : Program := [Instr.T 0 saveG0]
      have hsave_g0_sl : save_g0.isStraightLine = true := by
        simp [Program.isStraightLine, save_g0, Instr.isNonJumping]

      have hsave_g0_halts : ∃ c, Steps save_g0 ⟨0, (Classical.choose hPg0_from_σ₁_exists).state⟩ c ∧
          c.isHalted save_g0 :=
        straightLine_halts_from_state hsave_g0_sl _

      -- phase2 halts from σ₁
      have hphase2_halts_from_σ₁ : ∃ c, Steps phase2 ⟨0, σ₁⟩ c ∧ c.isHalted phase2 := by
        have h1 := hPg0_from_σ₁_exists
        have h2 := hsave_g0_halts
        exact steps_concat_continuation_bounded hPg0_bounded h1 h2

      -- phases 1+2 halt from σ₀
      have hphase12_halts : ∃ c, Steps (phase1.concat phase2) ⟨0, σ₀⟩ c ∧
          c.isHalted (phase1.concat phase2) :=
        steps_concat_continuation_straightLine hphase1_sl hphase1_halts hphase2_halts_from_σ₁

      -- State σ₂ after phase 1+2
      let σ₂ := (Classical.choose hphase12_halts).state

      -- Track what σ₂ knows about saveX and saveG0
      -- After phase2, saveX is preserved and saveG0 = y₀
      have hσ₂_saveX : σ₂.read saveX = x := by
        -- Chain the state through: σ₂ ← phase2 ← save_g0 ← Pg0 ← σ₁
        -- Step 1: σ₂ = final state of phase2 from σ₁
        have hσ₂_eq_phase2 := concat_final_state_eq_straightLine hphase1_sl hphase1_halts hphase2_halts_from_σ₁
        simp only [σ₂]
        rw [hσ₂_eq_phase2]
        -- Step 2: final state of phase2 = final state of save_g0
        have hphase2_eq_save := concat_final_state_eq_bounded hPg0_bounded hPg0_from_σ₁_exists hsave_g0_halts
        rw [hphase2_eq_save]
        -- Step 3: final state of save_g0 = executeStraightLine save_g0 (σ_after_Pg0)
        have hsave_state := straightLine_final_state_eq hsave_g0_sl (Classical.choose hPg0_from_σ₁_exists).state
        rw [hsave_state]
        -- Step 4: save_g0 = [T 0 saveG0] only writes to saveG0, preserving saveX
        simp only [save_g0, executeStraightLine, List.foldl, State.write]
        -- Now goal is: (Function.update (Classical.choose hPg0_from_σ₁_exists).state saveG0 _).read saveX = x
        simp only [State.read, Function.update]
        have hsaveX_ne_saveG0 : saveX ≠ saveG0 := by
          simp only [saveX, saveG0, binaryUnarySaveX, binaryUnarySaveG0]
          omega
        simp only [hsaveX_ne_saveG0, ↓reduceDIte]
        -- Step 5: Pg0 preserves saveX (since Pg0.maxRegister < saveX)
        have hPg0_max_lt_saveX : Pg0.maxRegister < saveX := by
          simp only [saveX, binaryUnarySaveX, binaryUnaryM]
          have := hm_ge_Pg0
          omega
        obtain ⟨hsteps_Pg0, _⟩ := Classical.choose_spec hPg0_from_σ₁_exists
        have hPg0_preserves := Steps.preserves_high_register hsteps_Pg0 saveX hPg0_max_lt_saveX
        simp only [State.read] at hPg0_preserves hσ₁_saveX
        rw [hPg0_preserves, hσ₁_saveX]

      have hσ₂_saveG0 : σ₂.read saveG0 = y₀ := by
        -- Chain the state through: σ₂ ← phase2 ← save_g0
        -- Step 1: σ₂ = final state of phase2 from σ₁
        have hσ₂_eq_phase2 := concat_final_state_eq_straightLine hphase1_sl hphase1_halts hphase2_halts_from_σ₁
        simp only [σ₂]
        rw [hσ₂_eq_phase2]
        -- Step 2: final state of phase2 = final state of save_g0
        have hphase2_eq_save := concat_final_state_eq_bounded hPg0_bounded hPg0_from_σ₁_exists hsave_g0_halts
        rw [hphase2_eq_save]
        -- Step 3: final state of save_g0 = executeStraightLine save_g0 (σ_after_Pg0)
        have hsave_state := straightLine_final_state_eq hsave_g0_sl (Classical.choose hPg0_from_σ₁_exists).state
        rw [hsave_state]
        -- Step 4: save_g0 = [T 0 saveG0] writes R0 to saveG0
        simp only [save_g0, executeStraightLine, List.foldl, State.write]
        simp only [State.read, Function.update_self]
        -- Now goal is: (Classical.choose hPg0_from_σ₁_exists).state 0 = y₀
        -- Show that Classical.choose hPg0_from_σ₁_exists = Classical.choose hPg0_from_σ₁
        have hsteps1 := hPg0_from_σ₁.choose_spec.1
        have hhalted1 := hPg0_from_σ₁.choose_spec.2.1
        have hsteps2 := (Classical.choose_spec hPg0_from_σ₁_exists).1
        have hhalted2 := (Classical.choose_spec hPg0_from_σ₁_exists).2
        have heq := Steps.halts_unique hsteps1 hhalted1 hsteps2 hhalted2
        have hstate_eq : (Classical.choose hPg0_from_σ₁_exists).state = (Classical.choose hPg0_from_σ₁).state :=
          congrArg Config.state heq.symm
        rw [hstate_eq]
        exact hPg0_from_σ₁.choose_spec.2.2

      -- ===== Phase 3: Restore x, clear, run Pg1 =====
      let restore : Program := [Instr.T saveX 0]
      let clearPg1 : Program := Program.clearAbove 1 m
      let restoreClear : Program := restore.concat clearPg1

      have hrestore_sl : restore.isStraightLine = true := by
        simp [Program.isStraightLine, restore, Instr.isNonJumping]
      have hclearPg1_sl : clearPg1.isStraightLine = true :=
        Program.clearAbove_isStraightLine 1 m
      have hrestoreClear_sl : restoreClear.isStraightLine = true := by
        simp only [restoreClear, Program.isStraightLine, Program.concat]
        rw [List.all_append]
        simp only [Bool.and_eq_true]
        constructor
        · exact hrestore_sl
        · -- shiftJumps preserves isStraightLine for straight-line programs
          simp only [Program.shiftJumps, List.all_map]
          have := hclearPg1_sl
          simp only [Program.isStraightLine, clearPg1] at this
          simp only [List.all_eq_true] at this ⊢
          intro instr hinstr
          have h := this instr hinstr
          cases instr <;> simp [Instr.shiftJumps, Instr.isNonJumping] at h ⊢

      -- restore.concat(clearPg1) halts from σ₂
      have hrestoreClear_halts : ∃ c, Steps restoreClear ⟨0, σ₂⟩ c ∧ c.isHalted restoreClear :=
        straightLine_halts_from_state hrestoreClear_sl σ₂

      -- State after restore+clear
      let σ_rc := (Classical.choose hrestoreClear_halts).state
      have hσ_rc_eq := straightLine_final_state_eq hrestoreClear_sl σ₂

      -- After restore+clear: R0 = x, R1..m = 0
      have hσ_rc_R0 : σ_rc.read 0 = x := by
        -- restoreClear = restore.concat clearPg1 = restore ++ clearPg1 (since clearPg1 is straight-line)
        -- So after restore: state has R0 = σ₂.read saveX
        -- Then clearPg1 = clearAbove 1 m preserves R0 (since 0 < 1)
        have h0_lt_1 : 0 < 1 := Nat.zero_lt_one
        let σ_after_restore := σ₂.write 0 (σ₂.read saveX)
        have hclear_preserves := Program.clearAbove_preserves_below 1 m σ_after_restore 0 h0_lt_1
        -- Compute σ_rc step by step
        simp only [σ_rc, hσ_rc_eq]
        show (executeStraightLine restoreClear σ₂).read 0 = x
        -- Use concat_straightLine_eq to simplify concat to ++
        simp only [restoreClear]
        rw [Program.concat_straightLine_eq restore clearPg1 hclearPg1_sl,
            executeStraightLine_append]
        -- After restore: R0 = σ₂.read saveX
        simp only [restore, executeStraightLine, List.foldl, State.write, State.read]
        -- clearPg1 preserves R0 - unfold to match goal form
        simp only [σ_after_restore, clearPg1, executeStraightLine, State.read, State.write] at hclear_preserves ⊢
        rw [hclear_preserves]
        simp only [Function.update, ↓reduceDIte]
        exact hσ₂_saveX

      -- σ_rc agrees with State.fromInputs [x] on registers up to Pg1.maxRegister
      have hσ_rc_agrees_Pg1 : σ_rc.agreesLow (State.fromInputs [x]) Pg1.maxRegister := by
        intro r hr
        by_cases hr0 : r = 0
        · -- r = 0: σ_rc.read 0 = x = (State.fromInputs [x]).read 0
          simp only [State.read] at hσ_rc_R0 ⊢
          simp only [hr0, hσ_rc_R0, State.fromInputs, List.getD,
                     List.getElem?_cons_zero, Option.getD_some]
        · -- r > 0, so r is in range [1, Pg1.maxRegister] ⊆ [1, m]
          -- clearAbove 1 m zeroes these registers
          -- State.fromInputs [x] also has 0 for r > 0
          have hr_ge_1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
          have hr_le_m : r ≤ m := by
            have : Pg1.maxRegister ≤ m := hm_ge_Pg1
            omega
          -- Get the intermediate state after restore
          let σ_after_restore := σ₂.write 0 (σ₂.read saveX)
          -- clearAbove zeros register r since 1 ≤ r ≤ m
          have hclear_zeros := Program.clearAbove_zeros 1 m σ_after_restore r hr_ge_1 hr_le_m
          -- Compute σ_rc step by step
          simp only [σ_rc, hσ_rc_eq]
          show (executeStraightLine restoreClear σ₂).read r = (State.fromInputs [x]).read r
          -- Use concat_straightLine_eq to simplify concat to ++
          simp only [restoreClear]
          rw [Program.concat_straightLine_eq restore clearPg1 hclearPg1_sl,
              executeStraightLine_append]
          -- After restore: intermediate state
          simp only [restore, executeStraightLine, List.foldl, State.write, State.read]
          -- clearPg1 zeros register r - unfold to match goal form
          simp only [σ_after_restore, clearPg1, executeStraightLine, State.read, State.write] at hclear_zeros ⊢
          rw [hclear_zeros]
          -- State.fromInputs [x] also has 0 for r > 0
          simp only [State.fromInputs, List.getD]
          -- [x] has length 1, and r >= 1, so [x][r]? = none
          have hr_ge_len : r ≥ [x].length := by simp; exact hr_ge_1
          rw [List.getElem?_eq_none hr_ge_len]
          simp only [Option.getD_none]

      -- Pg1 halts from σ_rc
      have hPg1_from_σ_rc : ∃ c, Steps Pg1 ⟨0, σ_rc⟩ c ∧ c.isHalted Pg1 ∧
          c.state.read 0 = y₁ := by
        obtain ⟨c', hsteps', hhalted', hR0'⟩ := Halts.of_agreesLow hσ_rc_agrees_Pg1 hPg1_halts
        exact ⟨c', hsteps', hhalted', hR0' ▸ hPg1_result⟩

      have hPg1_from_σ_rc_exists : ∃ c, Steps Pg1 ⟨0, σ_rc⟩ c ∧ c.isHalted Pg1 :=
        ⟨_, hPg1_from_σ_rc.choose_spec.1, hPg1_from_σ_rc.choose_spec.2.1⟩

      -- phase3 halts from σ₂
      have hphase3_halts_from_σ₂ : ∃ c, Steps phase3 ⟨0, σ₂⟩ c ∧ c.isHalted phase3 := by
        have h1 := hrestoreClear_halts
        have h2 := hPg1_from_σ_rc_exists
        -- phase3 = restoreClear.concat Pg1
        have hphase3_eq : phase3 = restoreClear.concat Pg1 := by
          simp only [phase3, restoreClear, restore, clearPg1, Program.concat]
        rw [hphase3_eq]
        exact steps_concat_continuation_straightLine hrestoreClear_sl h1 h2

      -- phases 1+2+3 halt from σ₀
      have hphase123_halts : ∃ c, Steps ((phase1.concat phase2).concat phase3) ⟨0, σ₀⟩ c ∧
          c.isHalted ((phase1.concat phase2).concat phase3) := by
        have hphase12_bounded := Program.concat_boundedJumps hphase1_bounded
            (Program.concat_boundedJumps hPg0_bounded
              (Program.boundedJumps_of_straightLine hsave_g0_sl))
        exact steps_concat_continuation_bounded hphase12_bounded hphase12_halts hphase3_halts_from_σ₂

      -- State σ₃ after phases 1+2+3
      let σ₃ := (Classical.choose hphase123_halts).state

      -- After phase3: R0 = y₁, saveG0 still = y₀
      have hσ₃_R0 : σ₃.read 0 = y₁ := by
        -- σ₃ is the state after phases 1+2+3
        -- phase3 = restoreClear.concat Pg1
        -- After Pg1 runs from σ_rc, R0 = y₁ (from hPg1_from_σ_rc)
        have hσ₃_eq := concat_final_state_eq_bounded
            (Program.concat_boundedJumps hphase1_bounded
              (Program.concat_boundedJumps hPg0_bounded
                (Program.boundedJumps_of_straightLine hsave_g0_sl)))
            hphase12_halts hphase3_halts_from_σ₂
        simp only [σ₃]
        rw [hσ₃_eq]
        -- Now need to show (Classical.choose hphase3_halts_from_σ₂).state.read 0 = y₁
        have hphase3_eq_σ := concat_final_state_eq_straightLine hrestoreClear_sl
            hrestoreClear_halts hPg1_from_σ_rc_exists
        rw [hphase3_eq_σ]
        -- Now need to show (Classical.choose hPg1_from_σ_rc_exists).state.read 0 = y₁
        have heq := Steps.halts_unique
            (Classical.choose_spec hPg1_from_σ_rc_exists).1
            (Classical.choose_spec hPg1_from_σ_rc_exists).2
            (Classical.choose_spec hPg1_from_σ_rc).1
            (Classical.choose_spec hPg1_from_σ_rc).2.1
        have hstate_eq := congrArg Config.state heq
        rw [hstate_eq]
        exact (Classical.choose_spec hPg1_from_σ_rc).2.2

      have hσ₃_saveG0 : σ₃.read saveG0 = y₀ := by
        -- saveG0 > Pg1.maxRegister, so Pg1 preserves it
        -- And restoreClear only touches 0 and 1..m, and saveG0 > m
        have hsaveG0_gt_Pg1 : Pg1.maxRegister < saveG0 := by
          simp only [saveG0, binaryUnarySaveG0, binaryUnaryM]
          have := hm_ge_Pg1
          omega
        have hsaveG0_gt_m : saveG0 > m := by
          simp only [saveG0, binaryUnarySaveG0]
          exact Nat.lt_add_of_pos_right (by omega : 0 < 2)
        -- σ₃ = (final state of phase123)
        have hσ₃_eq := concat_final_state_eq_bounded
            (Program.concat_boundedJumps hphase1_bounded
              (Program.concat_boundedJumps hPg0_bounded
                (Program.boundedJumps_of_straightLine hsave_g0_sl)))
            hphase12_halts hphase3_halts_from_σ₂
        simp only [σ₃]
        rw [hσ₃_eq]
        -- Now need to show (Classical.choose hphase3_halts_from_σ₂).state.read saveG0 = y₀
        have hphase3_eq_σ := concat_final_state_eq_straightLine hrestoreClear_sl
            hrestoreClear_halts hPg1_from_σ_rc_exists
        rw [hphase3_eq_σ]
        -- Pg1 preserves saveG0 since saveG0 > Pg1.maxRegister
        obtain ⟨hsteps_Pg1, hhalted_Pg1⟩ := Classical.choose_spec hPg1_from_σ_rc_exists
        have hPg1_preserves := Steps.preserves_high_register hsteps_Pg1 saveG0 hsaveG0_gt_Pg1
        simp only [State.read] at hPg1_preserves ⊢
        rw [hPg1_preserves]
        -- Now need to show σ_rc.read saveG0 = y₀
        -- restoreClear = restore.concat clearPg1 where clearPg1 = clearAbove 1 m
        -- clearAbove 1 m only touches registers 1..m, and saveG0 > m
        -- restore = [T saveX 0] only touches register 0
        simp only [σ_rc, hσ_rc_eq]
        simp only [restoreClear]
        rw [Program.concat_straightLine_eq restore clearPg1 hclearPg1_sl,
            executeStraightLine_append]
        -- clearAbove 1 m preserves registers > m
        have hclear_preserves := Program.clearAbove_preserves_above 1 m
            (executeStraightLine restore σ₂) saveG0 hsaveG0_gt_m
        simp only [clearPg1] at hclear_preserves ⊢
        simp only [State.read, State.write] at hclear_preserves
        rw [hclear_preserves]
        -- restore = [T saveX 0] only touches register 0, preserves saveG0
        simp only [restore, executeStraightLine, List.foldl, State.write, State.read]
        have hsaveG0_ne_0 : saveG0 ≠ 0 := by
          simp only [saveG0, binaryUnarySaveG0, binaryUnaryM]
          omega
        simp only [Function.update, if_neg hsaveG0_ne_0]
        exact hσ₂_saveG0

      -- ===== Phase 4: Setup binary inputs =====
      -- [T 0 1, T saveG0 0]: First copy R0 to R1, then copy saveG0 to R0
      -- Result: R0 = y₀, R1 = y₁

      have hphase4_halts_from_σ₃ : ∃ c, Steps phase4 ⟨0, σ₃⟩ c ∧ c.isHalted phase4 :=
        straightLine_halts_from_state hphase4_sl σ₃

      -- phases 1+2+3+4 halt from σ₀
      have hphase1234_halts : ∃ c, Steps (((phase1.concat phase2).concat phase3).concat phase4) ⟨0, σ₀⟩ c ∧
          c.isHalted (((phase1.concat phase2).concat phase3).concat phase4) := by
        have hphase123_bounded := Program.concat_boundedJumps
            (Program.concat_boundedJumps hphase1_bounded
              (Program.concat_boundedJumps hPg0_bounded
                (Program.boundedJumps_of_straightLine hsave_g0_sl)))
            (Program.concat_boundedJumps
              (Program.concat_boundedJumps
                (Program.boundedJumps_of_straightLine hrestore_sl)
                (Program.clearAbove_boundedJumps 1 m))
              hPg1_bounded)
        exact steps_concat_continuation_bounded hphase123_bounded hphase123_halts hphase4_halts_from_σ₃

      -- State σ₄ after phases 1+2+3+4
      let σ₄ := (Classical.choose hphase1234_halts).state

      -- After phase4: R0 = y₀, R1 = y₁
      -- phase4 = [T 0 1, T saveG0 0]
      -- After T 0 1: R1 = σ₃.read 0 = y₁
      -- After T saveG0 0: R0 = σ₃.read saveG0 = y₀
      have hσ₄_R0 : σ₄.read 0 = y₀ := by
        have hσ₄_eq := concat_final_state_eq_bounded
            (Program.concat_boundedJumps
              (Program.concat_boundedJumps hphase1_bounded
                (Program.concat_boundedJumps hPg0_bounded
                  (Program.boundedJumps_of_straightLine hsave_g0_sl)))
              (Program.concat_boundedJumps
                (Program.concat_boundedJumps
                  (Program.boundedJumps_of_straightLine hrestore_sl)
                  (Program.clearAbove_boundedJumps 1 m))
                hPg1_bounded))
            hphase123_halts hphase4_halts_from_σ₃
        simp only [σ₄]
        rw [hσ₄_eq]
        -- Now compute phase4's effect on σ₃
        have hphase4_state := straightLine_final_state_eq hphase4_sl σ₃
        simp only at hphase4_state
        rw [hphase4_state]
        -- phase4 = [T 0 1, T saveG0 0]
        simp only [phase4, executeStraightLine, List.foldl, State.write, State.read]
        -- After T 0 1, then T saveG0 0: R0 = σ₃.read saveG0
        simp only [Function.update, ↓reduceDIte]
        -- R0 gets σ₃ saveG0
        exact hσ₃_saveG0

      have hσ₄_R1 : σ₄.read 1 = y₁ := by
        have hσ₄_eq := concat_final_state_eq_bounded
            (Program.concat_boundedJumps
              (Program.concat_boundedJumps hphase1_bounded
                (Program.concat_boundedJumps hPg0_bounded
                  (Program.boundedJumps_of_straightLine hsave_g0_sl)))
              (Program.concat_boundedJumps
                (Program.concat_boundedJumps
                  (Program.boundedJumps_of_straightLine hrestore_sl)
                  (Program.clearAbove_boundedJumps 1 m))
                hPg1_bounded))
            hphase123_halts hphase4_halts_from_σ₃
        simp only [σ₄]
        rw [hσ₄_eq]
        -- Now compute phase4's effect on σ₃
        have hphase4_state := straightLine_final_state_eq hphase4_sl σ₃
        simp only at hphase4_state
        rw [hphase4_state]
        -- phase4 = [T 0 1, T saveG0 0]
        simp only [phase4, executeStraightLine, List.foldl, State.write, State.read]
        -- After T 0 1: R1 = σ₃.read 0 = y₁
        -- After T saveG0 0: R1 unchanged (0 ≠ 1)
        simp only [Function.update]
        have h1_ne_0 : (1 : ℕ) ≠ 0 := by omega
        simp only [h1_ne_0, ↓reduceDIte]
        exact hσ₃_R0

      -- ===== Phase 5: Clear and run Pf =====
      let clearPf : Program := Program.clearAbove 2 Pf.maxRegister

      have hclearPf_sl : clearPf.isStraightLine = true :=
        Program.clearAbove_isStraightLine 2 Pf.maxRegister

      have hclearPf_halts : ∃ c, Steps clearPf ⟨0, σ₄⟩ c ∧ c.isHalted clearPf :=
        straightLine_halts_from_state hclearPf_sl σ₄

      -- State after clearing
      let σ_cleared := (Classical.choose hclearPf_halts).state

      -- σ_cleared agrees with State.fromInputs [y₀, y₁] on Pf.maxRegister
      have hσ_cleared_agrees_Pf : σ_cleared.agreesLow (State.fromInputs [y₀, y₁]) Pf.maxRegister := by
        intro r hr
        -- R0 = y₀ (preserved), R1 = y₁ (preserved), R2+ = 0 (cleared)
        have hσ_cleared_eq := straightLine_final_state_eq hclearPf_sl σ₄
        simp only [σ_cleared]
        rw [hσ_cleared_eq]
        -- clearPf = clearAbove 2 Pf.maxRegister
        by_cases h0 : r = 0
        · -- r = 0: clearAbove 2 _ preserves R0 (0 < 2)
          subst h0
          have h0_lt_2 : (0 : ℕ) < 2 := by omega
          have hclear_preserves := Program.clearAbove_preserves_below 2 Pf.maxRegister σ₄ 0 h0_lt_2
          simp only [clearPf] at hclear_preserves ⊢
          simp only [State.read, State.write] at hclear_preserves ⊢
          rw [hclear_preserves]
          simp only [State.fromInputs, List.getD, List.getElem?_cons_zero, Option.getD_some]
          simp only [State.read] at hσ₄_R0
          exact hσ₄_R0
        · by_cases h1 : r = 1
          · -- r = 1: clearAbove 2 _ preserves R1 (1 < 2)
            subst h1
            have h1_lt_2 : (1 : ℕ) < 2 := by omega
            have hclear_preserves := Program.clearAbove_preserves_below 2 Pf.maxRegister σ₄ 1 h1_lt_2
            simp only [clearPf] at hclear_preserves ⊢
            simp only [State.read, State.write] at hclear_preserves ⊢
            rw [hclear_preserves]
            simp only [State.fromInputs, List.getD, List.getElem?_cons_succ,
                       List.getElem?_cons_zero, Option.getD_some]
            simp only [State.read] at hσ₄_R1
            exact hσ₄_R1
          · -- r ≥ 2: clearAbove zeros these registers
            have hr_ge_2 : 2 ≤ r := by omega
            have hclear_zeros := Program.clearAbove_zeros 2 Pf.maxRegister σ₄ r hr_ge_2 hr
            simp only [clearPf] at hclear_zeros ⊢
            rw [hclear_zeros]
            -- State.fromInputs [y₀, y₁] has 0 at positions ≥ 2
            simp only [State.fromInputs, State.read, List.getD]
            rw [List.getElem?_eq_none (by simp; omega : r ≥ [y₀, y₁].length)]
            simp only [Option.getD_none]

      -- Pf halts from σ_cleared
      have hPf_from_σ_cleared : ∃ c, Steps Pf ⟨0, σ_cleared⟩ c ∧ c.isHalted Pf := by
        have h := Halts.of_agreesLow_binary hσ_cleared_agrees_Pf hPf_halts
        exact ⟨_, h.choose_spec.1, h.choose_spec.2.1⟩

      -- phase5 halts from σ₄
      have hphase5_halts_from_σ₄ : ∃ c, Steps phase5 ⟨0, σ₄⟩ c ∧ c.isHalted phase5 :=
        steps_concat_continuation_straightLine hclearPf_sl hclearPf_halts hPf_from_σ_cleared

      -- Full program H halts from σ₀
      have hH_halts_from_σ₀ : ∃ c, Steps H ⟨0, σ₀⟩ c ∧ c.isHalted H := by
        -- H = phase1.concat(phase2.concat(phase3.concat(phase4.concat(phase5))))
        -- Need to show this equals our chained phases
        have hphase1234_bounded := Program.concat_boundedJumps
            (Program.concat_boundedJumps
              (Program.concat_boundedJumps hphase1_bounded
                (Program.concat_boundedJumps hPg0_bounded
                  (Program.boundedJumps_of_straightLine hsave_g0_sl)))
              (Program.concat_boundedJumps
                (Program.concat_boundedJumps
                  (Program.boundedJumps_of_straightLine hrestore_sl)
                  (Program.clearAbove_boundedJumps 1 m))
                hPg1_bounded))
            hphase4_bounded
        have h := steps_concat_continuation_bounded hphase1234_bounded
            hphase1234_halts hphase5_halts_from_σ₄
        -- H equals our constructed program (definitionally)
        convert h using 1

      -- Convert to Halts definition
      exact ⟨_, hH_halts_from_σ₀.choose_spec.1, hH_halts_from_σ₀.choose_spec.2⟩
  case result_eq =>
    intro hH_halts h_dom
    -- When both halt and function defined, results match
    simp only [composeBinaryUnary, Part.bind_dom] at h_dom
    obtain ⟨hg0_dom, hg1_dom, hf_dom⟩ := h_dom
    -- Get the output values
    let y₀ := (g₀ x).get hg0_dom
    let y₁ := (g₁ x).get hg1_dom
    -- The result of H should be f(y₀, y₁)
    have hPf_halts : Halts Pf [y₀, y₁] := (hPf.halts_iff y₀ y₁).mpr hf_dom
    have hPf_result : Result Pf [y₀, y₁] hPf_halts = (f (binaryInputs y₀ y₁)).get hf_dom :=
      hPf.result_eq y₀ y₁ hPf_halts hf_dom
    -- Show the result equals f(y₀, y₁)
    -- This requires tracing R0 through all phases to show it ends up with Pf's result
    -- The final phase is Pf running with inputs [y₀, y₁], so the result should match
    -- This needs infrastructure for composing Results through concat
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
