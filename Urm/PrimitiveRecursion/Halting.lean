/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.PrimitiveRecursion.Preservation
import Urm.Composition.Helpers
import Urm.Embeddings
import Urm.Shift
import Urm.Halting.Common

/-! # Halting Proofs for Primitive Recursion

This file proves the halting properties of the primitive recursion witness program.

## Main results

- `primitiveRecursionProgram_halts`: If Pr domain, program halts
- `primitiveRecursionProgram_halts_imp_dom`: If program halts, Pr domain
-/

namespace Urm

open Program

/-! ## Embedding lemmas -/

/-- Setup phase is embedded at the start of the program. -/
theorem prSetupPhase_embed (n : ℕ) (pF pG : Program) :
    ∀ i, i < (prSetupPhase n pF pG).length →
    (primitiveRecursionProgram n pF pG).getInstr i = (prSetupPhase n pF pG).getInstr i := by
  intro i hi
  simp only [primitiveRecursionProgram, getInstr, List.getElem?_append, prSetupPhase_length,
    List.length_append, prBaseCasePhase_length, prLoopCheck_length, prLoopBody_length] at *
  split_ifs <;> first | rfl | omega

/-- Base case prologue is embedded after setup phase. -/
theorem prBaseCasePrologue_embed (n : ℕ) (pF pG : Program) :
    ∀ i, i < (prBaseCasePrologue n pF pG).length →
    (primitiveRecursionProgram n pF pG).getInstr (prBaseCasePC n + i) =
      (prBaseCasePrologue n pF pG).getInstr i := by
  intro i hi
  simp only [primitiveRecursionProgram, prBaseCasePC, prBaseCasePhase, getInstr, List.getElem?_append,
    prSetupPhase_length, prSetupPhaseLength, prBaseCasePrologue_length, prBaseCasePrologueLength,
    List.length_append, prLoopCheck_length, prLoopBody_length, shiftJumps_length] at *
  split_ifs <;> first | omega | (congr 1; omega)

/-- Shifted pF is embedded in the base case phase. -/
theorem prPF_shiftJumps_embed (n : ℕ) (pF pG : Program) :
    ∀ i, i < pF.length →
    (primitiveRecursionProgram n pF pG).getInstr (prPFOffset n pF pG + i) =
      (pF.shiftJumps (prPFOffset n pF pG)).getInstr i := by
  intro i hi
  simp only [primitiveRecursionProgram, prPFOffset, prBaseCasePhase, getInstr, List.getElem?_append,
    prSetupPhase_length, prSetupPhaseLength, prBaseCasePrologueLength, prBaseCasePrologue_length,
    shiftJumps_length, List.length_append, prLoopCheck_length, prLoopBody_length]
  split_ifs <;> try omega
  simp only [shiftJumps, List.getElem?_map]
  congr 2; omega

/-- Loop check instruction embedding. -/
theorem prLoopCheck_embed (n : ℕ) (pF pG : Program) :
    (primitiveRecursionProgram n pF pG).getInstr (prLoopCheckPC n pF pG) =
      some (Instr.J (prCounterReg n pF pG) (prSavedYReg n pF pG) (prOutputPC n pF pG)) :=
  instr_at_loopCheck n pF pG

/-- Loop prologue is embedded at the start of loop body. -/
theorem prLoopPrologue_embed (n : ℕ) (pF pG : Program) :
    ∀ i, i < (prLoopPrologue n pF pG).length →
    (primitiveRecursionProgram n pF pG).getInstr (prLoopBodyPC n pF pG + i) =
      (prLoopPrologue n pF pG).getInstr i := by
  intro i hi
  simp only [primitiveRecursionProgram, prLoopBodyPC_eq, prLoopBody, getInstr, List.getElem?_append,
    prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length, prLoopPrologue_length,
    List.length_append, shiftJumps_length, prLoopEpilogue_length] at *
  split_ifs <;> first | omega | (congr 1; omega)

/-- Shifted pG is embedded in the loop body. -/
theorem prPG_shiftJumps_embed (n : ℕ) (pF pG : Program) :
    ∀ i, i < pG.length →
    (primitiveRecursionProgram n pF pG).getInstr (prPGOffset n pF pG + i) =
      (pG.shiftJumps (prPGOffset n pF pG)).getInstr i := by
  intro i hi
  simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody, getInstr,
    List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length,
    prLoopPrologue_length, shiftJumps_length, List.length_append, prLoopEpilogue_length]
  split_ifs <;> try omega
  simp only [shiftJumps, List.getElem?_map]
  congr 2; omega

/-- Output phase is at outputPC. -/
theorem prOutputPhase_embed (n : ℕ) (pF pG : Program) :
    (primitiveRecursionProgram n pF pG).getInstr (prOutputPC n pF pG) =
      some (Instr.T (prAccumulatorReg n pF pG) 0) :=
  instr_at_output n pF pG

/-! ## Setup Phase Execution -/

/-- Result of executing the setup phase. -/
structure PrSetupPhaseResult (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ) where
  config : Config
  steps : Steps (primitiveRecursionProgram n pF pG) (Config.init (List.ofFn (Fin.snoc inputs y))) config
  pc_eq : config.pc = prBaseCasePC n
  savedInputs_eq : ∀ i : Fin n, config.state.read (prSavedInputsStart n pF pG + i) = inputs i
  savedY_eq : config.state.read (prSavedYReg n pF pG) = y
  counter_eq : config.state.read (prCounterReg n pF pG) = 0
  zero_eq : config.state.read (prZeroReg n pF pG) = 0

/-- Execute the setup phase. -/
noncomputable def prExecuteSetupPhase (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ) :
    PrSetupPhaseResult n pF pG inputs y :=
  let hsl_setup := prSetupPhase_isStraightLine n pF pG
  let initState := State.fromInputs (List.ofFn (Fin.snoc inputs y))
  let setupResult := straightLineExec hsl_setup initState
  let cSetup := setupResult.config
  let hSetup_steps := setupResult.steps
  let hSetup_halted := setupResult.halted
  let hSetup_pc := setupResult.pc_eq

  -- Lift setup steps to primitiveRecursionProgram
  let hSetup_steps_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨0, initState⟩
      ⟨(prSetupPhase n pF pG).length, cSetup.state⟩ := by
    have hembed : ∀ i, i < (prSetupPhase n pF pG).length →
        (primitiveRecursionProgram n pF pG).getInstr (0 + i) =
        (prSetupPhase n pF pG).getInstr i := by
      intro i hi
      simp only [Nat.zero_add]
      exact prSetupPhase_embed n pF pG i hi
    have h := Steps.straightLine_at_offset 0 hsl_setup hembed hSetup_steps
    simp only [Nat.zero_add] at h
    rw [hSetup_pc] at h; exact h

  -- Establish invariants using Preservation lemmas
  let hSavedInputs : ∀ i : Fin n, cSetup.state.read (prSavedInputsStart n pF pG + i) = inputs i :=
    fun i => prSetupPhase_saves_inputs n pF pG inputs y initState rfl cSetup hSetup_steps hSetup_halted i
  let hSavedY : cSetup.state.read (prSavedYReg n pF pG) = y :=
    prSetupPhase_saves_y n pF pG inputs y initState rfl cSetup hSetup_steps hSetup_halted
  let hCounter : cSetup.state.read (prCounterReg n pF pG) = 0 :=
    prSetupPhase_counter_zero n pF pG inputs y initState rfl cSetup hSetup_steps hSetup_halted
  let hZero : cSetup.state.read (prZeroReg n pF pG) = 0 :=
    prSetupPhase_zero_zero n pF pG inputs y initState rfl cSetup hSetup_steps hSetup_halted

  -- PC after setup = prBaseCasePC
  let hSetup_pc_basecase : (prSetupPhase n pF pG).length = prBaseCasePC n := by
    simp only [prBaseCasePC, prSetupPhase_length]

  { config := ⟨prBaseCasePC n, cSetup.state⟩
    steps := by rw [← hSetup_pc_basecase]; exact hSetup_steps_lifted
    pc_eq := rfl
    savedInputs_eq := hSavedInputs
    savedY_eq := hSavedY
    counter_eq := hCounter
    zero_eq := hZero }

/-! ## Base Case Phase Execution -/

/-- Result of executing the base case phase. -/
structure PrBaseCasePhaseResult (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (hpF_halts : Halts pF (List.ofFn inputs)) where
  config : Config
  steps : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩ config
  pc_eq : config.pc = prLoopCheckPC n pF pG
  accumulator_eq : config.state.read (prAccumulatorReg n pF pG) = Result pF (List.ofFn inputs) hpF_halts
  savedInputs_preserved : ∀ i : Fin n, config.state.read (prSavedInputsStart n pF pG + i) =
    s.read (prSavedInputsStart n pF pG + i)
  savedY_preserved : config.state.read (prSavedYReg n pF pG) = s.read (prSavedYReg n pF pG)
  counter_preserved : config.state.read (prCounterReg n pF pG) = s.read (prCounterReg n pF pG)
  zero_preserved : config.state.read (prZeroReg n pF pG) = s.read (prZeroReg n pF pG)

/-- Execute the base case phase. -/
noncomputable def prExecuteBaseCasePhase (n : ℕ) (pF pG : Program) (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (y : ℕ) (s : State)
    (hs_saved : ∀ i : Fin n, s.read (prSavedInputsStart n pF pG + i) = inputs i)
    (hpF_halts : Halts pF (List.ofFn inputs)) :
    PrBaseCasePhaseResult n pF pG inputs y s hpF_halts := by
  -- Phase 1: Execute prBaseCasePrologue (straight-line)
  have hsl_prologue := prBaseCasePrologue_isStraightLine n pF pG
  let prologueResult := straightLineExec hsl_prologue s
  let c_prologue := prologueResult.config
  let hsteps_prologue := prologueResult.steps
  let hhalted_prologue := prologueResult.halted
  let hpc_prologue := prologueResult.pc_eq

  -- Lift prologue steps to primitiveRecursionProgram
  have hembed_prologue : ∀ i, i < (prBaseCasePrologue n pF pG).length →
      (primitiveRecursionProgram n pF pG).getInstr (prBaseCasePC n + i) =
      (prBaseCasePrologue n pF pG).getInstr i := prBaseCasePrologue_embed n pF pG
  have hsteps_prologue_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩
      ⟨prBaseCasePC n + c_prologue.pc, c_prologue.state⟩ :=
    Steps.straightLine_at_offset (prBaseCasePC n) hsl_prologue hembed_prologue hsteps_prologue

  -- After prologue, PC is at prPFOffset
  have hpc_after_prologue : prBaseCasePC n + c_prologue.pc = prPFOffset n pF pG := by
    simp only [prBaseCasePC, prPFOffset, prSetupPhaseLength, prBaseCasePrologueLength]
    rw [hpc_prologue, prBaseCasePrologue_length, prBaseCasePrologueLength]
  rw [hpc_after_prologue] at hsteps_prologue_lifted

  -- Phase 2: Execute pF (shifted)
  -- After prologue, R[0..n-1] = inputs (restored from saved copies)
  -- pF executes and produces result in R[0]

  -- Get pF halting configuration
  let cpF := Classical.choose hpF_halts
  have hspec_pF := Classical.choose_spec hpF_halts
  let hsteps_pF := hspec_pF.1
  let hhalted_pF := hspec_pF.2

  -- After prologue, R[0..n-1] = inputs (restored from saved copies) and R[n..base] = 0
  have hR_after_prologue : ∀ i : Fin n, c_prologue.state.read i = inputs i := by
    intro i
    have h1 := prBaseCasePrologue_restores_inputs n pF pG s c_prologue hsteps_prologue hhalted_prologue i
    rw [h1, hs_saved i]

  -- State agreement: c_prologue.state agrees with initState on 0..pF.maxRegister
  let initState := (Config.init (List.ofFn inputs)).state
  have hagree_pF : c_prologue.state.agreeOn initState 0 pF.maxRegister :=
    agreeOn_after_copy_inputs (base := primitiveRecursionBase n pF pG)
      (fun j hj => hR_after_prologue ⟨j, hj⟩)
      (fun r hr_ge hr_le => prBaseCasePrologue_clears_above_n n pF pG s c_prologue
        hsteps_prologue hhalted_prologue r hr_ge hr_le)
      (primitiveRecursionBase_ge_pF n pF pG)

  -- Define c₂ to use agreeOn
  let c₂ : Config := ⟨0, c_prologue.state⟩
  have hpc_c2 : (Config.init (List.ofFn inputs)).pc = c₂.pc := rfl

  -- Use Steps.agreeOn to get execution from c_prologue.state
  have hagree_pF_symm : initState.agreeOn c₂.state 0 pF.maxRegister := State.agreeOn_symm hagree_pF
  let hagree_result := Steps.agreeOn hsteps_pF hpc_c2 hagree_pF_symm
  let c_pF' := Classical.choose hagree_result
  have hspec_pF' := Classical.choose_spec hagree_result
  let hsteps_pF' := hspec_pF'.1
  let hpc_pF' := hspec_pF'.2.1
  have hagree_pF' : cpF.state.agreeOn c_pF'.state 0 pF.maxRegister := hspec_pF'.2.2

  -- pF_result_eq: c_pF'.state.read 0 = Result pF ... hpF_halts
  have hpF_result_eq : c_pF'.state.read 0 = Result pF (List.ofFn inputs) hpF_halts := by
    have h_agree_at_0 := hagree_pF' 0 (Nat.zero_le 0) (Nat.zero_le _)
    simp only [Result, State.output]
    exact h_agree_at_0.symm

  -- Lift pF steps to primitiveRecursionProgram using shiftJumps_at_offset
  have hembed_pF := prPF_shiftJumps_embed n pF pG
  have hsteps_pF_lifted := Steps.shiftJumps_at_offset (prPFOffset n pF pG) hembed_pF hsteps_pF'

  -- Show that c_pF'.pc = pF.length (since pF is standard form)
  have hhalted_pF' : c_pF'.isHalted pF := by
    unfold Config.isHalted; rw [← hpc_pF']; exact hhalted_pF
  have hpc_pF'_length : c_pF'.pc = pF.length :=
    hpF_sf.pc_eq_length_of_halted hsteps_pF' (Nat.zero_le _) hhalted_pF'

  -- Simplify the lifted steps: from prPFOffset to prPFOffset + pF.length
  have hsteps_pF_lifted' : Steps (primitiveRecursionProgram n pF pG) ⟨prPFOffset n pF pG, c_prologue.state⟩
      ⟨prPFOffset n pF pG + pF.length, c_pF'.state⟩ := by
    have h1 : prPFOffset n pF pG + c₂.pc = prPFOffset n pF pG := rfl
    have h2 : prPFOffset n pF pG + c_pF'.pc = prPFOffset n pF pG + pF.length := by rw [hpc_pF'_length]
    rw [h1, h2] at hsteps_pF_lifted
    exact hsteps_pF_lifted

  -- Combined steps: from prBaseCasePC to prPFOffset + pF.length
  have hsteps_to_T : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩
      ⟨prPFOffset n pF pG + pF.length, c_pF'.state⟩ :=
    Relation.ReflTransGen.trans hsteps_prologue_lifted hsteps_pF_lifted'

  -- Phase 3: Execute T instruction (copy R[0] to accumulator)
  -- prPFOffset + pF.length = prBaseCasePC + prBaseCasePrologueLength + pF.length
  -- which is where the T instruction is located

  have hT_pc : prPFOffset n pF pG + pF.length = prLoopCheckPC n pF pG - 1 := by
    simp only [prPFOffset, prLoopCheckPC, prSetupPhaseLength, prBaseCasePrologueLength,
      prBaseCasePhaseLength]
    omega

  -- The T instruction copies R[0] to accumulator
  have hT_instr : (primitiveRecursionProgram n pF pG).getInstr (prPFOffset n pF pG + pF.length) =
      some (Instr.T 0 (prAccumulatorReg n pF pG)) := by
    -- Position is prSetupPhaseLength + prBaseCasePrologueLength + pF.length
    -- which is in prBaseCasePhase at index prBaseCasePrologueLength + pF.length
    -- prBaseCasePhase = prBaseCasePrologue ++ pF.shiftJumps ++ [T 0 acc]
    -- At index prBaseCasePrologueLength + pF.length, we access [T 0 acc][0]
    simp only [primitiveRecursionProgram, getInstr, prPFOffset, prBaseCasePhase]
    have h_not_in_setup : ¬(prSetupPhaseLength n + prBaseCasePrologueLength n pF pG + pF.length <
        (prSetupPhase n pF pG).length) := by
      simp only [prSetupPhase_length, prSetupPhaseLength]; omega
    have h_in_basecase : prSetupPhaseLength n + prBaseCasePrologueLength n pF pG + pF.length <
        (prSetupPhase n pF pG ++ (prBaseCasePrologue n pF pG ++
          pF.shiftJumps (prSetupPhaseLength n + prBaseCasePrologueLength n pF pG) ++
          [Instr.T 0 (prAccumulatorReg n pF pG)])).length := by
      simp only [List.length_append, prSetupPhase_length, prBaseCasePrologue_length,
        shiftJumps_length, List.length, prSetupPhaseLength, prBaseCasePrologueLength]
      omega
    simp only [prSetupPhaseLength]
    -- Now index is prBaseCasePrologueLength + pF.length within prBaseCasePrologue ++ pF.shiftJumps ++ [T]
    have h_not_in_prologue_pf : ¬(prBaseCasePrologueLength n pF pG + pF.length <
        (prBaseCasePrologue n pF pG ++ pF.shiftJumps (prSetupPhaseLength n + prBaseCasePrologueLength n pF pG)).length) := by
      simp only [List.length_append, prBaseCasePrologue_length, shiftJumps_length,
        prBaseCasePrologueLength]; omega
    have h_in_T : prBaseCasePrologueLength n pF pG + pF.length <
        (prBaseCasePrologue n pF pG ++ pF.shiftJumps (prSetupPhaseLength n + prBaseCasePrologueLength n pF pG) ++
          [Instr.T 0 (prAccumulatorReg n pF pG)]).length := by
      simp only [List.length_append, prBaseCasePrologue_length, shiftJumps_length,
        List.length, prBaseCasePrologueLength]; omega
    simp only [List.getElem?_append, List.length_append, prBaseCasePrologue_length, shiftJumps_length,
      prBaseCasePrologueLength, prLoopCheck_length, prLoopBody_length, prSetupPhase_length,
      prSetupPhaseLength, List.length]
    split_ifs <;> try omega
    have hidx : n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n) + pF.length - (n + 1 + 2) -
        (primitiveRecursionBase n pF pG + 1 + n + pF.length) = 0 := by omega
    simp only [hidx, List.getElem?_cons_zero]

  -- Execute the T step
  have hstep_T : Step (primitiveRecursionProgram n pF pG) ⟨prPFOffset n pF pG + pF.length, c_pF'.state⟩
      ⟨prPFOffset n pF pG + pF.length + 1, c_pF'.state.write (prAccumulatorReg n pF pG) (c_pF'.state.read 0)⟩ :=
    Step.trans hT_instr

  have hT_pc_eq : prPFOffset n pF pG + pF.length + 1 = prLoopCheckPC n pF pG := by
    simp only [prPFOffset, prLoopCheckPC, prSetupPhaseLength, prBaseCasePrologueLength,
      prBaseCasePhaseLength]
    omega

  -- Final state
  let finalState := c_pF'.state.write (prAccumulatorReg n pF pG) (c_pF'.state.read 0)

  -- Combined steps to loop check
  have hsteps_final : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩
      ⟨prLoopCheckPC n pF pG, finalState⟩ := by
    have h := Relation.ReflTransGen.trans hsteps_to_T (Relation.ReflTransGen.single hstep_T)
    rw [hT_pc_eq] at h
    exact h

  -- Preservation lemmas for high registers through pF execution
  have hpF_preserves_high : ∀ r, pF.maxRegister < r → c_pF'.state.read r = c_prologue.state.read r := by
    intro r hr
    exact Steps.preserves_high_register hsteps_pF' r hr

  have hprologue_preserves : ∀ r, primitiveRecursionBase n pF pG < r → c_prologue.state.read r = s.read r :=
    fun r hr => prBaseCasePrologue_preserves_high_register n pF pG s c_prologue hsteps_prologue hhalted_prologue r hr

  -- Build the result
  exact {
    config := ⟨prLoopCheckPC n pF pG, finalState⟩,
    steps := hsteps_final,
    pc_eq := rfl,
    accumulator_eq := by
      show finalState.read (prAccumulatorReg n pF pG) = Result pF (List.ofFn inputs) hpF_halts
      simp only [finalState, State.write_read_same]
      exact hpF_result_eq,
    savedInputs_preserved := fun i => by
      show finalState.read _ = s.read _
      simp only [finalState, State.write_read_diff _ _ _ _ (prSavedInput_ne_prAccumulatorReg n pF pG i)]
      have hgt : primitiveRecursionBase n pF pG < prSavedInputsStart n pF pG + i := by
        have := prSavedInputsStart_gt_base n pF pG; omega
      rw [pF_preserves_prSavedInputs n pF pG c_prologue.state c_pF' hsteps_pF' i,
          hprologue_preserves (prSavedInputsStart n pF pG + i) hgt],
    savedY_preserved := by
      show finalState.read _ = s.read _
      simp only [finalState, State.write_read_diff _ _ _ _ (prSavedYReg_ne_prAccumulatorReg n pF pG)]
      rw [pF_preserves_prSavedYReg n pF pG c_prologue.state c_pF' hsteps_pF',
          hprologue_preserves _ (prSavedYReg_gt_base n pF pG)],
    counter_preserved := by
      show finalState.read _ = s.read _
      simp only [finalState, State.write_read_diff _ _ _ _ (prCounterReg_ne_prAccumulatorReg n pF pG)]
      rw [pF_preserves_prCounterReg n pF pG c_prologue.state c_pF' hsteps_pF',
          hprologue_preserves _ (prCounterReg_gt_base n pF pG)],
    zero_preserved := by
      show finalState.read _ = s.read _
      simp only [finalState, State.write_read_diff _ _ _ _ (prAccumulatorReg_ne_prZeroReg n pF pG).symm]
      rw [pF_preserves_prZeroReg n pF pG c_prologue.state c_pF' hsteps_pF',
          hprologue_preserves _ (prZeroReg_gt_base n pF pG)]
  }

/-! ## Loop Iteration -/

/-- Result of a single loop iteration from loopCheckPC.
    Tracks whether we exited (counter = savedY) or continued (counter < savedY). -/
structure PrLoopIterationResult (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (k : ℕ) (accBefore : ℕ) (hpG_halts : Halts pG (List.ofFn (extendInputsForG inputs k accBefore))) where
  config : Config
  steps : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩ config
  /-- Either we exited to output (k = y) or we're back at loop check with counter = k+1 -/
  outcome : (config.pc = prOutputPC n pF pG ∧ k = y) ∨
            (config.pc = prLoopCheckPC n pF pG ∧ k < y)
  /-- In continue case, counter is k+1 -/
  counter_next : config.pc = prLoopCheckPC n pF pG →
    config.state.read (prCounterReg n pF pG) = k + 1
  /-- In continue case, accumulator updated -/
  accumulator_updated : config.pc = prLoopCheckPC n pF pG →
    config.state.read (prAccumulatorReg n pF pG) =
      Result pG (List.ofFn (extendInputsForG inputs k accBefore)) hpG_halts
  /-- Saved inputs preserved -/
  savedInputs_preserved : ∀ i : Fin n,
    config.state.read (prSavedInputsStart n pF pG + i) = s.read (prSavedInputsStart n pF pG + i)
  /-- SavedY preserved -/
  savedY_preserved : config.state.read (prSavedYReg n pF pG) = s.read (prSavedYReg n pF pG)
  /-- Zero register preserved -/
  zero_preserved : config.state.read (prZeroReg n pF pG) = s.read (prZeroReg n pF pG)

/-- Execute a single loop iteration. -/
noncomputable def pr_loop_iteration (n : ℕ) (pF pG : Program)
    (_hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (inputs : Fin n → ℕ) (y : ℕ) (s : State) (k : ℕ) (accBefore : ℕ)
    (hk_le_y : k ≤ y)
    (hs_counter : s.read (prCounterReg n pF pG) = k)
    (hs_savedY : s.read (prSavedYReg n pF pG) = y)
    (hs_acc : s.read (prAccumulatorReg n pF pG) = accBefore)
    (hs_zero : s.read (prZeroReg n pF pG) = 0)
    (hs_saved : ∀ i : Fin n, s.read (prSavedInputsStart n pF pG + i) = inputs i)
    (hpG_halts : Halts pG (List.ofFn (extendInputsForG inputs k accBefore))) :
    PrLoopIterationResult n pF pG inputs y s k accBefore hpG_halts := by
  -- The loop check instruction: J counter savedY outputPC
  have hJ_instr := prLoopCheck_embed n pF pG

  -- Branch on whether k = y or k < y
  by_cases hky : k = y
  · -- Case k = y: counter = savedY, so J instruction jumps to outputPC
    have heq : s.read (prCounterReg n pF pG) = s.read (prSavedYReg n pF pG) := by
      rw [hs_counter, hs_savedY, hky]
    have hstep_J : Step (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prOutputPC n pF pG, s⟩ := Step.jump_eq hJ_instr heq

    exact {
      config := ⟨prOutputPC n pF pG, s⟩
      steps := Relation.ReflTransGen.single hstep_J
      outcome := Or.inl ⟨rfl, hky⟩
      counter_next := fun hpc => by
        simp only [prOutputPC, prLoopBodyPC, prLoopBodyLength, prLoopPrologueLength,
          prLoopEpilogueLength] at hpc
        omega
      accumulator_updated := fun hpc => by
        simp only [prOutputPC, prLoopBodyPC, prLoopBodyLength, prLoopPrologueLength,
          prLoopEpilogueLength] at hpc
        omega
      savedInputs_preserved := fun i => rfl
      savedY_preserved := rfl
      zero_preserved := rfl
    }

  · -- Case k ≠ y: counter ≠ savedY, so J instruction doesn't jump, proceed to loop body
    have hne : s.read (prCounterReg n pF pG) ≠ s.read (prSavedYReg n pF pG) := by
      rw [hs_counter, hs_savedY]; exact hky
    have hstep_J : Step (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prLoopCheckPC n pF pG + 1, s⟩ := Step.jump_ne hJ_instr hne

    have hLoopBodyPC_eq : prLoopCheckPC n pF pG + 1 = prLoopBodyPC n pF pG := by
      simp only [prLoopBodyPC, prLoopCheckPC, prSetupPhaseLength, prBaseCasePhaseLength]

    -- Execute prLoopPrologue (straight-line)
    have hsl_prologue := prLoopPrologue_isStraightLine n pF pG
    let prologueResult := straightLineExec hsl_prologue s
    let c_prologue := prologueResult.config
    let hsteps_prologue := prologueResult.steps
    let hhalted_prologue := prologueResult.halted
    let hpc_prologue := prologueResult.pc_eq

    -- Lift prologue steps to primitiveRecursionProgram
    have hembed_prologue := prLoopPrologue_embed n pF pG
    have hsteps_prologue_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopBodyPC n pF pG, s⟩
        ⟨prLoopBodyPC n pF pG + c_prologue.pc, c_prologue.state⟩ :=
      Steps.straightLine_at_offset (prLoopBodyPC n pF pG) hsl_prologue hembed_prologue hsteps_prologue

    -- After prologue, PC is at prPGOffset
    have hpc_after_prologue : prLoopBodyPC n pF pG + c_prologue.pc = prPGOffset n pF pG := by
      simp only [prLoopBodyPC, prPGOffset, prLoopCheckPC, prLoopPrologueLength]
      rw [hpc_prologue, prLoopPrologue_length, prLoopPrologueLength]
    rw [hpc_after_prologue] at hsteps_prologue_lifted

    -- Steps from J to end of prologue
    have hsteps_to_prologue_end : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prPGOffset n pF pG, c_prologue.state⟩ := by
      have h1 := Relation.ReflTransGen.single hstep_J
      rw [hLoopBodyPC_eq] at h1
      exact Relation.ReflTransGen.trans h1 hsteps_prologue_lifted

    -- Phase 2: Execute pG (shifted)
    -- Get pG halting configuration
    let cpG := Classical.choose hpG_halts
    have hspec_pG := Classical.choose_spec hpG_halts
    let hsteps_pG := hspec_pG.1
    let hhalted_pG := hspec_pG.2

    -- After prologue, R[0..n-1] = inputs, R[n] = k, R[n+1] = accBefore
    have hR_after_prologue : ∀ i : Fin n, c_prologue.state.read i = inputs i := by
      intro i
      have h := prLoopPrologue_restores_inputs n pF pG s c_prologue hsteps_prologue hhalted_prologue i (fun _ => rfl)
      rw [h, hs_saved i]

    have hRn_after_prologue : c_prologue.state.read n = k := by
      have h := prLoopPrologue_sets_Rn n pF pG s c_prologue hsteps_prologue hhalted_prologue
      rw [h, hs_counter]

    have hRn1_after_prologue : c_prologue.state.read (n + 1) = accBefore := by
      have h := prLoopPrologue_sets_Rn1 n pF pG s c_prologue hsteps_prologue hhalted_prologue
      rw [h, hs_acc]

    -- State agreement: c_prologue.state agrees with initStateG on 0..pG.maxRegister
    let initStateG := (Config.init (List.ofFn (extendInputsForG inputs k accBefore))).state
    have hagree_pG : c_prologue.state.agreeOn initStateG 0 pG.maxRegister := by
      intro r _ hr_hi
      by_cases hr_lt_n : r < n
      · -- Case r < n: both sides equal inputs r
        have hleft : c_prologue.state.read r = inputs ⟨r, hr_lt_n⟩ := hR_after_prologue ⟨r, hr_lt_n⟩
        have hright : initStateG.read r = inputs ⟨r, hr_lt_n⟩ := by
          unfold initStateG Config.init State.fromInputs State.read
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          have hlen : r < (n + 2) := by omega
          simp only [hlen, ↓reduceDIte]
          exact extendInputsForG_castSucc_castSucc inputs k accBefore ⟨r, hr_lt_n⟩
        rw [hleft, hright]
      · by_cases hr_eq_n : r = n
        · -- Case r = n: both sides equal k
          subst hr_eq_n
          have hleft : c_prologue.state.read r = k := hRn_after_prologue
          have hright : initStateG.read r = k := by
            unfold initStateG Config.init State.fromInputs State.read
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            have hr : r < r + 2 := by omega
            simp only [hr, ↓reduceDIte]
            -- Position r in (r+2)-tuple = Fin.castSucc (Fin.last r) = k
            have heq : (⟨r, hr⟩ : Fin (r + 2)) = Fin.castSucc (Fin.last r) := by
              ext; simp [Fin.castSucc, Fin.last]
            rw [heq]
            exact extendInputsForG_castSucc_last inputs k accBefore
          rw [hleft, hright]
        · by_cases hr_eq_n1 : r = n + 1
          · -- Case r = n+1: both sides equal accBefore
            subst hr_eq_n1
            have hleft : c_prologue.state.read (n + 1) = accBefore := hRn1_after_prologue
            have hright : initStateG.read (n + 1) = accBefore := by
              unfold initStateG Config.init State.fromInputs State.read
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
              have hlt : n + 1 < n + 2 := Nat.lt_succ_self _
              simp only [hlt, ↓reduceDIte, Option.getD_some]
              exact extendInputsForG_last inputs k accBefore
            rw [hleft, hright]
          · -- Case r > n+1: both sides equal 0
            have hr_gt_n1 : n + 1 < r := by omega
            have hleft : c_prologue.state.read r = 0 := by
              have hr_le_pG_max : r ≤ pG.maxRegister := hr_hi
              have hpG_le_base : pG.maxRegister ≤ primitiveRecursionBase n pF pG :=
                primitiveRecursionBase_ge_pG n pF pG
              have hr_le_base : r ≤ primitiveRecursionBase n pF pG := Nat.le_trans hr_le_pG_max hpG_le_base
              -- Cleared by prologue
              have hk : r < (prLoopPrologue n pF pG).length := by
                simp only [prLoopPrologue, List.length_append, clearRegisters_length,
                  copyRegisterRange_length, List.length]
                omega
              have hwrite : (prLoopPrologue n pF pG)[r] = Instr.Z r := by
                simp only [prLoopPrologue]
                have h_in_clear : r < (clearRegisters (primitiveRecursionBase n pF pG)).length := by
                  simp only [clearRegisters_length]; exact Nat.lt_succ_of_le hr_le_base
                have h_in_ext2 : r < (clearRegisters (primitiveRecursionBase n pF pG) ++
                    copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length := by
                  simp only [List.length_append, clearRegisters_length, copyRegisterRange_length]; omega
                rw [List.getElem_append_left h_in_ext2, List.getElem_append_left h_in_clear]
                simp only [Program.clearRegisters, List.getElem_map, List.getElem_range]
              have hnowrite : ∀ j (hj : j < (prLoopPrologue n pF pG).length), r < j →
                  ((prLoopPrologue n pF pG)[j]).writesTo ≠ some r := by
                intro j hj hjr
                simp only [prLoopPrologue, List.length_append, clearRegisters_length,
                  copyRegisterRange_length, List.length] at hj
                simp only [prLoopPrologue]
                by_cases hj_clear2 : j < (clearRegisters (primitiveRecursionBase n pF pG) ++
                    copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length
                · rw [List.getElem_append_left hj_clear2]
                  by_cases hj_in_clear : j < (clearRegisters (primitiveRecursionBase n pF pG)).length
                  · rw [List.getElem_append_left hj_in_clear]
                    simp only [Program.clearRegisters, List.getElem_map, List.getElem_range,
                      Instr.writesTo, ne_eq, Option.some.injEq]
                    omega
                  · rw [List.getElem_append_right (Nat.not_lt.mp hj_in_clear)]
                    simp only [clearRegisters_length, Program.copyRegisterRange, List.getElem_map,
                      List.getElem_range, Nat.zero_add, Instr.writesTo, ne_eq, Option.some.injEq]
                    simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear2
                    simp only [clearRegisters_length] at hj_in_clear
                    omega
                · rw [List.getElem_append_right (Nat.not_lt.mp hj_clear2)]
                  simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear2
                  simp only [List.length_append, clearRegisters_length, copyRegisterRange_length]
                  have hidx : j - (primitiveRecursionBase n pF pG + 1 + n) < 2 := by omega
                  by_cases hidx0 : j - (primitiveRecursionBase n pF pG + 1 + n) = 0
                  · simp only [hidx0, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
                    omega
                  · have hidx1 : j - (primitiveRecursionBase n pF pG + 1 + n) = 1 := by omega
                    simp only [hidx1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo,
                      ne_eq, Option.some.injEq]
                    omega
              exact straightLine_zeros_register (prLoopPrologue_isStraightLine n pF pG) s r r hk hwrite hnowrite
            have hright : initStateG.read r = 0 := by
              unfold initStateG Config.init State.fromInputs State.read
              have hr_ge : ¬ r < n + 2 := by omega
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr_ge, dite_false, Option.getD_none]
            rw [hleft, hright]

    -- Define c₂ to use agreeOn
    let c₂ : Config := ⟨0, c_prologue.state⟩
    have hpc_c2 : (Config.init (List.ofFn (extendInputsForG inputs k accBefore))).pc = c₂.pc := rfl

    -- Use Steps.agreeOn to get execution from c_prologue.state
    have hagree_pG_symm : initStateG.agreeOn c₂.state 0 pG.maxRegister := State.agreeOn_symm hagree_pG
    let hagree_result := Steps.agreeOn hsteps_pG hpc_c2 hagree_pG_symm
    let c_pG' := Classical.choose hagree_result
    have hspec_pG' := Classical.choose_spec hagree_result
    let hsteps_pG' := hspec_pG'.1
    let hpc_pG' := hspec_pG'.2.1
    have hagree_pG' : cpG.state.agreeOn c_pG'.state 0 pG.maxRegister := hspec_pG'.2.2

    -- pG_result_eq: c_pG'.state.read 0 = Result pG ... hpG_halts
    have hpG_result_eq : c_pG'.state.read 0 = Result pG (List.ofFn (extendInputsForG inputs k accBefore)) hpG_halts := by
      have h_agree_at_0 := hagree_pG' 0 (Nat.zero_le 0) (Nat.zero_le _)
      simp only [Result, State.output]
      exact h_agree_at_0.symm

    -- Lift pG steps to primitiveRecursionProgram using shiftJumps_at_offset
    have hembed_pG := prPG_shiftJumps_embed n pF pG
    have hsteps_pG_lifted := Steps.shiftJumps_at_offset (prPGOffset n pF pG) hembed_pG hsteps_pG'

    -- Show that c_pG'.pc = pG.length (since pG is standard form)
    have hhalted_pG' : c_pG'.isHalted pG := by
      unfold Config.isHalted; rw [← hpc_pG']; exact hhalted_pG
    have hpc_pG'_length : c_pG'.pc = pG.length :=
      hpG_sf.pc_eq_length_of_halted hsteps_pG' (Nat.zero_le _) hhalted_pG'

    -- Simplify the lifted steps: from prPGOffset to prPGOffset + pG.length
    have hsteps_pG_lifted' : Steps (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG, c_prologue.state⟩
        ⟨prPGOffset n pF pG + pG.length, c_pG'.state⟩ := by
      have h1 : prPGOffset n pF pG + c₂.pc = prPGOffset n pF pG := rfl
      have h2 : prPGOffset n pF pG + c_pG'.pc = prPGOffset n pF pG + pG.length := by rw [hpc_pG'_length]
      rw [h1, h2] at hsteps_pG_lifted
      exact hsteps_pG_lifted

    -- Combined steps to end of pG
    have hsteps_to_pG_end : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prPGOffset n pF pG + pG.length, c_pG'.state⟩ :=
      Relation.ReflTransGen.trans hsteps_to_prologue_end hsteps_pG_lifted'

    -- Phase 3: Execute loop epilogue (T, S, J)
    -- Epilogue PC positions
    have hT_pc : prPGOffset n pF pG + pG.length = prPGOffset n pF pG + pG.length := rfl
    have hS_pc : prPGOffset n pF pG + pG.length + 1 = prPGOffset n pF pG + pG.length + 1 := rfl

    -- Epilogue instruction embeddings (inline proofs)
    have hT_instr : (primitiveRecursionProgram n pF pG).getInstr (prPGOffset n pF pG + pG.length) =
        some (Instr.T 0 (prAccumulatorReg n pF pG)) := by
      simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody, prLoopEpilogue,
        getInstr, List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length,
        prLoopPrologue_length, shiftJumps_length, List.length_append,
        prLoopPrologueLength, prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength, List.length]
      split_ifs <;> try omega
      have hidx : n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + List.length pF + 1) + 1 +
            (primitiveRecursionBase n pF pG + 1 + n + 2) +
          List.length pG -
        (n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + List.length pF + 1) + 1) -
        (primitiveRecursionBase n pF pG + 1 + n + 2 + List.length pG) = 0 := by omega
      simp only [hidx, List.getElem?_cons_zero]

    have hS_instr : (primitiveRecursionProgram n pF pG).getInstr (prPGOffset n pF pG + pG.length + 1) =
        some (Instr.S (prCounterReg n pF pG)) := by
      simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody, prLoopEpilogue,
        getInstr, List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length,
        prLoopPrologue_length, shiftJumps_length, List.length_append,
        prLoopPrologueLength, prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength, List.length]
      split_ifs <;> try omega
      have hidx : n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + List.length pF + 1) + 1 +
            (primitiveRecursionBase n pF pG + 1 + n + 2) +
          List.length pG + 1 -
        (n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + List.length pF + 1) + 1) -
        (primitiveRecursionBase n pF pG + 1 + n + 2 + List.length pG) = 1 := by omega
      simp only [hidx, List.getElem?_cons_succ, List.getElem?_cons_zero]

    have hJ_instr_epilogue : (primitiveRecursionProgram n pF pG).getInstr (prPGOffset n pF pG + pG.length + 2) =
        some (Instr.J (prZeroReg n pF pG) (prZeroReg n pF pG) (prLoopCheckPC n pF pG)) := by
      simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody, prLoopEpilogue,
        getInstr, List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length,
        prLoopPrologue_length, shiftJumps_length, List.length_append,
        prLoopPrologueLength, prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength, List.length]
      split_ifs <;> try omega
      have hidx : n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + List.length pF + 1) + 1 +
            (primitiveRecursionBase n pF pG + 1 + n + 2) +
          List.length pG + 2 -
        (n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + List.length pF + 1) + 1) -
        (primitiveRecursionBase n pF pG + 1 + n + 2 + List.length pG) = 2 := by omega
      simp only [hidx, List.getElem?_cons_succ, List.getElem?_cons_zero]

    -- Execute T instruction
    let state_after_T := c_pG'.state.write (prAccumulatorReg n pF pG) (c_pG'.state.read 0)
    have hstep_T : Step (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length, c_pG'.state⟩
        ⟨prPGOffset n pF pG + pG.length + 1, state_after_T⟩ :=
      Step.trans hT_instr

    -- Execute S instruction
    let state_after_S := state_after_T.write (prCounterReg n pF pG) (state_after_T.read (prCounterReg n pF pG) + 1)
    have hstep_S : Step (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length + 1, state_after_T⟩
        ⟨prPGOffset n pF pG + pG.length + 2, state_after_S⟩ :=
      Step.succ hS_instr

    -- Execute J instruction (unconditional jump since zeroReg = zeroReg)
    have hzero_eq : state_after_S.read (prZeroReg n pF pG) = state_after_S.read (prZeroReg n pF pG) := rfl
    have hstep_J_back : Step (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length + 2, state_after_S⟩
        ⟨prLoopCheckPC n pF pG, state_after_S⟩ :=
      Step.jump_eq hJ_instr_epilogue hzero_eq

    -- Combined epilogue steps
    have hsteps_epilogue : Steps (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length, c_pG'.state⟩
        ⟨prLoopCheckPC n pF pG, state_after_S⟩ := by
      apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep_T)
      apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep_S)
      exact Relation.ReflTransGen.single hstep_J_back

    -- Full steps from loopCheckPC back to loopCheckPC
    have hsteps_full : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prLoopCheckPC n pF pG, state_after_S⟩ :=
      Relation.ReflTransGen.trans hsteps_to_pG_end hsteps_epilogue

    -- Preservation lemmas
    have hpG_preserves_high : ∀ r, pG.maxRegister < r → c_pG'.state.read r = c_prologue.state.read r := by
      intro r hr
      exact Steps.preserves_high_register hsteps_pG' r hr

    have hprologue_preserves : ∀ r, primitiveRecursionBase n pF pG < r → c_prologue.state.read r = s.read r :=
      fun r hr => prLoopPrologue_preserves_high_register n pF pG s c_prologue hsteps_prologue hhalted_prologue r hr

    -- Counter value in state_after_S
    have hcounter_after_S : state_after_S.read (prCounterReg n pF pG) = k + 1 := by
      simp only [state_after_S, State.write_read_same]
      -- Need to show state_after_T.read counter = k
      -- pG doesn't touch counter (above pG.maxRegister), prologue sets counter via T
      have hcounter_after_T : state_after_T.read (prCounterReg n pF pG) = k := by
        have hne : prCounterReg n pF pG ≠ prAccumulatorReg n pF pG := by
          have := prCounterReg_gt_base n pF pG
          have := prAccumulatorReg_gt_base n pF pG
          simp only [prCounterReg, prAccumulatorReg]; omega
        simp only [state_after_T, State.write_read_diff _ _ _ _ hne]
        have hpG_preserves_counter := pG_preserves_prCounterReg n pF pG c_prologue.state c_pG' hsteps_pG'
        rw [hpG_preserves_counter]
        -- After prologue, counter = k (from T instruction)
        have := prLoopPrologue_preserves_high_register n pF pG s c_prologue hsteps_prologue hhalted_prologue
          (prCounterReg n pF pG) (prCounterReg_gt_base n pF pG)
        rw [this, hs_counter]
      rw [hcounter_after_T]

    -- Build the result: k < y since k ≤ y (by hypothesis) and k ≠ y (by case split)
    have hk_lt_y : k < y := Nat.lt_of_le_of_ne hk_le_y hky

    exact {
      config := ⟨prLoopCheckPC n pF pG, state_after_S⟩
      steps := hsteps_full
      outcome := Or.inr ⟨rfl, hk_lt_y⟩
      counter_next := fun _ => hcounter_after_S
      accumulator_updated := fun _ => by
        -- state_after_S.read accumulatorReg = Result pG ...
        -- state_after_S = state_after_T.write counterReg (...)
        -- state_after_T = c_pG'.state.write accumulatorReg (c_pG'.state.read 0)
        have hne_acc_counter : prAccumulatorReg n pF pG ≠ prCounterReg n pF pG := by
          have := prCounterReg_gt_base n pF pG
          have := prAccumulatorReg_gt_base n pF pG
          simp only [prCounterReg, prAccumulatorReg]; omega
        show state_after_S.read (prAccumulatorReg n pF pG) = _
        simp only [state_after_S, State.write_read_diff _ _ _ _ hne_acc_counter]
        simp only [state_after_T, State.write_read_same]
        exact hpG_result_eq
      savedInputs_preserved := fun i => by
        show state_after_S.read _ = s.read _
        simp only [state_after_S, State.write_read_diff _ _ _ _ (prSavedInput_ne_prCounterReg n pF pG i)]
        simp only [state_after_T, State.write_read_diff _ _ _ _ (prSavedInput_ne_prAccumulatorReg n pF pG i)]
        have hgt : primitiveRecursionBase n pF pG < prSavedInputsStart n pF pG + i := by
          have := prSavedInputsStart_gt_base n pF pG; omega
        rw [pG_preserves_prSavedInputs n pF pG c_prologue.state c_pG' hsteps_pG' i,
            hprologue_preserves (prSavedInputsStart n pF pG + i) hgt]
      savedY_preserved := by
        show state_after_S.read _ = s.read _
        simp only [state_after_S, State.write_read_diff _ _ _ _ (prSavedYReg_ne_prCounterReg n pF pG)]
        simp only [state_after_T, State.write_read_diff _ _ _ _ (prSavedYReg_ne_prAccumulatorReg n pF pG)]
        rw [pG_preserves_prSavedYReg n pF pG c_prologue.state c_pG' hsteps_pG',
            hprologue_preserves _ (prSavedYReg_gt_base n pF pG)]
      zero_preserved := by
        show state_after_S.read _ = s.read _
        simp only [state_after_S, State.write_read_diff _ _ _ _ (prCounterReg_ne_prZeroReg n pF pG).symm]
        simp only [state_after_T, State.write_read_diff _ _ _ _ (prAccumulatorReg_ne_prZeroReg n pF pG).symm]
        rw [pG_preserves_prZeroReg n pF pG c_prologue.state c_pG' hsteps_pG',
            hprologue_preserves _ (prZeroReg_gt_base n pF pG)]
    }

/-! ## K Iterations -/

/-- Result of k loop iterations. -/
structure PrLoopKIterationsResult (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (k : ℕ)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ) where
  config : Config
  steps : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩ config
  pc_eq : config.pc = prLoopCheckPC n pF pG
  counter_eq : config.state.read (prCounterReg n pF pG) = k
  savedInputs_eq : ∀ i : Fin n, config.state.read (prSavedInputsStart n pF pG + i) = inputs i
  savedY_eq : config.state.read (prSavedYReg n pF pG) = y
  zero_eq : config.state.read (prZeroReg n pF pG) = 0
  acc_eq : ∀ hPr_dom_k : (Pr f g (Fin.snoc inputs k)).Dom,
    config.state.read (prAccumulatorReg n pF pG) = (Pr f g (Fin.snoc inputs k)).get hPr_dom_k

/-- Execute k loop iterations. -/
noncomputable def pr_loop_k_iterations (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (_hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ) (s : State) (k : ℕ)
    (hk_le_y : k ≤ y)
    (hs_counter : s.read (prCounterReg n pF pG) = 0)
    (hs_savedY : s.read (prSavedYReg n pF pG) = y)
    (hs_zero : s.read (prZeroReg n pF pG) = 0)
    (hs_saved : ∀ i : Fin n, s.read (prSavedInputsStart n pF pG + i) = inputs i)
    (hPr_dom_k : (Pr f g (Fin.snoc inputs k)).Dom)
    (hs_acc : s.read (prAccumulatorReg n pF pG) = (Pr f g (Fin.snoc inputs 0)).get (Pr_dom_of_dom_le inputs hPr_dom_k (Nat.zero_le k))) :
    PrLoopKIterationsResult n pF pG inputs y s k f g := by
  induction k generalizing s with
  | zero =>
    -- Base case: 0 iterations, just return the initial state
    exact {
      config := ⟨prLoopCheckPC n pF pG, s⟩
      steps := Relation.ReflTransGen.refl
      pc_eq := rfl
      counter_eq := hs_counter
      savedInputs_eq := hs_saved
      savedY_eq := hs_savedY
      zero_eq := hs_zero
      acc_eq := fun _ => hs_acc
    }
  | succ m ih =>
    -- Inductive case: do m iterations, then one more
    -- First, get domain proofs for m
    have hPr_dom_m : (Pr f g (Fin.snoc inputs m)).Dom :=
      Pr_dom_of_dom_le inputs hPr_dom_k (Nat.le_succ m)

    -- Get result after m iterations
    have hm_le_y : m ≤ y := Nat.le_of_lt (Nat.lt_of_succ_le hk_le_y)
    let result_m := ih s hm_le_y hs_counter hs_savedY hs_zero hs_saved hPr_dom_m hs_acc

    -- After m iterations, we're at loopCheckPC with counter = m
    let s_m := result_m.config.state
    have hcounter_m : s_m.read (prCounterReg n pF pG) = m := result_m.counter_eq
    have hsavedY_m : s_m.read (prSavedYReg n pF pG) = y := result_m.savedY_eq
    have hzero_m : s_m.read (prZeroReg n pF pG) = 0 := result_m.zero_eq
    have hsaved_m : ∀ i : Fin n, s_m.read (prSavedInputsStart n pF pG + i) = inputs i := result_m.savedInputs_eq

    -- The accumulator after m iterations equals Pr(inputs, m)
    have hacc_m : s_m.read (prAccumulatorReg n pF pG) = (Pr f g (Fin.snoc inputs m)).get hPr_dom_m :=
      result_m.acc_eq hPr_dom_m

    -- pG halts for the m-th iteration inputs
    have hpG_halts_m : Halts pG (List.ofFn (extendInputsForG inputs m (s_m.read (prAccumulatorReg n pF pG)))) := by
      rw [hacc_m]
      -- Pr(inputs, m+1) is defined means g(inputs, m, Pr(inputs, m)) is defined
      have h := (Pr_dom_succ inputs m).mp hPr_dom_k
      have hg_dom := h.2 h.1
      rw [(hpG_spec (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))).1]
      exact hg_dom

    -- Do one more iteration
    let one_iter := pr_loop_iteration n pF pG hpF_sf hpG_sf inputs y s_m m
      (s_m.read (prAccumulatorReg n pF pG)) hm_le_y hcounter_m hsavedY_m
      rfl hzero_m hsaved_m hpG_halts_m

    -- Get the outcome - it should be Or.inr (continue case) since m < y
    have hm_lt_y : m < y := Nat.lt_of_succ_le hk_le_y
    -- The exit case requires m = y, but we have m < y, so use Or.resolve_left
    have hcontinue : one_iter.config.pc = prLoopCheckPC n pF pG ∧ m < y :=
      Or.resolve_left one_iter.outcome (fun hexit => Nat.lt_irrefl y (hexit.2 ▸ hm_lt_y))

    -- Establish that result_m.config matches the starting config of one_iter
    have hconfig_m : result_m.config = ⟨prLoopCheckPC n pF pG, s_m⟩ := by
      ext
      · exact result_m.pc_eq
      · rfl

    -- Get steps from s to s_m via result_m.config
    have hsteps_m' : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩ ⟨prLoopCheckPC n pF pG, s_m⟩ :=
      hconfig_m ▸ result_m.steps

    -- Continue case: back at loopCheckPC with counter = m + 1
    exact {
      config := one_iter.config
      steps := Relation.ReflTransGen.trans hsteps_m' one_iter.steps
      pc_eq := hcontinue.1
      counter_eq := one_iter.counter_next hcontinue.1
      savedInputs_eq := fun i => by
        rw [one_iter.savedInputs_preserved i, hsaved_m i]
      savedY_eq := by rw [one_iter.savedY_preserved, hsavedY_m]
      zero_eq := by rw [one_iter.zero_preserved, hzero_m]
      acc_eq := fun hPr_dom_succ => by
        -- After iteration: acc = Result pG (extendInputsForG inputs m acc_before)
        have h1 := one_iter.accumulator_updated hcontinue.1
        rw [h1]
        -- The accumulator before was Pr(inputs, m).get
        simp only [hacc_m]
        -- By hpG_spec: Result pG args = g(args).get for the halting case
        have hpG_halts_m' : Halts pG (List.ofFn (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))) := by
          simp only [← hacc_m]; exact hpG_halts_m
        have hg_dom : (g (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))).Dom := by
          rw [← (hpG_spec (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))).1]
          exact hpG_halts_m'
        have h2 := (hpG_spec (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))).2 hpG_halts_m' hg_dom
        rw [h2]
        -- Now: g(extendInputsForG inputs m Pr(inputs,m).get).get = Pr(inputs, m+1).get
        rw [Pr_succ_spec inputs m hPr_dom_succ]
    }

/-! ## Output Phase -/

/-- Output phase halts and copies accumulator to R[0]. -/
theorem prOutputPhase_halts (n : ℕ) (pF pG : Program) (s : State) :
    ∃ c, Steps (primitiveRecursionProgram n pF pG) ⟨prOutputPC n pF pG, s⟩ c ∧
         c.isHalted (primitiveRecursionProgram n pF pG) ∧
         c.state.read 0 = s.read (prAccumulatorReg n pF pG) := by
  use ⟨prOutputPC n pF pG + 1, s.write 0 (s.read (prAccumulatorReg n pF pG))⟩
  constructor
  · apply Steps.single
    apply Step.trans
    exact prOutputPhase_embed n pF pG
  · constructor
    · simp only [Config.isHalted, primitiveRecursionProgram_length]
      omega
    · simp only [State.read, State.write, Function.update_self]

/-! ## Main Halting Theorems -/

/-- If Pr is defined, the primitive recursion program halts. -/
theorem primitiveRecursionProgram_halts (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ)
    (hPr_dom : (Pr f g (Fin.snoc inputs y)).Dom) :
    Halts (primitiveRecursionProgram n pF pG) (List.ofFn (Fin.snoc inputs y)) := by
  -- Phase 1: Setup phase
  let setup := prExecuteSetupPhase n pF pG inputs y

  -- Phase 2: Base case phase
  -- First derive that pF halts (from Pr_dom → f.Dom)
  have hf_dom : (f inputs).Dom := (Pr_dom_iff inputs y).mp hPr_dom |>.1
  have hpF_halts : Halts pF (List.ofFn inputs) := (hpF_spec inputs).1.mpr hf_dom
  let baseCase := prExecuteBaseCasePhase n pF pG hpF_sf inputs y setup.config.state
    setup.savedInputs_eq hpF_halts

  -- Phase 3: Loop iterations (y iterations)
  -- We need to prove Pr(inputs, y).Dom, which we have
  -- Also need accumulator = Pr(inputs, 0) = f(inputs)
  have hPr_dom_0 : (Pr f g (Fin.snoc inputs 0)).Dom := Pr_dom_of_dom_le inputs hPr_dom (Nat.zero_le y)
  have hacc_eq_f : baseCase.config.state.read (prAccumulatorReg n pF pG) =
      (Pr f g (Fin.snoc inputs 0)).get hPr_dom_0 := by
    rw [baseCase.accumulator_eq]
    -- Result pF (List.ofFn inputs) hpF_halts = f(inputs).get = Pr(inputs, 0).get
    have hResult_eq := (hpF_spec inputs).2 hpF_halts hf_dom
    rw [hResult_eq]
    simp only [Pr_zero_spec]

  let loopResult := pr_loop_k_iterations n pF pG hpF_sf hpG_sf f g hpF_spec hpG_spec
    inputs y baseCase.config.state y (Nat.le_refl y)
    (by rw [baseCase.counter_preserved, setup.counter_eq])
    (by rw [baseCase.savedY_preserved, setup.savedY_eq])
    (by rw [baseCase.zero_preserved, setup.zero_eq])
    (fun i => by rw [baseCase.savedInputs_preserved, setup.savedInputs_eq])
    hPr_dom
    hacc_eq_f

  -- Phase 4: Final loop check - counter = savedY = y, so J jumps to outputPC
  have hJ_instr := prLoopCheck_embed n pF pG
  have hcounter_eq_savedY : loopResult.config.state.read (prCounterReg n pF pG) =
      loopResult.config.state.read (prSavedYReg n pF pG) := by
    rw [loopResult.counter_eq, loopResult.savedY_eq]
  have hstep_exit : Step (primitiveRecursionProgram n pF pG)
      ⟨prLoopCheckPC n pF pG, loopResult.config.state⟩
      ⟨prOutputPC n pF pG, loopResult.config.state⟩ :=
    Step.jump_eq hJ_instr hcounter_eq_savedY

  -- Phase 5: Output phase halts
  obtain ⟨finalConfig, hOutput_steps, hOutput_halted, _⟩ :=
    prOutputPhase_halts n pF pG loopResult.config.state

  -- Chain all steps together
  have hsteps_to_output : Steps (primitiveRecursionProgram n pF pG)
      (Config.init (List.ofFn (Fin.snoc inputs y))) ⟨prOutputPC n pF pG, loopResult.config.state⟩ := by
    -- init → prBaseCasePC (setup)
    have h1 := setup.steps
    -- prBaseCasePC → prLoopCheckPC (base case)
    have h2 : Steps (primitiveRecursionProgram n pF pG) setup.config baseCase.config :=
      baseCase.steps
    -- prLoopCheckPC → prLoopCheckPC with counter=y (loop iterations)
    have h3 : Steps (primitiveRecursionProgram n pF pG) baseCase.config loopResult.config :=
      loopResult.steps
    -- prLoopCheckPC → prOutputPC (exit jump)
    have h4 : Steps (primitiveRecursionProgram n pF pG) loopResult.config
        ⟨prOutputPC n pF pG, loopResult.config.state⟩ := by
      have hconfig : loopResult.config = ⟨prLoopCheckPC n pF pG, loopResult.config.state⟩ := by
        ext; exact loopResult.pc_eq; rfl
      rw [hconfig]
      exact Relation.ReflTransGen.single hstep_exit
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.trans (Relation.ReflTransGen.trans h1 h2) h3) h4

  -- Final chain: init → outputPC → halted
  exact ⟨finalConfig, Relation.ReflTransGen.trans hsteps_to_output hOutput_steps, hOutput_halted⟩

/-- Helper: Extract pF halting from main program execution passing through pF region.
    If we start at prPFOffset + k and reach a config with pc ≥ prPFOffset + pF.length,
    then pF halts from ⟨k, state⟩. Uses strong induction on step count. -/
theorem pF_halts_of_pr_exits_pF_region (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (k : ℕ) (state : State) (c : Config)
    (hk_le : k ≤ pF.length)
    (hsteps : Steps (primitiveRecursionProgram n pF pG) ⟨prPFOffset n pF pG + k, state⟩ c)
    (hpc_ge : c.pc ≥ prPFOffset n pF pG + pF.length) :
    ∃ c_pF, Steps pF ⟨k, state⟩ c_pF ∧ c_pF.pc = pF.length :=
  halts_of_exits_embedded_region (prPF_shiftJumps_embed n pF pG) hpF_sf k state c hk_le hsteps hpc_ge

/-- Helper: Extract pG halting from main program execution passing through pG region. -/
theorem pG_halts_of_pr_exits_pG_region (n : ℕ) (pF pG : Program)
    (hpG_sf : pG.IsStandardForm) (k : ℕ) (state : State) (c : Config)
    (hk_le : k ≤ pG.length)
    (hsteps : Steps (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + k, state⟩ c)
    (hpc_ge : c.pc ≥ prPGOffset n pF pG + pG.length) :
    ∃ c_pG, Steps pG ⟨k, state⟩ c_pG ∧ c_pG.pc = pG.length :=
  halts_of_exits_embedded_region (prPG_shiftJumps_embed n pF pG) hpG_sf k state c hk_le hsteps hpc_ge

/-- If the primitive recursion program halts, Pr is defined. -/
theorem primitiveRecursionProgram_halts_imp_dom (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ)
    (hHalts : Halts (primitiveRecursionProgram n pF pG) (List.ofFn (Fin.snoc inputs y))) :
    (Pr f g (Fin.snoc inputs y)).Dom := by
  -- Use Pr_dom_iff to reduce to proving f.Dom and the conditional for g
  rw [Pr_dom_iff]
  constructor
  -- Part 1: Prove f.Dom
  · -- From hHalts, extract that pF must have halted
    -- The program execution: init → setup → base case (pF) → loop → output → halt
    -- If pF didn't halt, the overall program wouldn't halt
    -- Use contrapositive: if f not defined, then pF doesn't halt, then program doesn't halt
    by_contra hf_not_dom
    -- If f.Dom is false, then pF doesn't halt
    have hpF_not_halts : ¬Halts pF (List.ofFn inputs) := by
      intro hpF_halts
      exact hf_not_dom ((hpF_spec inputs).1.mp hpF_halts)
    -- But if the overall program halts, pF must halt - derive contradiction
    obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ := hHalts
    -- Execute setup phase
    let setup := prExecuteSetupPhase n pF pG inputs y
    -- After setup, execution continues from prBaseCasePC
    have hContinuation := Steps.deterministic_continuation setup.steps hFinal_steps hFinal_halted
    -- Base case phase: if pF doesn't halt, execution diverges here
    -- prExecuteBaseCasePhase requires pF to halt, so we can't construct it
    -- Instead, analyze the base case phase directly
    -- The base case phase runs prBaseCasePrologue (straight-line, always halts)
    -- then runs pF.shiftJumps embedded at prPFOffset
    have hsl_prologue := prBaseCasePrologue_isStraightLine n pF pG
    let prologueResult := straightLineExec hsl_prologue setup.config.state
    let c_prologue := prologueResult.config
    let hsteps_prologue := prologueResult.steps
    let hhalted_prologue := prologueResult.halted
    let hpc_prologue := prologueResult.pc_eq
    -- Lift prologue steps to main program
    have hembed_prologue := prBaseCasePrologue_embed n pF pG
    have hsteps_prologue_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, setup.config.state⟩
        ⟨prBaseCasePC n + c_prologue.pc, c_prologue.state⟩ :=
      Steps.straightLine_at_offset (prBaseCasePC n) hsl_prologue hembed_prologue hsteps_prologue
    have hpc_after_prologue : prBaseCasePC n + c_prologue.pc = prPFOffset n pF pG := by
      simp only [prBaseCasePC, prPFOffset, prSetupPhaseLength, prBaseCasePrologueLength]
      rw [hpc_prologue, prBaseCasePrologue_length, prBaseCasePrologueLength]
    rw [hpc_after_prologue] at hsteps_prologue_lifted
    -- Combined: init → setup → prologue end
    have hsteps_to_pF : Steps (primitiveRecursionProgram n pF pG) (Config.init (List.ofFn (Fin.snoc inputs y)))
        ⟨prPFOffset n pF pG, c_prologue.state⟩ := by
      have h1 := setup.steps
      have hconfig : setup.config = ⟨prBaseCasePC n, setup.config.state⟩ := by
        ext; exact setup.pc_eq; rfl
      rw [hconfig] at h1
      exact Relation.ReflTransGen.trans h1 hsteps_prologue_lifted
    -- Now at prPFOffset, pF.shiftJumps runs
    -- After prologue, R[0..n-1] = inputs (restored from saved copies)
    have hR_after_prologue : ∀ i : Fin n, c_prologue.state.read i = inputs i := by
      intro i
      have h1 := prBaseCasePrologue_restores_inputs n pF pG setup.config.state c_prologue
        hsteps_prologue hhalted_prologue i
      rw [h1, setup.savedInputs_eq i]
    -- State agreement for pF execution
    let initState := (Config.init (List.ofFn inputs)).state
    have hagree_pF : c_prologue.state.agreeOn initState 0 pF.maxRegister :=
      agreeOn_after_copy_inputs (base := primitiveRecursionBase n pF pG)
        (fun j hj => hR_after_prologue ⟨j, hj⟩)
        (fun r hr_ge hr_le => prBaseCasePrologue_clears_above_n n pF pG setup.config.state c_prologue
          hsteps_prologue hhalted_prologue r hr_ge hr_le)
        (primitiveRecursionBase_ge_pF n pF pG)
    -- Now use agreeOn to transfer pF's divergence
    -- If pF doesn't halt on initState, it doesn't halt on c_prologue.state either (by agreeOn)
    have hpF_not_halts' : ¬Halts pF (List.ofFn inputs) := hpF_not_halts
    -- pF starting from c_prologue.state also diverges (by state agreement)
    -- This means pF.shiftJumps embedded at prPFOffset diverges
    -- So the overall program diverges from prPFOffset - contradiction with hHalts
    -- Use deterministic_continuation: if program halts, it must continue from prPFOffset
    have hContinuation' := Steps.deterministic_continuation hsteps_to_pF hFinal_steps hFinal_halted
    -- hContinuation' : Steps from ⟨prPFOffset, c_prologue.state⟩ to cFinal
    -- But pF diverges from this state, so we can't reach cFinal
    -- Need a lemma: if embedded pF diverges, main program diverges from prPFOffset
    -- Actually, use: if pF halts on initState (agreeing), then pF halts from c_prologue.state
    -- Contrapositive: if pF diverges from initState, it diverges from c_prologue.state
    -- First, show that if we can continue, pF must have halted
    -- The execution from prPFOffset must go through pF.shiftJumps
    -- If pF.shiftJumps halts, it means pF halts (standard form)
    -- Show: Steps from prPFOffset implies pF.shiftJumps halts, which implies pF halts
    -- Actually, easier: show that execution from ⟨0, c_prologue.state⟩ via pF halts
    -- by using the agreement and the shiftJumps embedding
    -- Define c₂ for pF execution
    let c₂ : Config := ⟨0, c_prologue.state⟩
    have hpc_c2 : (Config.init (List.ofFn inputs)).pc = c₂.pc := rfl
    have hagree_pF_symm : initState.agreeOn c₂.state 0 pF.maxRegister := State.agreeOn_symm hagree_pF
    -- If pF doesn't halt on initState, show it doesn't halt on c₂.state
    -- Then show the main program diverges
    -- Use: shiftJumps preserves halting behavior
    -- From prPFOffset, the main program runs pF.shiftJumps
    -- If pF halts on c₂.state, pF.shiftJumps halts at prPFOffset
    -- If pF doesn't halt on c₂.state, pF.shiftJumps diverges
    -- But hContinuation' says we reach cFinal, so pF.shiftJumps halted
    -- So pF halts on c₂.state
    -- By agreement, pF halts on initState
    -- Contradiction with hpF_not_halts
    -- Need lemma: agreeOn implies halting equivalence for pF
    have hpF_halts_iff : Halts pF (List.ofFn inputs) ↔ ∃ c, Steps pF c₂ c ∧ c.isHalted pF := by
      unfold Halts
      constructor
      · intro ⟨c, hsteps, hhalted⟩
        -- Use agreeOn to transfer execution
        have hagree_result := Steps.agreeOn hsteps hpc_c2 hagree_pF_symm
        let c' := Classical.choose hagree_result
        have hspec := Classical.choose_spec hagree_result
        have hsteps' : Steps pF c₂ c' := hspec.1
        have hpc' : c.pc = c'.pc := hspec.2.1
        exact ⟨c', hsteps', by simp only [Config.isHalted] at hhalted ⊢; omega⟩
      · intro ⟨c, hsteps, hhalted⟩
        -- Use agreeOn in reverse to transfer execution
        have hagree_result := Steps.agreeOn hsteps hpc_c2.symm hagree_pF
        let c' := Classical.choose hagree_result
        have hspec := Classical.choose_spec hagree_result
        have hsteps' : Steps pF (Config.init (List.ofFn inputs)) c' := hspec.1
        have hpc' : c.pc = c'.pc := hspec.2.1
        exact ⟨c', hsteps', by simp only [Config.isHalted] at hhalted ⊢; omega⟩
    -- Now show that pF halts on c₂.state (from the overall program halting)
    have hpF_halts_c2 : ∃ c, Steps pF c₂ c ∧ c.isHalted pF := by
      -- From hContinuation', we have steps from prPFOffset to cFinal
      -- These steps go through pF.shiftJumps
      -- Extract the pF.shiftJumps execution and convert to pF execution
      -- Use shiftJumps_halts_iff or similar lemma
      -- Actually, we need to show that cFinal.pc ≥ prPFOffset + pF.length
      -- which means pF.shiftJumps completed
      -- This is complex - let's use a simpler argument
      -- If pF doesn't halt from c₂.state, the main program diverges at prPFOffset
      -- But we have hContinuation' showing it continues to cFinal
      -- So pF must halt
      by_contra hpF_not_halts_c2
      push_neg at hpF_not_halts_c2
      -- pF diverges from c₂.state
      -- This means pF.shiftJumps diverges from ⟨prPFOffset, c₂.state⟩
      -- But that means the main program diverges - contradiction
      -- Use: shiftJumps at offset embedding + divergence propagation
      -- Actually, this requires showing that if pF.shiftJumps is embedded and pF diverges,
      -- then the main program diverges from that point
      -- This is a standard embedding/simulation lemma
      -- For now, use the fact that standard form programs have unique halting behavior
      -- If pF is standard form and doesn't halt, it diverges
      -- The shiftJumps embedding preserves this behavior
      -- So if pF.shiftJumps is running and pF diverges, main program diverges
      -- This contradicts hContinuation' reaching cFinal
      -- Let's use a more direct approach: show pF halts by using hpF_sf
      -- Actually, the issue is that hpF_not_halts_c2 says there's no halting config
      -- But hContinuation' gives us steps to cFinal
      -- If pF never halts, those steps must be infinite - contradiction
      -- This requires a lemma about infinite steps vs finite steps
      -- For now, use classical logic: pF either halts or diverges
      -- If it halts, we're done; if it diverges, main program diverges, contradiction
      -- Use the embedding lemma from shiftJumps
      have hembed := prPF_shiftJumps_embed n pF pG
      -- From prPFOffset, execution follows pF.shiftJumps
      -- If pF diverges from c₂, pF.shiftJumps diverges from prPFOffset in main program
      -- Use: for standard form pF, halting is equivalent
      -- This is getting complex. Let me use a key fact:
      -- If the main program halts, then from any intermediate config on the path,
      -- the continuation to the halt is well-defined.
      -- From prPFOffset, pF.shiftJumps runs for exactly pF.length steps (if pF halts) or forever
      -- Since cFinal.pc > prPFOffset + pF.length (it's in output phase), pF.shiftJumps finished
      -- So pF halts.
      -- Check: cFinal.isHalted means cFinal.pc ≥ primitiveRecursionProgram.length
      -- primitiveRecursionProgram.length = setup + baseCase + loopCheck + loopBody + output
      -- > prPFOffset + pF.length
      -- So pF.shiftJumps must have completed for execution to reach cFinal
      -- This means pF halted (by standard form: halts iff reaches length)
      -- Let's formalize this key step
      have hFinal_pc_ge : cFinal.pc ≥ (primitiveRecursionProgram n pF pG).length := by
        simp only [Config.isHalted] at hFinal_halted
        exact hFinal_halted
      have hPF_end_lt_prog_len : prPFOffset n pF pG + pF.length < (primitiveRecursionProgram n pF pG).length := by
        simp only [prPFOffset, primitiveRecursionProgram_length, prOutputPC, prLoopBodyPC,
          prLoopCheckPC, prSetupPhaseLength, prBaseCasePrologueLength, prBaseCasePhaseLength,
          prLoopBodyLength, prLoopPrologueLength, prLoopEpilogueLength]
        omega
      -- cFinal.pc > prPFOffset + pF.length, so execution passed through pF.shiftJumps completely
      -- This means there was a halting config for pF at prPFOffset + pF.length
      -- Extract pF's halting from the continuation
      -- Actually, use a helper: standard form pF embedded via shiftJumps halts iff pF halts
      -- And if pF is standard form, it halts at exactly pc = pF.length
      -- Since cFinal.pc ≥ prog.length > prPFOffset + pF.length, pF completed
      -- The continuation hContinuation' passes through ⟨prPFOffset + pF.length, _⟩
      -- This is the halt point for pF.shiftJumps
      -- So pF halts (by standard form characterization)
      -- Need: IsStandardForm.halts_iff_reaches_length or similar
      -- Use hpF_sf: pF is standard form means it halts iff pc reaches length
      -- From hContinuation', execution passes prPFOffset + pF.length
      -- So there was a config at pc = prPFOffset + pF.length on the path
      -- This means pF.shiftJumps halted, which means pF halted
      -- This is the key insight - let's formalize it
      -- Use helper lemma to extract pF halting from main program execution
      have hsteps_from_pF : Steps (primitiveRecursionProgram n pF pG) ⟨prPFOffset n pF pG + 0, c_prologue.state⟩ cFinal := by
        simp only [Nat.add_zero]; exact hContinuation'
      have hpc_ge' : cFinal.pc ≥ prPFOffset n pF pG + pF.length := by omega
      obtain ⟨c_pF, hpF_steps, hpF_pc⟩ := pF_halts_of_pr_exits_pF_region n pF pG hpF_sf 0 c_prologue.state cFinal
          (Nat.zero_le _) hsteps_from_pF hpc_ge'
      have hpF_halted : c_pF.isHalted pF := by simp only [Config.isHalted, hpF_pc]; exact Nat.le_refl _
      exact hpF_not_halts_c2 c_pF hpF_steps hpF_halted
    exact hpF_not_halts (hpF_halts_iff.mpr hpF_halts_c2)

  -- Part 2: Prove ∀ k < y, ∀ h : Pr(k).Dom, g(...).Dom
  · intro k hk hPr_k
    -- Given: Pr(inputs, k).Dom for some k < y
    -- Need: g(extendInputsForG inputs k (Pr(k).get)).Dom
    -- Strategy: Show pG halts at iteration k, then use hpG_spec
    -- From hPr_k and the forward direction, program halts on (inputs, k)
    -- But we're running on (inputs, y) with y > k
    -- At iteration k, pG runs on (inputs, k, acc_k) where acc_k = Pr(k).get (by acc_eq)
    -- If pG didn't halt at iteration k, the overall program wouldn't halt
    -- So pG halts, meaning g.Dom
    -- This requires tracing through k iterations and extracting pG halting
    -- Use strong induction: if we've done k iterations successfully, acc_k = Pr(k).get
    -- Then pG at iteration k must halt for the overall to halt
    -- By hpG_spec, g.Dom
    -- The key is that PrLoopKIterationsResult.acc_eq already captures this
    -- But we need to extract pG halting from the overall program halting
    -- For now, use contrapositive: if g not defined, pG doesn't halt, program diverges
    by_contra hg_not_dom
    have hpG_not_halts : ¬Halts pG (List.ofFn (extendInputsForG inputs k ((Pr f g (Fin.snoc inputs k)).get hPr_k))) := by
      intro hpG_halts
      exact hg_not_dom ((hpG_spec _).1.mp hpG_halts)
    -- If pG doesn't halt at iteration k, the overall program diverges
    -- But hHalts says it halts - contradiction
    -- To show this, trace execution to iteration k and show divergence
    -- First, by Pr(k).Dom, the program halts on (inputs, k) by the forward direction
    -- Wait, we don't need that. We just need to show that on (inputs, y):
    -- - Iterations 0, 1, ..., k run successfully (because Pr(j).Dom for j < k)
    -- - At iteration k, pG runs on (inputs, k, Pr(k).get)
    -- - If pG doesn't halt here, program diverges
    -- The accumulator value at iteration k equals Pr(k).get (by induction using acc_eq)
    -- So if pG doesn't halt on (inputs, k, Pr(k).get), program diverges
    -- This contradicts hHalts
    -- For this, we need:
    -- 1. After k iterations, counter = k, acc = Pr(k).get
    -- 2. At iteration k, pG runs on (inputs, k, acc) = (inputs, k, Pr(k).get)
    -- 3. If pG diverges, main program diverges
    -- Part 1 follows from pr_loop_k_iterations and acc_eq
    -- Part 2-3 follow from the embedding argument (similar to pF case above)
    obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ := hHalts
    -- Execute setup, base case, and k iterations
    let setup := prExecuteSetupPhase n pF pG inputs y
    -- pF halts (from Part 1 proof, but we need it here too)
    have hf_dom : (f inputs).Dom := by
      by_contra hf_not_dom
      -- Same argument as Part 1 - if f.Dom false, program diverges
      -- But we just proved Part 1, so f.Dom is true
      -- Actually, we can use that Part 1 is already proven
      -- But we're in the middle of the proof, so let's just derive it
      -- From hPr_k and k < y, we have Pr(k).Dom
      -- Pr(k).Dom implies f.Dom (by Pr_dom_iff induction)
      have hPr_0 := Pr_dom_of_dom_le inputs hPr_k (Nat.zero_le k)
      exact hf_not_dom ((Pr_dom_zero inputs).mp hPr_0)
    have hpF_halts : Halts pF (List.ofFn inputs) := (hpF_spec inputs).1.mpr hf_dom
    let baseCase := prExecuteBaseCasePhase n pF pG hpF_sf inputs y setup.config.state
      setup.savedInputs_eq hpF_halts
    -- For k iterations, we need Pr(k).Dom - which we have as hPr_k
    have hPr_dom_0 : (Pr f g (Fin.snoc inputs 0)).Dom := Pr_dom_of_dom_le inputs hPr_k (Nat.zero_le k)
    have hacc_eq_f : baseCase.config.state.read (prAccumulatorReg n pF pG) =
        (Pr f g (Fin.snoc inputs 0)).get hPr_dom_0 := by
      rw [baseCase.accumulator_eq]
      have hResult_eq := (hpF_spec inputs).2 hpF_halts hf_dom
      rw [hResult_eq]
      simp only [Pr_zero_spec]
    let loopResult_k := pr_loop_k_iterations n pF pG hpF_sf hpG_sf f g hpF_spec hpG_spec
      inputs y baseCase.config.state k (Nat.le_of_lt hk)
      (by rw [baseCase.counter_preserved, setup.counter_eq])
      (by rw [baseCase.savedY_preserved, setup.savedY_eq])
      (by rw [baseCase.zero_preserved, setup.zero_eq])
      (fun i => by rw [baseCase.savedInputs_preserved, setup.savedInputs_eq])
      hPr_k
      hacc_eq_f
    -- After k iterations, acc = Pr(k).get
    have hacc_k := loopResult_k.acc_eq hPr_k
    -- Now at loopCheckPC with counter = k < y, so loop continues
    -- Execute one more step: J instruction fails (k ≠ y), goes to loop body
    -- Then loop prologue runs, then pG runs
    -- If pG diverges, main program diverges
    -- But hHalts says it halts - contradiction
    -- The pG at iteration k gets inputs (inputs, k, acc_k) = (inputs, k, Pr(k).get)
    -- Which equals what hpG_not_halts says doesn't halt
    -- So main program diverges at iteration k's pG execution
    -- Trace to iteration k's pG start
    -- Steps: init → setup → base case → k iterations → loop check → loop body start → pG
    -- From loopResult_k.config, execute the k+1-th iteration's beginning
    have hJ_instr := prLoopCheck_embed n pF pG
    have hk_ne_y : k ≠ y := Nat.ne_of_lt hk
    have hcounter_ne_savedY : loopResult_k.config.state.read (prCounterReg n pF pG) ≠
        loopResult_k.config.state.read (prSavedYReg n pF pG) := by
      rw [loopResult_k.counter_eq, loopResult_k.savedY_eq]; exact hk_ne_y
    have hstep_J : Step (primitiveRecursionProgram n pF pG)
        ⟨prLoopCheckPC n pF pG, loopResult_k.config.state⟩
        ⟨prLoopCheckPC n pF pG + 1, loopResult_k.config.state⟩ :=
      Step.jump_ne hJ_instr hcounter_ne_savedY
    have hLoopBodyPC_eq : prLoopCheckPC n pF pG + 1 = prLoopBodyPC n pF pG := by
      simp only [prLoopBodyPC, prLoopCheckPC, prSetupPhaseLength, prBaseCasePhaseLength]
    -- Execute loop prologue
    have hsl_prologue := prLoopPrologue_isStraightLine n pF pG
    let prologueResult := straightLineExec hsl_prologue loopResult_k.config.state
    let c_prologue := prologueResult.config
    let hsteps_prologue := prologueResult.steps
    let hhalted_prologue := prologueResult.halted
    let hpc_prologue := prologueResult.pc_eq
    have hembed_prologue := prLoopPrologue_embed n pF pG
    have hsteps_prologue_lifted : Steps (primitiveRecursionProgram n pF pG)
        ⟨prLoopBodyPC n pF pG, loopResult_k.config.state⟩
        ⟨prLoopBodyPC n pF pG + c_prologue.pc, c_prologue.state⟩ :=
      Steps.straightLine_at_offset (prLoopBodyPC n pF pG) hsl_prologue hembed_prologue hsteps_prologue
    have hpc_after_prologue : prLoopBodyPC n pF pG + c_prologue.pc = prPGOffset n pF pG := by
      simp only [prLoopBodyPC, prPGOffset, prLoopCheckPC, prLoopPrologueLength]
      rw [hpc_prologue, prLoopPrologue_length, prLoopPrologueLength]
    rw [hpc_after_prologue] at hsteps_prologue_lifted
    -- Combined steps to prPGOffset
    have hsteps_to_loop_k : Steps (primitiveRecursionProgram n pF pG)
        (Config.init (List.ofFn (Fin.snoc inputs y)))
        ⟨prLoopCheckPC n pF pG, loopResult_k.config.state⟩ := by
      have h1 := setup.steps
      have h2 : Steps (primitiveRecursionProgram n pF pG) setup.config baseCase.config :=
        baseCase.steps
      have h3 : Steps (primitiveRecursionProgram n pF pG) baseCase.config loopResult_k.config :=
        loopResult_k.steps
      have hconfig : loopResult_k.config = ⟨prLoopCheckPC n pF pG, loopResult_k.config.state⟩ := by
        ext; exact loopResult_k.pc_eq; rfl
      rw [hconfig] at h3
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.trans h1 h2) h3
    have hsteps_to_pG : Steps (primitiveRecursionProgram n pF pG)
        (Config.init (List.ofFn (Fin.snoc inputs y)))
        ⟨prPGOffset n pF pG, c_prologue.state⟩ := by
      have h4 : Steps (primitiveRecursionProgram n pF pG)
          ⟨prLoopCheckPC n pF pG, loopResult_k.config.state⟩
          ⟨prPGOffset n pF pG, c_prologue.state⟩ := by
        have hstep := Relation.ReflTransGen.single hstep_J
        rw [hLoopBodyPC_eq] at hstep
        exact Relation.ReflTransGen.trans hstep hsteps_prologue_lifted
      exact Relation.ReflTransGen.trans hsteps_to_loop_k h4
    -- Now at prPGOffset, pG runs
    -- After loop prologue, R[0..n-1] = inputs, R[n] = k, R[n+1] = acc = Pr(k).get
    have hR_after_prologue_inputs : ∀ i : Fin n, c_prologue.state.read i = inputs i := by
      intro i
      have h := prLoopPrologue_restores_inputs n pF pG loopResult_k.config.state c_prologue
        hsteps_prologue hhalted_prologue i (fun _ => rfl)
      rw [h, loopResult_k.savedInputs_eq i]
    have hRn_after_prologue : c_prologue.state.read n = k := by
      have h := prLoopPrologue_sets_Rn n pF pG loopResult_k.config.state c_prologue
        hsteps_prologue hhalted_prologue
      rw [h, loopResult_k.counter_eq]
    have hRn1_after_prologue : c_prologue.state.read (n + 1) = (Pr f g (Fin.snoc inputs k)).get hPr_k := by
      have h := prLoopPrologue_sets_Rn1 n pF pG loopResult_k.config.state c_prologue
        hsteps_prologue hhalted_prologue
      rw [h, hacc_k]
    -- So pG runs on (inputs, k, Pr(k).get) = extendInputsForG inputs k (Pr(k).get)
    -- pG state agreement
    let initStateG := (Config.init (List.ofFn (extendInputsForG inputs k ((Pr f g (Fin.snoc inputs k)).get hPr_k)))).state
    have hagree_pG : c_prologue.state.agreeOn initStateG 0 pG.maxRegister := by
      intro r _ hr_hi
      by_cases hr_lt_n : r < n
      · have hleft : c_prologue.state.read r = inputs ⟨r, hr_lt_n⟩ := hR_after_prologue_inputs ⟨r, hr_lt_n⟩
        have hright : initStateG.read r = inputs ⟨r, hr_lt_n⟩ := by
          unfold initStateG Config.init State.fromInputs State.read
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          have hlen : r < (n + 2) := by omega
          simp only [hlen, ↓reduceDIte]
          exact extendInputsForG_castSucc_castSucc inputs k _ ⟨r, hr_lt_n⟩
        rw [hleft, hright]
      · by_cases hr_eq_n : r = n
        · rw [hr_eq_n]
          have hleft : c_prologue.state.read n = k := hRn_after_prologue
          have hright : initStateG.read n = k := by
            unfold initStateG Config.init State.fromInputs State.read
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            have hr : n < n + 2 := by omega
            simp only [hr, ↓reduceDIte]
            have heq : (⟨n, hr⟩ : Fin (n + 2)) = Fin.castSucc (Fin.last n) := by
              ext; simp [Fin.castSucc, Fin.last]
            rw [heq]
            exact extendInputsForG_castSucc_last inputs k _
          rw [hleft, hright]
        · by_cases hr_eq_n1 : r = n + 1
          · subst hr_eq_n1
            have hleft := hRn1_after_prologue
            have hright : initStateG.read (n + 1) = (Pr f g (Fin.snoc inputs k)).get hPr_k := by
              unfold initStateG Config.init State.fromInputs State.read
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
              have hlt : n + 1 < n + 2 := Nat.lt_succ_self _
              simp only [hlt, ↓reduceDIte, Option.getD_some]
              exact extendInputsForG_last inputs k _
            rw [hleft, hright]
          · have hr_gt_n1 : n + 1 < r := by omega
            have hleft : c_prologue.state.read r = 0 := by
              have hr_le_pG_max : r ≤ pG.maxRegister := hr_hi
              have hpG_le_base : pG.maxRegister ≤ primitiveRecursionBase n pF pG :=
                primitiveRecursionBase_ge_pG n pF pG
              have hr_le_base : r ≤ primitiveRecursionBase n pF pG := Nat.le_trans hr_le_pG_max hpG_le_base
              have hkr : r < (prLoopPrologue n pF pG).length := by
                simp only [prLoopPrologue, List.length_append, clearRegisters_length,
                  copyRegisterRange_length, List.length]; omega
              have hwrite : (prLoopPrologue n pF pG)[r] = Instr.Z r := by
                simp only [prLoopPrologue]
                have h_in_clear : r < (clearRegisters (primitiveRecursionBase n pF pG)).length := by
                  simp only [clearRegisters_length]; exact Nat.lt_succ_of_le hr_le_base
                have h_in_ext2 : r < (clearRegisters (primitiveRecursionBase n pF pG) ++
                    copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length := by
                  simp only [List.length_append, clearRegisters_length, copyRegisterRange_length]; omega
                rw [List.getElem_append_left h_in_ext2, List.getElem_append_left h_in_clear]
                simp only [Program.clearRegisters, List.getElem_map, List.getElem_range]
              have hnowrite : ∀ j (hj : j < (prLoopPrologue n pF pG).length), r < j →
                  ((prLoopPrologue n pF pG)[j]).writesTo ≠ some r := by
                intro j hj hjr
                simp only [prLoopPrologue, List.length_append, clearRegisters_length,
                  copyRegisterRange_length, List.length] at hj
                simp only [prLoopPrologue]
                by_cases hj_clear2 : j < (clearRegisters (primitiveRecursionBase n pF pG) ++
                    copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length
                · rw [List.getElem_append_left hj_clear2]
                  by_cases hj_in_clear : j < (clearRegisters (primitiveRecursionBase n pF pG)).length
                  · rw [List.getElem_append_left hj_in_clear]
                    simp only [Program.clearRegisters, List.getElem_map, List.getElem_range,
                      Instr.writesTo, ne_eq, Option.some.injEq]; omega
                  · rw [List.getElem_append_right (Nat.not_lt.mp hj_in_clear)]
                    simp only [clearRegisters_length, Program.copyRegisterRange, List.getElem_map,
                      List.getElem_range, Nat.zero_add, Instr.writesTo, ne_eq, Option.some.injEq]
                    simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear2
                    simp only [clearRegisters_length] at hj_in_clear; omega
                · rw [List.getElem_append_right (Nat.not_lt.mp hj_clear2)]
                  simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear2
                  simp only [List.length_append, clearRegisters_length, copyRegisterRange_length]
                  have hidx : j - (primitiveRecursionBase n pF pG + 1 + n) < 2 := by omega
                  by_cases hidx0 : j - (primitiveRecursionBase n pF pG + 1 + n) = 0
                  · simp only [hidx0, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]; omega
                  · have hidx1 : j - (primitiveRecursionBase n pF pG + 1 + n) = 1 := by omega
                    simp only [hidx1, List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo,
                      ne_eq, Option.some.injEq]; omega
              exact straightLine_zeros_register (prLoopPrologue_isStraightLine n pF pG)
                loopResult_k.config.state r r hkr hwrite hnowrite
            have hright : initStateG.read r = 0 := by
              unfold initStateG Config.init State.fromInputs State.read
              have hr_ge : ¬ r < n + 2 := by omega
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr_ge, dite_false, Option.getD_none]
            rw [hleft, hright]
    -- Now use the same argument as for pF: if pG doesn't halt, main program diverges
    let c₂G : Config := ⟨0, c_prologue.state⟩
    have hpc_c2G : (Config.init (List.ofFn (extendInputsForG inputs k ((Pr f g (Fin.snoc inputs k)).get hPr_k)))).pc = c₂G.pc := rfl
    have hagree_pG_symm : initStateG.agreeOn c₂G.state 0 pG.maxRegister := State.agreeOn_symm hagree_pG
    -- If pG doesn't halt on initStateG, show it doesn't halt on c₂G.state, then main diverges
    have hpG_halts_iff : Halts pG (List.ofFn (extendInputsForG inputs k ((Pr f g (Fin.snoc inputs k)).get hPr_k))) ↔
        ∃ c, Steps pG c₂G c ∧ c.isHalted pG := by
      unfold Halts
      constructor
      · intro ⟨c, hsteps, hhalted⟩
        have hagree_result := Steps.agreeOn hsteps hpc_c2G hagree_pG_symm
        let c' := Classical.choose hagree_result
        have hspec := Classical.choose_spec hagree_result
        have hsteps' : Steps pG c₂G c' := hspec.1
        have hpc' : c.pc = c'.pc := hspec.2.1
        exact ⟨c', hsteps', by simp only [Config.isHalted] at hhalted ⊢; omega⟩
      · intro ⟨c, hsteps, hhalted⟩
        have hagree_result := Steps.agreeOn hsteps hpc_c2G.symm hagree_pG
        let c' := Classical.choose hagree_result
        have hspec := Classical.choose_spec hagree_result
        have hsteps' : Steps pG (Config.init (List.ofFn (extendInputsForG inputs k ((Pr f g (Fin.snoc inputs k)).get hPr_k)))) c' := hspec.1
        have hpc' : c.pc = c'.pc := hspec.2.1
        exact ⟨c', hsteps', by simp only [Config.isHalted] at hhalted ⊢; omega⟩
    have hpG_halts_c2G : ∃ c, Steps pG c₂G c ∧ c.isHalted pG := by
      -- Same argument as pF: if pG diverges, main program diverges, contradiction
      -- Use deterministic_continuation and the fact that cFinal.pc is beyond pG
      have hContinuation := Steps.deterministic_continuation hsteps_to_pG hFinal_steps hFinal_halted
      -- hContinuation shows we reach cFinal from prPGOffset
      -- If pG diverges, this is impossible
      -- Therefore pG halts
      by_contra hpG_not_halts_c2G
      push_neg at hpG_not_halts_c2G
      exfalso
      -- Use helper lemma to extract pG halting from main program execution
      have hFinal_pc_ge : cFinal.pc ≥ (primitiveRecursionProgram n pF pG).length := by
        simp only [Config.isHalted] at hFinal_halted
        exact hFinal_halted
      have hPG_end_lt_prog_len : prPGOffset n pF pG + pG.length < (primitiveRecursionProgram n pF pG).length := by
        simp only [prPGOffset, primitiveRecursionProgram_length, prOutputPC, prLoopBodyPC,
          prLoopCheckPC, prSetupPhaseLength, prBaseCasePrologueLength, prBaseCasePhaseLength,
          prLoopBodyLength, prLoopPrologueLength, prLoopEpilogueLength]
        omega
      have hsteps_from_pG : Steps (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + 0, c_prologue.state⟩ cFinal := by
        simp only [Nat.add_zero]; exact hContinuation
      have hpc_ge' : cFinal.pc ≥ prPGOffset n pF pG + pG.length := by omega
      obtain ⟨c_pG, hpG_steps, hpG_pc⟩ := pG_halts_of_pr_exits_pG_region n pF pG hpG_sf 0 c_prologue.state cFinal
          (Nat.zero_le _) hsteps_from_pG hpc_ge'
      have hpG_halted : c_pG.isHalted pG := by simp only [Config.isHalted, hpG_pc]; exact Nat.le_refl _
      exact hpG_not_halts_c2G c_pG hpG_steps hpG_halted
    exact hpG_not_halts (hpG_halts_iff.mpr hpG_halts_c2G)

end Urm
