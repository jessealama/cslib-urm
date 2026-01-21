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
import Urm.Halting.PhaseExecution



/-! # Halting Proofs for Primitive Recursion

This file proves the halting properties of the primitive recursion witness program.

## Main results

- `primitiveRecursionProgram_halts`: If Pr domain, program halts
- `primitiveRecursionProgram_halts_imp_dom`: If program halts, Pr domain
-/

namespace Urm

open Program

variable (n : ℕ) (pF pG : Program)

/-! ## Embedding lemmas -/

/-- Setup phase is embedded at the start of the program. -/
theorem prSetupPhase_embed :
    ∀ i, i < (prSetupPhase n pF pG).length →
    (primitiveRecursionProgram n pF pG)[i]? = (prSetupPhase n pF pG)[i]? := by
  intro i hi
  simp only [primitiveRecursionProgram, List.getElem?_append, prSetupPhase_length,
    List.length_append, prBaseCasePhase_length, prLoopCheck_length, prLoopBody_length] at *
  split_ifs <;> first | rfl | omega

/-- Base case prologue is embedded after setup phase. -/
theorem prBaseCasePrologue_embed :
    ∀ i, i < (prBaseCasePrologue n pF pG).length →
    (primitiveRecursionProgram n pF pG)[prBaseCasePC n + i]? =
      (prBaseCasePrologue n pF pG)[i]? := by
  intro i hi
  simp only [primitiveRecursionProgram, prBaseCasePC, prBaseCasePhase, List.getElem?_append,
    prSetupPhase_length, prSetupPhaseLength, prBaseCasePrologue_length, prBaseCasePrologueLength,
    List.length_append, prLoopCheck_length, prLoopBody_length, shiftJumps_length] at *
  split_ifs <;> first | omega | (congr 1; omega)

/-- Shifted pF is embedded in the base case phase. -/
theorem prPF_shiftJumps_embed :
    ∀ i, i < pF.length →
    (primitiveRecursionProgram n pF pG)[prPFOffset n pF pG + i]? =
      (pF.shiftJumps (prPFOffset n pF pG))[i]? := by
  intro i hi
  simp only [primitiveRecursionProgram, prPFOffset, prBaseCasePhase, List.getElem?_append,
    prSetupPhase_length, prSetupPhaseLength, prBaseCasePrologueLength, prBaseCasePrologue_length,
    shiftJumps_length, List.length_append, prLoopCheck_length, prLoopBody_length]
  split_ifs <;> try omega
  simp only [shiftJumps, List.getElem?_map]
  congr 2; omega

/-- Loop check instruction embedding. -/
theorem prLoopCheck_embed :
    (primitiveRecursionProgram n pF pG)[prLoopCheckPC n pF pG]? =
      some (Instr.J (prCounterReg n pF pG) (prSavedYReg n pF pG) (prOutputPC n pF pG)) :=
  instr_at_loopCheck n pF pG

/-- Loop prologue is embedded at the start of loop body. -/
theorem prLoopPrologue_embed :
    ∀ i, i < (prLoopPrologue n pF pG).length →
    (primitiveRecursionProgram n pF pG)[prLoopBodyPC n pF pG + i]? =
      (prLoopPrologue n pF pG)[i]? := by
  intro i hi
  simp only [primitiveRecursionProgram, prLoopBodyPC_eq, prLoopBody, List.getElem?_append,
    prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length, prLoopPrologue_length,
    List.length_append, shiftJumps_length, prLoopEpilogue_length] at *
  split_ifs <;> first | omega | (congr 1; omega)

/-- Shifted pG is embedded in the loop body. -/
theorem prPG_shiftJumps_embed :
    ∀ i, i < pG.length →
    (primitiveRecursionProgram n pF pG)[prPGOffset n pF pG + i]? =
      (pG.shiftJumps (prPGOffset n pF pG))[i]? := by
  intro i hi
  simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody,
    List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length,
    prLoopPrologue_length, shiftJumps_length, List.length_append, prLoopEpilogue_length]
  split_ifs <;> try omega
  simp only [shiftJumps, List.getElem?_map]
  congr 2; omega

/-- Output phase is at outputPC. -/
theorem prOutputPhase_embed :
    (primitiveRecursionProgram n pF pG)[prOutputPC n pF pG]? =
      some (Instr.T (prAccumulatorReg n pF pG) 0) :=
  instr_at_output n pF pG

/-! ## Setup Phase Execution -/

/-- Result of executing the setup phase. -/
structure PrSetupPhaseResult (inputs : Fin n → ℕ) (y : ℕ) where
  /-- The configuration after setup phase execution -/
  config : Config
  steps : Steps (primitiveRecursionProgram n pF pG) (Config.init (List.ofFn (Fin.snoc inputs y))) config
  pc_eq : config.pc = prBaseCasePC n
  savedInputs_eq : ∀ i : Fin n, config.state.read (prSavedInputsStart n pF pG + i) = inputs i
  savedY_eq : config.state.read (prSavedYReg n pF pG) = y
  counter_eq : config.state.read (prCounterReg n pF pG) = 0
  zero_eq : config.state.read (prZeroReg n pF pG) = 0

/-- Execute the setup phase. -/
noncomputable def prExecuteSetupPhase (inputs : Fin n → ℕ) (y : ℕ) :
    PrSetupPhaseResult n pF pG inputs y :=
  let hsl_setup := prSetupPhase_isStraightLine n pF pG
  let initState := State.fromInputs (List.ofFn (Fin.snoc inputs y))
  let hembed : ∀ i, i < (prSetupPhase n pF pG).length →
      (primitiveRecursionProgram n pF pG)[0 + i]? = (prSetupPhase n pF pG)[i]? :=
    fun i hi => by simp only [Nat.zero_add]; exact prSetupPhase_embed n pF pG i hi
  let setupExec := execPhaseInHost hsl_setup 0 hembed initState
  let cSetup := setupExec.phaseResult.config

  let hSetup_steps_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨0, initState⟩
      ⟨prBaseCasePC n, cSetup.state⟩ := by
    have hpc : 0 + (prSetupPhase n pF pG).length = prBaseCasePC n := by
      simp only [prBaseCasePC, prSetupPhase_length, Nat.zero_add]
    exact hpc ▸ setupExec.liftedSteps

  let hSavedInputs : ∀ i : Fin n, cSetup.state.read (prSavedInputsStart n pF pG + i) = inputs i :=
    fun i => prSetupPhase_saves_inputs n pF pG inputs y initState rfl cSetup
      setupExec.localSteps setupExec.localHalted i
  let hSavedY : cSetup.state.read (prSavedYReg n pF pG) = y :=
    prSetupPhase_saves_y n pF pG inputs y initState rfl cSetup setupExec.localSteps setupExec.localHalted
  let hCounter : cSetup.state.read (prCounterReg n pF pG) = 0 :=
    prSetupPhase_counter_zero n pF pG initState cSetup setupExec.localSteps setupExec.localHalted
  let hZero : cSetup.state.read (prZeroReg n pF pG) = 0 :=
    prSetupPhase_zero_zero n pF pG initState cSetup setupExec.localSteps setupExec.localHalted

  { config := ⟨prBaseCasePC n, cSetup.state⟩
    steps := hSetup_steps_lifted
    pc_eq := rfl
    savedInputs_eq := hSavedInputs
    savedY_eq := hSavedY
    counter_eq := hCounter
    zero_eq := hZero }

/-! ## Base Case Phase Execution -/

/-- Result of executing the base case phase. -/
structure PrBaseCasePhaseResult (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (hpF_halts : Halts pF (List.ofFn inputs)) where
  /-- The configuration after base case phase execution -/
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
noncomputable def prExecuteBaseCasePhase (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (y : ℕ) (s : State)
    (hs_saved : ∀ i : Fin n, s.read (prSavedInputsStart n pF pG + i) = inputs i)
    (hpF_halts : Halts pF (List.ofFn inputs)) :
    PrBaseCasePhaseResult n pF pG inputs y s hpF_halts := by
  have hsl_prologue := prBaseCasePrologue_isStraightLine n pF pG
  let prologueExec := execPhaseInHost hsl_prologue (prBaseCasePC n) (prBaseCasePrologue_embed n pF pG) s
  let c_prologue := prologueExec.phaseResult.config

  have hsteps_prologue_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩
      ⟨prPFOffset n pF pG, c_prologue.state⟩ := by
    have hpc : prBaseCasePC n + (prBaseCasePrologue n pF pG).length = prPFOffset n pF pG := by
      simp only [prBaseCasePC, prPFOffset, prSetupPhaseLength, prBaseCasePrologueLength,
        prBaseCasePrologue_length]
    exact hpc ▸ prologueExec.liftedSteps

  have hR_after_prologue : ∀ i : Fin n, c_prologue.state.read i = inputs i := by
    intro i
    rw [prBaseCasePrologue_restores_inputs n pF pG s c_prologue
      prologueExec.localSteps prologueExec.localHalted i, hs_saved i]

  have hagree_pF : c_prologue.state.agreeOn (Config.init (List.ofFn inputs)).state 0 pF.maxRegister :=
    agreeOn_after_copy_inputs (base := primitiveRecursionBase n pF pG)
      (fun j hj => hR_after_prologue ⟨j, hj⟩)
      (fun r hr_ge hr_le => prBaseCasePrologue_clears_above_n n pF pG s c_prologue
        prologueExec.localSteps prologueExec.localHalted r hr_ge hr_le)
      (primitiveRecursionBase_ge_pF n pF pG)

  let pFExec := execSubprogramInHost hpF_sf (prPFOffset n pF pG) (prPF_shiftJumps_embed n pF pG)
    hpF_halts c_prologue.state hagree_pF
  let c_pF' := pFExec.finalState

  have hsteps_to_T : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩
      ⟨prPFOffset n pF pG + pF.length, c_pF'⟩ :=
    Relation.ReflTransGen.trans hsteps_prologue_lifted pFExec.liftedSteps

  have hT_pc : prPFOffset n pF pG + pF.length = prLoopCheckPC n pF pG - 1 := by
    simp only [prPFOffset, prLoopCheckPC, prSetupPhaseLength, prBaseCasePrologueLength,
      prBaseCasePhaseLength]
    omega

  have hT_instr : (primitiveRecursionProgram n pF pG)[prPFOffset n pF pG + pF.length]? =
      some (Instr.T 0 (prAccumulatorReg n pF pG)) := by
    simp only [primitiveRecursionProgram, prPFOffset, prBaseCasePhase, prSetupPhaseLength,
      List.getElem?_append, List.length_append, prBaseCasePrologue_length, shiftJumps_length,
      prBaseCasePrologueLength, prLoopCheck_length, prLoopBody_length, prSetupPhase_length, List.length]
    split_ifs <;> try omega
    simp only [show n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n) + pF.length - (n + 1 + 2) -
        (primitiveRecursionBase n pF pG + 1 + n + pF.length) = 0 by omega, List.getElem?_cons_zero]

  have hstep_T : Step (primitiveRecursionProgram n pF pG) ⟨prPFOffset n pF pG + pF.length, c_pF'⟩
      ⟨prPFOffset n pF pG + pF.length + 1, c_pF'.write (prAccumulatorReg n pF pG) (c_pF'.read 0)⟩ :=
    Step.trans hT_instr

  have hT_pc_eq : prPFOffset n pF pG + pF.length + 1 = prLoopCheckPC n pF pG := by
    simp only [prPFOffset, prLoopCheckPC, prSetupPhaseLength, prBaseCasePrologueLength,
      prBaseCasePhaseLength]
    omega

  let finalState := c_pF'.write (prAccumulatorReg n pF pG) (c_pF'.read 0)

  have hsteps_final : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩
      ⟨prLoopCheckPC n pF pG, finalState⟩ := by
    let h := Relation.ReflTransGen.trans hsteps_to_T (Relation.ReflTransGen.single hstep_T)
    rw [hT_pc_eq] at h
    exact h

  have hpF_preserves_high : ∀ r, pF.maxRegister < r → c_pF'.read r = c_prologue.state.read r :=
    pFExec.highPreserved

  have hprologue_preserves : ∀ r, primitiveRecursionBase n pF pG < r → c_prologue.state.read r = s.read r :=
    fun r hr => prBaseCasePrologue_preserves_high_register n pF pG s c_prologue prologueExec.localSteps prologueExec.localHalted r hr

  exact {
    config := ⟨prLoopCheckPC n pF pG, finalState⟩,
    steps := hsteps_final,
    pc_eq := rfl,
    accumulator_eq := by
      show finalState.read (prAccumulatorReg n pF pG) = Result pF (List.ofFn inputs) hpF_halts
      simp only [finalState, State.write_read_same]
      exact pFExec.result_eq,
    savedInputs_preserved := fun i => by
      simp only [finalState, State.write_read_diff _ _ _ _ (prSavedInput_ne_prAccumulatorReg n pF pG i)]
      rw [hpF_preserves_high _ (program_doesnt_touch_prSavedInputs n pF pG pF (primitiveRecursionBase_ge_pF n pF pG) i),
          hprologue_preserves _ (by have := prSavedInputsStart_gt_base n pF pG; omega)],
    savedY_preserved := by
      simp only [finalState, State.write_read_diff _ _ _ _ (prSavedYReg_ne_prAccumulatorReg n pF pG)]
      rw [hpF_preserves_high _ (program_doesnt_touch_prSavedYReg n pF pG pF (primitiveRecursionBase_ge_pF n pF pG)),
          hprologue_preserves _ (prSavedYReg_gt_base n pF pG)],
    counter_preserved := by
      simp only [finalState, State.write_read_diff _ _ _ _ (prCounterReg_ne_prAccumulatorReg n pF pG)]
      rw [hpF_preserves_high _ (program_doesnt_touch_prCounterReg n pF pG pF (primitiveRecursionBase_ge_pF n pF pG)),
          hprologue_preserves _ (prCounterReg_gt_base n pF pG)],
    zero_preserved := by
      simp only [finalState, State.write_read_diff _ _ _ _ (prAccumulatorReg_ne_prZeroReg n pF pG).symm]
      rw [hpF_preserves_high _ (program_doesnt_touch_prZeroReg n pF pG pF (primitiveRecursionBase_ge_pF n pF pG)),
          hprologue_preserves _ (prZeroReg_gt_base n pF pG)]
  }

/-! ## Loop Iteration -/

/-- Result of a single loop iteration from loopCheckPC.
    Tracks whether we exited (counter = savedY) or continued (counter < savedY). -/
structure PrLoopIterationResult (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (k : ℕ) (accBefore : ℕ) (hpG_halts : Halts pG (List.ofFn (extendInputsForG inputs k accBefore))) where
  /-- The configuration after loop iteration execution -/
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
noncomputable def pr_loop_iteration
    (hpG_sf : pG.IsStandardForm)
    (inputs : Fin n → ℕ) (y : ℕ) (s : State) (k : ℕ) (accBefore : ℕ)
    (hk_le_y : k ≤ y)
    (hs_counter : s.read (prCounterReg n pF pG) = k)
    (hs_savedY : s.read (prSavedYReg n pF pG) = y)
    (hs_acc : s.read (prAccumulatorReg n pF pG) = accBefore)
    (_hs_zero : s.read (prZeroReg n pF pG) = 0)
    (hs_saved : ∀ i : Fin n, s.read (prSavedInputsStart n pF pG + i) = inputs i)
    (hpG_halts : Halts pG (List.ofFn (extendInputsForG inputs k accBefore))) :
    PrLoopIterationResult n pF pG inputs y s k accBefore hpG_halts := by
  have hJ_instr := prLoopCheck_embed n pF pG

  by_cases hky : k = y
  · have heq : s.read (prCounterReg n pF pG) = s.read (prSavedYReg n pF pG) := by
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

  · have hne : s.read (prCounterReg n pF pG) ≠ s.read (prSavedYReg n pF pG) := by
      rw [hs_counter, hs_savedY]; exact hky
    have hstep_J : Step (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prLoopCheckPC n pF pG + 1, s⟩ := Step.jump_ne hJ_instr hne

    have hLoopBodyPC_eq : prLoopCheckPC n pF pG + 1 = prLoopBodyPC n pF pG := by
      simp only [prLoopBodyPC, prLoopCheckPC, prSetupPhaseLength, prBaseCasePhaseLength]

    have hsl_prologue := prLoopPrologue_isStraightLine n pF pG
    let prologueExec := execPhaseInHost hsl_prologue (prLoopBodyPC n pF pG) (prLoopPrologue_embed n pF pG) s
    let c_prologue := prologueExec.phaseResult.config

    have hpc_after_prologue : prLoopBodyPC n pF pG + (prLoopPrologue n pF pG).length = prPGOffset n pF pG := by
      simp only [prLoopBodyPC, prPGOffset, prLoopCheckPC, prLoopPrologueLength, prLoopPrologue_length]
    have hsteps_prologue_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopBodyPC n pF pG, s⟩
        ⟨prPGOffset n pF pG, c_prologue.state⟩ := hpc_after_prologue ▸ prologueExec.liftedSteps

    have hsteps_to_prologue_end : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prPGOffset n pF pG, c_prologue.state⟩ := by
      let h1 := Relation.ReflTransGen.single hstep_J
      rw [hLoopBodyPC_eq] at h1
      exact Relation.ReflTransGen.trans h1 hsteps_prologue_lifted

    have hR_after_prologue : ∀ i : Fin n, c_prologue.state.read i = inputs i := by
      intro i
      rw [prLoopPrologue_restores_inputs n pF pG s c_prologue
        prologueExec.localSteps prologueExec.localHalted i, hs_saved i]

    have hRn_after_prologue : c_prologue.state.read n = k := by
      rw [prLoopPrologue_sets_Rn n pF pG s c_prologue
        prologueExec.localSteps prologueExec.localHalted, hs_counter]

    have hRn1_after_prologue : c_prologue.state.read (n + 1) = accBefore := by
      rw [prLoopPrologue_sets_Rn1 n pF pG s c_prologue
        prologueExec.localSteps prologueExec.localHalted, hs_acc]

    have hagree_pG := prLoopPrologue_state_agreeOn_pG_init n pF pG s c_prologue
      prologueExec.localSteps prologueExec.localHalted inputs k accBefore
      hR_after_prologue hRn_after_prologue hRn1_after_prologue

    let pGExec := execSubprogramInHost hpG_sf (prPGOffset n pF pG) (prPG_shiftJumps_embed n pF pG)
      hpG_halts c_prologue.state hagree_pG
    let c_pG' := pGExec.finalState

    have hsteps_to_pG_end : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prPGOffset n pF pG + pG.length, c_pG'⟩ :=
      Relation.ReflTransGen.trans hsteps_to_prologue_end pGExec.liftedSteps

    have hT_instr : (primitiveRecursionProgram n pF pG)[prPGOffset n pF pG + pG.length]? =
        some (Instr.T 0 (prAccumulatorReg n pF pG)) := by
      simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody,
        prLoopEpilogue, List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length,
        prLoopCheck_length, prLoopPrologue_length, shiftJumps_length, List.length_append,
        prLoopPrologueLength, prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength, List.length]
      split_ifs <;> try omega
      simp only [show n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + pF.length + 1) + 1 +
          (primitiveRecursionBase n pF pG + 1 + n + 2) + pG.length -
          (n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + pF.length + 1) + 1) -
          (primitiveRecursionBase n pF pG + 1 + n + 2 + pG.length) = 0 by omega, List.getElem?_cons_zero]

    have hS_instr : (primitiveRecursionProgram n pF pG)[prPGOffset n pF pG + pG.length + 1]? =
        some (Instr.S (prCounterReg n pF pG)) := by
      simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody,
        prLoopEpilogue, List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length,
        prLoopCheck_length, prLoopPrologue_length, shiftJumps_length, List.length_append,
        prLoopPrologueLength, prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength, List.length]
      split_ifs <;> try omega
      simp only [show n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + pF.length + 1) + 1 +
          (primitiveRecursionBase n pF pG + 1 + n + 2) + pG.length + 1 -
          (n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + pF.length + 1) + 1) -
          (primitiveRecursionBase n pF pG + 1 + n + 2 + pG.length) = 1 by omega,
        List.getElem?_cons_succ, List.getElem?_cons_zero]

    have hJ_instr_epilogue : (primitiveRecursionProgram n pF pG)[prPGOffset n pF pG + pG.length + 2]? =
        some (Instr.J (prZeroReg n pF pG) (prZeroReg n pF pG) (prLoopCheckPC n pF pG)) := by
      simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody,
        prLoopEpilogue, List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length,
        prLoopCheck_length, prLoopPrologue_length, shiftJumps_length, List.length_append,
        prLoopPrologueLength, prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength, List.length]
      split_ifs <;> try omega
      simp only [show n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + pF.length + 1) + 1 +
          (primitiveRecursionBase n pF pG + 1 + n + 2) + pG.length + 2 -
          (n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n + pF.length + 1) + 1) -
          (primitiveRecursionBase n pF pG + 1 + n + 2 + pG.length) = 2 by omega,
        List.getElem?_cons_succ, List.getElem?_cons_zero]

    let state_after_T := c_pG'.write (prAccumulatorReg n pF pG) (c_pG'.read 0)
    have hstep_T : Step (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length, c_pG'⟩
        ⟨prPGOffset n pF pG + pG.length + 1, state_after_T⟩ :=
      Step.trans hT_instr

    let state_after_S := state_after_T.write (prCounterReg n pF pG) (state_after_T.read (prCounterReg n pF pG) + 1)
    have hstep_S : Step (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length + 1, state_after_T⟩
        ⟨prPGOffset n pF pG + pG.length + 2, state_after_S⟩ :=
      Step.succ hS_instr

    have hzero_eq : state_after_S.read (prZeroReg n pF pG) = state_after_S.read (prZeroReg n pF pG) := rfl
    have hstep_J_back : Step (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length + 2, state_after_S⟩
        ⟨prLoopCheckPC n pF pG, state_after_S⟩ :=
      Step.jump_eq hJ_instr_epilogue hzero_eq

    have hsteps_epilogue : Steps (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length, c_pG'⟩
        ⟨prLoopCheckPC n pF pG, state_after_S⟩ := by
      apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep_T)
      apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep_S)
      exact Relation.ReflTransGen.single hstep_J_back

    have hsteps_full : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prLoopCheckPC n pF pG, state_after_S⟩ :=
      Relation.ReflTransGen.trans hsteps_to_pG_end hsteps_epilogue

    have hpG_preserves_high : ∀ r, pG.maxRegister < r → c_pG'.read r = c_prologue.state.read r :=
      pGExec.highPreserved

    have hprologue_preserves : ∀ r, primitiveRecursionBase n pF pG < r → c_prologue.state.read r = s.read r :=
      fun r hr => prLoopPrologue_preserves_high_register n pF pG s c_prologue prologueExec.localSteps prologueExec.localHalted r hr

    have hcounter_after_S : state_after_S.read (prCounterReg n pF pG) = k + 1 := by
      simp only [state_after_S, State.write_read_same]
      let hne : prCounterReg n pF pG ≠ prAccumulatorReg n pF pG := by pr_register_omega
      let hcounter_after_T : state_after_T.read (prCounterReg n pF pG) = k := by
        simp only [state_after_T, State.write_read_diff _ _ _ _ hne]
        rw [pGExec.highPreserved (prCounterReg n pF pG)
            (program_doesnt_touch_prCounterReg n pF pG pG (primitiveRecursionBase_ge_pG n pF pG))]
        let h := prLoopPrologue_preserves_high_register n pF pG s c_prologue
          prologueExec.localSteps prologueExec.localHalted (prCounterReg n pF pG) (prCounterReg_gt_base n pF pG)
        rw [h, hs_counter]
      rw [hcounter_after_T]

    have hk_lt_y : k < y := Nat.lt_of_le_of_ne hk_le_y hky

    exact {
      config := ⟨prLoopCheckPC n pF pG, state_after_S⟩
      steps := hsteps_full
      outcome := Or.inr ⟨rfl, hk_lt_y⟩
      counter_next := fun _ => hcounter_after_S
      accumulator_updated := fun _ => by
        let hne_acc_counter : prAccumulatorReg n pF pG ≠ prCounterReg n pF pG := by pr_register_omega
        show state_after_S.read (prAccumulatorReg n pF pG) = _
        simp only [state_after_S, State.write_read_diff _ _ _ _ hne_acc_counter]
        simp only [state_after_T, State.write_read_same]
        exact pGExec.result_eq
      savedInputs_preserved := fun i => by
        simp only [state_after_S, State.write_read_diff _ _ _ _ (prSavedInput_ne_prCounterReg n pF pG i),
          state_after_T, State.write_read_diff _ _ _ _ (prSavedInput_ne_prAccumulatorReg n pF pG i)]
        rw [pGExec.highPreserved _ (program_doesnt_touch_prSavedInputs n pF pG pG (primitiveRecursionBase_ge_pG n pF pG) i),
            hprologue_preserves _ (by have := prSavedInputsStart_gt_base n pF pG; omega)]
      savedY_preserved := by
        simp only [state_after_S, State.write_read_diff _ _ _ _ (prSavedYReg_ne_prCounterReg n pF pG),
          state_after_T, State.write_read_diff _ _ _ _ (prSavedYReg_ne_prAccumulatorReg n pF pG)]
        rw [pGExec.highPreserved _ (program_doesnt_touch_prSavedYReg n pF pG pG (primitiveRecursionBase_ge_pG n pF pG)),
            hprologue_preserves _ (prSavedYReg_gt_base n pF pG)]
      zero_preserved := by
        simp only [state_after_S, State.write_read_diff _ _ _ _ (prCounterReg_ne_prZeroReg n pF pG).symm,
          state_after_T, State.write_read_diff _ _ _ _ (prAccumulatorReg_ne_prZeroReg n pF pG).symm]
        rw [pGExec.highPreserved _ (program_doesnt_touch_prZeroReg n pF pG pG (primitiveRecursionBase_ge_pG n pF pG)),
            hprologue_preserves _ (prZeroReg_gt_base n pF pG)]
    }

/-! ## K Iterations -/

/-- Result of k loop iterations. -/
structure PrLoopKIterationsResult (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (k : ℕ)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ) where
  /-- The configuration after k loop iterations -/
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
noncomputable def pr_loop_k_iterations
    (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
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
    have hPr_dom_m : (Pr f g (Fin.snoc inputs m)).Dom :=
      Pr_dom_of_dom_le inputs hPr_dom_k (Nat.le_succ m)

    have hm_le_y : m ≤ y := Nat.le_of_lt (Nat.lt_of_succ_le hk_le_y)
    let result_m := ih s hm_le_y hs_counter hs_savedY hs_zero hs_saved hPr_dom_m hs_acc

    let s_m := result_m.config.state
    have hcounter_m : s_m.read (prCounterReg n pF pG) = m := result_m.counter_eq
    have hsavedY_m : s_m.read (prSavedYReg n pF pG) = y := result_m.savedY_eq
    have hzero_m : s_m.read (prZeroReg n pF pG) = 0 := result_m.zero_eq
    have hsaved_m : ∀ i : Fin n, s_m.read (prSavedInputsStart n pF pG + i) = inputs i := result_m.savedInputs_eq

    have hacc_m : s_m.read (prAccumulatorReg n pF pG) = (Pr f g (Fin.snoc inputs m)).get hPr_dom_m :=
      result_m.acc_eq hPr_dom_m

    let hpG_halts_m : Halts pG (List.ofFn (extendInputsForG inputs m (s_m.read (prAccumulatorReg n pF pG)))) := by
      rw [hacc_m]
      let h := (Pr_dom_succ inputs m).mp hPr_dom_k
      let hg_dom := h.2 h.1
      rw [(hpG_spec (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))).1]
      exact hg_dom

    let one_iter := pr_loop_iteration n pF pG hpG_sf inputs y s_m m
      (s_m.read (prAccumulatorReg n pF pG)) hm_le_y hcounter_m hsavedY_m
      rfl hzero_m hsaved_m hpG_halts_m

    have hm_lt_y : m < y := Nat.lt_of_succ_le hk_le_y
    have hcontinue : one_iter.config.pc = prLoopCheckPC n pF pG ∧ m < y :=
      Or.resolve_left one_iter.outcome (fun hexit => Nat.lt_irrefl y (hexit.2 ▸ hm_lt_y))

    have hconfig_m : result_m.config = ⟨prLoopCheckPC n pF pG, s_m⟩ := by
      ext
      · exact result_m.pc_eq
      · rfl

    have hsteps_m' : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩ ⟨prLoopCheckPC n pF pG, s_m⟩ :=
      hconfig_m ▸ result_m.steps

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
        let h1 := one_iter.accumulator_updated hcontinue.1
        rw [h1]
        simp only [hacc_m]
        let hpG_halts_m' : Halts pG (List.ofFn (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))) := by
          simp only [← hacc_m]; exact hpG_halts_m
        let hg_dom : (g (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))).Dom := by
          rw [← (hpG_spec (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))).1]
          exact hpG_halts_m'
        let h2 := (hpG_spec (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))).2 hpG_halts_m' hg_dom
        rw [h2]
        rw [Pr_succ_spec inputs m hPr_dom_succ]
    }

/-! ## Output Phase -/

/-- Output phase halts and copies accumulator to R[0]. -/
theorem prOutputPhase_halts (s : State) :
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
theorem primitiveRecursionProgram_halts
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ)
    (hPr_dom : (Pr f g (Fin.snoc inputs y)).Dom) :
    Halts (primitiveRecursionProgram n pF pG) (List.ofFn (Fin.snoc inputs y)) := by
  let setup := prExecuteSetupPhase n pF pG inputs y

  have hf_dom : (f inputs).Dom := (Pr_dom_iff inputs y).mp hPr_dom |>.1
  have hpF_halts : Halts pF (List.ofFn inputs) := (hpF_spec inputs).1.mpr hf_dom
  let baseCase := prExecuteBaseCasePhase n pF pG hpF_sf inputs y setup.config.state
    setup.savedInputs_eq hpF_halts

  have hPr_dom_0 : (Pr f g (Fin.snoc inputs 0)).Dom := Pr_dom_of_dom_le inputs hPr_dom (Nat.zero_le y)
  let hacc_eq_f : baseCase.config.state.read (prAccumulatorReg n pF pG) =
      (Pr f g (Fin.snoc inputs 0)).get hPr_dom_0 := by
    rw [baseCase.accumulator_eq]
    let hResult_eq := (hpF_spec inputs).2 hpF_halts hf_dom
    rw [hResult_eq]
    simp only [Pr_zero_spec]

  let loopResult := pr_loop_k_iterations n pF pG hpG_sf f g hpG_spec
    inputs y baseCase.config.state y (Nat.le_refl y)
    (by rw [baseCase.counter_preserved, setup.counter_eq])
    (by rw [baseCase.savedY_preserved, setup.savedY_eq])
    (by rw [baseCase.zero_preserved, setup.zero_eq])
    (fun i => by rw [baseCase.savedInputs_preserved, setup.savedInputs_eq])
    hPr_dom
    hacc_eq_f

  have hJ_instr := prLoopCheck_embed n pF pG
  have hcounter_eq_savedY : loopResult.config.state.read (prCounterReg n pF pG) =
      loopResult.config.state.read (prSavedYReg n pF pG) := by
    rw [loopResult.counter_eq, loopResult.savedY_eq]
  have hstep_exit : Step (primitiveRecursionProgram n pF pG)
      ⟨prLoopCheckPC n pF pG, loopResult.config.state⟩
      ⟨prOutputPC n pF pG, loopResult.config.state⟩ :=
    Step.jump_eq hJ_instr hcounter_eq_savedY

  obtain ⟨finalConfig, hOutput_steps, hOutput_halted, _⟩ :=
    prOutputPhase_halts n pF pG loopResult.config.state

  have hconfig : loopResult.config = ⟨prLoopCheckPC n pF pG, loopResult.config.state⟩ := by
    ext; exact loopResult.pc_eq; rfl
  have hsteps_to_output : Steps (primitiveRecursionProgram n pF pG)
      (Config.init (List.ofFn (Fin.snoc inputs y))) ⟨prOutputPC n pF pG, loopResult.config.state⟩ :=
    setup.steps.trans (baseCase.steps.trans (loopResult.steps.trans (hconfig ▸ Steps.single hstep_exit)))

  exact ⟨finalConfig, hsteps_to_output.trans hOutput_steps, hOutput_halted⟩

/-- Helper: Extract pF halting from main program execution passing through pF region.
    If we start at prPFOffset + k and reach a config with pc ≥ prPFOffset + pF.length,
    then pF halts from ⟨k, state⟩. Uses strong induction on step count. -/
theorem pF_halts_of_pr_exits_pF_region
    (hpF_sf : pF.IsStandardForm) (k : ℕ) (state : State) (c : Config)
    (hk_le : k ≤ pF.length)
    (hsteps : Steps (primitiveRecursionProgram n pF pG) ⟨prPFOffset n pF pG + k, state⟩ c)
    (hpc_ge : c.pc ≥ prPFOffset n pF pG + pF.length) :
    ∃ c_pF, Steps pF ⟨k, state⟩ c_pF ∧ c_pF.pc = pF.length :=
  halts_of_exits_embedded_region (prPF_shiftJumps_embed n pF pG) hpF_sf k state c hk_le hsteps hpc_ge

/-- Helper: Extract pG halting from main program execution passing through pG region. -/
theorem pG_halts_of_pr_exits_pG_region
    (hpG_sf : pG.IsStandardForm) (k : ℕ) (state : State) (c : Config)
    (hk_le : k ≤ pG.length)
    (hsteps : Steps (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + k, state⟩ c)
    (hpc_ge : c.pc ≥ prPGOffset n pF pG + pG.length) :
    ∃ c_pG, Steps pG ⟨k, state⟩ c_pG ∧ c_pG.pc = pG.length :=
  halts_of_exits_embedded_region (prPG_shiftJumps_embed n pF pG) hpG_sf k state c hk_le hsteps hpc_ge

/-- If the primitive recursion program halts, Pr is defined. -/
theorem primitiveRecursionProgram_halts_imp_dom
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ)
    (hHalts : Halts (primitiveRecursionProgram n pF pG) (List.ofFn (Fin.snoc inputs y))) :
    (Pr f g (Fin.snoc inputs y)).Dom := by
  rw [Pr_dom_iff]
  constructor
  · by_contra hf_not_dom
    have hpF_not_halts : ¬Halts pF (List.ofFn inputs) := by
      intro hpF_halts
      exact hf_not_dom ((hpF_spec inputs).1.mp hpF_halts)
    obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ := hHalts
    let setup := prExecuteSetupPhase n pF pG inputs y
    have hContinuation := Steps.deterministic_continuation setup.steps hFinal_steps hFinal_halted
    have hsl_prologue := prBaseCasePrologue_isStraightLine n pF pG
    let prologueExec := execPhaseInHost hsl_prologue (prBaseCasePC n) (prBaseCasePrologue_embed n pF pG) setup.config.state
    let c_prologue := prologueExec.phaseResult.config
    have hpc_after_prologue : prBaseCasePC n + (prBaseCasePrologue n pF pG).length = prPFOffset n pF pG := by
      simp only [prBaseCasePC, prPFOffset, prSetupPhaseLength, prBaseCasePrologueLength, prBaseCasePrologue_length]
    have hsteps_prologue_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, setup.config.state⟩
        ⟨prPFOffset n pF pG, c_prologue.state⟩ := hpc_after_prologue ▸ prologueExec.liftedSteps
    let hsteps_to_pF : Steps (primitiveRecursionProgram n pF pG) (Config.init (List.ofFn (Fin.snoc inputs y)))
        ⟨prPFOffset n pF pG, c_prologue.state⟩ := by
      let h1 := setup.steps
      let hconfig : setup.config = ⟨prBaseCasePC n, setup.config.state⟩ := by
        ext; exact setup.pc_eq; rfl
      rw [hconfig] at h1
      exact Relation.ReflTransGen.trans h1 hsteps_prologue_lifted
    let hR_after_prologue : ∀ i : Fin n, c_prologue.state.read i = inputs i := by
      intro i
      rw [prBaseCasePrologue_restores_inputs n pF pG setup.config.state c_prologue
        prologueExec.localSteps prologueExec.localHalted i, setup.savedInputs_eq i]
    let initState := (Config.init (List.ofFn inputs)).state
    have hagree_pF : c_prologue.state.agreeOn initState 0 pF.maxRegister :=
      agreeOn_after_copy_inputs (base := primitiveRecursionBase n pF pG)
        (fun j hj => hR_after_prologue ⟨j, hj⟩)
        (fun r hr_ge hr_le => prBaseCasePrologue_clears_above_n n pF pG setup.config.state c_prologue
          prologueExec.localSteps prologueExec.localHalted r hr_ge hr_le)
        (primitiveRecursionBase_ge_pF n pF pG)
    have hpF_not_halts' : ¬Halts pF (List.ofFn inputs) := hpF_not_halts
    have hContinuation' := Steps.deterministic_continuation hsteps_to_pF hFinal_steps hFinal_halted
    let c₂ : Config := ⟨0, c_prologue.state⟩
    have hpc_c2 : (Config.init (List.ofFn inputs)).pc = c₂.pc := rfl
    have hpF_halts_iff : Halts pF (List.ofFn inputs) ↔ ∃ c, Steps pF c₂ c ∧ c.isHalted pF :=
      halts_iff_of_agreeing_state hpc_c2 (State.agreeOn_symm hagree_pF)
    have hpF_halts_c2 : ∃ c, Steps pF c₂ c ∧ c.isHalted pF := by
      by_contra hpF_not_halts_c2
      push_neg at hpF_not_halts_c2
      exfalso
      let hembed := prPF_shiftJumps_embed n pF pG
      let hFinal_pc_ge : cFinal.pc ≥ (primitiveRecursionProgram n pF pG).length := by
        simp only [Config.isHalted] at hFinal_halted
        exact hFinal_halted
      let hPF_end_lt_prog_len : prPFOffset n pF pG + pF.length < (primitiveRecursionProgram n pF pG).length := by
        simp only [prPFOffset, primitiveRecursionProgram_length, prOutputPC, prLoopBodyPC,
          prLoopCheckPC, prSetupPhaseLength, prBaseCasePrologueLength, prBaseCasePhaseLength,
          prLoopBodyLength, prLoopPrologueLength, prLoopEpilogueLength]
        omega
      let hsteps_from_pF : Steps (primitiveRecursionProgram n pF pG) ⟨prPFOffset n pF pG + 0, c_prologue.state⟩ cFinal := by
        simp only [Nat.add_zero]; exact hContinuation'
      let hpc_ge' : cFinal.pc ≥ prPFOffset n pF pG + pF.length := by omega
      obtain ⟨c_pF, hpF_steps, hpF_pc⟩ := pF_halts_of_pr_exits_pF_region n pF pG hpF_sf 0 c_prologue.state cFinal
          (Nat.zero_le _) hsteps_from_pF hpc_ge'
      let hpF_halted : c_pF.isHalted pF := by simp only [Config.isHalted, hpF_pc]; exact Nat.le_refl _
      exact hpF_not_halts_c2 c_pF hpF_steps hpF_halted
    exact hpF_not_halts (hpF_halts_iff.mpr hpF_halts_c2)

  · intro k hk hPr_k
    by_contra hg_not_dom
    have hpG_not_halts : ¬Halts pG (List.ofFn (extendInputsForG inputs k ((Pr f g (Fin.snoc inputs k)).get hPr_k))) := by
      intro hpG_halts
      exact hg_not_dom ((hpG_spec _).1.mp hpG_halts)
    obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ := hHalts
    let setup := prExecuteSetupPhase n pF pG inputs y
    have hf_dom : (f inputs).Dom := by
      by_contra hf_not_dom
      let hPr_0 := Pr_dom_of_dom_le inputs hPr_k (Nat.zero_le k)
      exact hf_not_dom ((Pr_dom_zero inputs).mp hPr_0)
    have hpF_halts : Halts pF (List.ofFn inputs) := (hpF_spec inputs).1.mpr hf_dom
    let baseCase := prExecuteBaseCasePhase n pF pG hpF_sf inputs y setup.config.state
      setup.savedInputs_eq hpF_halts
    have hPr_dom_0 : (Pr f g (Fin.snoc inputs 0)).Dom := Pr_dom_of_dom_le inputs hPr_k (Nat.zero_le k)
    let hacc_eq_f : baseCase.config.state.read (prAccumulatorReg n pF pG) =
        (Pr f g (Fin.snoc inputs 0)).get hPr_dom_0 := by
      rw [baseCase.accumulator_eq]
      let hResult_eq := (hpF_spec inputs).2 hpF_halts hf_dom
      rw [hResult_eq]
      simp only [Pr_zero_spec]
    let loopResult_k := pr_loop_k_iterations n pF pG hpG_sf f g hpG_spec
      inputs y baseCase.config.state k (Nat.le_of_lt hk)
      (by rw [baseCase.counter_preserved, setup.counter_eq])
      (by rw [baseCase.savedY_preserved, setup.savedY_eq])
      (by rw [baseCase.zero_preserved, setup.zero_eq])
      (fun i => by rw [baseCase.savedInputs_preserved, setup.savedInputs_eq])
      hPr_k
      hacc_eq_f
    have hacc_k := loopResult_k.acc_eq hPr_k
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
    have hsl_prologue := prLoopPrologue_isStraightLine n pF pG
    let prologueExec := execPhaseInHost hsl_prologue (prLoopBodyPC n pF pG) (prLoopPrologue_embed n pF pG) loopResult_k.config.state
    let c_prologue := prologueExec.phaseResult.config
    have hpc_after_prologue : prLoopBodyPC n pF pG + (prLoopPrologue n pF pG).length = prPGOffset n pF pG := by
      simp only [prLoopBodyPC, prPGOffset, prLoopCheckPC, prLoopPrologueLength, prLoopPrologue_length]
    have hsteps_prologue_lifted : Steps (primitiveRecursionProgram n pF pG)
        ⟨prLoopBodyPC n pF pG, loopResult_k.config.state⟩
        ⟨prPGOffset n pF pG, c_prologue.state⟩ := hpc_after_prologue ▸ prologueExec.liftedSteps
    have hconfig_k : loopResult_k.config = ⟨prLoopCheckPC n pF pG, loopResult_k.config.state⟩ := by
      ext; exact loopResult_k.pc_eq; rfl
    let hsteps_to_loop_k : Steps (primitiveRecursionProgram n pF pG)
        (Config.init (List.ofFn (Fin.snoc inputs y)))
        ⟨prLoopCheckPC n pF pG, loopResult_k.config.state⟩ :=
      setup.steps.trans (baseCase.steps.trans (hconfig_k ▸ loopResult_k.steps))
    let hsteps_to_pG : Steps (primitiveRecursionProgram n pF pG)
        (Config.init (List.ofFn (Fin.snoc inputs y)))
        ⟨prPGOffset n pF pG, c_prologue.state⟩ :=
      hsteps_to_loop_k.trans ((hLoopBodyPC_eq ▸ Steps.single hstep_J).trans hsteps_prologue_lifted)
    let hR_after_prologue_inputs : ∀ i : Fin n, c_prologue.state.read i = inputs i := by
      intro i
      rw [prLoopPrologue_restores_inputs n pF pG loopResult_k.config.state c_prologue
        prologueExec.localSteps prologueExec.localHalted i,
        loopResult_k.savedInputs_eq i]
    let hRn_after_prologue : c_prologue.state.read n = k := by
      rw [prLoopPrologue_sets_Rn n pF pG loopResult_k.config.state c_prologue
        prologueExec.localSteps prologueExec.localHalted, loopResult_k.counter_eq]
    let hRn1_after_prologue : c_prologue.state.read (n + 1) = (Pr f g (Fin.snoc inputs k)).get hPr_k := by
      rw [prLoopPrologue_sets_Rn1 n pF pG loopResult_k.config.state c_prologue
        prologueExec.localSteps prologueExec.localHalted, hacc_k]
    have hagree_pG := prLoopPrologue_state_agreeOn_pG_init n pF pG loopResult_k.config.state c_prologue
      prologueExec.localSteps prologueExec.localHalted inputs k ((Pr f g (Fin.snoc inputs k)).get hPr_k)
      hR_after_prologue_inputs hRn_after_prologue hRn1_after_prologue
    let c₂G : Config := ⟨0, c_prologue.state⟩
    have hpc_c2G : (Config.init (List.ofFn (extendInputsForG inputs k ((Pr f g (Fin.snoc inputs k)).get hPr_k)))).pc = c₂G.pc := rfl
    have hpG_halts_iff : Halts pG (List.ofFn (extendInputsForG inputs k ((Pr f g (Fin.snoc inputs k)).get hPr_k))) ↔
        ∃ c, Steps pG c₂G c ∧ c.isHalted pG :=
      halts_iff_of_agreeing_state hpc_c2G (State.agreeOn_symm hagree_pG)
    let hpG_halts_c2G : ∃ c, Steps pG c₂G c ∧ c.isHalted pG := by
      let hContinuation := Steps.deterministic_continuation hsteps_to_pG hFinal_steps hFinal_halted
      by_contra hpG_not_halts_c2G
      push_neg at hpG_not_halts_c2G
      exfalso
      let hFinal_pc_ge : cFinal.pc ≥ (primitiveRecursionProgram n pF pG).length := by
        simp only [Config.isHalted] at hFinal_halted
        exact hFinal_halted
      let hPG_end_lt_prog_len : prPGOffset n pF pG + pG.length < (primitiveRecursionProgram n pF pG).length := by
        simp only [prPGOffset, primitiveRecursionProgram_length, prOutputPC, prLoopBodyPC,
          prLoopCheckPC, prSetupPhaseLength, prBaseCasePrologueLength, prBaseCasePhaseLength,
          prLoopBodyLength, prLoopPrologueLength, prLoopEpilogueLength]
        omega
      let hsteps_from_pG : Steps (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + 0, c_prologue.state⟩ cFinal := by
        simp only [Nat.add_zero]; exact hContinuation
      let hpc_ge' : cFinal.pc ≥ prPGOffset n pF pG + pG.length := by omega
      obtain ⟨c_pG, hpG_steps, hpG_pc⟩ := pG_halts_of_pr_exits_pG_region n pF pG hpG_sf 0 c_prologue.state cFinal
          (Nat.zero_le _) hsteps_from_pG hpc_ge'
      let hpG_halted : c_pG.isHalted pG := by simp only [Config.isHalted, hpG_pc]; exact Nat.le_refl _
      exact hpG_not_halts_c2G c_pG hpG_steps hpG_halted
    exact hpG_not_halts (hpG_halts_iff.mpr hpG_halts_c2G)

end Urm
