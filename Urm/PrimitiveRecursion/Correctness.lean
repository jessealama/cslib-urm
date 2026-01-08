/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.PrimitiveRecursion.Halting



/-! # Correctness Proofs for Primitive Recursion

This file proves that the primitive recursion program computes the correct result.

## Main results

- `primitiveRecursionProgram_result`: The result equals (Pr f g inputs).get
-/

namespace Urm

open Program

/-- The result of the primitive recursion program equals the Pr function value. -/
theorem primitiveRecursionProgram_result (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ)
    (hHalts : Halts (primitiveRecursionProgram n pF pG) (List.ofFn (Fin.snoc inputs y)))
    (hPr_dom : (Pr f g (Fin.snoc inputs y)).Dom) :
    Result (primitiveRecursionProgram n pF pG) (List.ofFn (Fin.snoc inputs y)) hHalts =
      (Pr f g (Fin.snoc inputs y)).get hPr_dom := by
  -- Step 1: Execute setup phase
  let setup := prExecuteSetupPhase n pF pG inputs y

  -- Step 2: Execute base case phase
  have hf_dom : (f inputs).Dom := (Pr_dom_iff inputs y).mp hPr_dom |>.1
  have hpF_halts : Halts pF (List.ofFn inputs) := (hpF_spec inputs).1.mpr hf_dom
  let baseCase := prExecuteBaseCasePhase n pF pG hpF_sf inputs y setup.config.state
    setup.savedInputs_eq hpF_halts

  -- Step 3: Execute y loop iterations
  have hPr_dom_0 : (Pr f g (Fin.snoc inputs 0)).Dom := Pr_dom_of_dom_le inputs hPr_dom (Nat.zero_le y)
  have hacc_eq_f : baseCase.config.state.read (prAccumulatorReg n pF pG) =
      (Pr f g (Fin.snoc inputs 0)).get hPr_dom_0 := by
    rw [baseCase.accumulator_eq]
    let hResult_eq := (hpF_spec inputs).2 hpF_halts hf_dom
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

  -- After y iterations, accumulator = Pr(inputs, y).get
  have hacc_y : loopResult.config.state.read (prAccumulatorReg n pF pG) =
      (Pr f g (Fin.snoc inputs y)).get hPr_dom := loopResult.acc_eq hPr_dom

  -- Step 4: Execute exit jump (counter = y = savedY)
  have hJ_instr := prLoopCheck_embed n pF pG
  have hcounter_eq_savedY : loopResult.config.state.read (prCounterReg n pF pG) =
      loopResult.config.state.read (prSavedYReg n pF pG) := by
    rw [loopResult.counter_eq, loopResult.savedY_eq]
  have hstep_exit : Step (primitiveRecursionProgram n pF pG)
      ⟨prLoopCheckPC n pF pG, loopResult.config.state⟩
      ⟨prOutputPC n pF pG, loopResult.config.state⟩ :=
    Step.jump_eq hJ_instr hcounter_eq_savedY

  -- Step 5: Execute output phase
  obtain ⟨cOutput, hOutput_steps, hOutput_halted, hOutput_read⟩ :=
    prOutputPhase_halts n pF pG loopResult.config.state

  -- cOutput.state.read 0 = accumulator = Pr(inputs, y).get
  have hOutput_eq_Pr : cOutput.state.read 0 = (Pr f g (Fin.snoc inputs y)).get hPr_dom := by
    rw [hOutput_read, hacc_y]

  -- Step 6: Chain all steps together
  have hTotal : Steps (primitiveRecursionProgram n pF pG)
      (Config.init (List.ofFn (Fin.snoc inputs y))) cOutput := by
    -- init → prBaseCasePC (setup)
    let h1 := setup.steps
    -- prBaseCasePC → prLoopCheckPC (base case)
    let h2 : Steps (primitiveRecursionProgram n pF pG) setup.config baseCase.config :=
      baseCase.steps
    -- prLoopCheckPC → prLoopCheckPC with counter=y (loop iterations)
    let h3 : Steps (primitiveRecursionProgram n pF pG) baseCase.config loopResult.config :=
      loopResult.steps
    -- prLoopCheckPC → prOutputPC (exit jump)
    let hconfig : loopResult.config = ⟨prLoopCheckPC n pF pG, loopResult.config.state⟩ := by
      ext; exact loopResult.pc_eq; rfl
    let h4 : Steps (primitiveRecursionProgram n pF pG) loopResult.config
        ⟨prOutputPC n pF pG, loopResult.config.state⟩ := by
      rw [hconfig]
      exact Relation.ReflTransGen.single hstep_exit
    -- prOutputPC → halted (output)
    let h5 : Steps (primitiveRecursionProgram n pF pG)
        ⟨prOutputPC n pF pG, loopResult.config.state⟩ cOutput := hOutput_steps
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

  -- Step 7: Get the final config from hHalts (keep hHalts intact)
  have hHalts' := hHalts
  obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ := hHalts'

  -- By uniqueness of halting, cFinal = cOutput
  have hFinal_eq_Output : cFinal = cOutput :=
    Steps.halts_unique hFinal_steps hFinal_halted hTotal hOutput_halted

  -- Step 8: Result = cFinal.state.read 0 = cOutput.state.read 0 = Pr value
  let hwit := Classical.choose_spec hHalts
  have hcFinal_is_witness : cFinal = Classical.choose hHalts :=
    Steps.halts_unique hFinal_steps hFinal_halted hwit.1 hwit.2

  simp only [Result, State.output]
  rw [← hcFinal_is_witness, hFinal_eq_Output]
  exact hOutput_eq_Pr

/-- Bundled specification for primitive recursion program. -/
theorem primitiveRecursionProgram_spec (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ) :
    (Halts (primitiveRecursionProgram n pF pG) (List.ofFn (Fin.snoc inputs y)) ↔
      (Pr f g (Fin.snoc inputs y)).Dom) ∧
    ∀ hH hD, Result (primitiveRecursionProgram n pF pG) (List.ofFn (Fin.snoc inputs y)) hH =
      (Pr f g (Fin.snoc inputs y)).get hD := by
  constructor
  · constructor
    · intro hH
      exact primitiveRecursionProgram_halts_imp_dom n pF pG hpF_sf hpG_sf f g hpF_spec hpG_spec inputs y hH
    · intro hD
      exact primitiveRecursionProgram_halts n pF pG hpF_sf hpG_sf f g hpF_spec hpG_spec inputs y hD
  · intro hH hD
    exact primitiveRecursionProgram_result n pF pG hpF_sf hpG_sf f g hpF_spec hpG_spec inputs y hH hD

end Urm
