/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.PrimitiveRecursion.Halting



/-! # Correctness Proofs for Primitive Recursion

This file proves that the primitive recursion program computes the correct result.

## Main results

- `primitive_recursion_program_result`: The result equals (Pr f g inputs).get
-/

namespace Urm

open Program

/-- The result of the primitive recursion program equals the Pr function value. -/
theorem primitive_recursion_program_result (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ)
    (hHalts : Halts (primitive_recursion_program n pF pG) (List.ofFn (Fin.snoc inputs y)))
    (hPr_dom : (Pr f g (Fin.snoc inputs y)).Dom) :
    Result (primitive_recursion_program n pF pG) (List.ofFn (Fin.snoc inputs y)) hHalts =
      (Pr f g (Fin.snoc inputs y)).get hPr_dom := by
  let setup := pr_execute_setup_phase n pF pG inputs y
  have hf_dom : (f inputs).Dom := (Pr_dom_iff inputs y).mp hPr_dom |>.1
  have hpF_halts : Halts pF (List.ofFn inputs) := (hpF_spec inputs).1.mpr hf_dom
  let baseCase := pr_execute_base_case_phase n pF pG hpF_sf inputs y setup.config.state
    setup.savedInputs_eq hpF_halts
  have hPr_dom_0 : (Pr f g (Fin.snoc inputs 0)).Dom := Pr_dom_of_dom_le inputs hPr_dom (Nat.zero_le y)
  have hacc_eq_f : baseCase.config.state.read (pr_accumulator_reg n pF pG) =
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
  have hacc_y : loopResult.config.state.read (pr_accumulator_reg n pF pG) =
      (Pr f g (Fin.snoc inputs y)).get hPr_dom := loopResult.acc_eq hPr_dom
  have hJ_instr := pr_loop_check_embed n pF pG
  have hcounter_eq_savedY : loopResult.config.state.read (pr_counter_reg n pF pG) =
      loopResult.config.state.read (pr_saved_y_reg n pF pG) := by
    rw [loopResult.counter_eq, loopResult.savedY_eq]
  have hstep_exit : Step (primitive_recursion_program n pF pG)
      ⟨pr_loop_check_pc n pF pG, loopResult.config.state⟩
      ⟨pr_output_pc n pF pG, loopResult.config.state⟩ :=
    Step.jump_eq hJ_instr hcounter_eq_savedY
  obtain ⟨cOutput, hOutput_steps, hOutput_halted, hOutput_read⟩ :=
    pr_output_phase_halts n pF pG loopResult.config.state
  have hOutput_eq_Pr : cOutput.state.read 0 = (Pr f g (Fin.snoc inputs y)).get hPr_dom := by
    rw [hOutput_read, hacc_y]
  have hTotal : Steps (primitive_recursion_program n pF pG)
      (Config.init (List.ofFn (Fin.snoc inputs y))) cOutput := by
    have hconfig : loopResult.config = ⟨pr_loop_check_pc n pF pG, loopResult.config.state⟩ := by
      ext; exact loopResult.pc_eq; rfl
    have h4 : Steps (primitive_recursion_program n pF pG) loopResult.config
        ⟨pr_output_pc n pF pG, loopResult.config.state⟩ := by
      rw [hconfig]; exact Relation.ReflTransGen.single hstep_exit
    exact setup.steps.trans (baseCase.steps.trans (loopResult.steps.trans (h4.trans hOutput_steps)))
  have hHalts' := hHalts
  obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ := hHalts'
  have hFinal_eq_Output : cFinal = cOutput :=
    Steps.eq_of_halts hFinal_steps hFinal_halted hTotal hOutput_halted
  have hwit := Classical.choose_spec hHalts
  have hcFinal_is_witness : cFinal = Classical.choose hHalts :=
    Steps.eq_of_halts hFinal_steps hFinal_halted hwit.1 hwit.2
  simp only [Result, State.output]
  rw [← hcFinal_is_witness, hFinal_eq_Output]
  exact hOutput_eq_Pr

/-- Bundled specification for primitive recursion program. -/
theorem primitive_recursion_program_spec (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ) :
    (Halts (primitive_recursion_program n pF pG) (List.ofFn (Fin.snoc inputs y)) ↔
      (Pr f g (Fin.snoc inputs y)).Dom) ∧
    ∀ hH hD, Result (primitive_recursion_program n pF pG) (List.ofFn (Fin.snoc inputs y)) hH =
      (Pr f g (Fin.snoc inputs y)).get hD := by
  constructor
  · constructor
    · intro hH
      exact primitive_recursion_program_halts_imp_dom n pF pG hpF_sf hpG_sf f g hpF_spec hpG_spec inputs y hH
    · intro hD
      exact primitive_recursion_program_halts n pF pG hpF_sf hpG_sf f g hpF_spec hpG_spec inputs y hD
  · intro hH hD
    exact primitive_recursion_program_result n pF pG hpF_sf hpG_sf f g hpF_spec hpG_spec inputs y hH hD

end Urm
