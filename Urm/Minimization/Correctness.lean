/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.Halting



/-! # Correctness Proofs for Minimization

This file proves the correctness of the minimization witness program:
- Halts ↔ μ f is defined
- Result equals μ f value

## Main results

- `minimize_program_iff_dom`: The program halts iff μ f is defined
- `minimize_program_result`: The result equals (μ f).get
-/

namespace Urm

open Program

/-! ## Result Correctness -/

/-- The result of minimize_program equals (μ f).get when both are defined. -/
theorem minimize_program_result (n : ℕ) (pF : Program)
    (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (minimize_program n pF) (List.ofFn inputs))
    (hDom : (μ f inputs).Dom) :
    Result (minimize_program n pF) (List.ofFn inputs) hHalts = (μ f inputs).get hDom := by
  let setup := executeSetupPhase n pF inputs
  have hHalts' := hHalts
  obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ := hHalts'
  have hLoopHalts : ∃ c, Steps (minimize_program n pF) ⟨loop_start_pc n, setup.state⟩ c ∧
      c.is_halted (minimize_program n pF) := by
    let hInit_eq : Config.init (List.ofFn inputs) = ⟨0, State.of_inputs (List.ofFn inputs)⟩ := rfl
    rw [hInit_eq] at hFinal_steps
    let hContinuation := Steps.deterministic_continuation setup.steps hFinal_steps hFinal_halted
    exact ⟨cFinal, hContinuation, hFinal_halted⟩
  let exitResult := loop_halts_exit n pF hpF_sf inputs setup.state
      setup.counter_eq setup.zero_eq setup.saved_eq hLoopHalts
  let k := exitResult.k
  obtain ⟨cOutput, hOutput_steps, hOutput_halted, hOutput_read⟩ := output_phase_halts n pF exitResult.config.state
  have hOutput_eq_k : cOutput.state.read 0 = k := by
    rw [hOutput_read, exitResult.counter_eq]
  have hTotal : Steps (minimize_program n pF) ⟨0, State.of_inputs (List.ofFn inputs)⟩ cOutput := by
    have h2' : Steps (minimize_program n pF) ⟨loop_start_pc n, setup.state⟩
        ⟨outputPC n pF, exitResult.config.state⟩ := by
      convert exitResult.steps using 2; exact exitResult.pc_eq.symm
    exact setup.steps.trans (h2'.trans hOutput_steps)
  have hFinal_eq_Output : cFinal = cOutput := by
    simp only [Config.init] at hFinal_steps
    exact Steps.eq_of_halts hFinal_steps hFinal_halted hTotal hOutput_halted
  have hResult_eq_k : Result (minimize_program n pF) (List.ofFn inputs) hHalts = k := by
    have hwit := Classical.choose_spec hHalts
    have hcFinal_is_witness : cFinal = Classical.choose hHalts :=
      Steps.eq_of_halts hFinal_steps hFinal_halted hwit.1 hwit.2
    simp only [Result, State.output, State.read] at hOutput_eq_k ⊢
    rw [← hcFinal_is_witness, hFinal_eq_Output, hOutput_eq_k]
  let k' := (μ f inputs).get hDom
  have hf_k'_zero : f (extend_inputs inputs k') = Part.some 0 := μ_spec hDom
  have hpF_halts_k := exitResult.pF_halts k (Nat.le_refl k)
  have hpF_result_zero := exitResult.pF_zero_at_k
  have hf_k_dom : (f (extend_inputs inputs k)).Dom := by
    rw [← (hpF_spec (extend_inputs inputs k)).1]
    exact hpF_halts_k
  have hf_k_get_zero : (f (extend_inputs inputs k)).get hf_k_dom = 0 := by
    let h := (hpF_spec (extend_inputs inputs k)).2 hpF_halts_k hf_k_dom
    rw [← h]
    convert hpF_result_zero using 2
  have hf_k_zero : f (extend_inputs inputs k) = Part.some 0 := by
    rw [Part.eq_some_iff, Part.mem_eq]
    exact ⟨hf_k_dom, hf_k_get_zero⟩
  have hk_eq_k' : k = k' := by
    apply Nat.le_antisymm
    · by_contra hk_gt
      push_neg at hk_gt
      have hpF_halts_k' := exitResult.pF_halts k' (Nat.le_of_lt hk_gt)
      have hpF_nonzero_k' := exitResult.pF_nonzero_below k' hk_gt
      have hf_k'_dom : (f (extend_inputs inputs k')).Dom := by
        rw [← (hpF_spec (extend_inputs inputs k')).1]; exact hpF_halts_k'
      have hf_k'_get : (f (extend_inputs inputs k')).get hf_k'_dom = 0 :=
        Part.get_eq_of_mem (Part.eq_some_iff.mp hf_k'_zero) hf_k'_dom
      rw [(hpF_spec (extend_inputs inputs k')).2 hpF_halts_k' hf_k'_dom, hf_k'_get] at hpF_nonzero_k'
      exact hpF_nonzero_k' rfl
    · by_contra hk'_gt
      push_neg at hk'_gt
      obtain ⟨v, hv_eq, hv_ne0⟩ := μ_min hDom hk'_gt
      rw [hf_k_zero] at hv_eq
      exact hv_ne0 (Part.some_inj.mp hv_eq.symm)
  rw [hResult_eq_k, hk_eq_k']

/-! ## Main Equivalence -/

/-- Combined halting equivalence: minimize_program halts iff μ f is defined. -/
theorem minimize_program_iff_dom (n : ℕ) (pF : Program)
    (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ) :
    Halts (minimize_program n pF) (List.ofFn inputs) ↔ (μ f inputs).Dom :=
  ⟨minimize_program_halts_imp_dom n pF hpF_sf f hpF_spec inputs,
   minimize_program_halts n pF hpF_sf f hpF_spec inputs⟩

/-! ## Bundled Specification -/

/-- Complete specification: Halts ↔ Dom and Result = get. -/
theorem minimize_program_spec (n : ℕ) (pF : Program)
    (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ) :
    (Halts (minimize_program n pF) (List.ofFn inputs) ↔ (μ f inputs).Dom) ∧
    ∀ hHalts hDom, Result (minimize_program n pF) (List.ofFn inputs) hHalts = (μ f inputs).get hDom :=
  ⟨minimize_program_iff_dom n pF hpF_sf f hpF_spec inputs,
   minimize_program_result n pF hpF_sf f hpF_spec inputs⟩

end Urm
