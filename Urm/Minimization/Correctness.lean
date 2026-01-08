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

- `minimizeProgram_iff_dom`: The program halts iff μ f is defined
- `minimizeProgram_result`: The result equals (μ f).get
-/

namespace Urm

open Program

/-! ## Result Correctness -/

/-- When minimizeProgram halts, R[0] contains the counter value (the minimal y). -/
theorem minimizeProgram_result_eq_counter (n : ℕ) (pF : Program)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (minimizeProgram n pF) (List.ofFn inputs)) :
    ∃ k, Result (minimizeProgram n pF) (List.ofFn inputs) hHalts = k :=
  ⟨_, rfl⟩

/-- The result of minimizeProgram equals (μ f).get when both are defined. -/
theorem minimizeProgram_result (n : ℕ) (pF : Program)
    (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (minimizeProgram n pF) (List.ofFn inputs))
    (hDom : (μ f inputs).Dom) :
    Result (minimizeProgram n pF) (List.ofFn inputs) hHalts = (μ f inputs).get hDom := by
  -- Step 1: Execute setup phase using helper
  let setup := executeSetupPhase n pF inputs

  -- Step 2: Get halting from loopStartPC
  -- Keep hHalts intact by using a copy
  have hHalts' := hHalts
  obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ := hHalts'

  have hLoopHalts : ∃ c, Steps (minimizeProgram n pF) ⟨loopStartPC n, setup.state⟩ c ∧
      c.isHalted (minimizeProgram n pF) := by
    let hInit_eq : Config.init (List.ofFn inputs) = ⟨0, State.fromInputs (List.ofFn inputs)⟩ := rfl
    rw [hInit_eq] at hFinal_steps
    let hContinuation := Steps.deterministic_continuation setup.steps hFinal_steps hFinal_halted
    exact ⟨cFinal, hContinuation, hFinal_halted⟩

  -- Step 3: Use loop_halts_exit to get the exit result
  let exitResult := loop_halts_exit n pF hpF_sf inputs setup.state
      setup.counter_eq setup.zero_eq setup.saved_eq hLoopHalts

  -- exitResult gives us k where pF(k) = 0 and pF(j) ≠ 0 for j < k
  let k := exitResult.k

  -- Step 4: Execute output phase from outputPC
  obtain ⟨cOutput, hOutput_steps, hOutput_halted, hOutput_read⟩ := outputPhase_halts n pF exitResult.config.state

  -- cOutput.state.read 0 = exitResult.config.state.read (counterReg n pF) = k
  have hOutput_eq_k : cOutput.state.read 0 = k := by
    rw [hOutput_read, exitResult.counter_eq]

  -- Step 5: Show that cOutput is the halted config for hHalts (by uniqueness)
  -- Total execution: init → setup → loop → output
  have hTotal : Steps (minimizeProgram n pF) ⟨0, State.fromInputs (List.ofFn inputs)⟩ cOutput := by
    let h1 : Steps (minimizeProgram n pF) ⟨0, State.fromInputs (List.ofFn inputs)⟩
        ⟨loopStartPC n, setup.state⟩ := setup.steps
    let h2 : Steps (minimizeProgram n pF) ⟨loopStartPC n, setup.state⟩ exitResult.config := exitResult.steps
    let h3 : Steps (minimizeProgram n pF) ⟨outputPC n pF, exitResult.config.state⟩ cOutput := hOutput_steps
    let h2' : Steps (minimizeProgram n pF) ⟨loopStartPC n, setup.state⟩
        ⟨outputPC n pF, exitResult.config.state⟩ := by
      convert h2 using 2; exact exitResult.pc_eq.symm
    exact h1.trans (h2'.trans h3)

  -- By uniqueness of halting, cFinal = cOutput
  have hFinal_eq_Output : cFinal = cOutput := by
    let hInit_eq : Config.init (List.ofFn inputs) = ⟨0, State.fromInputs (List.ofFn inputs)⟩ := rfl
    rw [hInit_eq] at hFinal_steps
    exact Steps.halts_unique hFinal_steps hFinal_halted hTotal hOutput_halted

  -- So Result = cFinal.state.read 0 = cOutput.state.read 0 = k
  have hResult_eq_k : Result (minimizeProgram n pF) (List.ofFn inputs) hHalts = k := by
    -- Result = (Classical.choose hHalts).state.output = cFinal.state.read 0
    let hcFinal_is_witness : cFinal = Classical.choose hHalts := by
      let hwit := Classical.choose_spec hHalts
      exact Steps.halts_unique hFinal_steps hFinal_halted hwit.1 hwit.2
    simp only [Result, State.output]
    rw [← hcFinal_is_witness, hFinal_eq_Output]
    exact hOutput_eq_k

  -- Step 6: Show k = (μ f inputs).get hDom
  -- Both are the minimal y where f returns 0

  -- Let k' = (μ f inputs).get hDom
  let k' := (μ f inputs).get hDom

  -- From μ_spec: f(k') = Part.some 0
  have hf_k'_zero : f (extendInputs inputs k') = Part.some 0 := μ_spec hDom

  -- From exitResult: pF(k) halts and Result = 0
  have hpF_halts_k := exitResult.pF_halts k (Nat.le_refl k)
  have hpF_result_zero := exitResult.pF_zero_at_k

  -- Convert pF result to f result
  have hf_k_dom : (f (extendInputs inputs k)).Dom := by
    rw [← (hpF_spec (extendInputs inputs k)).1]
    exact hpF_halts_k

  have hf_k_get_zero : (f (extendInputs inputs k)).get hf_k_dom = 0 := by
    let h := (hpF_spec (extendInputs inputs k)).2 hpF_halts_k hf_k_dom
    rw [← h]
    convert hpF_result_zero using 2

  have hf_k_zero : f (extendInputs inputs k) = Part.some 0 := by
    rw [Part.eq_some_iff, Part.mem_eq]
    exact ⟨hf_k_dom, hf_k_get_zero⟩

  -- Show k = k' by showing k ≤ k' and k' ≤ k
  have hk_eq_k' : k = k' := by
    apply Nat.le_antisymm
    · -- k ≤ k': If k > k', then f(k') = 0 but exitResult says f(j) ≠ 0 for j < k
      by_contra hk_gt
      push_neg at hk_gt
      let hk'_lt_k : k' < k := hk_gt
      -- For j < k, pF returns non-zero, hence f returns non-zero
      let hpF_halts_k' := exitResult.pF_halts k' (Nat.le_of_lt hk'_lt_k)
      let hpF_nonzero_k' := exitResult.pF_nonzero_below k' hk'_lt_k
      -- But f(k') = Part.some 0
      let hf_k'_dom : (f (extendInputs inputs k')).Dom := by
        rw [← (hpF_spec (extendInputs inputs k')).1]; exact hpF_halts_k'
      let hf_k'_get : (f (extendInputs inputs k')).get hf_k'_dom = 0 := by
        rw [Part.eq_some_iff] at hf_k'_zero
        exact Part.get_eq_of_mem hf_k'_zero hf_k'_dom
      let hpF_result_k' := (hpF_spec (extendInputs inputs k')).2 hpF_halts_k' hf_k'_dom
      -- pF result = f.get = 0, contradicting pF_nonzero_k'
      rw [hpF_result_k', hf_k'_get] at hpF_nonzero_k'
      exact hpF_nonzero_k' rfl
    · -- k' ≤ k: If k' > k, then f(k) = 0 but μ_min says f(j) ≠ 0 for j < k'
      by_contra hk'_gt
      push_neg at hk'_gt
      let hk_lt_k' : k < k' := hk'_gt
      -- By μ_min, for y' < k', f returns non-zero
      obtain ⟨v, hv_eq, hv_ne0⟩ := μ_min hDom hk_lt_k'
      rw [hf_k_zero] at hv_eq
      exact hv_ne0 (Part.some_inj.mp hv_eq.symm)

  -- Combine: Result = k = k' = (μ f inputs).get hDom
  rw [hResult_eq_k, hk_eq_k']

/-! ## Main Equivalence -/

/-- Combined halting equivalence: minimizeProgram halts iff μ f is defined. -/
theorem minimizeProgram_iff_dom (n : ℕ) (pF : Program)
    (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ) :
    Halts (minimizeProgram n pF) (List.ofFn inputs) ↔ (μ f inputs).Dom :=
  ⟨minimizeProgram_halts_imp_dom n pF hpF_sf f hpF_spec inputs,
   minimizeProgram_halts n pF hpF_sf f hpF_spec inputs⟩

/-! ## Bundled Specification -/

/-- Complete specification: Halts ↔ Dom and Result = get. -/
theorem minimizeProgram_spec (n : ℕ) (pF : Program)
    (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ) :
    (Halts (minimizeProgram n pF) (List.ofFn inputs) ↔ (μ f inputs).Dom) ∧
    ∀ hHalts hDom, Result (minimizeProgram n pF) (List.ofFn inputs) hHalts = (μ f inputs).get hDom :=
  ⟨minimizeProgram_iff_dom n pF hpF_sf f hpF_spec inputs,
   minimizeProgram_result n pF hpF_sf f hpF_spec inputs⟩

end Urm
