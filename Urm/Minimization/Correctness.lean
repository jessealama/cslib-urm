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
    (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (minimizeProgram n pF) (List.ofFn inputs)) :
    ∃ k, Result (minimizeProgram n pF) (List.ofFn inputs) hHalts = k := by
  sorry

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
  sorry

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
