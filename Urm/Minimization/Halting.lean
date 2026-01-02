/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.Preservation

/-! # Halting Proofs for Minimization

This file proves halting properties for the minimization witness program.

## Main results

- `minimizeProgram_halts`: If μ f is defined, the minimization program halts
- Various lemmas about loop iteration behavior
-/

namespace Urm

open Program

/-! ## Loop Iteration Lemmas -/

/-- One complete loop iteration: from loopStart with counter = k,
    execute loop body once, either exit (if f returns 0) or return to loopStart with counter = k+1. -/
structure LoopIterationResult (n : ℕ) (pF : Program) (s : State) (k : ℕ) where
  /-- Final configuration after one iteration -/
  config : Config
  /-- Steps taken during this iteration -/
  steps : Steps (minimizeProgram n pF) ⟨loopStartPC n, s⟩ config
  /-- Either we exited to output, or we're back at loop start with incremented counter -/
  outcome : (config.pc = outputPC n pF ∧ s.read 0 = 0) ∨
            (config.pc = loopStartPC n ∧ config.state.read (counterReg n pF) = k + 1 ∧ s.read 0 ≠ 0)

/-- Execute one loop iteration when starting at loopStart. -/
def loop_iteration (n : ℕ) (pF : Program) (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (k : ℕ)
    (hs_counter : s.read (counterReg n pF) = k)
    (hs_zero : s.read (zeroReg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hf_halts : Halts pF (List.ofFn (extendInputs inputs k))) :
    LoopIterationResult n pF s k := by
  sorry

/-! ## Main Halting Theorem -/

/-- After k loop iterations starting from loopStart, we reach loopStart with counter = k
    (if f hasn't returned 0 on any earlier iteration). -/
theorem loop_k_iterations (n : ℕ) (pF : Program) (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (k : ℕ)
    (hs_counter : s.read (counterReg n pF) = 0)
    (hs_zero : s.read (zeroReg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hf_halts_below : ∀ j < k, Halts pF (List.ofFn (extendInputs inputs j)))
    (hf_nonzero_below : ∀ j (hj : j < k), Result pF (List.ofFn (extendInputs inputs j))
        (hf_halts_below j hj) ≠ 0) :
    ∃ c, Steps (minimizeProgram n pF) ⟨loopStartPC n, s⟩ c ∧
         c.pc = loopStartPC n ∧
         c.state.read (counterReg n pF) = k := by
  sorry

/-- If μ f is defined, then minimizeProgram halts. -/
theorem minimizeProgram_halts (n : ℕ) (pF : Program)
    (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ)
    (hμ_dom : (μ f inputs).Dom) :
    Halts (minimizeProgram n pF) (List.ofFn inputs) := by
  sorry

/-! ## Converse: Halts → Dom -/

/-- If minimizeProgram halts, then μ f is defined. -/
theorem minimizeProgram_halts_imp_dom (n : ℕ) (pF : Program)
    (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (minimizeProgram n pF) (List.ofFn inputs)) :
    (μ f inputs).Dom := by
  sorry

end Urm
