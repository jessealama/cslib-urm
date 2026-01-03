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
  sorry

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
