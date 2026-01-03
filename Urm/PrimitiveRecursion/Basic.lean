/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.PrimitiveRecursion.Correctness

/-! # Primitive Recursion Closure Theorem

This file contains the main closure theorem for primitive recursion.

## Main results

- `URMComputableSF.primRec`: If f and g are SF-computable, so is Pr f g
- `URMComputable.primRec`: If f and g are computable, so is Pr f g
-/

namespace Urm

open Program

/-- Closure under primitive recursion for standard form computability. -/
theorem URMComputableSF.primRec {n : ℕ}
    {f : (Fin n → ℕ) → Part ℕ} {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (hf : URMComputableSF n f) (hg : URMComputableSF (n + 2) g) :
    URMComputableSF (n + 1) (PrFunction f g) := by
  obtain ⟨pF, hF_sf, hF_spec⟩ := hf
  obtain ⟨pG, hG_sf, hG_spec⟩ := hg
  refine ⟨primitiveRecursionProgram n pF pG,
          primitiveRecursionProgram_isStandardForm n pF pG hF_sf hG_sf,
          fun inputs => ?_⟩
  -- Extract x and y from inputs
  have hinputs_eq : inputs = Fin.snoc (initInputs inputs) (lastInput inputs) := by
    ext i
    by_cases hi : i.val < n
    · have heq : i = Fin.castSucc ⟨i.val, hi⟩ := by
        ext; simp
      rw [heq]; simp [Fin.snoc, initInputs]
    · have heq : i = Fin.last n := by
        ext
        have := i.isLt
        omega
      rw [heq]; simp [Fin.snoc, lastInput]
  rw [hinputs_eq]
  have x := initInputs inputs
  have y := lastInput inputs
  -- Apply the bundled spec
  have hspec := primitiveRecursionProgram_spec n pF pG hF_sf hG_sf f g
    (fun args => ⟨(hF_spec args).1, (hF_spec args).2⟩)
    (fun args => ⟨(hG_spec args).1, (hG_spec args).2⟩)
    x y
  simp only [PrFunction]
  exact hspec

/-- Closure under primitive recursion for general computability. -/
theorem URMComputable.primRec {n : ℕ}
    {f : (Fin n → ℕ) → Part ℕ} {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (hf : URMComputable n f) (hg : URMComputable (n + 2) g) :
    URMComputable (n + 1) (PrFunction f g) := by
  exact URMComputableSF.toComputable (URMComputableSF.primRec hf.toSF hg.toSF)

end Urm
