/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.Correctness
import Mathlib.Tactic.WLOG

/-! # Main Minimization Theorem

This file proves the main result: URM-computable functions are closed under
minimization (μ-recursion).

## Main results

- `URMComputableSF.min`: If f is SF-computable, then μ f is SF-computable
- `URMComputable.min`: If f is computable, then μ f is SF-computable

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

open Program

/-- Closure under minimization for standard form programs.
    If f : (Fin (n+1) → ℕ) → Part ℕ is computable by a standard form program,
    then μ f : (Fin n → ℕ) → Part ℕ is also computable by a standard form program. -/
theorem URMComputableSF.min {n : ℕ} {f : (Fin (n + 1) → ℕ) → Part ℕ}
    (hf : URMComputableSF (n + 1) f) : URMComputableSF n (μFunction f) := by
  obtain ⟨pF, hF_sf, hF_spec⟩ := hf
  refine ⟨minimizeProgram n pF, minimizeProgram_isStandardForm n pF hF_sf, fun inputs => ?_⟩
  exact minimizeProgram_spec n pF hF_sf f hF_spec inputs

/-- Closure under minimization for general URM-computable functions.
    This version relaxes the standard form requirement on the hypothesis -
    any URM-computable function f gives a standard form program for μ f.

    The proof uses wlog to reduce to the standard form case. -/
theorem URMComputable.min {n : ℕ} {f : (Fin (n + 1) → ℕ) → Part ℕ}
    (hf : URMComputable (n + 1) f) : URMComputableSF n (μFunction f) := by
  -- Reduce to standard form case using wlog
  wlog hf_sf : URMComputableSF (n + 1) f with h_reduce
  · exact h_reduce hf hf.toSF
  -- Now in SF case, apply existing theorem
  exact URMComputableSF.min hf_sf

end Urm

-- Export the main minimization theorems for easy access
export Urm (URMComputableSF.min URMComputable.min)
