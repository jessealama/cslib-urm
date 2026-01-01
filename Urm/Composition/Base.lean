/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Helpers
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-! # Base Register Computation

Defines the base register for safe storage in general composition.

## Main definitions

- `maxGsRegister`: Maximum register used by any of the G programs
- `compositionBase`: The base register for safe storage in general composition

## Main results

- `compositionBase_ge_*`: Various bounds showing compositionBase is large enough
-/

namespace Urm

open Program

/-! ## Base Register Computation -/

/-- Maximum register used by any of the G programs. -/
def maxGsRegister (m : ℕ) (pGs : Fin m → Program) : ℕ :=
  Finset.univ.sup fun i => (pGs i).maxRegister

/-- The base register for safe storage in general composition.
This is at least (n-1) (to ensure input saving doesn't overlap with working registers),
at least (m-1) (to accommodate m-1 as a valid input register for f),
and above all registers used by F and all the Gᵢ. -/
def compositionBase (m n : ℕ) (pF : Program) (pGs : Fin m → Program) : ℕ :=
  max (n - 1) (max (m - 1) (max pF.maxRegister (maxGsRegister m pGs)))

theorem compositionBase_ge_n_sub_one (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    n - 1 ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, le_max_iff]; left; rfl

theorem compositionBase_ge_m_sub_one (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    m - 1 ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, le_max_iff]; right; left; rfl

theorem compositionBase_ge_F (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    pF.maxRegister ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, le_max_iff]; right; right; left; rfl

theorem compositionBase_ge_Gi (m n : ℕ) (pF : Program) (pGs : Fin m → Program) (i : Fin m) :
    (pGs i).maxRegister ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, maxGsRegister, le_max_iff]
  right; right; right
  exact @Finset.le_sup ℕ (Fin m) _ _ Finset.univ (fun j => (pGs j).maxRegister) i (Finset.mem_univ i)

/-- n ≤ compositionBase + 1 (derived from n - 1 ≤ compositionBase). -/
theorem compositionBase_ge_n (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    n ≤ compositionBase m n pF pGs + 1 := by
  have h := compositionBase_ge_n_sub_one m n pF pGs
  omega

/-- m ≤ compositionBase + 1 (derived from m - 1 ≤ compositionBase). -/
theorem compositionBase_ge_m (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    m ≤ compositionBase m n pF pGs + 1 := by
  have h := compositionBase_ge_m_sub_one m n pF pGs
  omega

/-- Alias: pF.maxRegister ≤ compositionBase. -/
theorem compositionBase_ge_pF_max (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    pF.maxRegister ≤ compositionBase m n pF pGs :=
  compositionBase_ge_F m n pF pGs

/-- Each pGs i has maxRegister ≤ compositionBase. -/
theorem compositionBase_ge_pGs_max (m n : ℕ) (pF : Program) (pGs : Fin m → Program) (i : Fin m) :
    (pGs i).maxRegister ≤ compositionBase m n pF pGs :=
  compositionBase_ge_Gi m n pF pGs i

end Urm
