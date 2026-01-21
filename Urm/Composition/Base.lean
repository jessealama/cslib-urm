/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Helpers
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-! # Base Register Computation for Composition -/

namespace Urm

open Program

/-- Maximum register used by any of the programs `pGs i`. -/
def max_gs_register (m : ℕ) (pGs : Fin m → Program) : ℕ := Finset.univ.sup fun i => (pGs i).max_register

/-- Base register for composition: ensures all working registers are above
    the input/output registers and the max registers used by pF and any pGs. -/
def composition_base (m n : ℕ) (pF : Program) (pGs : Fin m → Program) : ℕ :=
  max (n - 1) (max (m - 1) (max pF.max_register (max_gs_register m pGs)))

theorem composition_base_ge_n_sub_one (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    n - 1 ≤ composition_base m n pF pGs := by simp only [composition_base, le_max_iff]; left; rfl

theorem composition_base_ge_m_sub_one (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    m - 1 ≤ composition_base m n pF pGs := by simp only [composition_base, le_max_iff]; right; left; rfl

theorem composition_base_ge_F (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    pF.max_register ≤ composition_base m n pF pGs := by
  simp only [composition_base, le_max_iff]; right; right; left; rfl

theorem composition_base_ge_Gi (m n : ℕ) (pF : Program) (pGs : Fin m → Program) (i : Fin m) :
    (pGs i).max_register ≤ composition_base m n pF pGs := by
  simp only [composition_base, max_gs_register, le_max_iff]; right; right; right
  exact @Finset.le_sup ℕ (Fin m) _ _ Finset.univ (fun j => (pGs j).max_register) i (Finset.mem_univ i)

theorem composition_base_ge_n (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    n ≤ composition_base m n pF pGs + 1 := by have h := composition_base_ge_n_sub_one m n pF pGs; omega

theorem composition_base_ge_m (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    m ≤ composition_base m n pF pGs + 1 := by have h := composition_base_ge_m_sub_one m n pF pGs; omega

theorem composition_base_ge_pF_max (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    pF.max_register ≤ composition_base m n pF pGs := composition_base_ge_F m n pF pGs

theorem composition_base_ge_pGs_max (m n : ℕ) (pF : Program) (pGs : Fin m → Program) (i : Fin m) :
    (pGs i).max_register ≤ composition_base m n pF pGs := composition_base_ge_Gi m n pF pGs i

end Urm
