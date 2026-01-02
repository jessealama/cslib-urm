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

def maxGsRegister (m : ℕ) (pGs : Fin m → Program) : ℕ := Finset.univ.sup fun i => (pGs i).maxRegister

def compositionBase (m n : ℕ) (pF : Program) (pGs : Fin m → Program) : ℕ :=
  max (n - 1) (max (m - 1) (max pF.maxRegister (maxGsRegister m pGs)))

theorem compositionBase_ge_n_sub_one (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    n - 1 ≤ compositionBase m n pF pGs := by simp only [compositionBase, le_max_iff]; left; rfl

theorem compositionBase_ge_m_sub_one (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    m - 1 ≤ compositionBase m n pF pGs := by simp only [compositionBase, le_max_iff]; right; left; rfl

theorem compositionBase_ge_F (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    pF.maxRegister ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, le_max_iff]; right; right; left; rfl

theorem compositionBase_ge_Gi (m n : ℕ) (pF : Program) (pGs : Fin m → Program) (i : Fin m) :
    (pGs i).maxRegister ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, maxGsRegister, le_max_iff]; right; right; right
  exact @Finset.le_sup ℕ (Fin m) _ _ Finset.univ (fun j => (pGs j).maxRegister) i (Finset.mem_univ i)

theorem compositionBase_ge_n (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    n ≤ compositionBase m n pF pGs + 1 := by have h := compositionBase_ge_n_sub_one m n pF pGs; omega

theorem compositionBase_ge_m (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    m ≤ compositionBase m n pF pGs + 1 := by have h := compositionBase_ge_m_sub_one m n pF pGs; omega

theorem compositionBase_ge_pF_max (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    pF.maxRegister ≤ compositionBase m n pF pGs := compositionBase_ge_F m n pF pGs

theorem compositionBase_ge_pGs_max (m n : ℕ) (pF : Program) (pGs : Fin m → Program) (i : Fin m) :
    (pGs i).maxRegister ≤ compositionBase m n pF pGs := compositionBase_ge_Gi m n pF pGs i

end Urm
