/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Construction

/-! # Standard Form Proofs

Proves that the general composition program is standard form.

## Main results

- `gPhase_isStandardForm`: gPhase is standard form when pG is
- `allGPhases_isStandardForm`: allGPhases is standard form
- `finalPhase_isStandardForm`: finalPhase is standard form
- `composeGeneral_isStandardForm`: composeGeneral is standard form
-/

namespace Urm

open Program

/-! ## Standard Form Proof -/

/-- Single transfer instruction is straight-line. -/
theorem single_T_isStraightLine' (src dst : ℕ) :
    Program.isStraightLine [Instr.T src dst] = true := rfl

/-- Helper: gPhase is standard form when pG is standard form. -/
theorem gPhase_isStandardForm {base n : ℕ} {pG : Program} {i : ℕ}
    (hG : pG.IsStandardForm) :
    (gPhase base n pG i).IsStandardForm := by
  simp only [gPhase]
  apply Program.IsStandardForm.concat (straightLine_isStandardForm (clearRegisters_isStraightLine base))
  apply Program.IsStandardForm.concat (straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n))
  apply Program.IsStandardForm.concat hG
  exact straightLine_isStandardForm (single_T_isStraightLine' 0 (base + n + 1 + i))

/-- Helper: foldl over a list preserves standard form when the combining function does. -/
private theorem foldl_preserves_isStandardForm
    {α : Type*} (l : List α) (f : Program → α → Program)
    (hf : ∀ acc a, acc.IsStandardForm → (f acc a).IsStandardForm)
    (acc : Program) (hacc : acc.IsStandardForm) :
    (l.foldl f acc).IsStandardForm := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (f acc x) (hf acc x hacc)

/-- allGPhases is standard form when all pGs are standard form. -/
theorem allGPhases_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) :
    (allGPhases m n base pGs).IsStandardForm := by
  simp only [allGPhases]
  apply foldl_preserves_isStandardForm
  · intro acc i hacc
    apply Program.IsStandardForm.concat hacc
    exact gPhase_isStandardForm (hGs i)
  · exact straightLine_isStandardForm rfl  -- empty program is straight-line

/-- finalPhase is standard form when pF is standard form. -/
theorem finalPhase_isStandardForm {m n base : ℕ} {pF : Program}
    (hF : pF.IsStandardForm) :
    (finalPhase m n base pF).IsStandardForm := by
  simp only [finalPhase]
  apply Program.IsStandardForm.concat (straightLine_isStandardForm (clearRegisters_isStraightLine base))
  apply Program.IsStandardForm.concat (straightLine_isStandardForm (transferResultsToInputs_isStraightLine (base + n + 1) m))
  exact hF

/-- composeGeneral is standard form when F and all Gs are standard form. -/
theorem composeGeneral_isStandardForm {m n : ℕ} {pF : Program} {pGs : Fin m → Program}
    (hF : pF.IsStandardForm)
    (hGs : ∀ i, (pGs i).IsStandardForm) :
    (Program.composeGeneral m n pF pGs).IsStandardForm := by
  simp only [Program.composeGeneral]
  apply Program.IsStandardForm.concat
    (straightLine_isStandardForm (copyRegisterRange_isStraightLine 0 (compositionBase m n pF pGs + 1) n))
  apply Program.IsStandardForm.concat (allGPhases_isStandardForm hGs)
  exact finalPhase_isStandardForm hF

/-! ## Standard Form Helpers for Prefix/Suffix -/

/-- allGPhases_prefix is standard form when all pGs are standard form. -/
theorem allGPhases_prefix_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) (k : ℕ) :
    (allGPhases_prefix m n base pGs k).IsStandardForm := by
  simp only [allGPhases_prefix]
  apply foldl_preserves_isStandardForm
  · intro acc j hacc
    apply Program.IsStandardForm.concat hacc
    exact gPhase_isStandardForm (hGs j)
  · exact straightLine_isStandardForm rfl

/-- allGPhases_suffix is standard form when all pGs are standard form. -/
theorem allGPhases_suffix_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) (k : ℕ) :
    (allGPhases_suffix m n base pGs k).IsStandardForm := by
  simp only [allGPhases_suffix]
  apply foldl_preserves_isStandardForm
  · intro acc j hacc
    apply Program.IsStandardForm.concat hacc
    exact gPhase_isStandardForm (hGs j)
  · exact straightLine_isStandardForm rfl

/-- saveInputs is standard form. -/
theorem saveInputs_isStandardForm (base n : ℕ) :
    (copyRegisterRange 0 (base + 1) n).IsStandardForm :=
  straightLine_isStandardForm (copyRegisterRange_isStraightLine 0 (base + 1) n)

end Urm
