/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Construction

/-! # Standard Form Proofs for Composition -/

namespace Urm

open Program

theorem single_T_isStraightLine' (src dst : ℕ) : Program.isStraightLine [Instr.T src dst] = true := rfl

theorem gPhase_isStandardForm {base n : ℕ} {pG : Program} {i : ℕ} (hG : pG.IsStandardForm) :
    (gPhase base n pG i).IsStandardForm := by
  simp only [gPhase]
  exact (straightLine_isStandardForm (clearRegisters_isStraightLine base)).concat
    ((straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n)).concat
    (hG.concat (straightLine_isStandardForm (single_T_isStraightLine' 0 (base + n + 1 + i)))))

private theorem foldl_preserves_isStandardForm {α : Type*} (l : List α) (f : Program → α → Program)
    (hf : ∀ acc a, acc.IsStandardForm → (f acc a).IsStandardForm) (acc : Program) (hacc : acc.IsStandardForm) :
    (l.foldl f acc).IsStandardForm := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons x xs ih => simp only [List.foldl_cons]; exact ih (f acc x) (hf acc x hacc)

theorem allGPhases_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) : (allGPhases m n base pGs).IsStandardForm := by
  simp only [allGPhases]
  exact foldl_preserves_isStandardForm _ _ (fun acc i hacc => hacc.concat (gPhase_isStandardForm (hGs i)))
    [] (straightLine_isStandardForm rfl)

theorem finalPhase_isStandardForm {m n base : ℕ} {pF : Program} (hF : pF.IsStandardForm) :
    (finalPhase m n base pF).IsStandardForm := by
  simp only [finalPhase]
  exact (straightLine_isStandardForm (clearRegisters_isStraightLine base)).concat
    ((straightLine_isStandardForm (transferResultsToInputs_isStraightLine (base + n + 1) m)).concat hF)

theorem composeGeneral_isStandardForm {m n : ℕ} {pF : Program} {pGs : Fin m → Program}
    (hF : pF.IsStandardForm) (hGs : ∀ i, (pGs i).IsStandardForm) :
    (Program.composeGeneral m n pF pGs).IsStandardForm := by
  simp only [Program.composeGeneral]
  exact (straightLine_isStandardForm (copyRegisterRange_isStraightLine 0 (compositionBase m n pF pGs + 1) n)).concat
    ((allGPhases_isStandardForm hGs).concat (finalPhase_isStandardForm hF))

theorem allGPhases_prefix_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) (k : ℕ) : (allGPhases_prefix m n base pGs k).IsStandardForm := by
  simp only [allGPhases_prefix]
  exact foldl_preserves_isStandardForm _ _ (fun acc j hacc => hacc.concat (gPhase_isStandardForm (hGs j)))
    [] (straightLine_isStandardForm rfl)

theorem allGPhases_suffix_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) (k : ℕ) : (allGPhases_suffix m n base pGs k).IsStandardForm := by
  simp only [allGPhases_suffix]
  exact foldl_preserves_isStandardForm _ _ (fun acc j hacc => hacc.concat (gPhase_isStandardForm (hGs j)))
    [] (straightLine_isStandardForm rfl)

theorem saveInputs_isStandardForm (base n : ℕ) : (copyRegisterRange 0 (base + 1) n).IsStandardForm :=
  straightLine_isStandardForm (copyRegisterRange_isStraightLine 0 (base + 1) n)

end Urm
