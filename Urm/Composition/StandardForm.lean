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

theorem single_T_isStandardForm (src dst : ℕ) : Program.IsStandardForm [Instr.T src dst] :=
  straightLine_isStandardForm (single_T_isStraightLine' src dst)

theorem gPhase_isStandardForm {base n : ℕ} {pG : Program} {i : ℕ} (hG : pG.IsStandardForm) :
    (gPhase base n pG i).IsStandardForm := by
  simp only [gPhase]
  exact (clearRegisters_isStandardForm base).concat
    ((copyRegisterRange_isStandardForm (base + 1) 0 n).concat
    (hG.concat (single_T_isStandardForm 0 (base + n + 1 + i))))

private theorem prod_preserves_isStandardForm (l : List Program)
    (hl : ∀ p ∈ l, p.IsStandardForm) : l.prod.IsStandardForm := by
  induction l with
  | nil => exact straightLine_isStandardForm rfl
  | cons x xs ih =>
    rw [List.prod_cons]
    show (x.concat xs.prod).IsStandardForm
    exact Program.IsStandardForm.concat (hl x List.mem_cons_self)
      (ih (fun p hp => hl p (List.mem_cons_of_mem x hp)))

theorem allGPhases_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) : (allGPhases m n base pGs).IsStandardForm := by
  unfold allGPhases gPhaseList
  exact prod_preserves_isStandardForm _ (fun p hp => by
    simp only [List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact gPhase_isStandardForm (hGs i))

theorem finalPhase_isStandardForm {m n base : ℕ} {pF : Program} (hF : pF.IsStandardForm) :
    (finalPhase m n base pF).IsStandardForm := by
  simp only [finalPhase]
  exact (clearRegisters_isStandardForm base).concat
    ((transferResultsToInputs_isStandardForm (base + n + 1) m).concat hF)

theorem composeGeneral_isStandardForm {m n : ℕ} {pF : Program} {pGs : Fin m → Program}
    (hF : pF.IsStandardForm) (hGs : ∀ i, (pGs i).IsStandardForm) :
    (Program.composeGeneral m n pF pGs).IsStandardForm := by
  simp only [Program.composeGeneral]
  exact (copyRegisterRange_isStandardForm 0 (compositionBase m n pF pGs + 1) n).concat
    ((allGPhases_isStandardForm hGs).concat (finalPhase_isStandardForm hF))

theorem allGPhases_prefix_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) (k : ℕ) : (allGPhases_prefix m n base pGs k).IsStandardForm := by
  unfold allGPhases_prefix gPhaseList
  exact prod_preserves_isStandardForm _ (fun p hp => by
    simp only [List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact gPhase_isStandardForm (hGs i))

theorem allGPhases_suffix_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) (k : ℕ) : (allGPhases_suffix m n base pGs k).IsStandardForm := by
  unfold allGPhases_suffix gPhaseList
  exact prod_preserves_isStandardForm _ (fun p hp => by
    simp only [List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact gPhase_isStandardForm (hGs i))

theorem saveInputs_isStandardForm (base n : ℕ) : (copyRegisterRange 0 (base + 1) n).IsStandardForm :=
  copyRegisterRange_isStandardForm 0 (base + 1) n

end Urm
