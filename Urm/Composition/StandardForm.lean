/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Construction

/-! # Standard Form Proofs for Composition -/

namespace Urm

open Program

theorem single_T_is_straight_line' (src dst : ℕ) : Program.is_straight_line [Instr.T src dst] = true := rfl

theorem single_T_isStandardForm (src dst : ℕ) : Program.IsStandardForm [Instr.T src dst] :=
  straight_line_isStandardForm (single_T_is_straight_line' src dst)

theorem g_phase_isStandardForm {base n : ℕ} {pG : Program} {i : ℕ} (hG : pG.IsStandardForm) :
    (g_phase base n pG i).IsStandardForm := by
  simp only [g_phase]
  exact (clear_registers_isStandardForm base).concat
    ((copy_register_range_isStandardForm (base + 1) 0 n).concat
    (hG.concat (single_T_isStandardForm 0 (base + n + 1 + i))))

private theorem prod_preserves_isStandardForm (l : List Program)
    (hl : ∀ p ∈ l, p.IsStandardForm) : l.prod.IsStandardForm := by
  induction l with
  | nil => exact straight_line_isStandardForm rfl
  | cons x xs ih =>
    rw [List.prod_cons]
    show (x.concat xs.prod).IsStandardForm
    exact Program.IsStandardForm.concat (hl x List.mem_cons_self)
      (ih (fun p hp => hl p (List.mem_cons_of_mem x hp)))

theorem all_g_phases_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) : (all_g_phases m n base pGs).IsStandardForm := by
  unfold all_g_phases g_phaseList
  exact prod_preserves_isStandardForm _ (fun p hp => by
    simp only [List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact g_phase_isStandardForm (hGs i))

theorem final_phase_isStandardForm {m n base : ℕ} {pF : Program} (hF : pF.IsStandardForm) :
    (final_phase m n base pF).IsStandardForm := by
  simp only [final_phase]
  exact (clear_registers_isStandardForm base).concat
    ((transfer_results_to_inputs_isStandardForm (base + n + 1) m).concat hF)

theorem compose_general_isStandardForm {m n : ℕ} {pF : Program} {pGs : Fin m → Program}
    (hF : pF.IsStandardForm) (hGs : ∀ i, (pGs i).IsStandardForm) :
    (Program.compose_general m n pF pGs).IsStandardForm := by
  simp only [Program.compose_general]
  exact (copy_register_range_isStandardForm 0 (composition_base m n pF pGs + 1) n).concat
    ((all_g_phases_isStandardForm hGs).concat (final_phase_isStandardForm hF))

theorem all_g_phases_prefix_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) (k : ℕ) : (all_g_phases_prefix m n base pGs k).IsStandardForm := by
  unfold all_g_phases_prefix g_phaseList
  exact prod_preserves_isStandardForm _ (fun p hp => by
    simp only [List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact g_phase_isStandardForm (hGs i))

theorem all_g_phases_suffix_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) (k : ℕ) : (all_g_phases_suffix m n base pGs k).IsStandardForm := by
  unfold all_g_phases_suffix g_phaseList
  exact prod_preserves_isStandardForm _ (fun p hp => by
    simp only [List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact g_phase_isStandardForm (hGs i))

theorem save_inputs_isStandardForm (base n : ℕ) : (copy_register_range 0 (base + 1) n).IsStandardForm :=
  copy_register_range_isStandardForm 0 (base + 1) n

end Urm
