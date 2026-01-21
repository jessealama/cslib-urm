/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Correctness
import Mathlib.Tactic.WLOG

/-! # General Composition Theorem -/

namespace Urm

open Program

theorem URMComputableSF.comp_general {m n : ℕ} [NeZero m] {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ} (hf : URMComputableSF m f) (hgs : ∀ i, URMComputableSF n (gs i)) :
    URMComputableSF n (comp_function m n f gs) := by
  obtain ⟨pF, hF_sf, hF_spec⟩ := hf
  choose pGs hGs_sf hGs_spec using fun i => hgs i
  refine ⟨Program.compose_general m n pF pGs, compose_general_isStandardForm hF_sf hGs_sf, fun inputs => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro hHalts
    simp only [comp_function]
    have hGs_dom : ∀ i, (gs i inputs).Dom :=
      fun i => comp_general_halts_imp_gi_dom hF_sf hGs_sf hF_spec hGs_spec inputs hHalts i
    have hSeq_dom : (Part.sequence (fun i => gs i inputs)).Dom := Part.sequence_dom.mpr hGs_dom
    rw [Part.bind_dom]; refine ⟨hSeq_dom, ?_⟩
    have hf_dom := comp_general_halts_imp_f_dom hGs_sf hF_spec hGs_spec inputs hHalts hGs_dom
    have harg_eq : (Part.sequence (fun i => gs i inputs)).get hSeq_dom =
        (fun i => (gs i inputs).get (hGs_dom i)) := funext fun i => Part.sequence_get hSeq_dom i
    rw [harg_eq]; exact hf_dom
  · intro hDom; exact comp_general_dom_imp_halts hF_sf hGs_sf hF_spec hGs_spec inputs hDom
  · intro hHalts hDom; exact comp_general_result hF_sf hGs_sf hF_spec hGs_spec inputs hHalts hDom

/-- Composition of URM-computable functions is URM-computable.
This version relaxes the standard form requirement on hypotheses - any URM-computable
functions compose to a standard form program. The proof uses wlog to reduce to the
standard form case. -/
theorem URMComputable.comp_general {m n : ℕ} [NeZero m] {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hf : URMComputable m f) (hgs : ∀ i, URMComputable n (gs i)) :
    URMComputableSF n (comp_function m n f gs) := by
  -- Reduce to standard form case using wlog
  wlog hf_sf : URMComputableSF m f with h_reduce
  · exact h_reduce hf hgs hf.toSF
  wlog hgs_sf : ∀ i, URMComputableSF n (gs i) with h_reduce2
  · exact h_reduce2 hf hgs hf_sf (fun i => (hgs i).toSF)
  -- Now in SF case, apply existing theorem
  exact URMComputableSF.comp_general hf_sf hgs_sf

end Urm

-- Export the main composition theorems for easy access
export Urm (URMComputableSF.comp_general URMComputable.comp_general)
