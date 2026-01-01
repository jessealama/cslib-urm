/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Correctness

/-! # General Composition Theorem

This file proves the main general composition theorem for URM computability.

## Main results

- `URMComputableSF.comp_general`: General closure under composition.
  Given m-ary f and m n-ary functions g₁,...,gₘ, the composition
  h(x₁,...,xₙ) = f(g₁(x),...,gₘ(x)) is computable.
-/

namespace Urm

open Program

/-- General closure under composition.
Given m-ary f and m n-ary functions g₁,...,gₘ, the composition
h(x₁,...,xₙ) = f(g₁(x),...,gₘ(x)) is computable. -/
theorem URMComputableSF.comp_general
    {m n : ℕ} [NeZero m]
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hf : URMComputableSF m f)
    (hgs : ∀ i, URMComputableSF n (gs i)) :
    URMComputableSF n (compFunction m n f gs) := by
  -- Extract the programs
  obtain ⟨pF, hF_sf, hF_spec⟩ := hf
  choose pGs hGs_sf hGs_spec using fun i => hgs i
  -- Construct the composed program
  let pH := Program.composeGeneral m n pF pGs
  use pH
  constructor
  · -- Standard form
    exact composeGeneral_isStandardForm hF_sf hGs_sf
  · -- Correctness
    intro inputs
    constructor
    · -- Halts ↔ Dom
      constructor
      · -- Halts → Dom
        intro hHalts
        simp only [compFunction]
        -- Need to show (Part.sequence (fun i => gs i inputs)).bind f is defined
        -- This means (1) Part.sequence is defined and (2) f applied to the result is defined
        have hGs_dom : ∀ i, (gs i inputs).Dom :=
          fun i => comp_general_halts_imp_gi_dom hF_sf hGs_sf hF_spec hGs_spec inputs hHalts i
        have hSeq_dom : (Part.sequence (fun i => gs i inputs)).Dom := Part.sequence_dom.mpr hGs_dom
        rw [Part.bind_dom]
        refine ⟨hSeq_dom, ?_⟩
        -- Now show f ((Part.sequence ...).get hSeq_dom) is defined
        have hf_dom := comp_general_halts_imp_f_dom hF_sf hGs_sf hF_spec hGs_spec inputs hHalts hGs_dom
        -- Need to show the get matches: the argument to f is the same
        have harg_eq : (Part.sequence (fun i => gs i inputs)).get hSeq_dom =
            (fun i => (gs i inputs).get (hGs_dom i)) := by
          funext i
          exact Part.sequence_get hSeq_dom i
        rw [harg_eq]
        exact hf_dom
      · -- Dom → Halts
        intro hDom
        exact comp_general_dom_imp_halts hF_sf hGs_sf hF_spec hGs_spec inputs hDom
    · -- Result correctness
      intro hHalts hDom
      exact comp_general_result hF_sf hGs_sf hF_spec hGs_spec inputs hHalts hDom

end Urm
