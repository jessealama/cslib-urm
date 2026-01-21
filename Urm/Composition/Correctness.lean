/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Halting



/-! # Correctness Proofs for General Composition -/

namespace Urm

open Program

/-- The composed function h(x) = f(g₁(x), ..., gₘ(x)) -/
def comp_function (m n : ℕ) (f : (Fin m → ℕ) → Part ℕ) (gs : Fin m → (Fin n → ℕ) → Part ℕ)
    (x : Fin n → ℕ) : Part ℕ := (Part.sequence (fun i => gs i x)).bind f

/-- If the composition halts, then each gᵢ is defined on the inputs. -/
theorem comp_general_halts_imp_gi_dom
    {m n : ℕ} [NeZero m] {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ} {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (_hF_sf : pF.IsStandardForm) (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (_hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.compose_general m n pF pGs) (List.ofFn inputs)) (i : Fin m) :
    (gs i inputs).Dom := by
  let base := composition_base m n pF pGs
  let save_inputs := copy_register_range 0 (base + 1) n
  let g_phases := all_g_phases m n base pGs
  let final := final_phase m n base pF
  have hSaveInputs_sf := save_inputs_isStandardForm base n
  have hGPhases_sf : g_phases.IsStandardForm := all_g_phases_isStandardForm hGs_sf
  have hGPhase_i_sf : (g_phase base n (pGs i) i.val).IsStandardForm := g_phase_isStandardForm (hGs_sf i)
  have hH_eq : Program.compose_general m n pF pGs = save_inputs.concat (g_phases.concat final) := rfl
  have hGPhases_split := all_g_phases_split m n base pGs i.val
  have hPrefix_i_sf : (all_g_phases_prefix m n base pGs i.val).IsStandardForm :=
    all_g_phases_prefix_isStandardForm hGs_sf i.val
  have hSuffix_i_sf : (all_g_phases_suffix m n base pGs i.val).IsStandardForm :=
    all_g_phases_suffix_isStandardForm hGs_sf i.val
  have hSavePrefix_sf := hSaveInputs_sf.concat hPrefix_i_sf
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  rw [hH_eq, ← concat_assoc] at hHalts
  have hSaveGPhases_halts := Halts.prefix_of_concat_sf hHalts hSaveGPhases_sf
  have hSaveGPhases_eq : save_inputs.concat g_phases =
      (save_inputs.concat (all_g_phases_prefix m n base pGs i.val)).concat
        (all_g_phases_suffix m n base pGs i.val) := by
    show save_inputs.concat (all_g_phases m n base pGs) = _; rw [hGPhases_split, concat_assoc]
  rw [hSaveGPhases_eq] at hSaveGPhases_halts
  have hSavePrefix_halts := Halts.prefix_of_concat_sf hSaveGPhases_halts hSavePrefix_sf
  obtain ⟨sSavePrefix, _, hsSavePrefix_eq, cSuffix, hSuffix_steps, hSuffix_halted⟩ :=
    Halts.suffix_of_concat_sf hSaveGPhases_halts hSavePrefix_sf
  have hSuffix_i_eq : all_g_phases_suffix m n base pGs i.val =
      (g_phase base n (pGs i) i.val).concat (all_g_phases_suffix m n base pGs (i.val + 1)) :=
    all_g_phases_suffix_cons pGs i.val i.isLt
  rw [hSuffix_i_eq] at hSuffix_steps hSuffix_halted
  obtain ⟨_, hGPhase_i_steps, hGPhase_i_halted⟩ :=
    prefix_of_concat_from_zero hSuffix_steps hSuffix_halted hGPhase_i_sf
  -- Decompose g_phase_i = clear.concat(copy.concat(pGs_i.concat(transfer)))
  let dClear := decompose_concat hGPhase_i_steps hGPhase_i_halted (clear_registers_isStandardForm base)
  obtain ⟨_, hCopyRest_steps, hCopyRest_halted⟩ := dClear.halts_right
  let dCopy := decompose_concat hCopyRest_steps hCopyRest_halted (copy_register_range_isStandardForm (base + 1) 0 n)
  obtain ⟨_, hGiT_steps, hGiT_halted⟩ := dCopy.halts_right
  obtain ⟨cGi', hGi_steps, hGi_halted⟩ :=
    prefix_of_concat_from_zero hGiT_steps hGiT_halted (hGs_sf i)

  have hbase_ge : (pGs i).max_register ≤ base := composition_base_ge_Gi m n pF pGs i
  have hagreeGi : ∀ r, r ≤ (pGs i).max_register →
      dCopy.state.read r = (State.of_inputs (List.ofFn inputs)).read r := by
    intro r hr
    rcases Nat.lt_or_ge r n with hr_lt_n | hr_ge_n
    · obtain ⟨_, hsCopy_final_eq, hsCopy_copies, _⟩ :=
        copy_register_range_state (base + 1) 0 n dClear.state
          (Or.inr (by let _ := composition_base_ge_n m n pF pGs; omega))
      let hr' := hsCopy_copies r hr_lt_n
      let hsCopy_r : dCopy.state.read r = dClear.state.read (base + 1 + r) := by
        simp only [Nat.zero_add] at hr'
        rw [decompose_concat_state_straight_line (copy_register_range_is_straight_line (base + 1) 0 n), hsCopy_final_eq]
        convert hr' using 2
      let hsClear_preserves : dClear.state.read (base + 1 + r) = sSavePrefix.read (base + 1 + r) := by
        rw [decompose_concat_state_straight_line (clear_registers_is_straight_line base)]
        exact clear_registers_preserves_above' base sSavePrefix _ (by omega)
      let hRHS : (State.of_inputs (List.ofFn inputs)).read r = inputs ⟨r, hr_lt_n⟩ := by
        simp only [State.of_inputs, State.read]
        rw [List.getD_eq_getElem (List.ofFn inputs) 0 (by simp; exact hr_lt_n), List.getElem_ofFn]
      rw [hsCopy_r, hsClear_preserves, hRHS]
      let dSave := decompose_concat hSavePrefix_halts.choose_spec.1 hSavePrefix_halts.choose_spec.2 hSaveInputs_sf
      obtain ⟨cPrefix, hPrefix_steps, hPrefix_halted⟩ := dSave.halts_right
      let hSave_sl := copy_register_range_is_straight_line 0 (base + 1) n
      let hSave_halted' : (⟨save_inputs.length, dSave.state⟩ : Config).is_halted save_inputs := by simp
      let hsSave_eq : dSave.state = straight_lineFinalState hSave_sl (State.of_inputs (List.ofFn inputs)) :=
        straight_line_suffix_of_concat_state hSave_sl hSavePrefix_halts.choose_spec.1
          hSavePrefix_halts.choose_spec.2 hSaveInputs_sf
      let hpGs_max : ∀ j, (pGs j).max_register ≤ base := fun j => composition_base_ge_Gi m n pF pGs j
      let _base_ge := composition_base_ge_n_sub_one m n pF pGs
      let hn_le_base : n ≤ base + 1 := by omega
      let hsSave_value : dSave.state.read (base + 1 + r) = inputs ⟨r, hr_lt_n⟩ := by
        rw [hsSave_eq]; exact save_inputs_state base n hn_le_base inputs r hr_lt_n
      let hSavePrefixChain := Steps.chain_concat_sf hSaveInputs_sf dSave.steps_left hSave_halted' hPrefix_steps hPrefix_halted
      let hPrefix_state_match : cPrefix.state = sSavePrefix := by
        simp only [hsSavePrefix_eq hSavePrefix_halts, ← Steps.eq_of_halts hSavePrefixChain.1 hSavePrefixChain.2 hSavePrefix_halts.choose_spec.1 hSavePrefix_halts.choose_spec.2]
      let hPrefix_preserves := all_g_phases_prefix_preserves_saved_inputs m n base pGs hGs_sf hpGs_max hn_le_base
        i.val (Nat.le_of_lt i.isLt) dSave.state sSavePrefix cPrefix hPrefix_steps hPrefix_halted hPrefix_state_match
      rw [hPrefix_preserves (base + 1 + r) (by omega) (by omega), hsSave_value]
    · rw [show (State.of_inputs (List.ofFn inputs)).read r = 0 from by
            simp only [State.of_inputs, State.read, List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by simp; exact hr_ge_n)]; rfl,
          decompose_concat_state_straight_line (copy_register_range_is_straight_line (base + 1) 0 n),
          copy_register_range_preserves _ _ _ _ _ (Or.inr (by omega)),
          decompose_concat_state_straight_line (clear_registers_is_straight_line base),
          clear_registers_zeros' base sSavePrefix r (Nat.le_trans hr hbase_ge)]
  exact (hGs_spec i inputs).1.mp (Halts.of_agreeing_state hGi_steps hGi_halted hagreeGi)

/-- If the composition halts and all gᵢ are defined, then f is defined. -/
theorem comp_general_halts_imp_f_dom
    {m n : ℕ} [NeZero m] {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ} {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.compose_general m n pF pGs) (List.ofFn inputs))
    (hGs_dom : ∀ i, (gs i inputs).Dom) :
    (f (fun i => (gs i inputs).get (hGs_dom i))).Dom := by
  let base := composition_base m n pF pGs
  let save_inputs := copy_register_range 0 (base + 1) n
  let g_phases := all_g_phases m n base pGs
  let final := final_phase m n base pF
  have hSaveInputs_sf := save_inputs_isStandardForm base n
  have hGPhases_sf : g_phases.IsStandardForm := all_g_phases_isStandardForm hGs_sf
  have hH_eq : Program.compose_general m n pF pGs = save_inputs.concat (g_phases.concat final) := rfl
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  rw [hH_eq, ← concat_assoc] at hHalts
  have hSaveGPhases_halts := Halts.prefix_of_concat_sf hHalts hSaveGPhases_sf
  obtain ⟨sFinal_start, hSaveGPhases_halts', hsFinal_start_eq', cFinal, hFinal_steps, hFinal_halted⟩ :=
    Halts.suffix_of_concat_sf hHalts hSaveGPhases_sf
  -- Decompose final = clear.concat(transfer.concat(pF))
  let dClear := decompose_concat hFinal_steps hFinal_halted (clear_registers_isStandardForm base)
  obtain ⟨_, hTF_steps, hTF_halted⟩ := dClear.halts_right
  let dTransfer := decompose_concat hTF_steps hTF_halted (transfer_results_to_inputs_isStandardForm (base + n + 1) m)
  obtain ⟨cF, hF_steps, hF_halted⟩ := dTransfer.halts_right
  have hagreeF : ∀ r, r ≤ pF.max_register →
      dTransfer.state.read r = (State.of_inputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r := by
    intro r hr
    let hr_le_base : r ≤ base := Nat.le_trans hr (composition_base_ge_F m n pF pGs)
    rcases Nat.lt_or_ge r m with hr_lt_m | hr_ge_m
    · let hRHS : (State.of_inputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r =
          (gs ⟨r, hr_lt_m⟩ inputs).get (hGs_dom ⟨r, hr_lt_m⟩) := by simp [State.of_inputs, State.read, hr_lt_m]
      let hNoOverlap_transfer : m ≤ base + n + 1 := by let _ := composition_base_ge_m m n pF pGs; omega
      obtain ⟨_, hsTransfer'_eq, hTransfer_copies, _⟩ :=
        transfer_results_to_inputs_state (base + n + 1) m dClear.state hNoOverlap_transfer
      let hSavedResult : sFinal_start.read (base + n + 1 + r) = (gs ⟨r, hr_lt_m⟩ inputs).get (hGs_dom ⟨r, hr_lt_m⟩) := by
        let h := Classical.choose_spec hSaveGPhases_halts'
        rw [hsFinal_start_eq' hSaveGPhases_halts']; exact all_g_phases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨r, hr_lt_m⟩ _ ⟨_, h.1, h.2, rfl⟩
      calc dTransfer.state.read r = dClear.state.read (base + n + 1 + r) := by
            rw [decompose_concat_state_straight_line (transfer_results_to_inputs_is_straight_line (base + n + 1) m), hsTransfer'_eq]
            exact hTransfer_copies r hr_lt_m
        _ = sFinal_start.read (base + n + 1 + r) := by
            rw [decompose_concat_state_straight_line (clear_registers_is_straight_line base)]
            exact clear_registers_preserves_above' base _ _ (by omega)
        _ = (gs ⟨r, hr_lt_m⟩ inputs).get (hGs_dom ⟨r, hr_lt_m⟩) := hSavedResult
        _ = _ := hRHS.symm
    · rw [show (State.of_inputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r = 0 from by
            simp [State.of_inputs, State.read, hr_ge_m],
          decompose_concat_state_straight_line (transfer_results_to_inputs_is_straight_line (base + n + 1) m),
          transfer_results_to_inputs_preserves _ _ _ _ hr_ge_m,
          decompose_concat_state_straight_line (clear_registers_is_straight_line base),
          clear_registers_zeros' base _ _ hr_le_base]
  exact (hF_spec _).1.mp (Halts.of_agreeing_state hF_steps hF_halted hagreeF)

/-- If the composed function is defined, then the program halts. -/
theorem comp_general_dom_imp_halts
    {m n : ℕ} [NeZero m] {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ} {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hF_sf : pF.IsStandardForm) (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ) (hDom : (comp_function m n f gs inputs).Dom) :
    Halts (Program.compose_general m n pF pGs) (List.ofFn inputs) := by
  simp only [comp_function, Part.bind_dom] at hDom
  obtain ⟨hSeq_dom, hf_dom⟩ := hDom
  have hGs_dom : ∀ i, (gs i inputs).Dom := Part.sequence_dom.mp hSeq_dom
  have hGi_halts : ∀ i, Halts (pGs i) (List.ofFn inputs) := fun i => (hGs_spec i inputs).1.mpr (hGs_dom i)
  let results : Fin m → ℕ := fun i => (gs i inputs).get (hGs_dom i)
  have hf_dom' : (f results).Dom := by
    rw [show results = (Part.sequence (fun i => gs i inputs)).get hSeq_dom from by funext i; simp only [results, Part.sequence_get]]
    exact hf_dom
  have hF_halts := (hF_spec results).1.mpr hf_dom'
  let base := composition_base m n pF pGs
  let save_inputs := copy_register_range 0 (base + 1) n
  let g_phases := all_g_phases m n base pGs
  let final := final_phase m n base pF
  have hSaveInputs_sf := save_inputs_isStandardForm base n
  have hGPhases_sf : g_phases.IsStandardForm := all_g_phases_isStandardForm hGs_sf
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  have hH_eq : Program.compose_general m n pF pGs = save_inputs.concat (g_phases.concat final) := rfl
  have hSave_sl := copy_register_range_is_straight_line 0 (base + 1) n
  have hNoOverlap : 0 + n ≤ base + 1 := by simp; exact composition_base_ge_n m n pF pGs
  obtain ⟨sSave, hsSave_eq, hSave_copies, _⟩ :=
    copy_register_range_state 0 (base + 1) n (State.of_inputs (List.ofFn inputs)) (Or.inl hNoOverlap)
  obtain ⟨cSave, hSave_steps, hSave_halted, hSave_pc'⟩ :=
    straight_line_halts_from_state hSave_sl (State.of_inputs (List.ofFn inputs))
  have hcSave_state : cSave.state = sSave := by
    rw [straight_lineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps hSave_halted, hsSave_eq]
  have hSaved : ∀ j : ℕ, (hj : j < n) → sSave.read (base + 1 + j) = inputs ⟨j, hj⟩ := fun j hj => by
    rw [hSave_copies j hj]; simp [State.of_inputs, State.read, hj]
  have hpGs_max : ∀ i, (pGs i).max_register ≤ base := fun i => composition_base_ge_pGs_max m n pF pGs i
  have hn_le_base : n ≤ base + 1 := composition_base_ge_n m n pF pGs
  obtain ⟨cGPhases, hGPhases_steps, hGPhases_halted⟩ :=
    all_g_phases_halts_from_saved_inputs hGs_sf hpGs_max hn_le_base hGi_halts sSave hSaved
  have hSave_halted' : (⟨save_inputs.length, sSave⟩ : Config).is_halted save_inputs := by simp
  have hSave_config_eq : cSave = ⟨save_inputs.length, sSave⟩ := Config.ext hSave_pc' hcSave_state
  have hSave_steps' : Steps save_inputs ⟨0, State.of_inputs (List.ofFn inputs)⟩ ⟨save_inputs.length, sSave⟩ :=
    hSave_config_eq ▸ hSave_steps
  have ⟨hSaveGPhases_steps, hSaveGPhases_halted⟩ := Steps.chain_concat hSave_steps' rfl hGPhases_steps hGPhases_halted
  have hGPhases_pc : cGPhases.pc = g_phases.length :=
    hGPhases_sf.pc_eq_length_of_halted hGPhases_steps (Nat.zero_le _) hGPhases_halted
  let sGPhases := cGPhases.state
  have hpc_eq : cGPhases.pc + save_inputs.length = (save_inputs.concat g_phases).length := by
    simp only [Program.concat_length, hGPhases_pc]; omega
  have hResults : ∀ j : ℕ, (hj : j < m) → sGPhases.read (base + n + 1 + j) = results ⟨j, hj⟩ := fun j hj => by
    let hSaveGPhases_halted' : ∃ c : Config,
        Steps (save_inputs.concat g_phases) ⟨0, State.of_inputs (List.ofFn inputs)⟩ c ∧
        c.is_halted (save_inputs.concat g_phases) ∧ c.state = cGPhases.state :=
      ⟨⟨(save_inputs.concat g_phases).length, sGPhases⟩, hpc_eq ▸ hSaveGPhases_steps, by simp, rfl⟩
    exact all_g_phases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨j, hj⟩ _ hSaveGPhases_halted'
  have hpF_max : pF.max_register ≤ base := composition_base_ge_pF_max m n pF pGs
  have hm_le_base : m ≤ base + 1 := composition_base_ge_m m n pF pGs
  obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ :=
    final_phase_halts_from_results hF_sf hpF_max hm_le_base hF_halts sGPhases hResults
  have hSaveGPhases_steps' : Steps (save_inputs.concat g_phases) ⟨0, State.of_inputs (List.ofFn inputs)⟩
      ⟨(save_inputs.concat g_phases).length, sGPhases⟩ := hpc_eq ▸ hSaveGPhases_steps
  have hSaveGPhases_halted' : (⟨(save_inputs.concat g_phases).length, sGPhases⟩ : Config).is_halted (save_inputs.concat g_phases) := by simp
  have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hSaveGPhases_steps' rfl hFinal_steps hFinal_halted
  rw [hH_eq, ← concat_assoc]; exact ⟨_, hTotal_steps, hTotal_halted⟩

/-- The result of the composition equals the composed function value. -/
theorem comp_general_result
    {m n : ℕ} [NeZero m] {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ} {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hF_sf : pF.IsStandardForm) (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.compose_general m n pF pGs) (List.ofFn inputs))
    (hDom : (comp_function m n f gs inputs).Dom) :
    Result (Program.compose_general m n pF pGs) (List.ofFn inputs) hHalts =
      (comp_function m n f gs inputs).get hDom := by
  let H := Program.compose_general m n pF pGs
  let base := composition_base m n pF pGs
  let save_inputs := copy_register_range 0 (base + 1) n
  let g_phases := all_g_phases m n base pGs
  let final := final_phase m n base pF
  simp only [comp_function] at hDom
  have hSeq_dom : (Part.sequence fun i => gs i inputs).Dom := Part.bind_dom.mp hDom |>.1
  have hGs_dom : ∀ i, (gs i inputs).Dom := Part.sequence_dom.mp hSeq_dom
  let results : Fin m → ℕ := fun i => (gs i inputs).get (hGs_dom i)
  have hf_dom : (f results).Dom := by
    let h := Part.bind_dom.mp hDom |>.2
    let harg_eq : (Part.sequence fun i => gs i inputs).get hSeq_dom = results := by funext i; exact Part.sequence_get hSeq_dom i
    rw [harg_eq] at h; exact h
  have hF_halts : Halts pF (List.ofFn results) := (hF_spec results).1.mpr hf_dom
  let cH := Classical.choose hHalts
  have hH_spec := Classical.choose_spec hHalts
  have hH_steps : Steps H (Config.init (List.ofFn inputs)) cH := hH_spec.1
  have hH_halted : cH.is_halted H := hH_spec.2
  let cF := Classical.choose hF_halts
  have hF_steps : Steps pF (Config.init (List.ofFn results)) cF := (Classical.choose_spec hF_halts).1
  have hF_halted : cF.is_halted pF := (Classical.choose_spec hF_halts).2
  have hpF_max : pF.max_register ≤ base := composition_base_ge_pF_max m n pF pGs
  have hpGs_max : ∀ i, (pGs i).max_register ≤ base := fun i => composition_base_ge_pGs_max m n pF pGs i
  have hn_le_base : n ≤ base + 1 := composition_base_ge_n m n pF pGs
  have hGi_halts : ∀ i, Halts (pGs i) (List.ofFn inputs) := fun i => (hGs_spec i inputs).1.mpr (hGs_dom i)
  have hGPhases_sf := all_g_phases_isStandardForm (n := n) (base := base) hGs_sf
  have hSaveInputs_sf := save_inputs_isStandardForm base n
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  have hSave_sl := copy_register_range_is_straight_line 0 (base + 1) n
  obtain ⟨cSave, hSave_steps, hSave_halted, hSave_pc'⟩ := straight_line_halts_from_state hSave_sl (State.of_inputs (List.ofFn inputs))
  have hNoOverlap' : 0 + n ≤ base + 1 := by simp; exact composition_base_ge_n m n pF pGs
  obtain ⟨sSave, hsSave_eq, hSave_copies, _⟩ := copy_register_range_state 0 (base + 1) n (State.of_inputs (List.ofFn inputs)) (Or.inl hNoOverlap')
  have hcSave_state : cSave.state = sSave := by
    rw [straight_lineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps hSave_halted, hsSave_eq]
  have hSaved : ∀ j : ℕ, (hj : j < n) → sSave.read (base + 1 + j) = inputs ⟨j, hj⟩ := fun j hj => by
    rw [hSave_copies j hj]; simp [State.of_inputs, State.read, hj]
  obtain ⟨cGPhases, hGPhases_steps, hGPhases_halted⟩ :=
    all_g_phases_halts_from_saved_inputs hGs_sf hpGs_max hn_le_base hGi_halts sSave hSaved
  have hSave_halted' : (⟨save_inputs.length, sSave⟩ : Config).is_halted save_inputs := by simp
  have hSave_config_eq : cSave = ⟨save_inputs.length, sSave⟩ := Config.ext hSave_pc' hcSave_state
  have hSave_steps' : Steps save_inputs ⟨0, State.of_inputs (List.ofFn inputs)⟩ ⟨save_inputs.length, sSave⟩ :=
    hSave_config_eq ▸ hSave_steps
  have ⟨hSaveGPhases_steps, hSaveGPhases_halted⟩ := Steps.chain_concat hSave_steps' rfl hGPhases_steps hGPhases_halted
  have hGPhases_pc : cGPhases.pc = g_phases.length :=
    hGPhases_sf.pc_eq_length_of_halted hGPhases_steps (Nat.zero_le _) hGPhases_halted
  let sGPhases := cGPhases.state
  have hpc_eq : cGPhases.pc + save_inputs.length = (save_inputs.concat g_phases).length := by
    simp only [Program.concat_length, hGPhases_pc]; omega
  have hResults : ∀ j : ℕ, (hj : j < m) → sGPhases.read (base + n + 1 + j) = results ⟨j, hj⟩ := fun j hj => by
    let hSaveGPhases_halted' : ∃ c : Config,
        Steps (save_inputs.concat g_phases) ⟨0, State.of_inputs (List.ofFn inputs)⟩ c ∧
        c.is_halted (save_inputs.concat g_phases) ∧ c.state = cGPhases.state :=
      ⟨⟨cGPhases.pc + save_inputs.length, cGPhases.state⟩, hSaveGPhases_steps, hSaveGPhases_halted, rfl⟩
    exact all_g_phases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨j, hj⟩ _ hSaveGPhases_halted'
  have hagree_pF : ∀ sSetup : State,
      (∀ j : ℕ, (hj : j < m) → sSetup.read j = results ⟨j, hj⟩) →
      (∀ r, m ≤ r → r ≤ base → sSetup.read r = 0) →
      sSetup.agree_on (State.of_inputs (List.ofFn results)) 0 pF.max_register := fun sSetup hInputs hZeros =>
    agrees_list_inputs_after_clear_transfer hpF_max
      (fun i hi => by simp only [List.length_ofFn] at hi; rw [hInputs i hi]; simp [hi])
      (fun r hr_ge hr_le => by simp only [List.length_ofFn] at hr_ge; exact hZeros r hr_ge hr_le)
  have hClear_sl := clear_registers_is_straight_line base
  have hTransfer_sl := transfer_results_to_inputs_is_straight_line (base + n + 1) m
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves⟩ := clear_registers_exec base sGPhases
  have hResults_after_clear : ∀ j : ℕ, (hj : j < m) → cClear.state.read (base + n + 1 + j) = results ⟨j, hj⟩ :=
    fun j hj => by rw [hClear_preserves (base + n + 1 + j) (by omega)]; exact hResults j hj
  have hNoOverlap : m ≤ base + n + 1 := by let _ := composition_base_ge_m m n pF pGs; omega
  obtain ⟨sTransfer, hsTransfer_eq, hTransfer_correct, hTransfer_preserves⟩ :=
    transfer_results_to_inputs_state (base + n + 1) m cClear.state hNoOverlap
  obtain ⟨cTransfer, hTransfer_steps', hTransfer_halted', hTransfer_pc⟩ := straight_line_halts_from_state hTransfer_sl cClear.state
  have hTransfer_state_eq : cTransfer.state = straight_lineFinalState hTransfer_sl cClear.state :=
    straight_lineFinalState_eq_of_halted hTransfer_sl cClear.state cTransfer hTransfer_steps' hTransfer_halted'
  have hTransfer_state_sTransfer : cTransfer.state = sTransfer := by rw [hTransfer_state_eq, hsTransfer_eq]
  have hInputs_set : ∀ j : ℕ, (hj : j < m) → sTransfer.read j = results ⟨j, hj⟩ := fun j hj => by
    rw [hTransfer_correct j hj, hResults_after_clear j hj]
  have hZeros_set : ∀ r, m ≤ r → r ≤ base → sTransfer.read r = 0 := fun r hr_ge hr_le => by
    rw [hTransfer_preserves r (by omega), hClear_zeros r (by omega)]
  have hagree : sTransfer.agree_on (State.of_inputs (List.ofFn results)) 0 pF.max_register :=
    hagree_pF sTransfer hInputs_set hZeros_set
  let epF := Halts.executeFromAgreeingState hF_halts hF_sf hagree
  have hOutput_eq : epF.config.state.read 0 = cF.state.read 0 := by
    let h := AgreeingExecution.result_matches_original epF
    simp only [Result, show Classical.choose hF_halts = cF from rfl] at h; exact h
  have hH_eq : H = save_inputs.concat (g_phases.concat final) := rfl
  have hTransfer_config_eq : cTransfer = ⟨(transfer_results_to_inputs (base + n + 1) m).length, sTransfer⟩ := by
    ext <;> simp only [hTransfer_pc, hTransfer_state_sTransfer]
  have hTransfer_steps : Steps (transfer_results_to_inputs (base + n + 1) m) ⟨0, cClear.state⟩
      ⟨(transfer_results_to_inputs (base + n + 1) m).length, sTransfer⟩ := hTransfer_config_eq ▸ hTransfer_steps'
  have hTransfer_halted : (⟨(transfer_results_to_inputs (base + n + 1) m).length, sTransfer⟩ : Config).is_halted
      (transfer_results_to_inputs (base + n + 1) m) := by simp
  have ⟨hTransferF_steps, hTransferF_halted⟩ := Steps.chain_concat hTransfer_steps rfl epF.steps epF.halted
  have ⟨hClearTransferF_steps, hClearTransferF_halted⟩ := Steps.chain_concat hClear_steps hClear_pc hTransferF_steps hTransferF_halted
  have hSaveGPhases_steps' : Steps (save_inputs.concat g_phases) ⟨0, State.of_inputs (List.ofFn inputs)⟩
      ⟨(save_inputs.concat g_phases).length, sGPhases⟩ := hpc_eq ▸ hSaveGPhases_steps
  have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hSaveGPhases_steps' rfl hClearTransferF_steps hClearTransferF_halted
  rw [hH_eq, ← concat_assoc] at hH_steps hH_halted
  let cH_built : Config := ⟨(save_inputs.concat g_phases).length + final.length + epF.config.pc - pF.length, epF.config.state⟩
  have hcH_built_halted : cH_built.is_halted ((save_inputs.concat g_phases).concat final) := by
    simp only [Config.is_halted, Program.concat_length, cH_built, epF.pc_eq]; omega
  have hH_steps_built : Steps ((save_inputs.concat g_phases).concat final)
      ⟨0, State.of_inputs (List.ofFn inputs)⟩ cH_built := by
    simp only [final, cH_built]; convert hTotal_steps using 2; simp only [Program.concat_length, epF.pc_eq, final_phase]; omega
  have hcH_eq := Steps.eq_of_halts hH_steps hH_halted hH_steps_built hcH_built_halted
  calc Result H (List.ofFn inputs) hHalts = cH.state.read 0 := rfl
    _ = cH_built.state.read 0 := by rw [hcH_eq]
    _ = cF.state.read 0 := hOutput_eq
    _ = (f results).get hf_dom := (hF_spec results).2 hF_halts hf_dom
    _ = (comp_function m n f gs inputs).get hDom := by
        simp only [comp_function, Part.Dom.bind hSeq_dom]; congr 2; funext i
        exact (Part.sequence_get hSeq_dom i).symm

end Urm
