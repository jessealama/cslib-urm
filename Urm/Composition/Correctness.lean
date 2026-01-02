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
def compFunction (m n : ℕ) (f : (Fin m → ℕ) → Part ℕ) (gs : Fin m → (Fin n → ℕ) → Part ℕ)
    (x : Fin n → ℕ) : Part ℕ := (Part.sequence (fun i => gs i x)).bind f

set_option maxHeartbeats 400000 in
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
    (hHalts : Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs)) (i : Fin m) :
    (gs i inputs).Dom := by
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF
  have hSaveInputs_sf := saveInputs_isStandardForm base n
  have hGPhases_sf : gPhases.IsStandardForm := allGPhases_isStandardForm hGs_sf
  have hGPhase_i_sf : (gPhase base n (pGs i) i.val).IsStandardForm := gPhase_isStandardForm (hGs_sf i)
  have hH_eq : Program.composeGeneral m n pF pGs = saveInputs.concat (gPhases.concat final) := rfl
  have hGPhases_split := allGPhases_split m n base pGs i.val (Nat.le_of_lt i.isLt)
  have hPrefix_i_sf : (allGPhases_prefix m n base pGs i.val).IsStandardForm :=
    allGPhases_prefix_isStandardForm hGs_sf i.val
  have hSuffix_i_sf : (allGPhases_suffix m n base pGs i.val).IsStandardForm :=
    allGPhases_suffix_isStandardForm hGs_sf i.val
  have hSavePrefix_sf := hSaveInputs_sf.concat hPrefix_i_sf
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  rw [hH_eq, ← concat_assoc] at hHalts
  have hSaveGPhases_halts := Halts.prefix_of_concat_sf hHalts hSaveGPhases_sf
  have hSaveGPhases_eq : saveInputs.concat gPhases =
      (saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat
        (allGPhases_suffix m n base pGs i.val) := by
    show saveInputs.concat (allGPhases m n base pGs) = _; rw [hGPhases_split, concat_assoc]
  rw [hSaveGPhases_eq] at hSaveGPhases_halts
  have hSavePrefix_halts := Halts.prefix_of_concat_sf hSaveGPhases_halts hSavePrefix_sf
  obtain ⟨sSavePrefix, _, hsSavePrefix_eq, cSuffix, hSuffix_steps, hSuffix_halted⟩ :=
    Halts.suffix_of_concat_sf hSaveGPhases_halts hSavePrefix_sf
  have hSuffix_i_eq : allGPhases_suffix m n base pGs i.val =
      (gPhase base n (pGs i) i.val).concat (allGPhases_suffix m n base pGs (i.val + 1)) := by
    simp only [allGPhases_suffix]
    have hdrop_eq : (List.finRange m).drop i.val = i :: (List.finRange m).drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons]; · congr 1; simp only [List.finRange, List.getElem_ofFn]
      · simp only [List.length_finRange]; exact i.isLt
    rw [hdrop_eq, List.foldl_cons, concat_nil_left]; exact foldl_concat_eq_acc_concat _ _ _
  rw [hSuffix_i_eq] at hSuffix_steps hSuffix_halted
  obtain ⟨_, hGPhase_i_steps, hGPhase_i_halted⟩ :=
    prefix_of_concat_from_zero hSuffix_steps hSuffix_halted hGPhase_i_sf
  obtain ⟨sClear, hClear_steps, ⟨cCopyRest, hCopyRest_steps, hCopyRest_halted⟩⟩ :=
    suffix_of_concat_from_zero hGPhase_i_steps hGPhase_i_halted (clearRegisters_isStandardForm base)
  obtain ⟨sCopy, hCopy_steps, ⟨cGiT, hGiT_steps, hGiT_halted⟩⟩ :=
    suffix_of_concat_from_zero hCopyRest_steps hCopyRest_halted (copyRegisterRange_isStandardForm (base + 1) 0 n)
  obtain ⟨cGi', hGi_steps, hGi_halted⟩ :=
    prefix_of_concat_from_zero hGiT_steps hGiT_halted (hGs_sf i)

  have hbase_ge : (pGs i).maxRegister ≤ base := compositionBase_ge_Gi m n pF pGs i
  have hagreeGi : ∀ r, r ≤ (pGs i).maxRegister →
      sCopy.read r = (State.fromInputs (List.ofFn inputs)).read r := by
    intro r hr
    have hr_le_base : r ≤ base := Nat.le_trans hr hbase_ge
    rcases Nat.lt_or_ge r n with hr_lt_n | hr_ge_n
    · have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
      have hsCopy_eq : sCopy = straightLineFinalState hCopy_sl sClear :=
        straightLineFinalState_eq_of_halted hCopy_sl sClear ⟨_, sCopy⟩ hCopy_steps (by simp)
      obtain ⟨_, hsCopy_final_eq, hsCopy_copies, _⟩ :=
        copyRegisterRange_state (base + 1) 0 n sClear (Or.inr (by have := compositionBase_ge_n m n pF pGs; omega))
      have hsCopy_r : sCopy.read r = sClear.read (base + 1 + r) := by
        have hr' := hsCopy_copies r hr_lt_n; simp only [Nat.zero_add] at hr'
        rw [hsCopy_eq, hsCopy_final_eq]; convert hr' using 2
      have hClear_sl := clearRegisters_isStraightLine base
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sSavePrefix :=
        straightLineFinalState_eq_of_halted hClear_sl sSavePrefix ⟨_, sClear⟩ hClear_steps (by simp)
      have hsClear_preserves : sClear.read (base + 1 + r) = sSavePrefix.read (base + 1 + r) := by
        rw [hsClear_eq]; exact clearRegisters_preserves_above' base sSavePrefix _ (by omega)
      have hRHS : (State.fromInputs (List.ofFn inputs)).read r = inputs ⟨r, hr_lt_n⟩ := by
        simp only [State.fromInputs, State.read]
        rw [List.getD_eq_getElem (List.ofFn inputs) 0 (by simp; exact hr_lt_n), List.getElem_ofFn]
      rw [hsCopy_r, hsClear_preserves, hRHS]
      obtain ⟨sSave, hSave_steps, ⟨cPrefix, hPrefix_steps, hPrefix_halted⟩⟩ :=
        suffix_of_concat_from_zero hSavePrefix_halts.choose_spec.1
          hSavePrefix_halts.choose_spec.2 hSaveInputs_sf
      have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
      have hSave_halted' : (⟨saveInputs.length, sSave⟩ : Config).isHalted saveInputs := by simp
      have hsSave_eq : sSave = straightLineFinalState hSave_sl (State.fromInputs (List.ofFn inputs)) :=
        straightLineFinalState_eq_of_halted hSave_sl _ ⟨_, sSave⟩ hSave_steps hSave_halted'
      have hpGs_max : ∀ j, (pGs j).maxRegister ≤ base := fun j => compositionBase_ge_Gi m n pF pGs j
      have hn_le_base : n ≤ base + 1 := by have := compositionBase_ge_n_sub_one m n pF pGs; omega
      have hsSave_value : sSave.read (base + 1 + r) = inputs ⟨r, hr_lt_n⟩ := by
        rw [hsSave_eq]; exact saveInputs_state base n hn_le_base inputs r hr_lt_n
      have hSavePrefixChain := Steps.chain_concat_sf hSaveInputs_sf hSave_steps hSave_halted' hPrefix_steps hPrefix_halted
      have hPrefix_state_match : cPrefix.state = sSavePrefix := by
        simp only [hsSavePrefix_eq hSavePrefix_halts, ← Steps.halts_unique hSavePrefixChain.1 hSavePrefixChain.2 hSavePrefix_halts.choose_spec.1 hSavePrefix_halts.choose_spec.2]
      have hPrefix_preserves := allGPhases_prefix_preserves_saved_inputs m n base pGs hGs_sf hpGs_max hn_le_base
        i.val (Nat.le_of_lt i.isLt) sSave sSavePrefix cPrefix hPrefix_steps hPrefix_halted hPrefix_state_match
      rw [hPrefix_preserves (base + 1 + r) (by omega) (by omega), hsSave_value]
    · have hRHS_zero : (State.fromInputs (List.ofFn inputs)).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; exact hr_ge_n)]; rfl
      have hClear_sl := clearRegisters_isStraightLine base
      have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
      have hsCopy_eq : sCopy = straightLineFinalState hCopy_sl sClear :=
        straightLineFinalState_eq_of_halted hCopy_sl sClear ⟨_, sCopy⟩ hCopy_steps (by simp)
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sSavePrefix :=
        straightLineFinalState_eq_of_halted hClear_sl sSavePrefix ⟨_, sClear⟩ hClear_steps (by simp)
      rw [hRHS_zero, hsCopy_eq, copyRegisterRange_preserves _ _ _ _ _ (Or.inr (by omega)),
          hsClear_eq, clearRegisters_zeros' base sSavePrefix r hr_le_base]
  exact (hGs_spec i inputs).1.mp (Halts.of_agreeing_state hGi_steps hGi_halted hagreeGi)

/-- If the composition halts and all gᵢ are defined, then f is defined. -/
theorem comp_general_halts_imp_f_dom
    {m n : ℕ} [NeZero m] {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ} {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (_ : pF.IsStandardForm) (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs))
    (hGs_dom : ∀ i, (gs i inputs).Dom) :
    (f (fun i => (gs i inputs).get (hGs_dom i))).Dom := by
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF
  have hSaveInputs_sf := saveInputs_isStandardForm base n
  have hGPhases_sf : gPhases.IsStandardForm := allGPhases_isStandardForm hGs_sf
  have hH_eq : Program.composeGeneral m n pF pGs = saveInputs.concat (gPhases.concat final) := rfl
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  rw [hH_eq, ← concat_assoc] at hHalts
  have hSaveGPhases_halts := Halts.prefix_of_concat_sf hHalts hSaveGPhases_sf
  obtain ⟨sFinal_start, hSaveGPhases_halts', hsFinal_start_eq', cFinal, hFinal_steps, hFinal_halted⟩ :=
    Halts.suffix_of_concat_sf hHalts hSaveGPhases_sf
  obtain ⟨sClear, hClear_steps, ⟨cTF, hTF_steps, hTF_halted⟩⟩ :=
    suffix_of_concat_from_zero hFinal_steps hFinal_halted (clearRegisters_isStandardForm base)
  obtain ⟨sTransfer, hTransfer_steps, ⟨cF, hF_steps, hF_halted⟩⟩ :=
    suffix_of_concat_from_zero hTF_steps hTF_halted (transferResultsToInputs_isStandardForm (base + n + 1) m)
  have hagreeF : ∀ r, r ≤ pF.maxRegister →
      sTransfer.read r = (State.fromInputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r := by
    intro r hr
    have hr_le_base : r ≤ base := Nat.le_trans hr (compositionBase_ge_F m n pF pGs)
    rcases Nat.lt_or_ge r m with hr_lt_m | hr_ge_m
    · have hRHS : (State.fromInputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r =
          (gs ⟨r, hr_lt_m⟩ inputs).get (hGs_dom ⟨r, hr_lt_m⟩) := by simp [State.fromInputs, State.read, hr_lt_m]
      have hClear_sl := clearRegisters_isStraightLine base
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sFinal_start :=
        straightLineFinalState_eq_of_halted hClear_sl _ _ hClear_steps (by simp)
      have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m
      have hsTransfer_eq : sTransfer = straightLineFinalState hTransfer_sl sClear :=
        straightLineFinalState_eq_of_halted hTransfer_sl _ _ hTransfer_steps (by simp)
      have hNoOverlap_transfer : m ≤ base + n + 1 := by have := compositionBase_ge_m m n pF pGs; omega
      obtain ⟨_, hsTransfer'_eq, hTransfer_copies, _⟩ :=
        transferResultsToInputs_state (base + n + 1) m sClear hNoOverlap_transfer
      have hSavedResult : sFinal_start.read (base + n + 1 + r) = (gs ⟨r, hr_lt_m⟩ inputs).get (hGs_dom ⟨r, hr_lt_m⟩) := by
        have h := Classical.choose_spec hSaveGPhases_halts'
        rw [hsFinal_start_eq' hSaveGPhases_halts']; exact allGPhases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨r, hr_lt_m⟩ _ ⟨_, h.1, h.2, rfl⟩
      calc sTransfer.read r = sClear.read (base + n + 1 + r) := by rw [hsTransfer_eq, hsTransfer'_eq]; exact hTransfer_copies r hr_lt_m
        _ = sFinal_start.read (base + n + 1 + r) := by rw [hsClear_eq]; exact clearRegisters_preserves_above' base _ _ (by omega)
        _ = (gs ⟨r, hr_lt_m⟩ inputs).get (hGs_dom ⟨r, hr_lt_m⟩) := hSavedResult
        _ = _ := hRHS.symm
    · have hRHS_zero : (State.fromInputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r = 0 := by
        simp [State.fromInputs, State.read, hr_ge_m]
      have hClear_sl := clearRegisters_isStraightLine base
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sFinal_start :=
        straightLineFinalState_eq_of_halted hClear_sl _ _ hClear_steps (by simp)
      have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m
      have hsTransfer_eq : sTransfer = straightLineFinalState hTransfer_sl sClear :=
        straightLineFinalState_eq_of_halted hTransfer_sl _ _ hTransfer_steps (by simp)
      rw [hRHS_zero, hsTransfer_eq, transferResultsToInputs_preserves _ _ _ _ hr_ge_m,
          hsClear_eq, clearRegisters_zeros' base _ _ hr_le_base]
  exact (hF_spec _).1.mp (Halts.of_agreeing_state hF_steps hF_halted hagreeF)

set_option maxHeartbeats 800000 in
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
    (inputs : Fin n → ℕ) (hDom : (compFunction m n f gs inputs).Dom) :
    Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs) := by
  simp only [compFunction, Part.bind_dom] at hDom
  obtain ⟨hSeq_dom, hf_dom⟩ := hDom
  have hGs_dom : ∀ i, (gs i inputs).Dom := Part.sequence_dom.mp hSeq_dom
  have hGi_halts : ∀ i, Halts (pGs i) (List.ofFn inputs) := fun i => (hGs_spec i inputs).1.mpr (hGs_dom i)
  let results : Fin m → ℕ := fun i => (gs i inputs).get (hGs_dom i)
  have hf_dom' : (f results).Dom := by
    have h : results = (Part.sequence (fun i => gs i inputs)).get hSeq_dom := by funext i; simp only [results, Part.sequence_get]
    rw [h]; exact hf_dom
  have hF_halts := (hF_spec results).1.mpr hf_dom'
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF
  have hSaveInputs_sf := saveInputs_isStandardForm base n
  have hGPhases_sf : gPhases.IsStandardForm := allGPhases_isStandardForm hGs_sf
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  have hH_eq : Program.composeGeneral m n pF pGs = saveInputs.concat (gPhases.concat final) := rfl
  have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
  have hNoOverlap : 0 + n ≤ base + 1 := by simp; exact compositionBase_ge_n m n pF pGs
  obtain ⟨sSave, hsSave_eq, hSave_copies, _⟩ :=
    copyRegisterRange_state 0 (base + 1) n (State.fromInputs (List.ofFn inputs)) (Or.inl hNoOverlap)
  obtain ⟨cSave, hSave_steps, hSave_halted, hSave_pc'⟩ :=
    straightLine_halts_from_state hSave_sl (State.fromInputs (List.ofFn inputs))
  have hcSave_state : cSave.state = sSave := by
    rw [straightLineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps hSave_halted, hsSave_eq]
  have hSaved : ∀ j : ℕ, (hj : j < n) → sSave.read (base + 1 + j) = inputs ⟨j, hj⟩ := fun j hj => by
    rw [hSave_copies j hj]; simp [State.fromInputs, State.read, hj]
  have hpGs_max : ∀ i, (pGs i).maxRegister ≤ base := fun i => compositionBase_ge_pGs_max m n pF pGs i
  have hn_le_base : n ≤ base + 1 := compositionBase_ge_n m n pF pGs
  obtain ⟨cGPhases, hGPhases_steps, hGPhases_halted⟩ :=
    allGPhases_halts_from_saved_inputs hGs_sf hpGs_max hn_le_base hGi_halts sSave hSaved
  have hSave_halted' : (⟨saveInputs.length, sSave⟩ : Config).isHalted saveInputs := by simp
  have hSave_config_eq : cSave = ⟨saveInputs.length, sSave⟩ := Config.ext hSave_pc' hcSave_state
  have hSave_steps' : Steps saveInputs ⟨0, State.fromInputs (List.ofFn inputs)⟩ ⟨saveInputs.length, sSave⟩ :=
    hSave_config_eq ▸ hSave_steps
  have ⟨hSaveGPhases_steps, hSaveGPhases_halted⟩ := Steps.chain_concat hSave_steps' hSave_halted' rfl hGPhases_steps hGPhases_halted
  have hGPhases_pc : cGPhases.pc = gPhases.length :=
    hGPhases_sf.pc_eq_length_of_halted hGPhases_steps (Nat.zero_le _) hGPhases_halted
  let sGPhases := cGPhases.state
  have hpc_eq : cGPhases.pc + saveInputs.length = (saveInputs.concat gPhases).length := by
    simp only [Program.concat_length, hGPhases_pc]; omega
  have hResults : ∀ j : ℕ, (hj : j < m) → sGPhases.read (base + n + 1 + j) = results ⟨j, hj⟩ := fun j hj => by
    have hSaveGPhases_halted' : ∃ c : Config,
        Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩ c ∧
        c.isHalted (saveInputs.concat gPhases) ∧ c.state = cGPhases.state :=
      ⟨⟨(saveInputs.concat gPhases).length, sGPhases⟩, hpc_eq ▸ hSaveGPhases_steps, by simp, rfl⟩
    exact allGPhases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨j, hj⟩ _ hSaveGPhases_halted'
  have hpF_max : pF.maxRegister ≤ base := compositionBase_ge_pF_max m n pF pGs
  have hm_le_base : m ≤ base + 1 := compositionBase_ge_m m n pF pGs
  obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ :=
    finalPhase_halts_from_results hF_sf hpF_max hm_le_base hF_halts sGPhases hResults
  have hSaveGPhases_steps' : Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩
      ⟨(saveInputs.concat gPhases).length, sGPhases⟩ := hpc_eq ▸ hSaveGPhases_steps
  have hSaveGPhases_halted' : (⟨(saveInputs.concat gPhases).length, sGPhases⟩ : Config).isHalted (saveInputs.concat gPhases) := by simp
  have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hSaveGPhases_steps' hSaveGPhases_halted' rfl hFinal_steps hFinal_halted
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
    (hHalts : Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs))
    (hDom : (compFunction m n f gs inputs).Dom) :
    Result (Program.composeGeneral m n pF pGs) (List.ofFn inputs) hHalts =
      (compFunction m n f gs inputs).get hDom := by
  let H := Program.composeGeneral m n pF pGs
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF
  simp only [compFunction] at hDom
  have hSeq_dom : (Part.sequence fun i => gs i inputs).Dom := Part.bind_dom.mp hDom |>.1
  have hGs_dom : ∀ i, (gs i inputs).Dom := Part.sequence_dom.mp hSeq_dom
  let results : Fin m → ℕ := fun i => (gs i inputs).get (hGs_dom i)
  have hf_dom : (f results).Dom := by
    have h := Part.bind_dom.mp hDom |>.2
    have harg_eq : (Part.sequence fun i => gs i inputs).get hSeq_dom = results := by funext i; exact Part.sequence_get hSeq_dom i
    rw [harg_eq] at h; exact h
  have hF_halts : Halts pF (List.ofFn results) := (hF_spec results).1.mpr hf_dom
  let cH := Classical.choose hHalts
  have hH_spec := Classical.choose_spec hHalts
  have hH_steps : Steps H (Config.init (List.ofFn inputs)) cH := hH_spec.1
  have hH_halted : cH.isHalted H := hH_spec.2
  let cF := Classical.choose hF_halts
  have hF_steps : Steps pF (Config.init (List.ofFn results)) cF := (Classical.choose_spec hF_halts).1
  have hF_halted : cF.isHalted pF := (Classical.choose_spec hF_halts).2
  have hpF_max : pF.maxRegister ≤ base := compositionBase_ge_pF_max m n pF pGs
  have hpGs_max : ∀ i, (pGs i).maxRegister ≤ base := fun i => compositionBase_ge_pGs_max m n pF pGs i
  have hn_le_base : n ≤ base + 1 := compositionBase_ge_n m n pF pGs
  have hGi_halts : ∀ i, Halts (pGs i) (List.ofFn inputs) := fun i => (hGs_spec i inputs).1.mpr (hGs_dom i)
  have hGPhases_sf := allGPhases_isStandardForm (n := n) (base := base) hGs_sf
  have hSaveInputs_sf := saveInputs_isStandardForm base n
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
  obtain ⟨cSave, hSave_steps, hSave_halted, hSave_pc'⟩ := straightLine_halts_from_state hSave_sl (State.fromInputs (List.ofFn inputs))
  have hNoOverlap' : 0 + n ≤ base + 1 := by simp; exact compositionBase_ge_n m n pF pGs
  obtain ⟨sSave, hsSave_eq, hSave_copies, _⟩ := copyRegisterRange_state 0 (base + 1) n (State.fromInputs (List.ofFn inputs)) (Or.inl hNoOverlap')
  have hcSave_state : cSave.state = sSave := by
    rw [straightLineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps hSave_halted, hsSave_eq]
  have hSaved : ∀ j : ℕ, (hj : j < n) → sSave.read (base + 1 + j) = inputs ⟨j, hj⟩ := fun j hj => by
    rw [hSave_copies j hj]; simp [State.fromInputs, State.read, hj]
  obtain ⟨cGPhases, hGPhases_steps, hGPhases_halted⟩ :=
    allGPhases_halts_from_saved_inputs hGs_sf hpGs_max hn_le_base hGi_halts sSave hSaved
  have hSave_halted' : (⟨saveInputs.length, sSave⟩ : Config).isHalted saveInputs := by simp
  have hSave_config_eq : cSave = ⟨saveInputs.length, sSave⟩ := Config.ext hSave_pc' hcSave_state
  have hSave_steps' : Steps saveInputs ⟨0, State.fromInputs (List.ofFn inputs)⟩ ⟨saveInputs.length, sSave⟩ :=
    hSave_config_eq ▸ hSave_steps
  have ⟨hSaveGPhases_steps, hSaveGPhases_halted⟩ := Steps.chain_concat hSave_steps' hSave_halted' rfl hGPhases_steps hGPhases_halted
  have hGPhases_pc : cGPhases.pc = gPhases.length :=
    hGPhases_sf.pc_eq_length_of_halted hGPhases_steps (Nat.zero_le _) hGPhases_halted
  let sGPhases := cGPhases.state
  have hpc_eq : cGPhases.pc + saveInputs.length = (saveInputs.concat gPhases).length := by
    simp only [Program.concat_length, hGPhases_pc]; omega
  have hResults : ∀ j : ℕ, (hj : j < m) → sGPhases.read (base + n + 1 + j) = results ⟨j, hj⟩ := fun j hj => by
    have hSaveGPhases_halted' : ∃ c : Config,
        Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩ c ∧
        c.isHalted (saveInputs.concat gPhases) ∧ c.state = cGPhases.state :=
      ⟨⟨cGPhases.pc + saveInputs.length, cGPhases.state⟩, hSaveGPhases_steps, hSaveGPhases_halted, rfl⟩
    exact allGPhases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨j, hj⟩ _ hSaveGPhases_halted'
  have hagree_pF : ∀ sSetup : State,
      (∀ j : ℕ, (hj : j < m) → sSetup.read j = results ⟨j, hj⟩) →
      (∀ r, m ≤ r → r ≤ base → sSetup.read r = 0) →
      sSetup.agreeOn (State.fromInputs (List.ofFn results)) 0 pF.maxRegister := fun sSetup hInputs hZeros =>
    agrees_list_inputs_after_clear_transfer hpF_max
      (fun i hi => by simp only [List.length_ofFn] at hi; rw [hInputs i hi]; simp [hi])
      (fun r hr_ge hr_le => by simp only [List.length_ofFn] at hr_ge; exact hZeros r hr_ge hr_le)
  have hClear_sl := clearRegisters_isStraightLine base
  have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves⟩ := clearRegisters_exec base sGPhases
  have hResults_after_clear : ∀ j : ℕ, (hj : j < m) → cClear.state.read (base + n + 1 + j) = results ⟨j, hj⟩ :=
    fun j hj => by rw [hClear_preserves (base + n + 1 + j) (by omega)]; exact hResults j hj
  have hNoOverlap : m ≤ base + n + 1 := by have := compositionBase_ge_m m n pF pGs; omega
  obtain ⟨sTransfer, hsTransfer_eq, hTransfer_correct, hTransfer_preserves⟩ :=
    transferResultsToInputs_state (base + n + 1) m cClear.state hNoOverlap
  obtain ⟨cTransfer, hTransfer_steps', hTransfer_halted', hTransfer_pc⟩ := straightLine_halts_from_state hTransfer_sl cClear.state
  have hTransfer_state_eq : cTransfer.state = straightLineFinalState hTransfer_sl cClear.state :=
    straightLineFinalState_eq_of_halted hTransfer_sl cClear.state cTransfer hTransfer_steps' hTransfer_halted'
  have hTransfer_state_sTransfer : cTransfer.state = sTransfer := by rw [hTransfer_state_eq, hsTransfer_eq]
  have hInputs_set : ∀ j : ℕ, (hj : j < m) → sTransfer.read j = results ⟨j, hj⟩ := fun j hj => by
    rw [hTransfer_correct j hj, hResults_after_clear j hj]
  have hZeros_set : ∀ r, m ≤ r → r ≤ base → sTransfer.read r = 0 := fun r hr_ge hr_le => by
    rw [hTransfer_preserves r (by omega), hClear_zeros r (by omega)]
  have hagree : sTransfer.agreeOn (State.fromInputs (List.ofFn results)) 0 pF.maxRegister :=
    hagree_pF sTransfer hInputs_set hZeros_set
  let epF := Halts.executeFromAgreeingState hF_halts hF_sf hagree
  have hOutput_eq : epF.config.state.read 0 = cF.state.read 0 := by
    have h := AgreeingExecution.result_matches_original epF
    simp only [Result, show Classical.choose hF_halts = cF from rfl] at h; exact h
  have hH_eq : H = saveInputs.concat (gPhases.concat final) := rfl
  have hTransfer_config_eq : cTransfer = ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
    ext <;> simp only [hTransfer_pc, hTransfer_state_sTransfer]
  have hTransfer_steps : Steps (transferResultsToInputs (base + n + 1) m) ⟨0, cClear.state⟩
      ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := hTransfer_config_eq ▸ hTransfer_steps'
  have hTransfer_halted : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).isHalted
      (transferResultsToInputs (base + n + 1) m) := by simp
  have ⟨hTransferF_steps, hTransferF_halted⟩ := Steps.chain_concat hTransfer_steps hTransfer_halted rfl epF.steps epF.halted
  have ⟨hClearTransferF_steps, hClearTransferF_halted⟩ := Steps.chain_concat hClear_steps hClear_halted hClear_pc hTransferF_steps hTransferF_halted
  have hSaveGPhases_steps' : Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩
      ⟨(saveInputs.concat gPhases).length, sGPhases⟩ := hpc_eq ▸ hSaveGPhases_steps
  have hSaveGPhases_halted' : (⟨(saveInputs.concat gPhases).length, sGPhases⟩ : Config).isHalted (saveInputs.concat gPhases) := by simp
  have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hSaveGPhases_steps' hSaveGPhases_halted' rfl hClearTransferF_steps hClearTransferF_halted
  rw [hH_eq, ← concat_assoc] at hH_steps hH_halted
  let cH_built : Config := ⟨(saveInputs.concat gPhases).length + final.length + epF.config.pc - pF.length, epF.config.state⟩
  have hcH_built_halted : cH_built.isHalted ((saveInputs.concat gPhases).concat final) := by
    simp only [Config.isHalted, Program.concat_length, cH_built, epF.pc_eq]; omega
  have hH_steps_built : Steps ((saveInputs.concat gPhases).concat final)
      ⟨0, State.fromInputs (List.ofFn inputs)⟩ cH_built := by
    simp only [final, cH_built]; convert hTotal_steps using 2; simp only [Program.concat_length, epF.pc_eq, finalPhase]; omega
  have hcH_eq := Steps.halts_unique hH_steps hH_halted hH_steps_built hcH_built_halted
  calc Result H (List.ofFn inputs) hHalts = cH.state.read 0 := rfl
    _ = cH_built.state.read 0 := by rw [hcH_eq]
    _ = cF.state.read 0 := hOutput_eq
    _ = (f results).get hf_dom := (hF_spec results).2 hF_halts hf_dom
    _ = (compFunction m n f gs inputs).get hDom := by
        simp only [compFunction, Part.Dom.bind hSeq_dom]; congr 2; funext i
        exact (Part.sequence_get hSeq_dom i).symm

end Urm
