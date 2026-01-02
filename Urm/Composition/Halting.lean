/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Preservation
import Mathlib.Data.List.GetD

/-! # Forward Direction Helpers: Dom → Halts -/

namespace Urm

open Program

theorem gPhase_halts_from_saved_inputs {base n : ℕ} {pG : Program} {i : ℕ} {inputs : Fin n → ℕ}
    (hpG_sf : pG.IsStandardForm) (hpG_max : pG.maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (hpG_halts : Halts pG (List.ofFn inputs)) (s : State)
    (hSaved : ∀ j : ℕ, (hj : j < n) → s.read (base + 1 + j) = inputs ⟨j, hj⟩) :
    ∃ c, Steps (gPhase base n pG i) ⟨0, s⟩ c ∧ c.isHalted (gPhase base n pG i) := by
  have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves⟩ :=
    clearRegisters_exec base s
  have hSaved_after_clear : ∀ j : ℕ, (hj : j < n) → cClear.state.read (base + 1 + j) = inputs ⟨j, hj⟩ :=
    fun j hj => by rw [hClear_preserves (base + 1 + j) (by omega)]; exact hSaved j hj
  obtain ⟨sCopy, hsCopy_eq, hCopy_correct, hCopy_preserves⟩ :=
    copyRegisterRange_state (base + 1) 0 n cClear.state (Or.inr (by omega))
  obtain ⟨cCopy, hCopy_steps', hCopy_halted', hCopy_pc⟩ := straightLine_halts_from_state hCopy_sl cClear.state
  have hCopy_state_sCopy : cCopy.state = sCopy := by
    rw [straightLineFinalState_eq_of_halted hCopy_sl cClear.state cCopy hCopy_steps' hCopy_halted', hsCopy_eq]
  have hCopy_steps : Steps (copyRegisterRange (base + 1) 0 n) ⟨0, cClear.state⟩
      ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ := by
    have : cCopy = ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ := by
      ext <;> simp only [hCopy_pc, hCopy_state_sCopy]
    rw [← this]; exact hCopy_steps'
  have hCopy_halted : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
      (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
  have hInputs_restored : ∀ j : ℕ, (hj : j < n) → sCopy.read j = inputs ⟨j, hj⟩ := fun j hj => by
    simp only [Nat.zero_add] at hCopy_correct; rw [hCopy_correct j hj, hSaved_after_clear j hj]
  have hagree : sCopy.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG.maxRegister := by
    intro r _hr0 hr_max
    by_cases hr_n : r < n
    · rw [hInputs_restored r hr_n]; simp [State.fromInputs, State.read, hr_n]
    · rw [hCopy_preserves r (by omega), hClear_zeros r (by omega : r ≤ base)]
      simp [State.fromInputs, State.read, hr_n]
  let epG := Halts.executeFromAgreeingState hpG_halts hpG_sf hagree
  let eT := executeSingleTransfer 0 (base + n + 1 + i) epG.config.state
  have ⟨hPGT_steps, hPGT_halted⟩ := Steps.chain_concat epG.steps epG.halted epG.pc_eq eT.steps eT.halted
  have ⟨hCopyPGT_steps, hCopyPGT_halted⟩ := Steps.chain_concat hCopy_steps hCopy_halted rfl hPGT_steps hPGT_halted
  have ⟨hGPhase_steps, hGPhase_halted⟩ := Steps.chain_concat hClear_steps hClear_halted hClear_pc hCopyPGT_steps hCopyPGT_halted
  exact ⟨_, hGPhase_steps, hGPhase_halted⟩

theorem gPhase_writes_result {base n : ℕ} {pG : Program} {j : ℕ} {inputs : Fin n → ℕ}
    (hpG_sf : pG.IsStandardForm) (hpG_max : pG.maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (hpG_halts : Halts pG (List.ofFn inputs)) (s : State)
    (hSaved : ∀ k : ℕ, (hk : k < n) → s.read (base + 1 + k) = inputs ⟨k, hk⟩) (c' : Config)
    (hsteps : Steps (gPhase base n pG j) ⟨0, s⟩ c') (hhalted : c'.isHalted (gPhase base n pG j)) :
    c'.state.read (base + n + 1 + j) = Result pG (List.ofFn inputs) hpG_halts := by
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine base)
  have hCopyRange_sf := straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n)
  obtain ⟨sClear, hClear_steps, cRest, hRest_steps, hRest_halted⟩ := suffix_of_concat_from_zero hsteps hhalted hClear_sf
  obtain ⟨sCopy, hCopy_steps, cPGT, hPGT_steps, hPGT_halted⟩ := suffix_of_concat_from_zero hRest_steps hRest_halted hCopyRange_sf
  obtain ⟨sPG, hPG_steps, cT, hT_steps, hT_halted⟩ := suffix_of_concat_from_zero hPGT_steps hPGT_halted hpG_sf
  have hsClear_eq : sClear = straightLineFinalState (clearRegisters_isStraightLine base) s :=
    straightLineFinalState_eq_of_halted _ s ⟨_, sClear⟩ hClear_steps (by simp [Config.isHalted])
  have hSaved_after_clear : ∀ k : ℕ, (hk : k < n) → sClear.read (base + 1 + k) = inputs ⟨k, hk⟩ := by
    intro k hk; rw [hsClear_eq, clearRegisters_preserves_above' base s _ (by omega), hSaved k hk]
  have hsCopy_eq : sCopy = straightLineFinalState (copyRegisterRange_isStraightLine (base + 1) 0 n) sClear :=
    straightLineFinalState_eq_of_halted _ sClear ⟨_, sCopy⟩ hCopy_steps (by simp [Config.isHalted])
  obtain ⟨_, hsCopy'_eq, hCopy_correct, hCopy_preserves⟩ := copyRegisterRange_state (base + 1) 0 n sClear (Or.inr (by omega))
  have hInputs_after_copy : ∀ k : ℕ, (hk : k < n) → sCopy.read k = inputs ⟨k, hk⟩ := fun k hk => by
    rw [hsCopy_eq, hsCopy'_eq]; simp only [Nat.zero_add] at hCopy_correct
    rw [hCopy_correct k hk, hSaved_after_clear k hk]
  have hagree : sCopy.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG.maxRegister := by
    intro r _ hr_max
    by_cases hr_n : r < n
    · rw [hInputs_after_copy r hr_n]; simp [State.fromInputs, State.read, hr_n]
    · rw [hsCopy_eq, hsCopy'_eq, hCopy_preserves r (Or.inr (by omega)), hsClear_eq,
          clearRegisters_zeros' base s r (by omega : r ≤ base)]
      simp [State.fromInputs, State.read, hr_n]
  let epG := Halts.executeFromAgreeingState hpG_halts hpG_sf hagree
  have hsPG_eq : sPG = epG.config.state :=
    congrArg Config.state (Steps.halts_unique hPG_steps (by simp [Config.isHalted]) epG.steps epG.halted)
  have hR0_after_pG : sPG.read 0 = Result pG (List.ofFn inputs) hpG_halts := by
    rw [hsPG_eq, AgreeingExecution.output_eq epG (Nat.zero_le _)]; rfl
  have hT_result : cT.state.read (base + n + 1 + j) = sPG.read 0 := by
    let tr := executeSingleTransfer 0 (base + n + 1 + j) sPG
    simp only [Steps.halts_unique hT_steps hT_halted tr.steps tr.halted, tr.dst_eq]
  have hc'_state_eq : c'.state = cT.state := by
    have hPGT := Steps.chain_concat hPG_steps (by simp [Config.isHalted]) rfl hT_steps hT_halted
    have hCopyPGT := Steps.chain_concat hCopy_steps (by simp [Config.isHalted]) rfl hPGT_steps hPGT_halted
    have hClearRest := Steps.chain_concat hClear_steps (by simp [Config.isHalted]) rfl hRest_steps hRest_halted
    rw [Steps.halts_unique hsteps hhalted hClearRest.1 hClearRest.2,
        Steps.halts_unique hRest_steps hRest_halted hCopyPGT.1 hCopyPGT.2,
        Steps.halts_unique hPGT_steps hPGT_halted hPGT.1 hPGT.2]
  rw [hc'_state_eq, hT_result, hR0_after_pG]

theorem allGPhases_halts_from_saved_inputs {m n base : ℕ} {pGs : Fin m → Program} {inputs : Fin n → ℕ}
    (hpGs_sf : ∀ i, (pGs i).IsStandardForm) (hpGs_max : ∀ i, (pGs i).maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (hpGs_halts : ∀ i, Halts (pGs i) (List.ofFn inputs)) (s : State)
    (hSaved : ∀ j : ℕ, (hj : j < n) → s.read (base + 1 + j) = inputs ⟨j, hj⟩) :
    ∃ c, Steps (allGPhases m n base pGs) ⟨0, s⟩ c ∧ c.isHalted (allGPhases m n base pGs) := by
  induction m with
  | zero => simp only [allGPhases, List.finRange_zero, List.foldl_nil]
            exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, by simp [Config.isHalted]⟩
  | succ m' ih =>
    simp only [allGPhases]
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map, List.foldl_cons, List.foldl_nil]
    let pGs' : Fin m' → Program := fun i => pGs i.castSucc
    have hPrefix_eq : List.foldl (fun x y => Program.concat x (gPhase base n (pGs y.castSucc) ↑y.castSucc))
        [] (List.finRange m') = allGPhases m' n base pGs' := rfl
    rw [hPrefix_eq]
    obtain ⟨cPrefix, hPrefix_steps, hPrefix_halted⟩ := ih (fun i => hpGs_sf i.castSucc)
      (fun i => hpGs_max i.castSucc) (fun i => hpGs_halts i.castSucc)
    have hPrefix_sf := allGPhases_isStandardForm (n := n) (base := base) (fun i => hpGs_sf i.castSucc)
    have hPrefix_pc := hPrefix_sf.pc_eq_length_of_halted hPrefix_steps (Nat.zero_le _) hPrefix_halted
    have hSaved_after_prefix : ∀ j : ℕ, (hj : j < n) → cPrefix.state.read (base + 1 + j) = inputs ⟨j, hj⟩ := fun j hj =>
      allGPhases_prefix_preserves_saved_inputs m' n base pGs' (fun i => hpGs_sf i.castSucc) (fun i => hpGs_max i.castSucc) hn_le_base
        m' (Nat.le_refl m') s cPrefix.state cPrefix
        (allGPhases_prefix_full m' n base pGs' ▸ hPrefix_steps) (allGPhases_prefix_full m' n base pGs' ▸ hPrefix_halted) rfl
        (base + 1 + j) (by omega) (by omega) ▸ hSaved j hj
    obtain ⟨cLast, hLast_steps, hLast_halted⟩ := gPhase_halts_from_saved_inputs (i := m')
      (hpGs_sf (Fin.last m')) (hpGs_max (Fin.last m')) hn_le_base (hpGs_halts (Fin.last m')) cPrefix.state hSaved_after_prefix
    have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hPrefix_steps hPrefix_halted hPrefix_pc hLast_steps hLast_halted
    exact ⟨_, hTotal_steps, hTotal_halted⟩

theorem finalPhase_halts_from_results {m n base : ℕ} {pF : Program} {results : Fin m → ℕ}
    (hpF_sf : pF.IsStandardForm) (hpF_max : pF.maxRegister ≤ base) (hm_le_base : m ≤ base + 1)
    (hpF_halts : Halts pF (List.ofFn results)) (s : State)
    (hResults : ∀ j : ℕ, (hj : j < m) → s.read (base + n + 1 + j) = results ⟨j, hj⟩) :
    ∃ c, Steps (finalPhase m n base pF) ⟨0, s⟩ c ∧ c.isHalted (finalPhase m n base pF) := by
  have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves⟩ := clearRegisters_exec base s
  have hResults_after_clear : ∀ j : ℕ, (hj : j < m) → cClear.state.read (base + n + 1 + j) = results ⟨j, hj⟩ :=
    fun j hj => by rw [hClear_preserves (base + n + 1 + j) (by omega)]; exact hResults j hj
  obtain ⟨sTransfer, hsTransfer_eq, hTransfer_correct, hTransfer_preserves⟩ :=
    transferResultsToInputs_state (base + n + 1) m cClear.state (by omega)
  obtain ⟨cTransfer, hTransfer_steps', hTransfer_halted', hTransfer_pc⟩ := straightLine_halts_from_state hTransfer_sl cClear.state
  have hTransfer_state_sTransfer : cTransfer.state = sTransfer := by
    rw [straightLineFinalState_eq_of_halted hTransfer_sl cClear.state cTransfer hTransfer_steps' hTransfer_halted', hsTransfer_eq]
  have hTransfer_steps : Steps (transferResultsToInputs (base + n + 1) m) ⟨0, cClear.state⟩
      ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
    have : cTransfer = ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
      ext <;> simp only [hTransfer_pc, hTransfer_state_sTransfer]
    rw [← this]; exact hTransfer_steps'
  have hTransfer_halted : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).isHalted
      (transferResultsToInputs (base + n + 1) m) := by simp [Config.isHalted]
  have hInputs_set : ∀ j : ℕ, (hj : j < m) → sTransfer.read j = results ⟨j, hj⟩ := fun j hj => by
    rw [hTransfer_correct j hj, hResults_after_clear j hj]
  have hagree : sTransfer.agreeOn (State.fromInputs (List.ofFn results)) 0 pF.maxRegister := by
    intro r _hr0 hr_max
    by_cases hr_m : r < m
    · rw [hInputs_set r hr_m]; simp [State.fromInputs, State.read, hr_m]
    · rw [hTransfer_preserves r (by omega), hClear_zeros r (by omega : r ≤ base)]
      simp [State.fromInputs, State.read, hr_m]
  let epF := Halts.executeFromAgreeingState hpF_halts hpF_sf hagree
  have ⟨hTransferF_steps, hTransferF_halted⟩ := Steps.chain_concat hTransfer_steps hTransfer_halted rfl epF.steps epF.halted
  have ⟨hFinal_steps, hFinal_halted⟩ := Steps.chain_concat hClear_steps hClear_halted hClear_pc hTransferF_steps hTransferF_halted
  exact ⟨_, hFinal_steps, hFinal_halted⟩

theorem allGPhases_suffix_preserves_earlier_results {m n base : ℕ} {pGs : Fin m → Program}
    (hpGs_sf : ∀ i, (pGs i).IsStandardForm) (hpGs_max : ∀ i, (pGs i).maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (start k : ℕ) (hk_lt_start : k < start) (s : State) (c' : Config)
    (hsteps : Steps (allGPhases_suffix m n base pGs start) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (allGPhases_suffix m n base pGs start)) :
    c'.state.read (base + n + 1 + k) = s.read (base + n + 1 + k) := by
  match m with
  | 0 => simp only [allGPhases_suffix, List.finRange_zero, List.drop_nil, List.foldl_nil] at hsteps hhalted
         rw [Steps.halts_unique hsteps hhalted Relation.ReflTransGen.refl (by simp [Config.isHalted])]
  | Nat.succ m' =>
    by_cases hEmpty : start ≥ m' + 1
    · have hSuffix_empty : allGPhases_suffix (m' + 1) n base pGs start = [] := by
        simp only [allGPhases_suffix]; rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl
      rw [hSuffix_empty] at hsteps hhalted
      rw [Steps.halts_unique hsteps hhalted Relation.ReflTransGen.refl (by simp [Config.isHalted])]
    · push_neg at hEmpty
      have hSuffix_decomp : allGPhases_suffix (m' + 1) n base pGs start =
          (gPhase base n (pGs ⟨start, hEmpty⟩) start).concat (allGPhases_suffix (m' + 1) n base pGs (start + 1)) := by
        simp only [allGPhases_suffix]
        rw [List.drop_eq_getElem_cons (by simp; exact hEmpty), List.foldl_cons, foldl_concat_eq_acc_concat]
        simp only [concat_nil_left, List.getElem_finRange]; congr 2
      rw [hSuffix_decomp] at hsteps hhalted
      obtain ⟨sFirst, hFirst_steps, cRest, hRest_steps, hRest_halted⟩ :=
        suffix_of_concat_from_zero hsteps hhalted (gPhase_isStandardForm (hpGs_sf ⟨start, hEmpty⟩))
      have hFirst_preserves := gPhase_preserves_other_results base n (pGs ⟨start, hEmpty⟩) start k
        (hpGs_sf _) (hpGs_max _) hn_le_base (by omega) s sFirst ⟨_, sFirst⟩ hFirst_steps (by simp [Config.isHalted]) rfl
      have hRest_preserves := allGPhases_suffix_preserves_earlier_results hpGs_sf hpGs_max hn_le_base
        (start + 1) k (by omega) sFirst cRest hRest_steps hRest_halted
      have hc'_eq_cRest : c'.state = cRest.state := by
        have hChain := Steps.chain_concat hFirst_steps (by simp [Config.isHalted]) rfl hRest_steps hRest_halted
        rw [Steps.halts_unique hsteps hhalted hChain.1 hChain.2]
      rw [hc'_eq_cRest, hRest_preserves, hFirst_preserves]
termination_by m - start
decreasing_by simp_wf; omega

set_option maxHeartbeats 400000 in
theorem allGPhases_saves_result {m n : ℕ} [NeZero m] {pF : Program} {pGs : Fin m → Program}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ} (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ, (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ) (hGs_dom : ∀ i, (gs i inputs).Dom) (i : Fin m) (sSaveGPhases : State)
    (hSaveGPhases_halted : ∃ c : Config,
      Steps ((copyRegisterRange 0 (compositionBase m n pF pGs + 1) n).concat
             (allGPhases m n (compositionBase m n pF pGs) pGs))
        ⟨0, State.fromInputs (List.ofFn inputs)⟩ c ∧
      c.isHalted ((copyRegisterRange 0 (compositionBase m n pF pGs + 1) n).concat
                  (allGPhases m n (compositionBase m n pF pGs) pGs)) ∧ c.state = sSaveGPhases) :
    sSaveGPhases.read (compositionBase m n pF pGs + n + 1 + i.val) = (gs i inputs).get (hGs_dom i) := by
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  obtain ⟨c, hsteps, hhalted, hstate_eq⟩ := hSaveGPhases_halted
  have hSplit := allGPhases_split m n base pGs (i.val + 1) (Nat.lt_iff_add_one_le.mp i.isLt)
  have hSave_sf := saveInputs_isStandardForm base n
  have hPrefix_sf := allGPhases_prefix_isStandardForm (n := n) (base := base) hGs_sf (i.val + 1)
  have hProg_eq : saveInputs.concat (allGPhases m n base pGs) =
      (saveInputs.concat (allGPhases_prefix m n base pGs (i.val + 1))).concat
      (allGPhases_suffix m n base pGs (i.val + 1)) := by rw [hSplit, concat_assoc]
  have hSavePrefix_sf := hSave_sf.concat hPrefix_sf
  rw [hProg_eq] at hsteps hhalted
  obtain ⟨sSavePrefix, hSavePrefix_steps, cSuffix, hSuffix_steps, hSuffix_halted⟩ :=
    suffix_of_concat_from_zero hsteps hhalted hSavePrefix_sf
  have hPrefixDecomp : allGPhases_prefix m n base pGs (i.val + 1) =
      (allGPhases_prefix m n base pGs i.val).concat (gPhase base n (pGs i) i.val) := by
    simp only [allGPhases_prefix]
    rw [List.take_succ_eq_append_getElem (by simp : i.val < (List.finRange m).length),
        List.foldl_append, List.foldl_cons, List.foldl_nil, foldl_concat_eq_acc_concat]
    simp only [List.getElem_finRange]; congr 1
  have hSavePrefixI_sf := hSave_sf.concat (allGPhases_prefix_isStandardForm (n := n) (base := base) hGs_sf i.val)
  have hSavePrefix_eq : saveInputs.concat (allGPhases_prefix m n base pGs (i.val + 1)) =
      (saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat (gPhase base n (pGs i) i.val) := by
    rw [hPrefixDecomp, concat_assoc]
  rw [hSavePrefix_eq] at hSavePrefix_steps
  have hSavePrefixI_halted : (⟨((saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat
      (gPhase base n (pGs i) i.val)).length, sSavePrefix⟩ : Config).isHalted
      ((saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat (gPhase base n (pGs i) i.val)) := by
    simp [Config.isHalted]
  obtain ⟨sSavePrefixI, hSavePrefixI_steps, cGPhase_i, hGPhase_i_steps, hGPhase_i_halted⟩ :=
    suffix_of_concat_from_zero hSavePrefix_steps hSavePrefixI_halted hSavePrefixI_sf
  have hpGs_max : ∀ j, (pGs j).maxRegister ≤ base := fun j => compositionBase_ge_pGs_max m n pF pGs j
  have hn_le_base : n ≤ base + 1 := compositionBase_ge_n m n pF pGs
  have hSaved_i : ∀ k : ℕ, (hk : k < n) → sSavePrefixI.read (base + 1 + k) = inputs ⟨k, hk⟩ := by
    intro k hk
    have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
    obtain ⟨sSave, hsSave_eq, hSave_copies, _⟩ :=
      copyRegisterRange_state 0 (base + 1) n (State.fromInputs (List.ofFn inputs)) (Or.inl (by omega))
    have hAfterSave : sSave.read (base + 1 + k) = inputs ⟨k, hk⟩ := by
      rw [hSave_copies k hk]; simp [State.fromInputs, State.read, hk]
    obtain ⟨cSave, hSave_steps', hSave_halted', hSave_pc'⟩ :=
      straightLine_halts_from_state hSave_sl (State.fromInputs (List.ofFn inputs))
    have hSave_state_sSave : cSave.state = sSave := by
      rw [straightLineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps' hSave_halted', hsSave_eq]
    by_cases hi_zero : i.val = 0
    · have hPrefix_empty : allGPhases_prefix m n base pGs i.val = [] := by
        simp only [hi_zero, allGPhases_prefix, List.take_zero, List.foldl_nil]
      rw [hPrefix_empty, concat_nil_right] at hSavePrefixI_steps
      have hstate_eq' : sSavePrefixI = cSave.state := congrArg Config.state
        (Steps.halts_unique hSavePrefixI_steps (by simp [Config.isHalted]) hSave_steps' hSave_halted')
      rw [hstate_eq', hSave_state_sSave, hAfterSave]
    · obtain ⟨sSave', hSave_steps'', cPrefix, hPrefix_steps, hPrefix_halted⟩ :=
        suffix_of_concat_from_zero hSavePrefixI_steps (by simp [Config.isHalted]) hSave_sf
      have hsSave'_eq : sSave' = sSave := by
        have : sSave' = cSave.state := congrArg Config.state
          (Steps.halts_unique hSave_steps'' (by simp [Config.isHalted]) hSave_steps' hSave_halted')
        rw [this, hSave_state_sSave]
      conv at hPrefix_steps => rw [hsSave'_eq]
      have hcPrefix_state : cPrefix.state = sSavePrefixI := by
        have hPrefix_steps' : Steps (allGPhases_prefix m n base pGs i.val) ⟨0, cSave.state⟩ cPrefix := hSave_state_sSave ▸ hPrefix_steps
        have hChain := Steps.chain_concat hSave_steps' hSave_halted' hSave_pc' hPrefix_steps' hPrefix_halted
        exact (congrArg Config.state (Steps.halts_unique hSavePrefixI_steps (by simp [Config.isHalted]) hChain.1 hChain.2)).symm
      rw [← hcPrefix_state, allGPhases_prefix_preserves_saved_inputs m n base pGs hGs_sf hpGs_max hn_le_base
        i.val (Nat.le_of_lt i.isLt) sSave cPrefix.state cPrefix hPrefix_steps hPrefix_halted rfl
        (base + 1 + k) (by omega) (by omega), hAfterSave]
  have hGPhase_halts_i := (hGs_spec i inputs).1.mpr (hGs_dom i)
  have hGPhase_i_result := gPhase_writes_result (hGs_sf i) (hpGs_max i) hn_le_base hGPhase_halts_i
    sSavePrefixI hSaved_i cGPhase_i hGPhase_i_steps hGPhase_i_halted
  have hSuffix_preserves := allGPhases_suffix_preserves_earlier_results hGs_sf hpGs_max hn_le_base
    (i.val + 1) i.val (by omega) sSavePrefix cSuffix hSuffix_steps hSuffix_halted
  have hsSavePrefix_eq_cGPhase : sSavePrefix = cGPhase_i.state := by
    have hChain := Steps.chain_concat hSavePrefixI_steps (by simp [Config.isHalted]) rfl hGPhase_i_steps hGPhase_i_halted
    exact congrArg Config.state (Steps.halts_unique hSavePrefix_steps (by simp [Config.isHalted]) hChain.1 hChain.2)
  have hc_eq_cSuffix : c.state = cSuffix.state := by
    rw [hSavePrefix_eq] at hsteps hhalted
    have hChain := Steps.chain_concat hSavePrefix_steps hSavePrefixI_halted rfl hSuffix_steps hSuffix_halted
    simp only [Steps.halts_unique hsteps hhalted hChain.1 hChain.2]
  rw [← hstate_eq, hc_eq_cSuffix, hSuffix_preserves, hsSavePrefix_eq_cGPhase, hGPhase_i_result,
      (hGs_spec i inputs).2 hGPhase_halts_i (hGs_dom i)]

end Urm
