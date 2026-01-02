/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Preservation
import Mathlib.Data.List.GetD

/-! # Forward Direction Helpers: Dom → Halts

Lemmas for proving that composition halts when all component functions halt.

## Main results

- `gPhase_halts_from_saved_inputs`: A single gPhase halts from saved inputs state
- `gPhase_writes_result`: A single gPhase writes the result to the correct register
- `allGPhases_halts_from_saved_inputs`: All gPhases halt from saved inputs state
- `allGPhases_saves_result`: After all gPhases, results are saved correctly
-/

namespace Urm

open Program

/-! ## Forward Direction Helpers: Dom → Halts -/

/-- A single gPhase halts from a state where R[base+1..base+n] contain the inputs.
This is the forward direction: given pGs i halts on inputs, gPhase halts from saved state. -/
theorem gPhase_halts_from_saved_inputs
    {base n : ℕ} {pG : Program} {i : ℕ}
    {inputs : Fin n → ℕ}
    (hpG_sf : pG.IsStandardForm)
    (hpG_max : pG.maxRegister ≤ base)
    (hn_le_base : n ≤ base + 1)
    (hpG_halts : Halts pG (List.ofFn inputs))
    (s : State)
    (hSaved : ∀ j : ℕ, (hj : j < n) → s.read (base + 1 + j) = inputs ⟨j, hj⟩) :
    ∃ c, Steps (gPhase base n pG i) ⟨0, s⟩ c ∧ c.isHalted (gPhase base n pG i) := by
  -- gPhase = clear ++ (copyRange ++ (pG ++ [T]))
  have hClear_sl := clearRegisters_isStraightLine base
  have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
  have hT_sl := single_T_isStraightLine' 0 (base + n + 1 + i)

  -- Clear halts
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves⟩ :=
    clearRegisters_exec base s

  -- After clear, saved inputs still there
  have hSaved_after_clear : ∀ j : ℕ, (hj : j < n) → cClear.state.read (base + 1 + j) = inputs ⟨j, hj⟩ :=
    fun j hj => by rw [hClear_preserves (base + 1 + j) (by omega)]; exact hSaved j hj

  -- Copy restored inputs: use straightLine_halts_from_state directly
  have hNoOverlap : base + 1 + n ≤ 0 ∨ 0 + n ≤ base + 1 := Or.inr (by omega)
  obtain ⟨sCopy, hsCopy_eq, hCopy_correct, hCopy_preserves⟩ :=
    copyRegisterRange_state (base + 1) 0 n cClear.state hNoOverlap

  -- Get halting from arbitrary state
  obtain ⟨cCopy, hCopy_steps', hCopy_halted', hCopy_pc⟩ :=
    straightLine_halts_from_state hCopy_sl cClear.state
  -- State equals straightLineFinalState
  have hCopy_state_eq : cCopy.state = straightLineFinalState hCopy_sl cClear.state :=
    straightLineFinalState_eq_of_halted hCopy_sl cClear.state cCopy hCopy_steps' hCopy_halted'
  -- So cCopy.state = sCopy
  have hCopy_state_sCopy : cCopy.state = sCopy := by rw [hCopy_state_eq, hsCopy_eq]

  -- Build steps/halted for target config
  have hCopy_steps : Steps (copyRegisterRange (base + 1) 0 n) ⟨0, cClear.state⟩
      ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ := by
    have : cCopy = ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ := by
      ext <;> simp only [hCopy_pc, hCopy_state_sCopy]
    rw [← this]; exact hCopy_steps'
  have hCopy_halted : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
      (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]

  -- After copy, R[0..n-1] = inputs
  have hInputs_restored : ∀ j : ℕ, (hj : j < n) → sCopy.read j = inputs ⟨j, hj⟩ := by
    intro j hj
    have h1 := hCopy_correct j hj
    simp only [Nat.zero_add] at h1
    rw [h1, hSaved_after_clear j hj]

  -- State agrees with inputs on R[0..pG.maxRegister]
  have hagree : sCopy.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG.maxRegister := by
    intro r _hr0 hr_max
    by_cases hr_n : r < n
    · rw [hInputs_restored r hr_n]
      simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hr_n, ↓reduceDIte, Option.getD_some]
    · -- r ≥ n, both should be 0
      have hr_le_base : r ≤ base := Nat.le_trans hr_max hpG_max
      have hsCopy_r : sCopy.read r = 0 := by
        have h1 : sCopy.read r = cClear.state.read r := hCopy_preserves r (by omega)
        have h2 : cClear.state.read r = 0 := hClear_zeros r (by omega)
        rw [h1, h2]
      have hfromInputs_r : (State.fromInputs (List.ofFn inputs)).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hr_n, ↓reduceDIte, Option.getD_none]
      rw [hsCopy_r, hfromInputs_r]

  -- pG halts from sCopy via agreeing execution
  let epG := Halts.executeFromAgreeingState hpG_halts hpG_sf hagree
  have hpG_steps' := epG.steps
  have hpG_halted' := epG.halted
  have hpG_pc' := epG.pc_eq

  -- T halts
  let eT := executeSingleTransfer 0 (base + n + 1 + i) epG.config.state

  -- Chain: pG ++ T
  have ⟨hPGT_steps, hPGT_halted⟩ := Steps.chain_concat hpG_steps' hpG_halted' hpG_pc' eT.steps eT.halted

  -- Chain: copy ++ (pG ++ T)
  have ⟨hCopyPGT_steps, hCopyPGT_halted⟩ := Steps.chain_concat hCopy_steps hCopy_halted rfl hPGT_steps hPGT_halted

  -- Chain: clear ++ (copy ++ (pG ++ T))
  have ⟨hGPhase_steps, hGPhase_halted⟩ := Steps.chain_concat hClear_steps hClear_halted hClear_pc hCopyPGT_steps hCopyPGT_halted

  exact ⟨_, hGPhase_steps, hGPhase_halted⟩

/-- A single gPhase writes the result of pG to R[base+n+1+j].
This tracks what value gPhase writes, not just that it halts. -/
theorem gPhase_writes_result
    {base n : ℕ} {pG : Program} {j : ℕ}
    {inputs : Fin n → ℕ}
    (hpG_sf : pG.IsStandardForm)
    (hpG_max : pG.maxRegister ≤ base)
    (hn_le_base : n ≤ base + 1)
    (hpG_halts : Halts pG (List.ofFn inputs))
    (s : State)
    (hSaved : ∀ k : ℕ, (hk : k < n) → s.read (base + 1 + k) = inputs ⟨k, hk⟩)
    (c' : Config)
    (hsteps : Steps (gPhase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (gPhase base n pG j)) :
    c'.state.read (base + n + 1 + j) = Result pG (List.ofFn inputs) hpG_halts := by
  -- gPhase = clear ++ (copyRange ++ (pG ++ [T]))
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine base)
  have hCopyRange_sf := straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n)

  -- Extract clear execution and suffix
  obtain ⟨sClear, hClear_steps, ⟨cRest, hRest_steps, hRest_halted⟩⟩ :=
    suffix_of_concat_from_zero hsteps hhalted hClear_sf

  -- Extract copyRange execution and suffix
  obtain ⟨sCopy, hCopy_steps, ⟨cPGT, hPGT_steps, hPGT_halted⟩⟩ :=
    suffix_of_concat_from_zero hRest_steps hRest_halted hCopyRange_sf

  -- Extract pG execution and T
  obtain ⟨sPG, hPG_steps, ⟨cT, hT_steps, hT_halted⟩⟩ :=
    suffix_of_concat_from_zero hPGT_steps hPGT_halted hpG_sf

  -- After clear, saved inputs still there
  have hsClear_eq : sClear = straightLineFinalState (clearRegisters_isStraightLine base) s :=
    straightLineFinalState_eq_of_halted _ s ⟨_, sClear⟩ hClear_steps (by simp [Config.isHalted])
  have hSaved_after_clear : ∀ k : ℕ, (hk : k < n) → sClear.read (base + 1 + k) = inputs ⟨k, hk⟩ := by
    intro k hk; rw [hsClear_eq, clearRegisters_preserves_above' base s _ (by omega), hSaved k hk]

  -- After copy, R[0..n-1] = inputs
  have hNoOverlap : base + 1 + n ≤ 0 ∨ 0 + n ≤ base + 1 := Or.inr (by omega)
  have hsCopy_eq : sCopy = straightLineFinalState (copyRegisterRange_isStraightLine (base + 1) 0 n) sClear :=
    straightLineFinalState_eq_of_halted _ sClear ⟨_, sCopy⟩ hCopy_steps (by simp [Config.isHalted])
  obtain ⟨_, hsCopy'_eq, hCopy_correct, hCopy_preserves⟩ := copyRegisterRange_state (base + 1) 0 n sClear hNoOverlap
  have hInputs_after_copy : ∀ k : ℕ, (hk : k < n) → sCopy.read k = inputs ⟨k, hk⟩ := fun k hk => by
    rw [hsCopy_eq, hsCopy'_eq]; simp only [Nat.zero_add] at hCopy_correct
    rw [hCopy_correct k hk, hSaved_after_clear k hk]

  -- State sCopy agrees with inputs on R[0..pG.maxRegister]
  have hagree : sCopy.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG.maxRegister := by
    intro r _ hr_max
    by_cases hr_n : r < n
    · rw [hInputs_after_copy r hr_n]
      simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        hr_n, ↓reduceDIte, Option.getD_some]
    · -- r ≥ n, both should be 0
      have hsCopy_r : sCopy.read r = 0 := by
        rw [hsCopy_eq, hsCopy'_eq, hCopy_preserves r (Or.inr (by omega)), hsClear_eq]
        exact clearRegisters_zeros' base s r (by omega : r ≤ base)
      rw [hsCopy_r]; simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, hr_n, ↓reduceDIte, Option.getD_none]

  -- pG runs from sCopy via agreeing execution
  let epG := Halts.executeFromAgreeingState hpG_halts hpG_sf hagree

  -- sPG = epG.config.state (by determinism)
  have hsPG_eq : sPG = epG.config.state := by
    have hPG_halted : (⟨pG.length, sPG⟩ : Config).isHalted pG := by simp [Config.isHalted]
    have huniq := Steps.halts_unique hPG_steps hPG_halted epG.steps epG.halted
    exact congrArg Config.state huniq

  -- After pG, R[0] = Result pG inputs
  have hR0_after_pG : sPG.read 0 = Result pG (List.ofFn inputs) hpG_halts := by
    rw [hsPG_eq]
    have hmax : 0 ≤ pG.maxRegister := Nat.zero_le _
    rw [AgreeingExecution.output_eq epG hmax]
    simp only [Result, State.output]
    rfl

  -- T copies R[0] to R[base+n+1+j]
  have hT_result : cT.state.read (base + n + 1 + j) = sPG.read 0 := by
    let tr := executeSingleTransfer 0 (base + n + 1 + j) sPG
    have hcT_eq : cT = tr.config := Steps.halts_unique hT_steps hT_halted tr.steps tr.halted
    simp only [hcT_eq, SingleTransferResult.config]
    exact tr.dst_eq

  -- Chain state equalities
  -- c' has the same state as cT (modulo pc)
  have hc'_state_eq : c'.state = cT.state := by
    -- Use determinism: both c' and our chain reach the same final state
    have hPG_halted : (⟨pG.length, sPG⟩ : Config).isHalted pG := by simp [Config.isHalted]
    have hPGT_combined := Steps.chain_concat hPG_steps hPG_halted rfl hT_steps hT_halted
    have hCopy_halted : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
        (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
    have hCopyPGT_combined := Steps.chain_concat hCopy_steps hCopy_halted rfl hPGT_steps hPGT_halted
    have hClear_halted : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
        (clearRegisters base) := by simp [Config.isHalted]
    have hClearRest_combined := Steps.chain_concat hClear_steps hClear_halted rfl hRest_steps hRest_halted
    have huniq := Steps.halts_unique hsteps hhalted hClearRest_combined.1 hClearRest_combined.2
    rw [huniq]
    -- Now show cRest.state = cT.state through the chain
    have hcRest_eq : cRest.state = cPGT.state := by
      have huniq := Steps.halts_unique hRest_steps hRest_halted hCopyPGT_combined.1 hCopyPGT_combined.2
      rw [huniq]
    have hcPGT_eq : cPGT.state = cT.state := by
      have huniq := Steps.halts_unique hPGT_steps hPGT_halted hPGT_combined.1 hPGT_combined.2
      rw [huniq]
    rw [hcRest_eq, hcPGT_eq]

  rw [hc'_state_eq, hT_result, hR0_after_pG]

/-- All gPhases halt from a state where R[base+1..base+n] contain the inputs.
This is proved by induction on the number of phases. -/
theorem allGPhases_halts_from_saved_inputs
    {m n : ℕ} {base : ℕ} {pGs : Fin m → Program}
    {inputs : Fin n → ℕ}
    (hpGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hpGs_max : ∀ i, (pGs i).maxRegister ≤ base)
    (hn_le_base : n ≤ base + 1)
    (hpGs_halts : ∀ i, Halts (pGs i) (List.ofFn inputs))
    (s : State)
    (hSaved : ∀ j : ℕ, (hj : j < n) → s.read (base + 1 + j) = inputs ⟨j, hj⟩) :
    ∃ c, Steps (allGPhases m n base pGs) ⟨0, s⟩ c ∧ c.isHalted (allGPhases m n base pGs) := by
  -- Induction on m (number of phases)
  induction m with
  | zero =>
    -- Empty program halts immediately
    simp only [allGPhases, List.finRange_zero, List.foldl_nil]
    exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, by simp [Config.isHalted]⟩
  | succ m' ih =>
    -- allGPhases (m'+1) = allGPhases m' ++ gPhase (Fin.last m')
    simp only [allGPhases]
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map, List.foldl_cons, List.foldl_nil]

    -- Define pGs' = pGs restricted to Fin m' via castSucc
    let pGs' : Fin m' → Program := fun i => pGs i.castSucc

    -- The inner foldl equals allGPhases m' n base pGs'
    have hPrefix_eq : List.foldl (fun x y => Program.concat x (gPhase base n (pGs y.castSucc) ↑y.castSucc))
        [] (List.finRange m') = allGPhases m' n base pGs' := by
      unfold allGPhases
      rfl

    rw [hPrefix_eq]

    -- Apply IH to get prefix halts
    have hpGs'_sf : ∀ i, (pGs' i).IsStandardForm := fun i => hpGs_sf i.castSucc
    have hpGs'_max : ∀ i, (pGs' i).maxRegister ≤ base := fun i => hpGs_max i.castSucc
    have hpGs'_halts : ∀ i, Halts (pGs' i) (List.ofFn inputs) := fun i => hpGs_halts i.castSucc

    obtain ⟨cPrefix, hPrefix_steps, hPrefix_halted⟩ := ih hpGs'_sf hpGs'_max hpGs'_halts

    -- Get prefix pc and standard form
    have hPrefix_sf : (allGPhases m' n base pGs').IsStandardForm := allGPhases_isStandardForm hpGs'_sf
    have hPrefix_pc : cPrefix.pc = (allGPhases m' n base pGs').length :=
      hPrefix_sf.pc_eq_length_of_halted hPrefix_steps (Nat.zero_le _) hPrefix_halted

    -- Saved inputs preserved after prefix (use preservation lemma)
    have hSaved_after_prefix : ∀ j : ℕ, (hj : j < n) → cPrefix.state.read (base + 1 + j) = inputs ⟨j, hj⟩ := by
      intro j hj
      -- Convert hPrefix_steps to use allGPhases_prefix form
      have hPrefix_steps' : Steps (allGPhases_prefix m' n base pGs' m') ⟨0, s⟩ cPrefix := by
        rw [allGPhases_prefix_full]; exact hPrefix_steps
      have hPrefix_halted' : cPrefix.isHalted (allGPhases_prefix m' n base pGs' m') := by
        rw [allGPhases_prefix_full]; exact hPrefix_halted
      exact allGPhases_prefix_preserves_saved_inputs m' n base pGs' hpGs'_sf hpGs'_max hn_le_base
        m' (Nat.le_refl m') s cPrefix.state cPrefix hPrefix_steps' hPrefix_halted' rfl
        (base + 1 + j) (by omega) (by omega)
        ▸ hSaved j hj

    -- gPhase (Fin.last m') halts from cPrefix.state
    have hLast_halts := gPhase_halts_from_saved_inputs (i := m')
      (hpGs_sf (Fin.last m'))
      (hpGs_max (Fin.last m'))
      hn_le_base
      (hpGs_halts (Fin.last m'))
      cPrefix.state
      hSaved_after_prefix
    obtain ⟨cLast, hLast_steps, hLast_halted⟩ := hLast_halts

    -- Chain prefix with last gPhase
    have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hPrefix_steps hPrefix_halted hPrefix_pc
      hLast_steps hLast_halted

    exact ⟨_, hTotal_steps, hTotal_halted⟩

/-- Final phase halts from a state where R[base+n+1..base+n+m] contain the results. -/
theorem finalPhase_halts_from_results
    {m n : ℕ} {base : ℕ} {pF : Program}
    {results : Fin m → ℕ}
    (hpF_sf : pF.IsStandardForm)
    (hpF_max : pF.maxRegister ≤ base)
    (hm_le_base : m ≤ base + 1)
    (hpF_halts : Halts pF (List.ofFn results))
    (s : State)
    (hResults : ∀ j : ℕ, (hj : j < m) → s.read (base + n + 1 + j) = results ⟨j, hj⟩) :
    ∃ c, Steps (finalPhase m n base pF) ⟨0, s⟩ c ∧ c.isHalted (finalPhase m n base pF) := by
  -- finalPhase = clear ++ (transfer ++ pF)
  have hClear_sl := clearRegisters_isStraightLine base
  have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m

  -- Clear halts
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves⟩ :=
    clearRegisters_exec base s

  -- After clear, results still there
  have hResults_after_clear : ∀ j : ℕ, (hj : j < m) → cClear.state.read (base + n + 1 + j) = results ⟨j, hj⟩ :=
    fun j hj => by rw [hClear_preserves (base + n + 1 + j) (by omega)]; exact hResults j hj

  -- Transfer halts and sets up inputs: use straightLine_halts_from_state directly
  have hNoOverlap : m ≤ base + n + 1 := by omega
  obtain ⟨sTransfer, hsTransfer_eq, hTransfer_correct, hTransfer_preserves⟩ :=
    transferResultsToInputs_state (base + n + 1) m cClear.state hNoOverlap

  -- Get halting from arbitrary state
  obtain ⟨cTransfer, hTransfer_steps', hTransfer_halted', hTransfer_pc⟩ :=
    straightLine_halts_from_state hTransfer_sl cClear.state
  -- State equals straightLineFinalState
  have hTransfer_state_eq : cTransfer.state = straightLineFinalState hTransfer_sl cClear.state :=
    straightLineFinalState_eq_of_halted hTransfer_sl cClear.state cTransfer hTransfer_steps' hTransfer_halted'
  -- So cTransfer.state = sTransfer
  have hTransfer_state_sTransfer : cTransfer.state = sTransfer := by rw [hTransfer_state_eq, hsTransfer_eq]

  -- Build steps/halted for target config
  have hTransfer_steps : Steps (transferResultsToInputs (base + n + 1) m) ⟨0, cClear.state⟩
      ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
    have : cTransfer = ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
      ext <;> simp only [hTransfer_pc, hTransfer_state_sTransfer]
    rw [← this]; exact hTransfer_steps'
  have hTransfer_halted : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).isHalted
      (transferResultsToInputs (base + n + 1) m) := by simp [Config.isHalted]

  -- After transfer, R[0..m-1] = results
  have hInputs_set : ∀ j : ℕ, (hj : j < m) → sTransfer.read j = results ⟨j, hj⟩ := by
    intro j hj
    rw [hTransfer_correct j hj, hResults_after_clear j hj]

  -- State agrees with results on R[0..pF.maxRegister]
  have hagree : sTransfer.agreeOn (State.fromInputs (List.ofFn results)) 0 pF.maxRegister := by
    intro r _hr0 hr_max
    by_cases hr_m : r < m
    · rw [hInputs_set r hr_m]
      simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hr_m, ↓reduceDIte, Option.getD_some]
    · -- r ≥ m, both should be 0
      have hr_le_base : r ≤ base := Nat.le_trans hr_max hpF_max
      have hsTransfer_r : sTransfer.read r = 0 := by
        rw [hTransfer_preserves r (by omega), hClear_zeros r (by omega)]
      have hfromResults_r : (State.fromInputs (List.ofFn results)).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hr_m, ↓reduceDIte, Option.getD_none]
      rw [hsTransfer_r, hfromResults_r]

  -- pF halts from sTransfer via agreeing execution
  let epF := Halts.executeFromAgreeingState hpF_halts hpF_sf hagree

  -- Chain: transfer ++ pF
  have hTransfer_pc : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).pc =
      (transferResultsToInputs (base + n + 1) m).length := rfl
  have ⟨hTransferF_steps, hTransferF_halted⟩ := Steps.chain_concat hTransfer_steps hTransfer_halted
    hTransfer_pc epF.steps epF.halted

  -- Chain: clear ++ (transfer ++ pF)
  have ⟨hFinal_steps, hFinal_halted⟩ := Steps.chain_concat hClear_steps hClear_halted hClear_pc
    hTransferF_steps hTransferF_halted

  exact ⟨_, hFinal_steps, hFinal_halted⟩

/-- Suffix of allGPhases preserves result registers R[base+n+1+k] for k < start index.
This is because each phase j in the suffix writes only to R[base+n+1+j] where j ≥ start. -/
theorem allGPhases_suffix_preserves_earlier_results
    {m n : ℕ} {base : ℕ} {pGs : Fin m → Program}
    (hpGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hpGs_max : ∀ i, (pGs i).maxRegister ≤ base)
    (hn_le_base : n ≤ base + 1)
    (start k : ℕ) (hk_lt_start : k < start)
    (s : State) (c' : Config)
    (hsteps : Steps (allGPhases_suffix m n base pGs start) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (allGPhases_suffix m n base pGs start)) :
    c'.state.read (base + n + 1 + k) = s.read (base + n + 1 + k) := by
  -- Recursion on m - start (decreasing as start increases toward m)
  match m with
  | 0 =>
    simp only [allGPhases_suffix, List.finRange_zero, List.drop_nil, List.foldl_nil] at hsteps hhalted
    have hc'_eq : c' = ⟨0, s⟩ := by
      have h : Steps [] ⟨0, s⟩ ⟨0, s⟩ := Relation.ReflTransGen.refl
      have hh : (⟨0, s⟩ : Config).isHalted [] := by simp [Config.isHalted]
      exact Steps.halts_unique hsteps hhalted h hh
    rw [hc'_eq]
  | Nat.succ m' =>
    by_cases hEmpty : start ≥ m' + 1
    · -- Suffix is empty
      have hSuffix_empty : allGPhases_suffix (m' + 1) n base pGs start = [] := by
        simp only [allGPhases_suffix]
        rw [List.drop_eq_nil_of_le (by simp; omega)]
        rfl
      rw [hSuffix_empty] at hsteps hhalted
      have hc'_eq : c' = ⟨0, s⟩ := by
        have h : Steps [] ⟨0, s⟩ ⟨0, s⟩ := Relation.ReflTransGen.refl
        have hh : (⟨0, s⟩ : Config).isHalted [] := by simp [Config.isHalted]
        exact Steps.halts_unique hsteps hhalted h hh
      rw [hc'_eq]
    · push_neg at hEmpty
      -- Suffix = gPhase start ++ rest_suffix
      have hSuffix_decomp : allGPhases_suffix (m' + 1) n base pGs start =
          (gPhase base n (pGs ⟨start, hEmpty⟩) start).concat
          (allGPhases_suffix (m' + 1) n base pGs (start + 1)) := by
        simp only [allGPhases_suffix]
        have hDrop : (List.finRange (m' + 1)).drop start =
            (List.finRange (m' + 1))[start]'(by simp; exact hEmpty) ::
            (List.finRange (m' + 1)).drop (start + 1) := by
          rw [List.drop_eq_getElem_cons (by simp; exact hEmpty)]
        rw [hDrop, List.foldl_cons]
        rw [foldl_concat_eq_acc_concat]
        simp only [concat_nil_left, List.getElem_finRange]
        congr 2

      rw [hSuffix_decomp] at hsteps hhalted
      have hGPhase_sf := gPhase_isStandardForm (n := n) (base := base) (i := start) (hpGs_sf ⟨start, hEmpty⟩)
      obtain ⟨sFirst, hFirst_steps, ⟨cRest, hRest_steps, hRest_halted⟩⟩ :=
        suffix_of_concat_from_zero hsteps hhalted hGPhase_sf

      -- gPhase start preserves R[base+n+1+k] since start ≠ k (start > k)
      have hFirst_preserves : sFirst.read (base + n + 1 + k) = s.read (base + n + 1 + k) := by
        have hFirst_halted : (⟨(gPhase base n (pGs ⟨start, hEmpty⟩) start).length, sFirst⟩ : Config).isHalted
            (gPhase base n (pGs ⟨start, hEmpty⟩) start) := by
          simp [Config.isHalted]
        exact gPhase_preserves_other_results base n (pGs ⟨start, hEmpty⟩) start k
          (hpGs_sf _) (hpGs_max _) hn_le_base (by omega)
          s sFirst ⟨_, sFirst⟩ hFirst_steps hFirst_halted rfl

      -- IH: rest_suffix preserves R[base+n+1+k]
      have hRest_preserves : cRest.state.read (base + n + 1 + k) = sFirst.read (base + n + 1 + k) := by
        have hk_lt_start' : k < start + 1 := by omega
        -- For suffixes starting at start+1, we need to adjust
        -- The rest suffix is allGPhases_suffix (m'+1) n base pGs (start+1)
        -- This is the same as allGPhases_suffix but with a later start
        -- Apply IH recursively

        -- Since hRest_steps/halted are for suffix starting at start+1,
        -- and we have k < start+1, the recursion applies
        exact allGPhases_suffix_preserves_earlier_results hpGs_sf hpGs_max hn_le_base
          (start + 1) k hk_lt_start' sFirst cRest hRest_steps hRest_halted

      -- c'.state = cRest.state by determinism
      have hc'_eq_cRest : c'.state = cRest.state := by
        have hChain := Steps.chain_concat hFirst_steps
          (by simp [Config.isHalted])
          rfl hRest_steps hRest_halted
        have huniq := Steps.halts_unique hsteps hhalted hChain.1 hChain.2
        rw [huniq]

      rw [hc'_eq_cRest, hRest_preserves, hFirst_preserves]
termination_by m - start
decreasing_by simp_wf; omega

set_option maxHeartbeats 400000 in
/-- After saveInputs ++ allGPhases halts, R[base+n+1+i] contains the result of g_i.
This is the key lemma for tracking how gPhase saves each result. -/
theorem allGPhases_saves_result
    {m n : ℕ} [NeZero m]
    {pF : Program} {pGs : Fin m → Program}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hGs_dom : ∀ i, (gs i inputs).Dom)
    (i : Fin m)
    (sSaveGPhases : State)
    (hSaveGPhases_halted : ∃ c : Config,
      Steps ((copyRegisterRange 0 (compositionBase m n pF pGs + 1) n).concat
             (allGPhases m n (compositionBase m n pF pGs) pGs))
        ⟨0, State.fromInputs (List.ofFn inputs)⟩ c ∧
      c.isHalted ((copyRegisterRange 0 (compositionBase m n pF pGs + 1) n).concat
                  (allGPhases m n (compositionBase m n pF pGs) pGs)) ∧
      c.state = sSaveGPhases) :
    sSaveGPhases.read (compositionBase m n pF pGs + n + 1 + i.val) =
      (gs i inputs).get (hGs_dom i) := by
  -- Setup
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  obtain ⟨c, hsteps, hhalted, hstate_eq⟩ := hSaveGPhases_halted

  -- We use allGPhases_split to decompose: allGPhases m = prefix(i+1) ++ suffix(i+1)
  -- where prefix(i+1) contains phases 0..i (so gPhase i is the last phase in prefix)
  have hSplit : allGPhases m n base pGs =
      (allGPhases_prefix m n base pGs (i.val + 1)).concat
      (allGPhases_suffix m n base pGs (i.val + 1)) :=
    allGPhases_split m n base pGs (i.val + 1) (Nat.lt_iff_add_one_le.mp i.isLt)

  -- Standard form facts
  have hSave_sf := saveInputs_isStandardForm base n
  have hPrefix_sf := allGPhases_prefix_isStandardForm (n := n) (base := base) hGs_sf (i.val + 1)
  have hSuffix_sf := allGPhases_suffix_isStandardForm (n := n) (base := base) hGs_sf (i.val + 1)

  -- Rewrite the program
  have hProg_eq : saveInputs.concat (allGPhases m n base pGs) =
      (saveInputs.concat (allGPhases_prefix m n base pGs (i.val + 1))).concat
      (allGPhases_suffix m n base pGs (i.val + 1)) := by
    rw [hSplit, concat_assoc]

  -- Get execution up to prefix (including gPhase i)
  have hSavePrefix_sf := hSave_sf.concat hPrefix_sf
  have hSuffixStart : Steps (saveInputs.concat (allGPhases m n base pGs))
      ⟨0, State.fromInputs (List.ofFn inputs)⟩ c := hsteps
  rw [hProg_eq] at hSuffixStart hhalted

  obtain ⟨sSavePrefix, hSavePrefix_steps, ⟨cSuffix, hSuffix_steps, hSuffix_halted⟩⟩ :=
    suffix_of_concat_from_zero hSuffixStart hhalted hSavePrefix_sf

  -- Now show R[base+n+1+i] has correct value after prefix and is preserved by suffix

  -- Part 1: Extract execution of gPhase i from the end of prefix
  -- prefix(i+1) = prefix(i) ++ gPhase i
  have hPrefixDecomp : allGPhases_prefix m n base pGs (i.val + 1) =
      (allGPhases_prefix m n base pGs i.val).concat (gPhase base n (pGs i) i.val) := by
    simp only [allGPhases_prefix]
    have hi_lt : i.val < (List.finRange m).length := by simp
    have hTake : (List.finRange m).take (i.val + 1) =
        (List.finRange m).take i.val ++ [(List.finRange m)[i.val]] :=
      List.take_succ_eq_append_getElem hi_lt
    rw [hTake, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [foldl_concat_eq_acc_concat]
    simp only [List.getElem_finRange]
    congr 1

  have hSavePrefixI_sf := hSave_sf.concat (allGPhases_prefix_isStandardForm (n := n) (base := base) hGs_sf i.val)
  have hGPhase_i_sf := gPhase_isStandardForm (base := base) (n := n) (i := i.val) (hGs_sf i)

  -- Rewrite saveInputs ++ prefix(i+1) = (saveInputs ++ prefix(i)) ++ gPhase i
  have hSavePrefix_eq : saveInputs.concat (allGPhases_prefix m n base pGs (i.val + 1)) =
      (saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat
      (gPhase base n (pGs i) i.val) := by
    rw [hPrefixDecomp, concat_assoc]

  rw [hSavePrefix_eq] at hSavePrefix_steps

  -- Extract gPhase i execution from the end of saveInputs ++ prefix(i+1)
  have hSavePrefixI_halted : (⟨((saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat (gPhase base n (pGs i) i.val)).length, sSavePrefix⟩ : Config).isHalted
      ((saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat (gPhase base n (pGs i) i.val)) := by
    simp [Config.isHalted]

  obtain ⟨sSavePrefixI, hSavePrefixI_steps, ⟨cGPhase_i, hGPhase_i_steps, hGPhase_i_halted⟩⟩ :=
    suffix_of_concat_from_zero hSavePrefix_steps hSavePrefixI_halted hSavePrefixI_sf

  -- Part 2: Show that sSavePrefix (after gPhase i) has R[base+n+1+i] = result of g_i
  -- First, show saved inputs are preserved up to the start of gPhase i
  have hpGs_max : ∀ j, (pGs j).maxRegister ≤ base := fun j => compositionBase_ge_pGs_max m n pF pGs j
  have hn_le_base : n ≤ base + 1 := compositionBase_ge_n m n pF pGs

  have hSaved_i : ∀ k : ℕ, (hk : k < n) → sSavePrefixI.read (base + 1 + k) = inputs ⟨k, hk⟩ := by
    intro k hk
    -- Show that saved inputs are preserved through saveInputs ++ prefix(i)
    -- First, saveInputs saves the inputs
    -- Then, prefix(i) preserves them
    have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
    have hNoOverlap : 0 + n ≤ base + 1 := by omega
    obtain ⟨sSave, hsSave_eq, hSave_copies, hSave_preserves⟩ :=
      copyRegisterRange_state 0 (base + 1) n (State.fromInputs (List.ofFn inputs)) (Or.inl hNoOverlap)

    -- After saveInputs: R[base+1+k] = inputs[k]
    have hAfterSave : sSave.read (base + 1 + k) = inputs ⟨k, hk⟩ := by
      rw [hSave_copies k hk]
      simp only [State.fromInputs, State.read, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hk, ↓reduceDIte, Option.getD_some]

    -- Get the state after saveInputs
    have hSave_halts := straightLine_halts hSave_sl (List.ofFn inputs)
    obtain ⟨cSave, hSave_steps', hSave_halted', hSave_pc'⟩ :=
      straightLine_halts_from_state hSave_sl (State.fromInputs (List.ofFn inputs))
    have hSave_state_eq : cSave.state = straightLineFinalState hSave_sl (State.fromInputs (List.ofFn inputs)) :=
      straightLineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps' hSave_halted'
    have hSave_state_sSave : cSave.state = sSave := by rw [hSave_state_eq, hsSave_eq]

    -- Then prefix(i) preserves saved inputs
    by_cases hi_zero : i.val = 0
    · -- prefix(0) is empty, so sSavePrefixI = cSave.state
      have hPrefix_empty : allGPhases_prefix m n base pGs i.val = [] := by
        simp only [hi_zero, allGPhases_prefix, List.take_zero, List.foldl_nil]
      rw [hPrefix_empty, concat_nil_right] at hSavePrefixI_steps
      have hSavePrefixI_halted' : (⟨saveInputs.length, sSavePrefixI⟩ : Config).isHalted saveInputs := by
        simp [Config.isHalted]
      have huniq := Steps.halts_unique hSavePrefixI_steps hSavePrefixI_halted' hSave_steps' hSave_halted'
      have hstate_eq' : sSavePrefixI = cSave.state := congrArg Config.state huniq
      rw [hstate_eq', hSave_state_sSave, hAfterSave]
    · -- prefix(i) is non-empty, use allGPhases_prefix_preserves_saved_inputs
      -- Decompose saveInputs.concat prefix into two parts
      have hPrefix_i_sf : (allGPhases_prefix m n base pGs i.val).IsStandardForm :=
        allGPhases_prefix_isStandardForm hGs_sf i.val
      obtain ⟨sSave', hSave_steps'', ⟨cPrefix, hPrefix_steps, hPrefix_halted⟩⟩ :=
        suffix_of_concat_from_zero hSavePrefixI_steps (by simp [Config.isHalted]) hSave_sf
      -- sSave' = sSave by uniqueness (through cSave)
      have hsSave'_eq : sSave' = sSave := by
        have hSave_halted'' : (⟨saveInputs.length, sSave'⟩ : Config).isHalted saveInputs := by
          simp [Config.isHalted]
        have huniq := Steps.halts_unique hSave_steps'' hSave_halted'' hSave_steps' hSave_halted'
        have : sSave' = cSave.state := congrArg Config.state huniq
        rw [this, hSave_state_sSave]
      -- Use the equality to rewrite prefix_steps
      conv at hPrefix_steps => rw [hsSave'_eq]
      -- cPrefix.state = sSavePrefixI by uniqueness
      have hcPrefix_state : cPrefix.state = sSavePrefixI := by
        have hPrefix_steps' : Steps (allGPhases_prefix m n base pGs i.val) ⟨0, cSave.state⟩ cPrefix := by
          rw [hSave_state_sSave]; exact hPrefix_steps
        have hChain := Steps.chain_concat hSave_steps' hSave_halted' hSave_pc' hPrefix_steps' hPrefix_halted
        have hSavePrefixI_halted'' : (⟨(saveInputs.concat (allGPhases_prefix m n base pGs i.val)).length, sSavePrefixI⟩ : Config).isHalted
            (saveInputs.concat (allGPhases_prefix m n base pGs i.val)) := by simp [Config.isHalted]
        have huniq := Steps.halts_unique hSavePrefixI_steps hSavePrefixI_halted'' hChain.1 hChain.2
        exact (congrArg Config.state huniq).symm
      -- Apply prefix preservation lemma
      have hPrefix_preserves := allGPhases_prefix_preserves_saved_inputs m n base pGs hGs_sf hpGs_max hn_le_base
        i.val (Nat.le_of_lt i.isLt)
        sSave cPrefix.state cPrefix hPrefix_steps hPrefix_halted rfl
      rw [← hcPrefix_state, hPrefix_preserves (base + 1 + k) (by omega) (by omega), hAfterSave]

  -- Now apply gPhase_writes_result
  have hGPhase_halts_i := (hGs_spec i inputs).1.mpr (hGs_dom i)

  have hGPhase_i_result := gPhase_writes_result
    (hGs_sf i) (hpGs_max i) hn_le_base hGPhase_halts_i
    sSavePrefixI hSaved_i cGPhase_i hGPhase_i_steps hGPhase_i_halted

  -- Part 3: Show that suffix preserves R[base+n+1+i]
  -- The suffix contains phases i+1..m-1, each of which preserves R[base+n+1+i]
  have hSuffix_preserves : cSuffix.state.read (base + n + 1 + i.val) = sSavePrefix.read (base + n + 1 + i.val) := by
    -- Use the helper lemma: suffix starting at (i+1) preserves register i
    have hi_lt : i.val < i.val + 1 := by omega
    exact allGPhases_suffix_preserves_earlier_results hGs_sf hpGs_max hn_le_base
      (i.val + 1) i.val hi_lt sSavePrefix cSuffix hSuffix_steps hSuffix_halted

  -- Connect sSavePrefix to cGPhase_i final state
  -- Chain: sSaveGPhases = c.state = cSuffix.state → sSavePrefix → cGPhase_i.state → Result → gs.get

  -- Step 1: sSavePrefix = cGPhase_i.state (by chaining saveInputs++prefix(i) with gPhase(i))
  have hsSavePrefix_eq_cGPhase : sSavePrefix = cGPhase_i.state := by
    have hChain := Steps.chain_concat hSavePrefixI_steps (by simp [Config.isHalted]) rfl hGPhase_i_steps hGPhase_i_halted
    have hSavePrefix_halted' : (⟨((saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat (gPhase base n (pGs i) i.val)).length, sSavePrefix⟩ : Config).isHalted
        ((saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat (gPhase base n (pGs i) i.val)) := by simp [Config.isHalted]
    have huniq := Steps.halts_unique hSavePrefix_steps hSavePrefix_halted' hChain.1 hChain.2
    exact congrArg Config.state huniq

  -- Step 2: c.state = cSuffix.state (by chaining saveInputs++prefix(i+1) with suffix)
  have hc_eq_cSuffix : c.state = cSuffix.state := by
    -- Use hSavePrefix_eq to rewrite the program
    rw [hSavePrefix_eq] at hSuffixStart hhalted
    have hChain := Steps.chain_concat hSavePrefix_steps hSavePrefixI_halted rfl hSuffix_steps hSuffix_halted
    have huniq := Steps.halts_unique hSuffixStart hhalted hChain.1 hChain.2
    simp only [huniq]

  -- Step 3: Result = gs.get (from hGs_spec)
  have hResult_eq : Result (pGs i) (List.ofFn inputs) hGPhase_halts_i = (gs i inputs).get (hGs_dom i) :=
    (hGs_spec i inputs).2 hGPhase_halts_i (hGs_dom i)

  -- Final chain
  rw [← hstate_eq, hc_eq_cSuffix, hSuffix_preserves, hsSavePrefix_eq_cGPhase, hGPhase_i_result, hResult_eq]

end Urm
