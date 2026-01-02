/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.StandardForm

/-! # Preservation Lemmas

Lemmas about register preservation during composition execution.

## Main results

- `gPhase_preserves_saved_inputs`: gPhase preserves registers in R[base+1..base+n]
- `allGPhases_prefix_preserves_saved_inputs`: allGPhases_prefix preserves saved inputs
- `gPhase_preserves_other_results`: gPhase preserves result registers R[base+n+1+k] for k ≠ j
-/

namespace Urm

open Program

/-! ## Execution Helpers -/

/-- Register preservation for copyRegisterRange: registers outside [dstStart, dstStart+count) unchanged. -/
theorem copyRegisterRange_preserves (srcStart dstStart count : ℕ) (s : State)
    (r : ℕ) (hr : r < dstStart ∨ r ≥ dstStart + count) :
    (straightLineFinalState (copyRegisterRange_isStraightLine srcStart dstStart count) s).read r = s.read r := by
  have hsl := copyRegisterRange_isStraightLine srcStart dstStart count
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  exact Steps.straightLine_preserves hsl hsteps (copyRegisterRange_preserves_outside srcStart dstStart count r hr)

/-- Register preservation for transferResultsToInputs: registers ≥ arityF unchanged. -/
theorem transferResultsToInputs_preserves (resultStart arityF : ℕ) (s : State)
    (r : ℕ) (hr : r ≥ arityF) :
    (straightLineFinalState (transferResultsToInputs_isStraightLine resultStart arityF) s).read r = s.read r := by
  have hsl := transferResultsToInputs_isStraightLine resultStart arityF
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  exact Steps.straightLine_preserves hsl hsteps (transferResultsToInputs_preserves_outside resultStart arityF r hr)

/-- State after saving inputs to safe storage (with non-overlapping ranges). -/
theorem copyRegisterRange_state (srcStart dstStart count : ℕ) (s : State)
    (hNoOverlap : srcStart + count ≤ dstStart ∨ dstStart + count ≤ srcStart) :
    ∃ s', straightLineFinalState (copyRegisterRange_isStraightLine srcStart dstStart count) s = s' ∧
      (∀ i : ℕ, i < count → s'.read (dstStart + i) = s.read (srcStart + i)) ∧
      (∀ r : ℕ, r < dstStart ∨ r ≥ dstStart + count → s'.read r = s.read r) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · -- Show copied values using straightLine_transfer_result
    intro i hi
    have hsl := copyRegisterRange_isStraightLine srcStart dstStart count
    let p := Program.copyRegisterRange srcStart dstStart count
    have hk : i < p.length := by simp only [p, copyRegisterRange_length]; exact hi
    have hwrite : p[i] = Instr.T (srcStart + i) (dstStart + i) := by
      simp only [p, Program.copyRegisterRange, List.getElem_map, List.getElem_range]
    have hnowrite : ∀ j (hj : j < p.length), i < j → (p[j]'hj).writesTo ≠ some (dstStart + i) := by
      intro j hj hij
      simp only [p, Program.copyRegisterRange, List.getElem_map, List.getElem_range, Instr.writesTo]
      simp only [ne_eq, Option.some.injEq]
      omega
    obtain ⟨s_before, ⟨c_i, hsteps_i, hpc_i, hs_before_eq⟩, hread_eq⟩ :=
      straightLine_transfer_result hsl s i (srcStart + i) (dstStart + i) hk hwrite hnowrite
    rw [hread_eq]
    -- Now show s_before.read (srcStart + i) = s.read (srcStart + i)
    -- Since srcStart + i is not in the dst range (by hNoOverlap), it's preserved
    have hsrc_preserved : s_before.read (srcStart + i) = s.read (srcStart + i) := by
      -- srcStart + i is outside [dstStart, dstStart + count) due to non-overlap
      have h_outside : srcStart + i < dstStart ∨ srcStart + i ≥ dstStart + count := by
        cases hNoOverlap with
        | inl h => left; omega
        | inr h => right; omega
      -- The execution from ⟨0, s⟩ to c_i preserves srcStart + i
      rw [← hs_before_eq]
      exact Steps.straightLine_preserves hsl hsteps_i
        (copyRegisterRange_preserves_outside srcStart dstStart count (srcStart + i) h_outside)
    exact hsrc_preserved
  · exact fun r hr => copyRegisterRange_preserves srcStart dstStart count s r hr

/-- State after transferring results to input registers (with non-overlapping ranges). -/
theorem transferResultsToInputs_state (resultStart arityF : ℕ) (s : State)
    (hNoOverlap : arityF ≤ resultStart) :
    ∃ s', straightLineFinalState (transferResultsToInputs_isStraightLine resultStart arityF) s = s' ∧
      (∀ i : ℕ, i < arityF → s'.read i = s.read (resultStart + i)) ∧
      (∀ r : ℕ, r ≥ arityF → s'.read r = s.read r) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · -- Show transferred values using straightLine_transfer_result
    intro i hi
    have hsl := transferResultsToInputs_isStraightLine resultStart arityF
    let p := Program.transferResultsToInputs resultStart arityF
    have hk : i < p.length := by simp only [p, transferResultsToInputs_length]; exact hi
    have hwrite : p[i] = Instr.T (resultStart + i) i := by
      simp only [p, Program.transferResultsToInputs, List.getElem_map, List.getElem_range]
    have hnowrite : ∀ j (hj : j < p.length), i < j → (p[j]'hj).writesTo ≠ some i := by
      intro j hj hij
      simp only [p, Program.transferResultsToInputs, List.getElem_map, List.getElem_range, Instr.writesTo]
      simp only [ne_eq, Option.some.injEq]
      omega
    obtain ⟨s_before, ⟨c_i, hsteps_i, hpc_i, hs_before_eq⟩, hread_eq⟩ :=
      straightLine_transfer_result hsl s i (resultStart + i) i hk hwrite hnowrite
    rw [hread_eq]
    -- Now show s_before.read (resultStart + i) = s.read (resultStart + i)
    -- Source (resultStart + i) is preserved since it's ≥ arityF (outside dst range)
    have hsrc_preserved : s_before.read (resultStart + i) = s.read (resultStart + i) := by
      have h_outside : resultStart + i ≥ arityF := by omega
      rw [← hs_before_eq]
      exact Steps.straightLine_preserves hsl hsteps_i
        (transferResultsToInputs_preserves_outside resultStart arityF (resultStart + i) h_outside)
    exact hsrc_preserved
  · exact fun r hr => transferResultsToInputs_preserves resultStart arityF s r hr

/-! ## Preservation Lemmas for Saved Inputs -/

/-- gPhase preserves registers in R[base+1..base+n].
These are the saved input registers that must be preserved through all G phases. -/
theorem gPhase_preserves_saved_inputs (base n : ℕ) (pG : Program) (j : ℕ)
    (hpG_sf : pG.IsStandardForm)
    (hpG_max : pG.maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (s s' : State) (c' : Config)
    (hsteps : Steps (gPhase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (gPhase base n pG j))
    (hstate_eq : c'.state = s') :
    ∀ r, base + 1 ≤ r → r ≤ base + n → s'.read r = s.read r := by
  intro r hr_lo hr_hi
  -- gPhase = clear ++ (copyRange ++ (pG ++ [T]))
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine base)
  have hCopyRange_sf := straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n)
  have hT_sf : Program.IsStandardForm [Instr.T 0 (base + n + 1 + j)] :=
    straightLine_isStandardForm rfl

  -- Extract clear execution and suffix
  obtain ⟨sClear, hClear_steps, ⟨cRest, hRest_steps, hRest_halted⟩⟩ :=
    suffix_of_concat_from_zero hsteps hhalted hClear_sf

  -- Extract copyRange execution and suffix
  obtain ⟨sCopy, hCopy_steps, ⟨cPGT, hPGT_steps, hPGT_halted⟩⟩ :=
    suffix_of_concat_from_zero hRest_steps hRest_halted hCopyRange_sf

  -- Extract pG execution and T
  obtain ⟨sPG, hPG_steps, ⟨cT, hT_steps, hT_halted⟩⟩ :=
    suffix_of_concat_from_zero hPGT_steps hPGT_halted hpG_sf

  -- 1. Clear preserves r > base
  have hClear_preserves : sClear.read r = s.read r := by
    rw [show sClear = _ from straightLineFinalState_eq_of_halted (clearRegisters_isStraightLine base) s
      ⟨_, sClear⟩ hClear_steps (by simp [Config.isHalted])]
    exact clearRegisters_preserves_above' base s r (by omega)

  -- 2. CopyRange preserves r ≥ n (dst is [0, n), so r ≥ n is outside)
  have hCopy_preserves : sCopy.read r = sClear.read r := by
    rw [show sCopy = _ from straightLineFinalState_eq_of_halted (copyRegisterRange_isStraightLine (base + 1) 0 n)
      sClear ⟨_, sCopy⟩ hCopy_steps (by simp [Config.isHalted])]
    exact copyRegisterRange_preserves (base + 1) 0 n sClear r (Or.inr (by omega))

  -- 3. pG preserves r > maxRegister(pG)
  have hPG_preserves : sPG.read r = sCopy.read r := by
    have hr_gt_max : pG.maxRegister < r := Nat.lt_of_le_of_lt hpG_max (by omega : base < r)
    exact Steps.preserves_high_register hPG_steps r hr_gt_max

  -- 4. T 0 (base+n+1+j) preserves r ≠ base+n+1+j
  have hT_preserves : s'.read r = sPG.read r := by
    let tr := executeSingleTransfer 0 (base + n + 1 + j) sPG
    have hT_state : cT.state.read r = sPG.read r := by
      simp only [Steps.halts_unique hT_steps hT_halted tr.steps tr.halted]
      exact tr.preserved r (by omega)
    -- Chain through determinism to show c'.state = cT.state
    have hPGT := Steps.chain_concat hPG_steps (by simp [Config.isHalted]) rfl hT_steps hT_halted
    have hRest := Steps.chain_concat hCopy_steps (by simp [Config.isHalted]) rfl hPGT_steps hPGT_halted
    have hGPhase := Steps.chain_concat hClear_steps (by simp [Config.isHalted]) rfl hRest_steps hRest_halted
    simp only [← hstate_eq, Steps.halts_unique hsteps hhalted hGPhase.1 hGPhase.2,
      Steps.halts_unique hRest_steps hRest_halted hRest.1 hRest.2,
      Steps.halts_unique hPGT_steps hPGT_halted hPGT.1 hPGT.2, hT_state]

  -- Chain the preservation
  rw [hT_preserves, hPG_preserves, hCopy_preserves, hClear_preserves]

/-- allGPhases_prefix preserves registers in R[base+1..base+n]. -/
theorem allGPhases_prefix_preserves_saved_inputs (m n base : ℕ) (pGs : Fin m → Program)
    (hpGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hpGs_max : ∀ i, (pGs i).maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (k : ℕ) (hk : k ≤ m)
    (s s' : State) (c' : Config)
    (hsteps : Steps (allGPhases_prefix m n base pGs k) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (allGPhases_prefix m n base pGs k))
    (hstate_eq : c'.state = s') :
    ∀ r, base + 1 ≤ r → r ≤ base + n → s'.read r = s.read r := by
  intro r hr_lo hr_hi
  -- Use strong induction on k
  induction k generalizing s s' c' with
  | zero =>
    -- prefix(0) = [], so s' = s
    simp only [allGPhases_prefix, List.take_zero, List.foldl_nil] at hsteps hhalted
    -- For empty program, hsteps is Relation.ReflTransGen.refl so c' = ⟨0, s⟩
    have hstate : c'.state = s := by
      -- No Step from empty program, so c' = ⟨0, s⟩
      have hc'_eq : c' = ⟨0, s⟩ := Steps.halts_unique hsteps hhalted (.refl _)
        (by simp [Config.isHalted])
      simp only [hc'_eq]
    -- Use transitivity: s' = c'.state = s
    calc s'.read r = (c'.state).read r := by rw [← hstate_eq]
      _ = s.read r := by rw [hstate]
  | succ k' ih =>
    -- prefix(k'+1) = prefix(k') ++ gPhase(k')
    have hk'_lt : k' < m := Nat.lt_of_succ_le hk
    let k'_fin : Fin m := ⟨k', hk'_lt⟩
    -- Establish that prefix(k'+1) = prefix(k').concat gPhase(k')
    have hPrefix_succ_eq : allGPhases_prefix m n base pGs (k' + 1) =
        (allGPhases_prefix m n base pGs k').concat (gPhase base n (pGs k'_fin) k') := by
      simp only [allGPhases_prefix]
      have htake_eq : (List.finRange m).take (k' + 1) = (List.finRange m).take k' ++ [k'_fin] := by
        rw [List.take_add_one]
        have hlen : k' < (List.finRange m).length := by simp only [List.length_finRange]; exact hk'_lt
        rw [getElem?_pos (List.finRange m) k' hlen, Option.toList_some]
        simp only [List.finRange, List.getElem_ofFn, k'_fin]
      rw [htake_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hPrefix_succ_eq] at hsteps hhalted
    -- Split execution: prefix(k') halts, then gPhase(k') halts
    have hPrefix_k'_sf : (allGPhases_prefix m n base pGs k').IsStandardForm :=
      allGPhases_prefix_isStandardForm hpGs_sf k'
    obtain ⟨sMid, hMid_steps, ⟨cGPhase, hGPhase_steps, hGPhase_halted⟩⟩ :=
      suffix_of_concat_from_zero hsteps hhalted hPrefix_k'_sf
    -- Apply IH to prefix(k')
    have hMid_halted : (⟨(allGPhases_prefix m n base pGs k').length, sMid⟩ : Config).isHalted
        (allGPhases_prefix m n base pGs k') := by simp [Config.isHalted]
    have hPrefix_preserves := ih (Nat.le_of_succ_le hk) s sMid ⟨(allGPhases_prefix m n base pGs k').length, sMid⟩
      hMid_steps hMid_halted rfl
    -- Apply gPhase preservation
    -- cGPhase.state = c'.state by determinism (both are final states of the same execution)
    have hGPhase_state_eq : cGPhase.state = s' := by
      rw [← hstate_eq]
      have hMid_halted' : (⟨(allGPhases_prefix m n base pGs k').length, sMid⟩ : Config).isHalted
          (allGPhases_prefix m n base pGs k') := by simp [Config.isHalted]
      have hMid_lifted := @Steps.concat_left_prefix _ (gPhase base n (pGs k'_fin) k') _ _ hMid_steps hMid_halted'
      have hSuffix_combined := Steps.deterministic_continuation hMid_lifted hsteps hhalted
      have hpc_ge : c'.pc ≥ (allGPhases_prefix m n base pGs k').length := by
        simp only [Config.isHalted, Program.concat_length] at hhalted
        omega
      obtain ⟨cGPhase', hGPhase'_steps, hGPhase'_halted, hGPhase'_state⟩ :=
        Steps.of_concat_right hSuffix_combined hhalted hpc_ge
      exact (Steps.halts_unique hGPhase_steps hGPhase_halted hGPhase'_steps hGPhase'_halted) ▸ hGPhase'_state
    have hGPhase_preserves := gPhase_preserves_saved_inputs base n (pGs k'_fin) k'
      (hpGs_sf k'_fin) (hpGs_max k'_fin) hn_le_base sMid s' cGPhase
      hGPhase_steps hGPhase_halted hGPhase_state_eq
    rw [hGPhase_preserves r hr_lo hr_hi, hPrefix_preserves]

/-- saveInputs writes inputs to R[base+1..base+n]. -/
theorem saveInputs_state (base n : ℕ) (hn_le_base : n ≤ base + 1) (inputs : Fin n → ℕ)
    (r : ℕ) (hr : r < n) :
    (straightLineFinalState (copyRegisterRange_isStraightLine 0 (base + 1) n)
      (State.fromInputs (List.ofFn inputs))).read (base + 1 + r) = inputs ⟨r, hr⟩ := by
  set s := State.fromInputs (List.ofFn inputs) with hs_def
  have hNoOverlap : 0 + n ≤ base + 1 ∨ (base + 1) + n ≤ 0 := Or.inl (by omega : 0 + n ≤ base + 1)
  obtain ⟨s', hs'_eq, hcopies, _⟩ := copyRegisterRange_state 0 (base + 1) n s hNoOverlap
  -- Show the goal's straightLineFinalState = s'
  have hsl := copyRegisterRange_isStraightLine 0 (base + 1) n
  have hfinal_eq : straightLineFinalState hsl s = s' := hs'_eq
  rw [hfinal_eq]
  have hcopy := hcopies r hr
  simp only [Nat.zero_add] at hcopy
  rw [hcopy]
  -- s.read r = inputs[r]
  simp only [hs_def, State.fromInputs, State.read]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr, ↓reduceDIte, Option.getD_some]

/-! ## Saved Results Tracking -/

/-- gPhase preserves result registers R[base+n+1+k] for k ≠ j.
This is because gPhase j only writes to R[base+n+1+j], and other writes are within R[0..base]. -/
theorem gPhase_preserves_other_results (base n : ℕ) (pG : Program) (j k : ℕ)
    (hpG_sf : pG.IsStandardForm)
    (hpG_max : pG.maxRegister ≤ base) (_hn_le_base : n ≤ base + 1)
    (hjk : j ≠ k)
    (s s' : State) (c' : Config)
    (hsteps : Steps (gPhase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (gPhase base n pG j))
    (hstate_eq : c'.state = s') :
    s'.read (base + n + 1 + k) = s.read (base + n + 1 + k) := by
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

  -- The register base+n+1+k where k ≠ j
  let r := base + n + 1 + k

  -- 1. Clear preserves r (r > base)
  have hClear_preserves : sClear.read r = s.read r := by
    rw [show sClear = _ from straightLineFinalState_eq_of_halted (clearRegisters_isStraightLine base) s
      ⟨_, sClear⟩ hClear_steps (by simp [Config.isHalted])]
    exact clearRegisters_preserves_above' base s r (by omega)

  -- 2. CopyRange preserves r (r ≥ n since r = base+n+1+k > n)
  have hCopy_preserves : sCopy.read r = sClear.read r := by
    rw [show sCopy = _ from straightLineFinalState_eq_of_halted (copyRegisterRange_isStraightLine (base + 1) 0 n)
      sClear ⟨_, sCopy⟩ hCopy_steps (by simp [Config.isHalted])]
    exact copyRegisterRange_preserves (base + 1) 0 n sClear r (Or.inr (by omega))

  -- 3. pG preserves r (r > maxRegister(pG))
  have hPG_preserves : sPG.read r = sCopy.read r :=
    Steps.preserves_high_register hPG_steps r (Nat.lt_of_le_of_lt hpG_max (by omega))

  -- 4. T 0 (base+n+1+j) preserves r = base+n+1+k (since k ≠ j)
  have hT_preserves : cT.state.read r = sPG.read r := by
    let tr := executeSingleTransfer 0 (base + n + 1 + j) sPG
    simp only [Steps.halts_unique hT_steps hT_halted tr.steps tr.halted]
    exact tr.preserved r (by omega)

  -- Connect c'.state to cT.state through determinism chain
  have hc'_state_eq : c'.state.read r = cT.state.read r := by
    have hPGT := Steps.chain_concat hPG_steps (by simp [Config.isHalted]) rfl hT_steps hT_halted
    have hCopyPGT := Steps.chain_concat hCopy_steps (by simp [Config.isHalted]) rfl hPGT_steps hPGT_halted
    have hClearRest := Steps.chain_concat hClear_steps (by simp [Config.isHalted]) rfl hRest_steps hRest_halted
    simp only [Steps.halts_unique hsteps hhalted hClearRest.1 hClearRest.2,
      Steps.halts_unique hRest_steps hRest_halted hCopyPGT.1 hCopyPGT.2,
      Steps.halts_unique hPGT_steps hPGT_halted hPGT.1 hPGT.2]

  -- Chain all preservations
  rw [← hstate_eq, hc'_state_eq, hT_preserves, hPG_preserves, hCopy_preserves, hClear_preserves]

end Urm
