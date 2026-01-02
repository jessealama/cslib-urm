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
  refine ⟨_, rfl, ?_, fun r hr => copyRegisterRange_preserves srcStart dstStart count s r hr⟩
  intro i hi
  have hsl := copyRegisterRange_isStraightLine srcStart dstStart count
  let p := Program.copyRegisterRange srcStart dstStart count
  have hnowrite : ∀ j (hj : j < p.length), i < j → (p[j]'hj).writesTo ≠ some (dstStart + i) := by
    intro j hj hij
    simp only [p, Program.copyRegisterRange, List.getElem_map, List.getElem_range, Instr.writesTo,
      ne_eq, Option.some.injEq]; omega
  obtain ⟨s_before, ⟨_, hsteps_i, _, hs_before_eq⟩, hread_eq⟩ := straightLine_transfer_result hsl s i
    (srcStart + i) (dstStart + i) (by simp [hi])
    (by simp [Program.copyRegisterRange]) hnowrite
  rw [hread_eq, ← hs_before_eq]
  exact Steps.straightLine_preserves hsl hsteps_i (copyRegisterRange_preserves_outside srcStart
    dstStart count (srcStart + i) (by cases hNoOverlap <;> omega))

/-- State after transferring results to input registers (with non-overlapping ranges). -/
theorem transferResultsToInputs_state (resultStart arityF : ℕ) (s : State)
    (hNoOverlap : arityF ≤ resultStart) :
    ∃ s', straightLineFinalState (transferResultsToInputs_isStraightLine resultStart arityF) s = s' ∧
      (∀ i : ℕ, i < arityF → s'.read i = s.read (resultStart + i)) ∧
      (∀ r : ℕ, r ≥ arityF → s'.read r = s.read r) := by
  refine ⟨_, rfl, ?_, fun r hr => transferResultsToInputs_preserves resultStart arityF s r hr⟩
  intro i hi
  have hsl := transferResultsToInputs_isStraightLine resultStart arityF
  let p := Program.transferResultsToInputs resultStart arityF
  have hnowrite : ∀ j (hj : j < p.length), i < j → (p[j]'hj).writesTo ≠ some i := by
    intro j hj hij
    simp only [p, Program.transferResultsToInputs, List.getElem_map, List.getElem_range,
      Instr.writesTo, ne_eq, Option.some.injEq]; omega
  obtain ⟨s_before, ⟨_, hsteps_i, _, hs_before_eq⟩, hread_eq⟩ := straightLine_transfer_result hsl s i
    (resultStart + i) i (by simp [hi])
    (by simp [Program.transferResultsToInputs]) hnowrite
  rw [hread_eq, ← hs_before_eq]
  exact Steps.straightLine_preserves hsl hsteps_i
    (transferResultsToInputs_preserves_outside resultStart arityF (resultStart + i) (by omega))

/-! ## Preservation Lemmas for Saved Inputs -/

/-- Helper: gPhase preserves any register r > base that isn't the transfer destination. -/
private theorem gPhase_preserves_register_aux (base n : ℕ) (pG : Program) (j : ℕ)
    (hpG_sf : pG.IsStandardForm) (hpG_max : pG.maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (s s' : State) (c' : Config) (hsteps : Steps (gPhase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (gPhase base n pG j)) (hstate_eq : c'.state = s')
    (r : ℕ) (hr_above_base : r > base) (hr_not_dst : r ≠ base + n + 1 + j) :
    s'.read r = s.read r := by
  obtain ⟨sClear, hClear_steps, ⟨_, hRest_steps, hRest_halted⟩⟩ :=
    suffix_of_concat_from_zero hsteps hhalted (clearRegisters_isStandardForm base)
  obtain ⟨sCopy, hCopy_steps, ⟨_, hPGT_steps, hPGT_halted⟩⟩ :=
    suffix_of_concat_from_zero hRest_steps hRest_halted (copyRegisterRange_isStandardForm (base + 1) 0 n)
  obtain ⟨sPG, hPG_steps, ⟨cT, hT_steps, hT_halted⟩⟩ :=
    suffix_of_concat_from_zero hPGT_steps hPGT_halted hpG_sf
  have hClear_preserves : sClear.read r = s.read r := by
    rw [show sClear = _ from straightLineFinalState_eq_of_halted (clearRegisters_isStraightLine base) s
      ⟨_, sClear⟩ hClear_steps (by simp)]
    exact clearRegisters_preserves_above' base s r (by omega)
  have hCopy_preserves : sCopy.read r = sClear.read r := by
    rw [show sCopy = _ from straightLineFinalState_eq_of_halted (copyRegisterRange_isStraightLine (base + 1) 0 n)
      sClear ⟨_, sCopy⟩ hCopy_steps (by simp)]
    exact copyRegisterRange_preserves (base + 1) 0 n sClear r (Or.inr (by omega))
  have hPG_preserves : sPG.read r = sCopy.read r :=
    Steps.preserves_high_register hPG_steps r (Nat.lt_of_le_of_lt hpG_max (by omega))
  let tr := executeSingleTransfer 0 (base + n + 1 + j) sPG
  have hT_preserves : cT.state.read r = sPG.read r := by
    simp only [Steps.halts_unique hT_steps hT_halted tr.steps tr.halted]; exact tr.preserved r (by omega)
  have hPGT := Steps.chain_concat hPG_steps (by simp) rfl hT_steps hT_halted
  have hRest' := Steps.chain_concat hCopy_steps (by simp) rfl hPGT_steps hPGT_halted
  have hGPhase := Steps.chain_concat hClear_steps (by simp) rfl hRest_steps hRest_halted
  simp only [← hstate_eq, Steps.halts_unique hsteps hhalted hGPhase.1 hGPhase.2,
    Steps.halts_unique hRest_steps hRest_halted hRest'.1 hRest'.2,
    Steps.halts_unique hPGT_steps hPGT_halted hPGT.1 hPGT.2,
    hT_preserves, hPG_preserves, hCopy_preserves, hClear_preserves]

/-- gPhase preserves registers in R[base+1..base+n]. -/
theorem gPhase_preserves_saved_inputs (base n : ℕ) (pG : Program) (j : ℕ)
    (hpG_sf : pG.IsStandardForm) (hpG_max : pG.maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (s s' : State) (c' : Config) (hsteps : Steps (gPhase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (gPhase base n pG j)) (hstate_eq : c'.state = s') :
    ∀ r, base + 1 ≤ r → r ≤ base + n → s'.read r = s.read r := fun r hr_lo hr_hi =>
  gPhase_preserves_register_aux base n pG j hpG_sf hpG_max hn_le_base s s' c' hsteps hhalted hstate_eq r (by omega) (by omega)

/-- allGPhases_prefix preserves registers in R[base+1..base+n]. -/
theorem allGPhases_prefix_preserves_saved_inputs (m n base : ℕ) (pGs : Fin m → Program)
    (hpGs_sf : ∀ i, (pGs i).IsStandardForm) (hpGs_max : ∀ i, (pGs i).maxRegister ≤ base)
    (hn_le_base : n ≤ base + 1) (k : ℕ) (hk : k ≤ m) (s s' : State) (c' : Config)
    (hsteps : Steps (allGPhases_prefix m n base pGs k) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (allGPhases_prefix m n base pGs k)) (hstate_eq : c'.state = s') :
    ∀ r, base + 1 ≤ r → r ≤ base + n → s'.read r = s.read r := by
  intro r hr_lo hr_hi
  induction k generalizing s s' c' with
  | zero =>
    simp only [allGPhases_prefix, List.take_zero, List.foldl_nil] at hsteps hhalted
    simp only [← hstate_eq, Steps.halts_unique hsteps hhalted (.refl _) (by simp)]
  | succ k' ih =>
    have hk'_lt : k' < m := Nat.lt_of_succ_le hk
    let k'_fin : Fin m := ⟨k', hk'_lt⟩
    have hPrefix_succ_eq : allGPhases_prefix m n base pGs (k' + 1) =
        (allGPhases_prefix m n base pGs k').concat (gPhase base n (pGs k'_fin) k') := by
      simp only [allGPhases_prefix]
      have htake_eq : (List.finRange m).take (k' + 1) = (List.finRange m).take k' ++ [k'_fin] := by
        rw [List.take_add_one, getElem?_pos (List.finRange m) k' (by simp [hk'_lt]), Option.toList_some]
        simp only [List.finRange, List.getElem_ofFn, k'_fin]
      rw [htake_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hPrefix_succ_eq] at hsteps hhalted
    obtain ⟨sMid, hMid_steps, ⟨cGPhase, hGPhase_steps, hGPhase_halted⟩⟩ :=
      suffix_of_concat_from_zero hsteps hhalted (allGPhases_prefix_isStandardForm hpGs_sf k')
    have hMid_halted : (⟨(allGPhases_prefix m n base pGs k').length, sMid⟩ : Config).isHalted
        (allGPhases_prefix m n base pGs k') := by simp
    have hPrefix_preserves := ih (Nat.le_of_succ_le hk) s sMid _ hMid_steps hMid_halted rfl
    have hMid_lifted := @Steps.concat_left_prefix _ (gPhase base n (pGs k'_fin) k') _ _ hMid_steps hMid_halted
    have hSuffix := Steps.deterministic_continuation hMid_lifted hsteps hhalted
    obtain ⟨cGPhase', hGPhase'_steps, hGPhase'_halted, hGPhase'_state⟩ := Steps.of_concat_right hSuffix hhalted
      (by simp only [Config.isHalted, Program.concat_length] at hhalted; omega)
    have hGPhase_state_eq : cGPhase.state = s' :=
      hstate_eq ▸ (Steps.halts_unique hGPhase_steps hGPhase_halted hGPhase'_steps hGPhase'_halted) ▸ hGPhase'_state
    rw [gPhase_preserves_saved_inputs base n (pGs k'_fin) k' (hpGs_sf k'_fin) (hpGs_max k'_fin)
      hn_le_base sMid s' cGPhase hGPhase_steps hGPhase_halted hGPhase_state_eq r hr_lo hr_hi, hPrefix_preserves]

/-- saveInputs writes inputs to R[base+1..base+n]. -/
theorem saveInputs_state (base n : ℕ) (_hn_le_base : n ≤ base + 1) (inputs : Fin n → ℕ)
    (r : ℕ) (hr : r < n) :
    (straightLineFinalState (copyRegisterRange_isStraightLine 0 (base + 1) n)
      (State.fromInputs (List.ofFn inputs))).read (base + 1 + r) = inputs ⟨r, hr⟩ := by
  set s := State.fromInputs (List.ofFn inputs) with hs_def
  obtain ⟨s', hs'_eq, hcopies, _⟩ := copyRegisterRange_state 0 (base + 1) n s (Or.inl (by omega))
  rw [hs'_eq, hcopies r hr]
  simp only [Nat.zero_add, hs_def, State.fromInputs, State.read, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, hr, ↓reduceDIte, Option.getD_some]

/-! ## Saved Results Tracking -/

/-- gPhase preserves result registers R[base+n+1+k] for k ≠ j. -/
theorem gPhase_preserves_other_results (base n : ℕ) (pG : Program) (j k : ℕ)
    (hpG_sf : pG.IsStandardForm) (hpG_max : pG.maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (hjk : j ≠ k) (s s' : State) (c' : Config) (hsteps : Steps (gPhase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (gPhase base n pG j)) (hstate_eq : c'.state = s') :
    s'.read (base + n + 1 + k) = s.read (base + n + 1 + k) :=
  gPhase_preserves_register_aux base n pG j hpG_sf hpG_max hn_le_base s s' c' hsteps hhalted hstate_eq
    (base + n + 1 + k) (by omega) (by omega)

/-! ## Bundled Execution Helpers -/

/-- Bundled execution of copyRegisterRange with all properties. -/
theorem copyRegisterRange_exec (srcStart dstStart count : ℕ) (s : State)
    (hNoOverlap : srcStart + count ≤ dstStart ∨ dstStart + count ≤ srcStart) :
    ∃ c, Steps (Program.copyRegisterRange srcStart dstStart count) ⟨0, s⟩ c ∧
         c.isHalted (Program.copyRegisterRange srcStart dstStart count) ∧
         c.pc = (Program.copyRegisterRange srcStart dstStart count).length ∧
         (∀ i, i < count → c.state.read (dstStart + i) = s.read (srcStart + i)) ∧
         (∀ r, r < dstStart ∨ r ≥ dstStart + count → c.state.read r = s.read r) := by
  have hsl := copyRegisterRange_isStraightLine srcStart dstStart count
  obtain ⟨c, hsteps, hhalted, hpc⟩ := straightLine_halts_from_state hsl s
  have hstate_eq := straightLineFinalState_eq_of_halted hsl s c hsteps hhalted
  obtain ⟨s', hs'_eq, hcopies, hpreserves⟩ := copyRegisterRange_state srcStart dstStart count s hNoOverlap
  have hc_state_eq_s' : c.state = s' := hstate_eq.trans hs'_eq
  exact ⟨c, hsteps, hhalted, hpc,
    fun i hi => hc_state_eq_s' ▸ hcopies i hi,
    fun r hr => hc_state_eq_s' ▸ hpreserves r hr⟩

/-- Bundled execution of transferResultsToInputs with all properties. -/
theorem transferResultsToInputs_exec (resultStart arityF : ℕ) (s : State)
    (hNoOverlap : arityF ≤ resultStart) :
    ∃ c, Steps (Program.transferResultsToInputs resultStart arityF) ⟨0, s⟩ c ∧
         c.isHalted (Program.transferResultsToInputs resultStart arityF) ∧
         c.pc = (Program.transferResultsToInputs resultStart arityF).length ∧
         (∀ i, i < arityF → c.state.read i = s.read (resultStart + i)) ∧
         (∀ r, r ≥ arityF → c.state.read r = s.read r) := by
  have hsl := transferResultsToInputs_isStraightLine resultStart arityF
  obtain ⟨c, hsteps, hhalted, hpc⟩ := straightLine_halts_from_state hsl s
  have hstate_eq := straightLineFinalState_eq_of_halted hsl s c hsteps hhalted
  obtain ⟨s', hs'_eq, hcopies, hpreserves⟩ := transferResultsToInputs_state resultStart arityF s hNoOverlap
  have hc_state_eq_s' : c.state = s' := hstate_eq.trans hs'_eq
  exact ⟨c, hsteps, hhalted, hpc,
    fun i hi => hc_state_eq_s' ▸ hcopies i hi,
    fun r hr => hc_state_eq_s' ▸ hpreserves r hr⟩

end Urm
