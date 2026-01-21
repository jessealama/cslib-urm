/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.StandardForm



/-! # Preservation Lemmas

Lemmas about register preservation during composition execution.

## Main results

- `g_phase_preserves_saved_inputs`: g_phase preserves registers in R[base+1..base+n]
- `all_g_phases_prefix_preserves_saved_inputs`: all_g_phases_prefix preserves saved inputs
- `g_phase_preserves_other_results`: g_phase preserves result registers R[base+n+1+k] for k ≠ j
-/

namespace Urm

open Program

/-! ## Execution Helpers -/

/-- Register preservation for copy_register_range: registers outside [dstStart, dstStart+count) unchanged. -/
theorem copy_register_range_preserves (srcStart dstStart count : ℕ) (s : State)
    (r : ℕ) (hr : r < dstStart ∨ r ≥ dstStart + count) :
    (straight_lineFinalState (copy_register_range_is_straight_line srcStart dstStart count) s).read r = s.read r := by
  have hsl := copy_register_range_is_straight_line srcStart dstStart count
  have ⟨hsteps, _, _⟩ := straight_lineFinalState_spec hsl s
  exact Steps.straight_line_preserves hsl hsteps (copy_register_range_preserves_outside srcStart dstStart count r hr)

/-- Register preservation for transfer_results_to_inputs: registers ≥ arityF unchanged. -/
theorem transfer_results_to_inputs_preserves (resultStart arityF : ℕ) (s : State)
    (r : ℕ) (hr : r ≥ arityF) :
    (straight_lineFinalState (transfer_results_to_inputs_is_straight_line resultStart arityF) s).read r = s.read r := by
  have hsl := transfer_results_to_inputs_is_straight_line resultStart arityF
  have ⟨hsteps, _, _⟩ := straight_lineFinalState_spec hsl s
  exact Steps.straight_line_preserves hsl hsteps (transfer_results_to_inputs_preserves_outside resultStart arityF r hr)

/-- State after saving inputs to safe storage (with non-overlapping ranges). -/
theorem copy_register_range_state (srcStart dstStart count : ℕ) (s : State)
    (hNoOverlap : srcStart + count ≤ dstStart ∨ dstStart + count ≤ srcStart) :
    ∃ s', straight_lineFinalState (copy_register_range_is_straight_line srcStart dstStart count) s = s' ∧
      (∀ i : ℕ, i < count → s'.read (dstStart + i) = s.read (srcStart + i)) ∧
      (∀ r : ℕ, r < dstStart ∨ r ≥ dstStart + count → s'.read r = s.read r) := by
  refine ⟨_, rfl, ?_, fun r hr => copy_register_range_preserves srcStart dstStart count s r hr⟩
  intro i hi
  have hsl := copy_register_range_is_straight_line srcStart dstStart count
  let p := Program.copy_register_range srcStart dstStart count
  have hnowrite : ∀ j (hj : j < p.length), i < j → (p[j]'hj).writes_to ≠ some (dstStart + i) := by
    intro j hj hij
    simp only [p, Program.copy_register_range, List.getElem_map, List.getElem_range, Instr.writes_to,
      ne_eq, Option.some.injEq]; omega
  obtain ⟨s_before, ⟨_, hsteps_i, _, hs_before_eq⟩, hread_eq⟩ := straight_line_transfer_result hsl s i
    (srcStart + i) (dstStart + i) (by simp [hi])
    (by simp [Program.copy_register_range]) hnowrite
  rw [hread_eq, ← hs_before_eq]
  exact Steps.straight_line_preserves hsl hsteps_i (copy_register_range_preserves_outside srcStart
    dstStart count (srcStart + i) (by cases hNoOverlap <;> omega))

/-- State after transferring results to input registers (with non-overlapping ranges). -/
theorem transfer_results_to_inputs_state (resultStart arityF : ℕ) (s : State)
    (hNoOverlap : arityF ≤ resultStart) :
    ∃ s', straight_lineFinalState (transfer_results_to_inputs_is_straight_line resultStart arityF) s = s' ∧
      (∀ i : ℕ, i < arityF → s'.read i = s.read (resultStart + i)) ∧
      (∀ r : ℕ, r ≥ arityF → s'.read r = s.read r) := by
  refine ⟨_, rfl, ?_, fun r hr => transfer_results_to_inputs_preserves resultStart arityF s r hr⟩
  intro i hi
  have hsl := transfer_results_to_inputs_is_straight_line resultStart arityF
  let p := Program.transfer_results_to_inputs resultStart arityF
  have hnowrite : ∀ j (hj : j < p.length), i < j → (p[j]'hj).writes_to ≠ some i := by
    intro j hj hij
    simp only [p, Program.transfer_results_to_inputs, List.getElem_map, List.getElem_range,
      Instr.writes_to, ne_eq, Option.some.injEq]; omega
  obtain ⟨s_before, ⟨_, hsteps_i, _, hs_before_eq⟩, hread_eq⟩ := straight_line_transfer_result hsl s i
    (resultStart + i) i (by simp [hi])
    (by simp [Program.transfer_results_to_inputs]) hnowrite
  rw [hread_eq, ← hs_before_eq]
  exact Steps.straight_line_preserves hsl hsteps_i
    (transfer_results_to_inputs_preserves_outside resultStart arityF (resultStart + i) (by omega))

/-! ## Preservation Lemmas for Saved Inputs -/

/-- Helper: g_phase preserves any register r > base that isn't the transfer destination. -/
private theorem g_phase_preserves_register_aux (base n : ℕ) (pG : Program) (j : ℕ)
    (hpG_sf : pG.IsStandardForm) (hpG_max : pG.max_register ≤ base) (hn_le_base : n ≤ base + 1)
    (s s' : State) (c' : Config) (hsteps : Steps (g_phase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (g_phase base n pG j)) (hstate_eq : c'.state = s')
    (r : ℕ) (hr_above_base : r > base) (hr_not_dst : r ≠ base + n + 1 + j) :
    s'.read r = s.read r := by
  -- Decompose g_phase = clear.concat(copy.concat(pG.concat(transfer)))
  let dClear := decompose_concat hsteps hhalted (clear_registers_isStandardForm base)
  obtain ⟨_, hRest_steps, hRest_halted⟩ := dClear.halts_right
  let dCopy := decompose_concat hRest_steps hRest_halted (copy_register_range_isStandardForm (base + 1) 0 n)
  obtain ⟨_, hPGT_steps, hPGT_halted⟩ := dCopy.halts_right
  let dPG := decompose_concat hPGT_steps hPGT_halted hpG_sf
  obtain ⟨cT, hT_steps, hT_halted⟩ := dPG.halts_right
  -- Use simp lemma to characterize intermediate states
  have hClear_preserves : dClear.state.read r = s.read r := by
    rw [decompose_concat_state_straight_line (clear_registers_is_straight_line base)]
    exact clear_registers_preserves_above' base s r (by omega)
  have hCopy_preserves : dCopy.state.read r = dClear.state.read r := by
    rw [decompose_concat_state_straight_line (copy_register_range_is_straight_line (base + 1) 0 n)]
    exact copy_register_range_preserves (base + 1) 0 n dClear.state r (Or.inr (by omega))
  have hPG_preserves : dPG.state.read r = dCopy.state.read r :=
    Steps.read_high_register_eq dPG.steps_left r (Nat.lt_of_le_of_lt hpG_max (by omega))
  let tr := executeSingleTransfer 0 (base + n + 1 + j) dPG.state
  have hT_preserves : cT.state.read r = dPG.state.read r := by
    simp only [Steps.eq_of_halts hT_steps hT_halted tr.steps tr.halted]; exact tr.preserved r (by omega)
  have hPGT := Steps.chain_concat_sf hpG_sf dPG.steps_left (by simp) hT_steps hT_halted
  have hRest' := Steps.chain_concat_sf (copy_register_range_isStandardForm (base + 1) 0 n) dCopy.steps_left (by simp) hPGT_steps hPGT_halted
  have hGPhase := Steps.chain_concat_sf (clear_registers_isStandardForm base) dClear.steps_left (by simp) hRest_steps hRest_halted
  simp only [← hstate_eq, Steps.eq_of_halts hsteps hhalted hGPhase.1 hGPhase.2,
    Steps.eq_of_halts hRest_steps hRest_halted hRest'.1 hRest'.2,
    Steps.eq_of_halts hPGT_steps hPGT_halted hPGT.1 hPGT.2,
    hT_preserves, hPG_preserves, hCopy_preserves, hClear_preserves]

/-- g_phase preserves registers in R[base+1..base+n]. -/
theorem g_phase_preserves_saved_inputs (base n : ℕ) (pG : Program) (j : ℕ)
    (hpG_sf : pG.IsStandardForm) (hpG_max : pG.max_register ≤ base) (hn_le_base : n ≤ base + 1)
    (s s' : State) (c' : Config) (hsteps : Steps (g_phase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (g_phase base n pG j)) (hstate_eq : c'.state = s') :
    ∀ r, base + 1 ≤ r → r ≤ base + n → s'.read r = s.read r := fun r hr_lo hr_hi =>
  g_phase_preserves_register_aux base n pG j hpG_sf hpG_max hn_le_base s s' c' hsteps hhalted hstate_eq r (by omega) (by omega)

/-- all_g_phases_prefix preserves registers in R[base+1..base+n]. -/
theorem all_g_phases_prefix_preserves_saved_inputs (m n base : ℕ) (pGs : Fin m → Program)
    (hpGs_sf : ∀ i, (pGs i).IsStandardForm) (hpGs_max : ∀ i, (pGs i).max_register ≤ base)
    (hn_le_base : n ≤ base + 1) (k : ℕ) (hk : k ≤ m) (s s' : State) (c' : Config)
    (hsteps : Steps (all_g_phases_prefix m n base pGs k) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (all_g_phases_prefix m n base pGs k)) (hstate_eq : c'.state = s') :
    ∀ r, base + 1 ≤ r → r ≤ base + n → s'.read r = s.read r := by
  intro r hr_lo hr_hi
  induction k generalizing s s' c' with
  | zero =>
    have hPrefix_zero : all_g_phases_prefix m n base pGs 0 = [] := by
      simp only [all_g_phases_prefix, g_phaseList, List.take_zero, List.map_nil, List.prod_nil]; rfl
    simp only [hPrefix_zero] at hsteps hhalted
    simp only [← hstate_eq, Steps.eq_of_halts hsteps hhalted (.refl _) (by simp)]
  | succ k' ih =>
    have hk'_lt : k' < m := Nat.lt_of_succ_le hk
    let k'_fin : Fin m := ⟨k', hk'_lt⟩
    have hPrefix_succ_eq : all_g_phases_prefix m n base pGs (k' + 1) =
        (all_g_phases_prefix m n base pGs k').concat (g_phase base n (pGs k'_fin) k') :=
      all_g_phases_prefix_succ pGs k' hk'_lt
    rw [hPrefix_succ_eq] at hsteps hhalted
    obtain ⟨sMid, hMid_steps, ⟨cGPhase, hGPhase_steps, hGPhase_halted⟩⟩ :=
      suffix_of_concat_from_zero hsteps hhalted (all_g_phases_prefix_isStandardForm hpGs_sf k')
    have hMid_halted : (⟨(all_g_phases_prefix m n base pGs k').length, sMid⟩ : Config).is_halted
        (all_g_phases_prefix m n base pGs k') := by simp
    have hPrefix_preserves := ih (Nat.le_of_succ_le hk) s sMid _ hMid_steps hMid_halted rfl
    have hMid_lifted := @Steps.concat_left_prefix _ (g_phase base n (pGs k'_fin) k') _ _ hMid_steps
    have hSuffix := Steps.deterministic_continuation hMid_lifted hsteps hhalted
    obtain ⟨cGPhase', hGPhase'_steps, hGPhase'_halted, hGPhase'_state⟩ := Steps.of_concat_right hSuffix hhalted
    have hGPhase_state_eq : cGPhase.state = s' :=
      hstate_eq ▸ (Steps.eq_of_halts hGPhase_steps hGPhase_halted hGPhase'_steps hGPhase'_halted) ▸ hGPhase'_state
    rw [g_phase_preserves_saved_inputs base n (pGs k'_fin) k' (hpGs_sf k'_fin) (hpGs_max k'_fin)
      hn_le_base sMid s' cGPhase hGPhase_steps hGPhase_halted hGPhase_state_eq r hr_lo hr_hi, hPrefix_preserves]

/-- save_inputs writes inputs to R[base+1..base+n]. -/
theorem save_inputs_state (base n : ℕ) (_hn_le_base : n ≤ base + 1) (inputs : Fin n → ℕ)
    (r : ℕ) (hr : r < n) :
    (straight_lineFinalState (copy_register_range_is_straight_line 0 (base + 1) n)
      (State.of_inputs (List.ofFn inputs))).read (base + 1 + r) = inputs ⟨r, hr⟩ := by
  set s := State.of_inputs (List.ofFn inputs) with hs_def
  obtain ⟨s', hs'_eq, hcopies, _⟩ := copy_register_range_state 0 (base + 1) n s (Or.inl (by omega))
  rw [hs'_eq, hcopies r hr]
  simp only [Nat.zero_add, hs_def, State.of_inputs, State.read, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, hr, ↓reduceDIte, Option.getD_some]

/-! ## Saved Results Tracking -/

/-- g_phase preserves result registers R[base+n+1+k] for k ≠ j. -/
theorem g_phase_preserves_other_results (base n : ℕ) (pG : Program) (j k : ℕ)
    (hpG_sf : pG.IsStandardForm) (hpG_max : pG.max_register ≤ base) (hn_le_base : n ≤ base + 1)
    (hjk : j ≠ k) (s s' : State) (c' : Config) (hsteps : Steps (g_phase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.is_halted (g_phase base n pG j)) (hstate_eq : c'.state = s') :
    s'.read (base + n + 1 + k) = s.read (base + n + 1 + k) :=
  g_phase_preserves_register_aux base n pG j hpG_sf hpG_max hn_le_base s s' c' hsteps hhalted hstate_eq
    (base + n + 1 + k) (by omega) (by omega)

/-! ## Bundled Execution Helpers -/

/-- Bundled execution of copy_register_range with all properties. -/
theorem copy_register_range_exec (srcStart dstStart count : ℕ) (s : State)
    (hNoOverlap : srcStart + count ≤ dstStart ∨ dstStart + count ≤ srcStart) :
    ∃ c, Steps (Program.copy_register_range srcStart dstStart count) ⟨0, s⟩ c ∧
         c.is_halted (Program.copy_register_range srcStart dstStart count) ∧
         c.pc = (Program.copy_register_range srcStart dstStart count).length ∧
         (∀ i, i < count → c.state.read (dstStart + i) = s.read (srcStart + i)) ∧
         (∀ r, r < dstStart ∨ r ≥ dstStart + count → c.state.read r = s.read r) := by
  have hsl := copy_register_range_is_straight_line srcStart dstStart count
  obtain ⟨c, hsteps, hhalted, hpc⟩ := straight_line_halts_from_state hsl s
  have hstate_eq := straight_lineFinalState_eq_of_halted hsl s c hsteps hhalted
  obtain ⟨s', hs'_eq, hcopies, hpreserves⟩ := copy_register_range_state srcStart dstStart count s hNoOverlap
  have hc_state_eq_s' : c.state = s' := hstate_eq.trans hs'_eq
  exact ⟨c, hsteps, hhalted, hpc,
    fun i hi => hc_state_eq_s' ▸ hcopies i hi,
    fun r hr => hc_state_eq_s' ▸ hpreserves r hr⟩

end Urm
