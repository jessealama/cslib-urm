/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.Preservation
import Urm.Embeddings
import Urm.Shift
import Urm.Halting.Common
import Urm.Halting.PhaseExecution



/-! # Halting Proofs for Minimization

This file proves halting properties for the minimization witness program.

## Main results

- `minimize_program_halts`: If μ f is defined, the minimization program halts
- Various lemmas about loop iteration behavior
-/

namespace Urm

open Program

section
variable (n : ℕ) (pF : Program)

/-! ## Minimization-Specific Embedding Lemmas -/

/-- loop_prologue is embedded in minimize_program at offset loop_start_pc n. -/
theorem loop_prologue_embed :
    ∀ i, i < (loop_prologue n pF).length →
    (minimize_program n pF)[loop_start_pc n + i]? = (loop_prologue n pF)[i]? := by
  intro i hi
  simp only [minimize_program, loop_start_pc, setup_phase_length, List.getElem?_append,
    List.length_append, setup_phase_len, loop_prologue_length, shift_jumps_length,
    loopEpilogue_length, loop_prologueLength] at *
  split_ifs <;> first | omega | (congr 1; omega)

/-- pF.shift_jumps is embedded in minimize_program at offset pFOffset n pF. -/
theorem pF_shift_jumps_embed :
    ∀ i, i < pF.length →
    (minimize_program n pF)[pFOffset n pF + i]? = (pF.shift_jumps (pFOffset n pF))[i]? := by
  intro i hi
  simp only [minimize_program, pFOffset, setup_phase_length, loop_prologueLength,
    List.getElem?_append, List.length_append, setup_phase_len, loop_prologue_length,
    shift_jumps_length, loopEpilogue_length]
  split_ifs <;> try omega
  simp only [shift_jumps, List.getElem?_map, Nat.add_sub_cancel_left]

/-! ## Loop Iteration Lemmas -/

/-- One complete loop iteration: from loopStart with counter = k,
    execute loop body once, either exit (if f returns 0) or return to loopStart with counter = k+1. -/
structure LoopIterationResult (inputs : Fin n → ℕ) (s : State) (k : ℕ) where
  /-- Final configuration after one iteration -/
  config : Config
  /-- Steps taken during this iteration -/
  steps : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ config
  /-- The value pF wrote to R[0] -/
  pF_result : ℕ
  /-- Either we exited to output, or we're back at loop start with incremented counter -/
  outcome : (config.pc = outputPC n pF ∧ pF_result = 0) ∨
            (config.pc = loop_start_pc n ∧ config.state.read (counter_reg n pF) = k + 1 ∧ pF_result ≠ 0)
  /-- In continue case, zero_reg is preserved from initial state -/
  zero_preserved : pF_result ≠ 0 → config.state.read (zero_reg n pF) = s.read (zero_reg n pF)
  /-- In continue case, savedInputs are preserved from initial state -/
  saved_preserved : pF_result ≠ 0 → ∀ i : Fin n, config.state.read (savedInputsStart n pF + i) = s.read (savedInputsStart n pF + i)
  /-- In exit case (pF_result = 0), counter is preserved equal to k -/
  counter_preserved_exit : pF_result = 0 → config.state.read (counter_reg n pF) = k
  /-- The halting hypothesis for pF on extended inputs -/
  hf_halts : Halts pF (List.ofFn (extend_inputs inputs k))
  /-- pF_result equals the Result from pF execution -/
  pF_result_eq : pF_result = Result pF (List.ofFn (extend_inputs inputs k)) hf_halts

/-- Execute one loop iteration when starting at loopStart. -/
noncomputable def loop_iteration (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (k : ℕ)
    (hs_counter : s.read (counter_reg n pF) = k)
    (hs_zero : s.read (zero_reg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hf_halts : Halts pF (List.ofFn (extend_inputs inputs k))) :
    LoopIterationResult n pF inputs s k := by
  have hsl_prologue := loop_prologue_is_straight_line n pF
  let prologueExec := execPhaseInHost hsl_prologue (loop_start_pc n) (loop_prologue_embed n pF) s
  let c_prologue := prologueExec.phaseResult.config
  have hR_after_prologue : ∀ i : Fin n, c_prologue.state.read i = inputs i := by
    intro i
    rw [loop_prologue_restores_inputs n pF s c_prologue prologueExec.localSteps prologueExec.localHalted i]
    exact hs_saved i
  have hRn_after_prologue : c_prologue.state.read n = k := by
    rw [loop_prologue_sets_counter_input n pF s c_prologue prologueExec.localSteps prologueExec.localHalted,
        hs_counter]
  have hcounter_after_prologue : c_prologue.state.read (counter_reg n pF) = k := by
    rw [loop_prologue_read_high_register_eq n pF s c_prologue prologueExec.localSteps prologueExec.localHalted
      (counter_reg n pF) (counter_reg_gt_base n pF), hs_counter]
  have hzero_after_prologue : c_prologue.state.read (zero_reg n pF) = 0 := by
    rw [loop_prologue_read_high_register_eq n pF s c_prologue prologueExec.localSteps prologueExec.localHalted
      (zero_reg n pF) (zero_reg_gt_base n pF), hs_zero]
  have hsaved_after_prologue : ∀ i : Fin n, c_prologue.state.read (savedInputsStart n pF + i) = inputs i := by
    intro i
    rw [loop_prologue_read_high_register_eq n pF s c_prologue prologueExec.localSteps prologueExec.localHalted
      (savedInputsStart n pF + i) (by let h := savedInputsStart_gt_base n pF; omega)]
    exact hs_saved i
  have hpc_after_prologue : loop_start_pc n + (loop_prologue n pF).length = pFOffset n pF := by
    simp only [loop_start_pc, pFOffset, setup_phase_length, loop_prologueLength, loop_prologue_length]
  have hsteps_prologue_lifted : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩
      ⟨pFOffset n pF, c_prologue.state⟩ :=
    hpc_after_prologue ▸ prologueExec.liftedSteps

  let initState := (Config.init (List.ofFn (extend_inputs inputs k))).state
  have hagree_pF : c_prologue.state.agree_on initState 0 pF.max_register := by
    intro r _ hr_hi
    by_cases hr_lt_n : r < n
    · let hleft : c_prologue.state.read r = inputs ⟨r, hr_lt_n⟩ := hR_after_prologue ⟨r, hr_lt_n⟩
      let hr_lt_n1 : r < n + 1 := Nat.lt_add_right 1 hr_lt_n
      let hright : initState.read r = inputs ⟨r, hr_lt_n⟩ := by
        unfold initState Config.init State.of_inputs State.read
        simp only [List.getD, List.getElem?_ofFn, hr_lt_n1, dite_true]
        simp only [Option.getD_some, extend_inputs, Fin.snoc, hr_lt_n, dite_true]
        rfl
      rw [hleft, hright]
    · by_cases hr_eq_n : r = n
      · subst hr_eq_n
        let hleft : c_prologue.state.read r = k := hRn_after_prologue
        let hr_lt_r1 : r < r + 1 := Nat.lt_succ_self r
        let hright : initState.read r = k := by
          unfold initState Config.init State.of_inputs State.read
          simp only [List.getD, List.getElem?_ofFn, hr_lt_r1, dite_true]
          simp only [Option.getD_some, extend_inputs, Fin.snoc, Nat.lt_irrefl, dite_false]
          simp
        rw [hleft, hright]
      · let hr_gt_n : n < r := Nat.lt_of_le_of_ne (Nat.not_lt.mp hr_lt_n) (Ne.symm hr_eq_n)
        let hr_ge_n1 : ¬ r < n + 1 := by omega
        let hright : initState.read r = 0 := by
          unfold initState Config.init State.of_inputs State.read
          simp only [List.getD, List.getElem?_ofFn, hr_ge_n1, dite_false]
          simp only [Option.getD_none]
        let hr_le_base : r ≤ minimization_base n pF := Nat.le_trans hr_hi (minimization_base_ge_pF n pF)
        let hk : r < (loop_prologue n pF).length := by
          simp only [loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
            List.length]; omega
        let h_in_clear : r < (clear_registers (minimization_base n pF)).length := by
          simp only [clear_registers_length]; exact Nat.lt_succ_of_le hr_le_base
        let h_in_clear_ext : r < (clear_registers (minimization_base n pF) ++
            copy_register_range (savedInputsStart n pF) 0 n).length := by len_append_omega
        let hwrite : (loop_prologue n pF)[r] = Instr.Z r := by
          simp only [loop_prologue]
          rw [List.getElem_append_left h_in_clear_ext, List.getElem_append_left h_in_clear]
          simp only [Program.clear_registers, List.getElem_map, List.getElem_range]
        let hnowrite : ∀ j (hj : j < (loop_prologue n pF).length), r < j →
            ((loop_prologue n pF)[j]).writes_to ≠ some r := by
          intro j hj hjr
          simp only [loop_prologue, List.length_append, clear_registers_length, copy_register_range_length,
            List.length] at hj
          simp only [loop_prologue]
          by_cases hj_clear1 : j < (clear_registers (minimization_base n pF) ++
              copy_register_range (savedInputsStart n pF) 0 n).length
          · rw [List.getElem_append_left hj_clear1]
            by_cases hj_clear : j < minimization_base n pF + 1
            · let h2 : j < (clear_registers (minimization_base n pF)).length := by
                simp only [clear_registers_length]; exact hj_clear
              rw [List.getElem_append_left h2]
              simp only [Program.clear_registers, List.getElem_map, List.getElem_range,
                Instr.writes_to, ne_eq, Option.some.injEq]
              intro heq; exact Nat.ne_of_lt hjr heq.symm
            · let h2 : ¬ j < (clear_registers (minimization_base n pF)).length := by
                simp only [clear_registers_length]; omega
              let h2' : (clear_registers (minimization_base n pF)).length ≤ j := Nat.not_lt.mp h2
              rw [List.getElem_append_right h2']
              simp only [clear_registers_length, Program.copy_register_range,
                List.getElem_map, List.getElem_range, Nat.zero_add, Instr.writes_to, ne_eq, Option.some.injEq]
              simp only [List.length_append, clear_registers_length, copy_register_range_length] at hj_clear1
              omega
          · let hge : (clear_registers (minimization_base n pF) ++
                copy_register_range (savedInputsStart n pF) 0 n).length ≤ j := Nat.not_lt.mp hj_clear1
            rw [List.getElem_append_right hge]
            let hidx : j - (clear_registers (minimization_base n pF) ++
                copy_register_range (savedInputsStart n pF) 0 n).length = 0 := by
              simp only [List.length_append, clear_registers_length, copy_register_range_length] at hj_clear1 ⊢; omega
            simp only [hidx, List.getElem_cons_zero, Instr.writes_to, ne_eq, Option.some.injEq]
            intro heq; exact hr_eq_n heq.symm
        let hleft : c_prologue.state.read r = 0 :=
          straight_line_zeros_register hsl_prologue s r r hk hwrite hnowrite
        rw [hleft, hright]

  let pFExec := execSubprogramInHost hpF_sf (pFOffset n pF) (pF_shift_jumps_embed n pF)
    hf_halts c_prologue.state hagree_pF
  let c_pF' := pFExec.finalState

  have hsteps_to_epilogue : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩
      ⟨pFOffset n pF + pF.length, c_pF'⟩ :=
    Relation.ReflTransGen.trans hsteps_prologue_lifted pFExec.liftedSteps

  have hzero_after_pF : c_pF'.read (zero_reg n pF) = 0 := by
    rw [pFExec.highPreserved (zero_reg n pF)
        (program_doesnt_touch_zero_reg n pF pF (minimization_base_ge_pF n pF)), hzero_after_prologue]
  have hcounter_after_pF : c_pF'.read (counter_reg n pF) = k := by
    rw [pFExec.highPreserved (counter_reg n pF)
        (program_doesnt_touch_counter n pF pF (minimization_base_ge_pF n pF)), hcounter_after_prologue]
  have hsaved_after_pF : ∀ i : Fin n, c_pF'.read (savedInputsStart n pF + i) = inputs i := by
    intro i
    rw [pFExec.highPreserved (savedInputsStart n pF + i)
        (program_doesnt_touch_savedInputs n pF pF (minimization_base_ge_pF n pF) i),
        hsaved_after_prologue]

  let pF_result := c_pF'.read 0
  have hJ0_instr := instr_at_epilogue_J0 n pF

  by_cases hresult : pF_result = 0
  · have heq_zero : c_pF'.read 0 = c_pF'.read (zero_reg n pF) := by
      simp only [pF_result] at hresult
      rw [hresult, hzero_after_pF]
    have hstep_J0 : Step (minimize_program n pF) ⟨epilogueStartPC n pF, c_pF'⟩
        ⟨outputPC n pF, c_pF'⟩ := Step.jump_eq hJ0_instr heq_zero
    exact ⟨⟨outputPC n pF, c_pF'⟩, hsteps_to_epilogue.trans (Steps.single hstep_J0), pF_result, Or.inl ⟨rfl, hresult⟩,
           fun h => absurd hresult h, fun h => absurd hresult h,
           fun _ => hcounter_after_pF, hf_halts, pFExec.result_eq⟩

  · have hne_zero : c_pF'.read 0 ≠ c_pF'.read (zero_reg n pF) := by
      simp only [pF_result] at hresult
      rw [hzero_after_pF]; exact hresult
    have hstep_J0 : Step (minimize_program n pF) ⟨epilogueStartPC n pF, c_pF'⟩
        ⟨epilogueStartPC n pF + 1, c_pF'⟩ := Step.jump_ne hJ0_instr hne_zero
    have hS_instr := instr_at_epilogue_S n pF
    let state_after_S := c_pF'.write (counter_reg n pF) (c_pF'.read (counter_reg n pF) + 1)
    have hstep_S : Step (minimize_program n pF) ⟨epilogueStartPC n pF + 1, c_pF'⟩
        ⟨epilogueStartPC n pF + 2, state_after_S⟩ := Step.succ hS_instr
    have hJ1_instr := instr_at_epilogue_J1 n pF
    have heq_self : state_after_S.read (zero_reg n pF) = state_after_S.read (zero_reg n pF) := rfl
    have hstep_J1 : Step (minimize_program n pF) ⟨epilogueStartPC n pF + 2, state_after_S⟩
        ⟨loop_start_pc n, state_after_S⟩ := Step.jump_eq hJ1_instr heq_self
    have hsteps_total := hsteps_to_epilogue.trans ((Steps.single hstep_J0).trans ((Steps.single hstep_S).trans (Steps.single hstep_J1)))
    have hcounter_k1 : state_after_S.read (counter_reg n pF) = k + 1 := by
      simp only [state_after_S, State.write, State.read, Function.update_self]
      simp only [State.read] at hcounter_after_pF
      omega
    have hzero_preserved : state_after_S.read (zero_reg n pF) = s.read (zero_reg n pF) := by
      simp only [state_after_S, State.write_read_of_ne _ _ _ _ (Nat.ne_of_gt (zero_reg_gt_counter_reg n pF))]
      rw [hzero_after_pF, hs_zero]
    have hsaved_preserved : ∀ i : Fin n, state_after_S.read (savedInputsStart n pF + i) = s.read (savedInputsStart n pF + i) := by
      intro i
      simp only [state_after_S, State.write_read_of_ne _ _ _ _ (by min_register_omega : savedInputsStart n pF + ↑i ≠ counter_reg n pF)]
      rw [hsaved_after_pF i, hs_saved i]
    exact ⟨⟨loop_start_pc n, state_after_S⟩, hsteps_total, pF_result, Or.inr ⟨rfl, hcounter_k1, hresult⟩,
           fun _ => hzero_preserved, fun _ => hsaved_preserved,
           fun h => absurd h hresult, hf_halts, pFExec.result_eq⟩

/-- The pF_result from loop_iteration equals the Result of running pF.
    This connects the internal construction to the abstract Result function. -/
theorem loop_iteration_pF_result_eq_Result (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (k : ℕ)
    (hs_counter : s.read (counter_reg n pF) = k)
    (hs_zero : s.read (zero_reg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hf_halts : Halts pF (List.ofFn (extend_inputs inputs k))) :
    (loop_iteration n pF hpF_sf inputs s k hs_counter hs_zero hs_saved hf_halts).pF_result =
    Result pF (List.ofFn (extend_inputs inputs k)) hf_halts :=
  (loop_iteration n pF hpF_sf inputs s k hs_counter hs_zero hs_saved hf_halts).pF_result_eq

/-! ## Loop Iteration Preservation Lemmas -/

/-- When loop_iteration returns with continue (non-zero result), zero_reg is preserved.
    This follows from the zero_preserved field of LoopIterationResult. -/
theorem loop_iteration_preserves_zero_reg (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (k : ℕ)
    (hs_counter : s.read (counter_reg n pF) = k)
    (hs_zero : s.read (zero_reg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hf_halts : Halts pF (List.ofFn (extend_inputs inputs k)))
    (iter : LoopIterationResult n pF inputs s k := loop_iteration n pF hpF_sf inputs s k hs_counter hs_zero hs_saved hf_halts)
    (hcontinue : iter.pF_result ≠ 0) :
    iter.config.state.read (zero_reg n pF) = 0 := by
  rw [iter.zero_preserved hcontinue, hs_zero]

/-- When loop_iteration returns with continue (non-zero result), savedInputs are preserved.
    This follows from the saved_preserved field of LoopIterationResult. -/
theorem loop_iteration_preserves_savedInputs (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (k : ℕ)
    (hs_counter : s.read (counter_reg n pF) = k)
    (hs_zero : s.read (zero_reg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hf_halts : Halts pF (List.ofFn (extend_inputs inputs k)))
    (iter : LoopIterationResult n pF inputs s k := loop_iteration n pF hpF_sf inputs s k hs_counter hs_zero hs_saved hf_halts)
    (hcontinue : iter.pF_result ≠ 0) :
    ∀ i : Fin n, iter.config.state.read (savedInputsStart n pF + i) = inputs i := by
  intro i
  rw [iter.saved_preserved hcontinue i, hs_saved i]

/-! ## Main Halting Theorem -/

/-- Result of executing k loop iterations: config at loopStart with counter = k and invariants preserved -/
structure LoopKIterationsResult (inputs : Fin n → ℕ) (s : State) (k : ℕ) where
  /-- Final configuration -/
  config : Config
  /-- Steps from initial state to final config -/
  steps : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ config
  /-- PC is at loop start -/
  pc_eq : config.pc = loop_start_pc n
  /-- Counter equals k -/
  counter_eq : config.state.read (counter_reg n pF) = k
  /-- Zero register preserved -/
  zero_preserved : config.state.read (zero_reg n pF) = 0
  /-- Saved inputs preserved -/
  saved_preserved : ∀ i : Fin n, config.state.read (savedInputsStart n pF + i) = inputs i

/-- Strong version of loop_k_iterations that bundles all invariants. -/
noncomputable def loop_k_iterations_strong (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (k : ℕ)
    (hs_counter : s.read (counter_reg n pF) = 0)
    (hs_zero : s.read (zero_reg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hf_halts_below : ∀ j < k, Halts pF (List.ofFn (extend_inputs inputs j)))
    (hf_nonzero_below : ∀ j (hj : j < k), Result pF (List.ofFn (extend_inputs inputs j))
        (hf_halts_below j hj) ≠ 0) :
    LoopKIterationsResult n pF inputs s k := by
  induction k with
  | zero =>
    exact ⟨⟨loop_start_pc n, s⟩, Relation.ReflTransGen.refl, rfl, hs_counter, hs_zero, hs_saved⟩
  | succ j ih =>
    have hf_halts_j : ∀ i < j, Halts pF (List.ofFn (extend_inputs inputs i)) :=
      fun i hi => hf_halts_below i (Nat.lt_succ_of_lt hi)
    have hf_nonzero_j : ∀ i (hi : i < j), Result pF (List.ofFn (extend_inputs inputs i)) (hf_halts_j i hi) ≠ 0 := by
      intro i hi
      let hi' := Nat.lt_succ_of_lt hi
      let h := hf_nonzero_below i hi'
      convert h using 2
    let res_j := ih hf_halts_j hf_nonzero_j
    have hf_halts_at_j := hf_halts_below j (Nat.lt_succ_self j)
    let iter := loop_iteration n pF hpF_sf inputs res_j.config.state j
        res_j.counter_eq res_j.zero_preserved res_j.saved_preserved hf_halts_at_j
    have hf_nonzero_at_j := hf_nonzero_below j (Nat.lt_succ_self j)
    have hiter_nonzero : iter.pF_result ≠ 0 := by
      rw [loop_iteration_pF_result_eq_Result]
      convert hf_nonzero_at_j using 2
    by_cases hexit : iter.pF_result = 0
    · exact absurd hexit hiter_nonzero
    · have hcontinue : iter.config.pc = loop_start_pc n ∧
          iter.config.state.read (counter_reg n pF) = j + 1 := by
        cases iter.outcome with
        | inl h => exact absurd h.2 hexit
        | inr h => exact ⟨h.1, h.2.1⟩
      have hzero_new := loop_iteration_preserves_zero_reg n pF hpF_sf inputs res_j.config.state j
          res_j.counter_eq res_j.zero_preserved res_j.saved_preserved hf_halts_at_j iter hexit
      have hsaved_new := loop_iteration_preserves_savedInputs n pF hpF_sf inputs res_j.config.state j
          res_j.counter_eq res_j.zero_preserved res_j.saved_preserved hf_halts_at_j iter hexit
      have hres_j_pc : res_j.config = ⟨loop_start_pc n, res_j.config.state⟩ := by
        ext
        · exact res_j.pc_eq
        · rfl

      have hsteps_combined : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ iter.config := by
        let h1 : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ ⟨loop_start_pc n, res_j.config.state⟩ := by
          rw [← hres_j_pc]; exact res_j.steps
        exact h1.trans iter.steps

      exact ⟨iter.config, hsteps_combined, hcontinue.1, hcontinue.2, hzero_new, hsaved_new⟩

/-- Result of loop execution that reaches outputPC (used for converse halting proof).
    Generalized to start from any counter value. -/
structure LoopExitResultGen (inputs : Fin n → ℕ) (s : State) (startCounter : ℕ) where
  /-- Number of complete iterations before exit (counter value at exit) -/
  k : ℕ
  /-- k ≥ startCounter since we're continuing from startCounter -/
  k_ge : startCounter ≤ k
  /-- Final config at outputPC -/
  config : Config
  /-- Execution steps from loop_start_pc -/
  steps : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ config
  /-- Exited at outputPC -/
  pc_eq : config.pc = outputPC n pF
  /-- Counter value at exit equals k -/
  counter_eq : config.state.read (counter_reg n pF) = k
  /-- pF halted on all iterations startCounter..k -/
  pF_halts : ∀ j, startCounter ≤ j → j ≤ k → Halts pF (List.ofFn (extend_inputs inputs j))
  /-- pF returned non-zero for startCounter ≤ j < k -/
  pF_nonzero_range : ∀ j (hlo : startCounter ≤ j) (hhi : j < k),
      Result pF (List.ofFn (extend_inputs inputs j)) (pF_halts j hlo (Nat.le_of_lt hhi)) ≠ 0
  /-- pF returned 0 for iteration k -/
  pF_zero_at_k : Result pF (List.ofFn (extend_inputs inputs k)) (pF_halts k k_ge (Nat.le_refl k)) = 0

/-- Helper: if minimize_program halts from loop_start_pc, pF must halt on current counter value.
    This is because execution must pass through pF to reach the epilogue. -/
theorem pF_halts_from_minimize_program_halts (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (counter : ℕ)
    (hs_counter : s.read (counter_reg n pF) = counter)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hHalts : ∃ c, Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ c ∧ c.is_halted (minimize_program n pF)) :
    Halts pF (List.ofFn (extend_inputs inputs counter)) := by
  by_contra hpF_diverges
  obtain ⟨cFinal, hsteps_final, hhalted_final⟩ := hHalts
  have hminSF := minimize_program_isStandardForm n pF hpF_sf
  have hpc_bound : loop_start_pc n ≤ (minimize_program n pF).length := by
    simp only [minimize_program_length, loop_start_pc, outputPC, pFOffset, setup_phase_length, loop_prologueLength]
    omega
  have hcFinal_pc : cFinal.pc = (minimize_program n pF).length :=
    hminSF.pc_eq_length_of_halted hsteps_final hpc_bound hhalted_final
  have hsl_prologue := loop_prologue_is_straight_line n pF
  let prologueExec := execPhaseInHost hsl_prologue (loop_start_pc n) (loop_prologue_embed n pF) s
  let cPrologue := prologueExec.phaseResult.config
  have hPrologue_steps_lifted : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩
      ⟨pFOffset n pF, cPrologue.state⟩ := by
    have hpc : loop_start_pc n + (loop_prologue n pF).length = pFOffset n pF := by
      simp only [pFOffset, loop_start_pc, loop_prologue_length, setup_phase_length, loop_prologueLength]
    exact hpc ▸ prologueExec.liftedSteps
  have hContinuation := Steps.deterministic_continuation hPrologue_steps_lifted hsteps_final hhalted_final
  have hpFOffset_lt : pFOffset n pF < (minimize_program n pF).length := by
    simp only [minimize_program_length, outputPC]; omega
  have hcFinal_past_pF : cFinal.pc > pFOffset n pF + pF.length := by
    rw [hcFinal_pc, minimize_program_length, outputPC]; omega
  have hpF_range_lo := pFOffset n pF
  have hpF_range_hi := pFOffset n pF + pF.length
  let pFStartState := cPrologue.state
  have hPrologue_sets_inputs : ∀ i : Fin n, pFStartState.read i = inputs i := by
    intro i
    let h1 := loop_prologue_restores_inputs n pF s cPrologue prologueExec.localSteps prologueExec.localHalted i
    let h2 := hs_saved i
    simp only at h1 h2 ⊢
    rw [h1, h2]

  have hPrologue_sets_counter_reg : pFStartState.read n = counter := by
    let h1 := loop_prologue_sets_counter_input n pF s cPrologue prologueExec.localSteps prologueExec.localHalted
    rw [h1, hs_counter]
  have hpFStartState_matches : ∀ i : Fin (n + 1), pFStartState.read i = extend_inputs inputs counter i := by
    intro i
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with h | h
    · let hi : (i : ℕ) < n := h
      rw [extend_inputs, Fin.snoc]
      simp only [hi, dite_true]
      exact hPrologue_sets_inputs ⟨i, hi⟩
    · let hi : (i : ℕ) = n := h
      rw [extend_inputs, Fin.snoc]
      simp only [hi, lt_irrefl, dite_false]
      exact hPrologue_sets_counter_reg
  have hpFStartState_of_inputs : ∀ i : Fin (n + 1),
      pFStartState.read i = State.of_inputs (List.ofFn (extend_inputs inputs counter)) i := by
    intro i
    simp only [State.of_inputs, hpFStartState_matches]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]
  let pFInitState := State.of_inputs (List.ofFn (extend_inputs inputs counter))
  suffices h : ∀ k (state'' : State) (c'' : Config),
      k ≤ pF.length →
      Steps (minimize_program n pF) ⟨pFOffset n pF + k, state''⟩ c'' →
      c''.pc ≥ pFOffset n pF + pF.length →
      ∃ c_pF, Steps pF ⟨k, state''⟩ c_pF ∧ c_pF.pc = pF.length by
    obtain ⟨c_pF, hsteps_pF, hpc_pF⟩ := h 0 cPrologue.state cFinal (Nat.zero_le _)
        (by rw [Nat.add_zero]; exact hContinuation) (Nat.le_of_lt hcFinal_past_pF)
    have hhalted_pF : c_pF.is_halted pF := by simp only [Config.is_halted, hpc_pF]; exact Nat.le_refl _
    have hagree : ∀ r, r ≤ pF.max_register →
        cPrologue.state.read r = (State.of_inputs (List.ofFn (extend_inputs inputs counter))).read r := by
      intro r hr
      by_cases hr_lt : r < n + 1
      · let h := hpFStartState_of_inputs ⟨r, hr_lt⟩
        exact h
      · simp only [State.of_inputs, State.read]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]
        let hr_le_base : r ≤ minimization_base n pF := by min_register_omega
        exact loop_prologue_clears_high_registers n pF s cPrologue prologueExec.localSteps prologueExec.localHalted
          r (Nat.le_of_not_lt hr_lt) hr_le_base
    exact hpF_diverges (Halts.of_agreeing_state hsteps_pF hhalted_pF hagree)
  intro k state'' c'' hk_le hsteps'' hpc''_ge
  exact halts_of_exits_embedded_region (pF_shift_jumps_embed n pF) hpF_sf k state'' c'' hk_le hsteps'' hpc''_ge

/-- Auxiliary function for loop_halts_exit_gen that takes step count explicitly.
    This allows for clean strong induction on step count. -/
noncomputable def loop_halts_exit_gen_aux (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (numSteps : ℕ) (s : State) (startCounter : ℕ) (cFinal : Config)
    (hs_counter : s.read (counter_reg n pF) = startCounter)
    (hs_zero : s.read (zero_reg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hstepsN : StepsN (minimize_program n pF) numSteps ⟨loop_start_pc n, s⟩ cFinal)
    (hhalted : cFinal.is_halted (minimize_program n pF)) :
    LoopExitResultGen n pF inputs s startCounter :=
  if hNumSteps : numSteps = 0 then
    absurd hhalted (by
      have hcFinal_eq : cFinal = ⟨loop_start_pc n, s⟩ := StepsN.zero_inv (hNumSteps ▸ hstepsN)
      rw [hcFinal_eq]
      simp only [Config.is_halted, minimize_program_length, loop_start_pc, setup_phase_length,
        outputPC, pFOffset, loop_prologueLength]
      omega)
  else
    let hpF_halts_counter : Halts pF (List.ofFn (extend_inputs inputs startCounter)) :=
      pF_halts_from_minimize_program_halts n pF hpF_sf inputs s startCounter
        hs_counter hs_saved ⟨cFinal, hstepsN.to_steps, hhalted⟩
    let iter := loop_iteration n pF hpF_sf inputs s startCounter
        hs_counter hs_zero hs_saved hpF_halts_counter
    if hpf_zero : iter.pF_result = 0 then
      have hexit : iter.config.pc = outputPC n pF ∧ iter.pF_result = 0 := by
        cases iter.outcome with
        | inl h => exact h
        | inr h => exact absurd h.2.2 (by simp [hpf_zero])
      let hpc_output : iter.config.pc = outputPC n pF := hexit.1
      have hcounter_preserved : iter.config.state.read (counter_reg n pF) = startCounter :=
        iter.counter_preserved_exit hpf_zero

      {
        k := startCounter
        k_ge := Nat.le_refl startCounter
        config := iter.config
        steps := iter.steps
        pc_eq := hpc_output
        counter_eq := hcounter_preserved
        pF_halts := fun j hlo hhi => by
          have hj_eq : j = startCounter := Nat.le_antisymm hhi hlo
          subst hj_eq; exact hpF_halts_counter
        pF_nonzero_range := fun j hlo hhi => by
          exfalso; exact Nat.not_lt.mpr hlo hhi
        pF_zero_at_k := by
          simp only [iter.pF_result_eq] at hpf_zero
          convert hpf_zero using 2
      }
    else
      have hcontinue : iter.config.pc = loop_start_pc n ∧
          iter.config.state.read (counter_reg n pF) = startCounter + 1 ∧ iter.pF_result ≠ 0 := by
        cases iter.outcome with
        | inl h => exact absurd h.2 hpf_zero
        | inr h => exact h
      let hpc_loop : iter.config.pc = loop_start_pc n := hcontinue.1
      let hcounter_incr : iter.config.state.read (counter_reg n pF) = startCounter + 1 := hcontinue.2.1
      let hresult_nonzero : iter.pF_result ≠ 0 := hcontinue.2.2
      have hzero_new : iter.config.state.read (zero_reg n pF) = 0 := by
        rw [iter.zero_preserved hresult_nonzero, hs_zero]
      have hsaved_new : ∀ i : Fin n, iter.config.state.read (savedInputsStart n pF + i) = inputs i := by
        intro i; rw [iter.saved_preserved hresult_nonzero i, hs_saved i]
      have hfewer_steps : ∃ m < numSteps, StepsN (minimize_program n pF) m
          ⟨loop_start_pc n, iter.config.state⟩ cFinal := by
        have hiter_config_eq' : iter.config = ⟨loop_start_pc n, iter.config.state⟩ := by
          ext; exact hpc_loop; rfl
        have h_moved : ⟨loop_start_pc n, s⟩ ≠ iter.config := by
          intro heq
          let h : (⟨loop_start_pc n, s⟩ : Config).state = iter.config.state := by rw [heq]
          let hs_eq : s = iter.config.state := h
          rw [← hs_eq] at hcounter_incr
          rw [hs_counter] at hcounter_incr
          omega
        have hsplit := StepsN.split_strictly_smaller hstepsN iter.steps hhalted h_moved
        obtain ⟨m, hm_lt, hm_stepsN⟩ := hsplit
        use m, hm_lt
        rw [← hiter_config_eq']
        exact hm_stepsN

      let m := Classical.choose hfewer_steps
      let hm_spec := Classical.choose_spec hfewer_steps
      let hm_lt : m < numSteps := hm_spec.1
      let hstepsN_m : StepsN (minimize_program n pF) m ⟨loop_start_pc n, iter.config.state⟩ cFinal := hm_spec.2
      have hiter_config_eq : iter.config = ⟨loop_start_pc n, iter.config.state⟩ := by
        ext; exact hpc_loop; rfl

      let recResult := loop_halts_exit_gen_aux hpF_sf inputs m iter.config.state (startCounter + 1) cFinal
          hcounter_incr hzero_new hsaved_new hstepsN_m hhalted
      have hcombined_steps : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ recResult.config := by
        have h1 : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ iter.config := iter.steps
        have h2 : Steps (minimize_program n pF) ⟨loop_start_pc n, iter.config.state⟩ recResult.config := recResult.steps
        rw [hiter_config_eq] at h1
        exact h1.trans h2
      {
        k := recResult.k
        k_ge := Nat.le_trans (Nat.le_succ startCounter) recResult.k_ge
        config := recResult.config
        steps := hcombined_steps
        pc_eq := recResult.pc_eq
        counter_eq := recResult.counter_eq
        pF_halts := fun j hlo hhi => by
          by_cases hj_eq : j = startCounter
          · subst hj_eq; exact hpF_halts_counter
          · exact recResult.pF_halts j (Nat.lt_of_le_of_ne hlo (Ne.symm hj_eq)) hhi
        pF_nonzero_range := fun j hlo hhi => by
          by_cases hj_eq : j = startCounter
          · subst hj_eq
            simp only [iter.pF_result_eq] at hresult_nonzero
            convert hresult_nonzero using 2
          · exact recResult.pF_nonzero_range j (Nat.lt_of_le_of_ne hlo (Ne.symm hj_eq)) hhi
        pF_zero_at_k := recResult.pF_zero_at_k
      }
termination_by numSteps
decreasing_by all_goals exact hm_spec.1

/-- If loop eventually reaches outputPC (halts from loop_start_pc), extract the exit result.
    Generalized version that works for any starting counter value. -/
noncomputable def loop_halts_exit_gen (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (startCounter : ℕ)
    (hs_counter : s.read (counter_reg n pF) = startCounter)
    (hs_zero : s.read (zero_reg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hHalts : ∃ c, Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ c ∧ c.is_halted (minimize_program n pF)) :
    LoopExitResultGen n pF inputs s startCounter := by
  let cFinal := Classical.choose hHalts
  have hspec := Classical.choose_spec hHalts
  let hsteps_final := hspec.1
  let hhalted_final := hspec.2
  let hStepsN := StepsN.from_steps hsteps_final
  let numSteps := Classical.choose hStepsN
  have hstepsN := Classical.choose_spec hStepsN
  exact loop_halts_exit_gen_aux n pF hpF_sf inputs numSteps s startCounter cFinal
      hs_counter hs_zero hs_saved hstepsN hhalted_final

/-- Specialized version for counter starting at 0 -/
structure LoopExitResult (inputs : Fin n → ℕ) (s : State) where
  /-- Number of complete iterations before exit (counter value at exit) -/
  k : ℕ
  /-- Final config at outputPC -/
  config : Config
  /-- Execution steps from loop_start_pc -/
  steps : Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ config
  /-- Exited at outputPC -/
  pc_eq : config.pc = outputPC n pF
  /-- Counter value at exit equals k -/
  counter_eq : config.state.read (counter_reg n pF) = k
  /-- pF halted on all iterations 0..k -/
  pF_halts : ∀ j ≤ k, Halts pF (List.ofFn (extend_inputs inputs j))
  /-- pF returned non-zero for j < k -/
  pF_nonzero_below : ∀ j (hj : j < k), Result pF (List.ofFn (extend_inputs inputs j)) (pF_halts j (Nat.le_of_lt hj)) ≠ 0
  /-- pF returned 0 for iteration k -/
  pF_zero_at_k : Result pF (List.ofFn (extend_inputs inputs k)) (pF_halts k (Nat.le_refl k)) = 0

/-- Convert generalized result to specialized result -/
noncomputable def LoopExitResult.ofGen (inputs : Fin n → ℕ) (s : State)
    (res : LoopExitResultGen n pF inputs s 0) : LoopExitResult n pF inputs s := {
  k := res.k
  config := res.config
  steps := res.steps
  pc_eq := res.pc_eq
  counter_eq := res.counter_eq
  pF_halts := fun j hj => res.pF_halts j (Nat.zero_le j) hj
  pF_nonzero_below := fun j hj => res.pF_nonzero_range j (Nat.zero_le j) hj
  pF_zero_at_k := res.pF_zero_at_k
}

/-- If loop eventually reaches outputPC (halts from loop_start_pc with counter=0), extract the exit result. -/
noncomputable def loop_halts_exit (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State)
    (hs_counter : s.read (counter_reg n pF) = 0)
    (hs_zero : s.read (zero_reg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hHalts : ∃ c, Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ c ∧ c.is_halted (minimize_program n pF)) :
    LoopExitResult n pF inputs s :=
  LoopExitResult.ofGen n pF inputs s
    (loop_halts_exit_gen n pF hpF_sf inputs s 0 hs_counter hs_zero hs_saved hHalts)

/-- After k loop iterations starting from loopStart, we reach loopStart with counter = k
    (if f hasn't returned 0 on any earlier iteration). -/
theorem loop_k_iterations (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (k : ℕ)
    (hs_counter : s.read (counter_reg n pF) = 0)
    (hs_zero : s.read (zero_reg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hf_halts_below : ∀ j < k, Halts pF (List.ofFn (extend_inputs inputs j)))
    (hf_nonzero_below : ∀ j (hj : j < k), Result pF (List.ofFn (extend_inputs inputs j))
        (hf_halts_below j hj) ≠ 0) :
    ∃ c, Steps (minimize_program n pF) ⟨loop_start_pc n, s⟩ c ∧
         c.pc = loop_start_pc n ∧
         c.state.read (counter_reg n pF) = k := by
  let res := loop_k_iterations_strong n pF hpF_sf inputs s k hs_counter hs_zero hs_saved hf_halts_below hf_nonzero_below
  exact ⟨res.config, res.steps, res.pc_eq, res.counter_eq⟩

/-- setup_phase instructions are embedded at the start of minimize_program. -/
theorem setup_phase_embed :
    ∀ i, i < (setup_phase n pF).length →
    (minimize_program n pF)[0 + i]? = (setup_phase n pF)[i]? := by
  intro i hi
  simp only [Nat.zero_add, minimize_program, List.getElem?_append, List.length_append,
    setup_phase_len, loop_prologue_length, shift_jumps_length, loopEpilogue_length] at *
  split_ifs <;> first | rfl | omega

/-- output_phase instruction is at outputPC in minimize_program. -/
theorem output_phase_instr :
    (minimize_program n pF)[outputPC n pF]? = some (Instr.T (counter_reg n pF) 0) := by
  simp only [minimize_program, outputPC, pFOffset, setup_phase_length, loop_prologueLength,
    List.getElem?_append, List.length_append, setup_phase_len, loop_prologue_length,
    shift_jumps_length, loopEpilogue_length]
  split_ifs <;> first | omega | simp [output_phase]

/-- Execute output phase: single T instruction from outputPC halts the program. -/
theorem output_phase_halts (s : State) :
    ∃ c, Steps (minimize_program n pF) ⟨outputPC n pF, s⟩ c ∧
         c.is_halted (minimize_program n pF) ∧
         c.state.read 0 = s.read (counter_reg n pF) := by
  have hinstr := output_phase_instr n pF
  let s' := s.write 0 (s.read (counter_reg n pF))
  have hstep : Step (minimize_program n pF) ⟨outputPC n pF, s⟩ ⟨outputPC n pF + 1, s'⟩ :=
    Step.trans hinstr
  have hhalted : (⟨outputPC n pF + 1, s'⟩ : Config).is_halted (minimize_program n pF) := by
    simp only [Config.is_halted, minimize_program_length]; omega
  have hread : s'.read 0 = s.read (counter_reg n pF) := by
    simp only [s', State.write, State.read, Function.update_self]
  exact ⟨⟨outputPC n pF + 1, s'⟩, Relation.ReflTransGen.single hstep, hhalted, hread⟩

/-- Result of executing the setup phase: state at loop_start_pc with invariants. -/
structure SetupPhaseResult (inputs : Fin n → ℕ) where
  /-- State after setup phase -/
  state : State
  /-- Steps from initial config to loop_start_pc -/
  steps : Steps (minimize_program n pF) ⟨0, State.of_inputs (List.ofFn inputs)⟩
      ⟨loop_start_pc n, state⟩
  /-- Counter is initialized to 0 -/
  counter_eq : state.read (counter_reg n pF) = 0
  /-- Zero register is initialized to 0 -/
  zero_eq : state.read (zero_reg n pF) = 0
  /-- Saved inputs contain original inputs -/
  saved_eq : ∀ i : Fin n, state.read (savedInputsStart n pF + i) = inputs i

/-- Execute setup phase and establish invariants.
    This factors out the common setup code used by minimize_program_halts,
    minimize_program_halts_imp_dom, and minimize_program_result. -/
noncomputable def executeSetupPhase (inputs : Fin n → ℕ) :
    SetupPhaseResult n pF inputs :=
  let hsl_setup := setup_phase_is_straight_line n pF
  let initState := State.of_inputs (List.ofFn inputs)
  let setupExec := execPhaseInHost hsl_setup 0 (setup_phase_embed n pF) initState
  let cSetup := setupExec.phaseResult.config
  let hSetup_steps_lifted : Steps (minimize_program n pF) ⟨0, initState⟩
      ⟨loop_start_pc n, cSetup.state⟩ := by
    have hpc : 0 + (setup_phase n pF).length = loop_start_pc n := by
      simp only [loop_start_pc, setup_phase_length, setup_phase_len, Nat.zero_add]
    exact hpc ▸ setupExec.liftedSteps
  let hSetup_counter : cSetup.state.read (counter_reg n pF) = 0 :=
    setup_phase_counter_zero n pF initState cSetup setupExec.localSteps setupExec.localHalted
  let hSetup_zero : cSetup.state.read (zero_reg n pF) = 0 :=
    setup_phase_zero_reg_zero n pF initState cSetup setupExec.localSteps setupExec.localHalted
  let hSetup_saved : ∀ i : Fin n, cSetup.state.read (savedInputsStart n pF + i) = inputs i :=
    fun i => setup_phase_saves_inputs n pF inputs initState rfl cSetup setupExec.localSteps setupExec.localHalted i

  ⟨cSetup.state, hSetup_steps_lifted, hSetup_counter, hSetup_zero, hSetup_saved⟩

/-! ## Main Halting Theorems -/

/-- If μ f is defined, then minimize_program halts. -/
theorem minimize_program_halts (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ)
    (hμ_dom : (μ f inputs).Dom) :
    Halts (minimize_program n pF) (List.ofFn inputs) := by
  let k := (μ f inputs).get hμ_dom
  have hk_zero : f (extend_inputs inputs k) = Part.some 0 := μ_spec hμ_dom
  have hk_dom : ∀ y' < k, (f (extend_inputs inputs y')).Dom := fun y' hy' => μ_dom_below hμ_dom hy'
  have hf_dom_k : (f (extend_inputs inputs k)).Dom := by
    rw [Part.eq_some_iff] at hk_zero
    exact Part.dom_iff_mem.mpr ⟨0, hk_zero⟩
  have hpF_halts_k : Halts pF (List.ofFn (extend_inputs inputs k)) := by
    rw [(hpF_spec (extend_inputs inputs k)).1]
    exact hf_dom_k
  have hpF_result_zero : Result pF (List.ofFn (extend_inputs inputs k)) hpF_halts_k = 0 := by
    rw [(hpF_spec (extend_inputs inputs k)).2 hpF_halts_k hf_dom_k]
    rw [Part.eq_some_iff] at hk_zero
    simp only [Part.get_eq_iff_mem, hk_zero]
  have hpF_halts_below : ∀ j < k, Halts pF (List.ofFn (extend_inputs inputs j)) := fun j hj => by
    rw [(hpF_spec (extend_inputs inputs j)).1]
    exact hk_dom j hj
  have hpF_nonzero_below : ∀ j (hj : j < k), Result pF (List.ofFn (extend_inputs inputs j))
      (hpF_halts_below j hj) ≠ 0 := fun j hj => by
    obtain ⟨v, hv_eq, hv_ne0⟩ := μ_min hμ_dom hj
    rw [(hpF_spec (extend_inputs inputs j)).2 (hpF_halts_below j hj) (hk_dom j hj)]
    rw [Part.eq_some_iff] at hv_eq
    rw [Part.get_eq_of_mem hv_eq]
    exact hv_ne0
  let setup := executeSetupPhase n pF inputs
  let resK := loop_k_iterations_strong n pF hpF_sf inputs setup.state k
    setup.counter_eq setup.zero_eq setup.saved_eq hpF_halts_below hpF_nonzero_below
  let iterK := loop_iteration n pF hpF_sf inputs resK.config.state k
    resK.counter_eq resK.zero_preserved resK.saved_preserved hpF_halts_k
  have hiterK_result_zero : iterK.pF_result = 0 := by
    rw [iterK.pF_result_eq]
    convert hpF_result_zero using 2
  have hiterK_exit : iterK.config.pc = outputPC n pF := by
    cases iterK.outcome with
    | inl h => exact h.1
    | inr h => exact absurd hiterK_result_zero h.2.2
  obtain ⟨cOutput, hOutput_steps, hOutput_halted, _⟩ := output_phase_halts n pF iterK.config.state
  have hTotal : Steps (minimize_program n pF) ⟨0, State.of_inputs (List.ofFn inputs)⟩ cOutput := by
    let h1 : Steps (minimize_program n pF) ⟨0, State.of_inputs (List.ofFn inputs)⟩
        ⟨loop_start_pc n, setup.state⟩ := setup.steps
    let h2 : Steps (minimize_program n pF) ⟨loop_start_pc n, setup.state⟩ resK.config := resK.steps
    let hresK_eq : resK.config = ⟨loop_start_pc n, resK.config.state⟩ := by
      ext; exact resK.pc_eq; rfl
    let h3 : Steps (minimize_program n pF) resK.config iterK.config := by
      convert iterK.steps using 1
    let hIterK_eq : iterK.config = ⟨outputPC n pF, iterK.config.state⟩ := by
      ext; exact hiterK_exit; rfl
    let h4 : Steps (minimize_program n pF) iterK.config cOutput := by
      convert hOutput_steps using 1
    exact h1.trans (h2.trans (h3.trans h4))

  exact ⟨cOutput, hTotal, hOutput_halted⟩

/-! ## Converse: Halts → Dom -/

/-- If minimize_program halts, then μ f is defined. -/
theorem minimize_program_halts_imp_dom (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (minimize_program n pF) (List.ofFn inputs)) :
    (μ f inputs).Dom := by
  let setup := executeSetupPhase n pF inputs
  obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ := hHalts
  have hLoopHalts : ∃ c, Steps (minimize_program n pF) ⟨loop_start_pc n, setup.state⟩ c ∧
      c.is_halted (minimize_program n pF) := by
    let hInit_eq : Config.init (List.ofFn inputs) = ⟨0, State.of_inputs (List.ofFn inputs)⟩ := rfl
    rw [hInit_eq] at hFinal_steps
    let hContinuation := Steps.deterministic_continuation setup.steps hFinal_steps hFinal_halted
    exact ⟨cFinal, hContinuation, hFinal_halted⟩
  let exitResult := loop_halts_exit n pF hpF_sf inputs setup.state
      setup.counter_eq setup.zero_eq setup.saved_eq hLoopHalts
  rw [μ_dom_iff]
  use exitResult.k
  constructor
  · have hpF_halts_k := exitResult.pF_halts exitResult.k (Nat.le_refl exitResult.k)
    have hpF_result_zero := exitResult.pF_zero_at_k
    have hf_dom : (f (extend_inputs inputs exitResult.k)).Dom := by
      rw [← (hpF_spec (extend_inputs inputs exitResult.k)).1]
      exact hpF_halts_k
    have hf_get : (f (extend_inputs inputs exitResult.k)).get hf_dom = 0 := by
      let h := (hpF_spec (extend_inputs inputs exitResult.k)).2 hpF_halts_k hf_dom
      rw [← h]
      convert hpF_result_zero using 2
    rw [Part.eq_some_iff, Part.mem_eq]
    exact ⟨hf_dom, hf_get⟩
  · intro y' hy'
    have hpF_halts_y' := exitResult.pF_halts y' (Nat.le_of_lt hy')
    rw [← (hpF_spec (extend_inputs inputs y')).1]
    exact hpF_halts_y'

end

end Urm
