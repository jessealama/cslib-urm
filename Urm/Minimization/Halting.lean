/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.Preservation

/-! # Halting Proofs for Minimization

This file proves halting properties for the minimization witness program.

## Main results

- `minimizeProgram_halts`: If μ f is defined, the minimization program halts
- Various lemmas about loop iteration behavior
-/

namespace Urm

open Program

/-! ## Execution at Offset Helpers -/

/-- A single Step in p corresponds to a Step in P when p is embedded at offset k in P.
    Requires p to be straight-line (no jumps) so the PC offset is preserved correctly. -/
theorem Step.at_offset {p P : Program} {c c' : Config} (k : ℕ)
    (hsl : p.isStraightLine = true)
    (hembed : ∀ i, i < p.length → P.getInstr (k + i) = p.getInstr i)
    (hstep : Step p c c')
    (hpc_bound : c.pc < p.length) :
    Step P ⟨k + c.pc, c.state⟩ ⟨k + c'.pc, c'.state⟩ := by
  have hinstr : P.getInstr (k + c.pc) = p.getInstr c.pc := hembed c.pc hpc_bound
  cases hstep with
  | zero h =>
    have h' : P.getInstr (k + c.pc) = some (Instr.Z _) := hinstr ▸ h
    have hstep' : Step P ⟨k + c.pc, c.state⟩ ⟨k + c.pc + 1, c.state.write _ 0⟩ := Step.zero h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | succ h =>
    have h' : P.getInstr (k + c.pc) = some (Instr.S _) := hinstr ▸ h
    have hstep' : Step P ⟨k + c.pc, c.state⟩ ⟨k + c.pc + 1, _⟩ := Step.succ h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | trans h =>
    have h' : P.getInstr (k + c.pc) = some (Instr.T _ _) := hinstr ▸ h
    have hstep' : Step P ⟨k + c.pc, c.state⟩ ⟨k + c.pc + 1, _⟩ := Step.trans h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | jump_eq h _ =>
    -- Can't happen: straight-line programs have no jumps
    have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact absurd (hsl _ (heq ▸ List.getElem_mem hlt)) (by simp [Instr.isNonJumping])
  | jump_ne h _ =>
    -- Can't happen: straight-line programs have no jumps
    have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact absurd (hsl _ (heq ▸ List.getElem_mem hlt)) (by simp [Instr.isNonJumping])

/-- Steps in a straight-line p lift to Steps in P at offset k. -/
theorem Steps.straightLine_at_offset {p P : Program} {c c' : Config} (k : ℕ)
    (hsl : p.isStraightLine = true)
    (hembed : ∀ i, i < p.length → P.getInstr (k + i) = p.getInstr i)
    (hsteps : Steps p c c') :
    Steps P ⟨k + c.pc, c.state⟩ ⟨k + c'.pc, c'.state⟩ := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep _ ih =>
    have hpc_bound := Step.pc_lt_length hstep
    have hstep' := Step.at_offset k hsl hembed hstep hpc_bound
    exact Relation.ReflTransGen.head hstep' ih

/-! ## Embedding Lemmas -/

/-- A step in p lifts to a step in P when p.shiftJumps(offset) is embedded at offset in P. -/
theorem Step.shiftJumps_at_offset {p P : Program} {c c' : Config} (offset : ℕ)
    (hembed : ∀ i, i < p.length → P.getInstr (offset + i) = (p.shiftJumps offset).getInstr i)
    (hstep : Step p c c')
    (hpc_bound : c.pc < p.length) :
    Step P ⟨offset + c.pc, c.state⟩ ⟨offset + c'.pc, c'.state⟩ := by
  have hinstr_eq : P.getInstr (offset + c.pc) = (p.shiftJumps offset).getInstr c.pc :=
    hembed c.pc hpc_bound
  match hstep with
  | .zero (n := n) h =>
    have h' : P.getInstr (offset + c.pc) = some (Instr.Z n) := by
      rw [hinstr_eq, Program.getInstr_shiftJumps, h]; rfl
    have hstep' : Step P ⟨offset + c.pc, c.state⟩ ⟨offset + c.pc + 1, c.state.write n 0⟩ := Step.zero h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | .succ (n := n) h =>
    have h' : P.getInstr (offset + c.pc) = some (Instr.S n) := by
      rw [hinstr_eq, Program.getInstr_shiftJumps, h]; rfl
    have hstep' : Step P ⟨offset + c.pc, c.state⟩ ⟨offset + c.pc + 1, _⟩ := Step.succ h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | .trans (m := m) (n := n) h =>
    have h' : P.getInstr (offset + c.pc) = some (Instr.T m n) := by
      rw [hinstr_eq, Program.getInstr_shiftJumps, h]; rfl
    have hstep' : Step P ⟨offset + c.pc, c.state⟩ ⟨offset + c.pc + 1, _⟩ := Step.trans h'
    simp only [Nat.add_assoc] at hstep'; exact hstep'
  | .jump_eq (m := m) (n := n) (q := q) h heq =>
    have h' : P.getInstr (offset + c.pc) = some (Instr.J m n (q + offset)) := by
      rw [hinstr_eq, Program.getInstr_shiftJumps, h]; rfl
    have hstep' := @Step.jump_eq P ⟨offset + c.pc, c.state⟩ m n (q + offset) h' heq
    simp only [Nat.add_comm q offset] at hstep'; exact hstep'
  | .jump_ne (m := m) (n := n) (q := q) h hne =>
    have h' : P.getInstr (offset + c.pc) = some (Instr.J m n (q + offset)) := by
      rw [hinstr_eq, Program.getInstr_shiftJumps, h]; rfl
    have hstep' : Step P ⟨offset + c.pc, c.state⟩ ⟨offset + c.pc + 1, c.state⟩ := Step.jump_ne h' hne
    simp only [Nat.add_assoc] at hstep'; exact hstep'

/-- Steps in p lift to steps in P when p.shiftJumps(offset) is embedded at offset in P. -/
theorem Steps.shiftJumps_at_offset {p P : Program} {c c' : Config} (offset : ℕ)
    (hembed : ∀ i, i < p.length → P.getInstr (offset + i) = (p.shiftJumps offset).getInstr i)
    (hsteps : Steps p c c') :
    Steps P ⟨offset + c.pc, c.state⟩ ⟨offset + c'.pc, c'.state⟩ := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep _ ih =>
    have hpc_bound := Step.pc_lt_length hstep
    have hstep' := Step.shiftJumps_at_offset offset hembed hstep hpc_bound
    exact Relation.ReflTransGen.head hstep' ih

/-- loopPrologue is embedded in minimizeProgram at offset loopStartPC n. -/
theorem loopPrologue_embed (n : ℕ) (pF : Program) :
    ∀ i, i < (loopPrologue n pF).length →
    (minimizeProgram n pF).getInstr (loopStartPC n + i) = (loopPrologue n pF).getInstr i := by
  intro i hi
  simp only [minimizeProgram, loopStartPC, setupPhaseLength, getInstr]
  -- Use omega to deal with the nested conditionals
  have hlen1 : n + 2 + i < (setupPhase n pF ++ loopPrologue n pF).length := by
    simp only [List.length_append, setupPhase_length, setupPhaseLength]; omega
  have hlen2 : ¬ n + 2 + i < (setupPhase n pF).length := by
    simp only [setupPhase_length, setupPhaseLength]; omega
  simp only [List.getElem?_append, hlen1, ↓reduceIte]
  simp only [List.length_append, setupPhase_length, loopPrologue_length, shiftJumps_length, loopEpilogue_length,
    setupPhaseLength, loopPrologueLength]
  have h1 : n + 2 + i < n + 2 + (loopPrologue n pF).length := by omega
  have hcond1 : n + 2 + i < n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 3 := by
    simp only [loopPrologue_length, loopPrologueLength] at h1; omega
  have hcond2 : n + 2 + i < n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length := by
    simp only [loopPrologue_length, loopPrologueLength] at h1; omega
  have hcond3 : ¬ n + 2 + i < n + 2 := by omega
  simp only [hcond1, hcond2, hcond3, hlen2, ↓reduceIte]
  have h2 : n + 2 + i - (n + 2) = i := by omega
  simp only [h2, hi, ↓reduceIte]

/-- pF.shiftJumps is embedded in minimizeProgram at offset pFOffset n pF. -/
theorem pF_shiftJumps_embed (n : ℕ) (pF : Program) :
    ∀ i, i < pF.length →
    (minimizeProgram n pF).getInstr (pFOffset n pF + i) = (pF.shiftJumps (pFOffset n pF)).getInstr i := by
  intro i hi
  simp only [minimizeProgram, pFOffset, setupPhaseLength, loopPrologueLength, getInstr]
  -- Setup length calculations
  let offset := n + 2 + (minimizationBase n pF + 1 + n + 1)
  have hoffset : offset = n + 2 + (minimizationBase n pF + 1 + n + 1) := rfl
  -- Position is offset + i
  have hpos : offset + i < (setupPhase n pF ++ loopPrologue n pF ++ pF.shiftJumps (n + 2 + (minimizationBase n pF + 1 + n + 1))).length := by
    simp only [List.length_append, setupPhase_length, loopPrologue_length, shiftJumps_length, setupPhaseLength, loopPrologueLength]; omega
  have hpos1 : ¬ offset + i < (setupPhase n pF).length := by
    simp only [setupPhase_length, setupPhaseLength]; omega
  have hpos2 : ¬ offset + i - (setupPhase n pF).length < (loopPrologue n pF).length := by
    simp only [setupPhase_length, loopPrologue_length, setupPhaseLength, loopPrologueLength]; omega
  have hpos3 : i < (pF.shiftJumps (n + 2 + (minimizationBase n pF + 1 + n + 1))).length := by
    simp only [shiftJumps_length]; exact hi
  have heq1 : offset + i - (n + 2) - (loopPrologue n pF).length = i := by
    simp only [loopPrologue_length, loopPrologueLength]; omega
  simp only [List.getElem?_append, hpos, ↓reduceIte]
  simp only [List.length_append, setupPhase_length, loopPrologue_length, shiftJumps_length, loopEpilogue_length,
    setupPhaseLength, loopPrologueLength]
  -- Discharge the nested conditionals
  have hcond1 : offset + i < offset + pF.length + 3 := by omega
  have hcond2 : offset + i < offset + pF.length := by omega
  have hcond3 : ¬ offset + i < offset := by omega
  have hcond4 : ¬ offset + i < n + 2 := by omega
  have heq2 : offset + i - offset = i := by omega
  simp only [hoffset] at hcond1 hcond2 hcond3 hcond4 heq2
  simp only [hcond1, hcond2, hcond3, hcond4, hpos1, hpos2, ↓reduceIte, heq2, hpos3]

/-! ## Loop Iteration Lemmas -/

/-- One complete loop iteration: from loopStart with counter = k,
    execute loop body once, either exit (if f returns 0) or return to loopStart with counter = k+1. -/
structure LoopIterationResult (n : ℕ) (pF : Program) (s : State) (k : ℕ) where
  /-- Final configuration after one iteration -/
  config : Config
  /-- Steps taken during this iteration -/
  steps : Steps (minimizeProgram n pF) ⟨loopStartPC n, s⟩ config
  /-- The value pF wrote to R[0] -/
  pF_result : ℕ
  /-- Either we exited to output, or we're back at loop start with incremented counter -/
  outcome : (config.pc = outputPC n pF ∧ pF_result = 0) ∨
            (config.pc = loopStartPC n ∧ config.state.read (counterReg n pF) = k + 1 ∧ pF_result ≠ 0)

/-- Execute one loop iteration when starting at loopStart. -/
noncomputable def loop_iteration (n : ℕ) (pF : Program) (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (k : ℕ)
    (hs_counter : s.read (counterReg n pF) = k)
    (hs_zero : s.read (zeroReg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hf_halts : Halts pF (List.ofFn (extendInputs inputs k))) :
    LoopIterationResult n pF s k := by
  -- Phase 1: Execute loopPrologue (straight-line)
  -- After loopPrologue: R[0..n-1] = saved inputs, R[n] = k
  have hsl_prologue : (loopPrologue n pF).isStraightLine = true := by
    simp only [loopPrologue, Program.isStraightLine, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
    simp only [Bool.and_eq_true]
    exact ⟨⟨clearRegisters_isStraightLine (minimizationBase n pF),
             copyRegisterRange_isStraightLine (savedInputsStart n pF) 0 n⟩, rfl⟩
  -- Get loopPrologue execution (use Classical.choose since we're defining data)
  let hPrologue := straightLine_halts_from_state hsl_prologue s
  let c_prologue := Classical.choose hPrologue
  have hspec_prologue := Classical.choose_spec hPrologue
  let hsteps_prologue := hspec_prologue.1
  let hhalted_prologue := hspec_prologue.2.1
  let hpc_prologue := hspec_prologue.2.2
  -- After prologue: R[i] = inputs i for i < n, R[n] = k
  have hR_after_prologue : ∀ i : Fin n, c_prologue.state.read i = inputs i := by
    intro i
    have := loopPrologue_restores_inputs n pF s c_prologue hsteps_prologue hhalted_prologue i
    rw [this]
    exact hs_saved i
  have hRn_after_prologue : c_prologue.state.read n = k := by
    have := loopPrologue_sets_counter_input n pF s c_prologue hsteps_prologue hhalted_prologue
    rw [this, hs_counter]
  have hcounter_after_prologue : c_prologue.state.read (counterReg n pF) = k := by
    have := loopPrologue_preserves_counter n pF s c_prologue hsteps_prologue hhalted_prologue
    rw [this, hs_counter]
  have hzero_after_prologue : c_prologue.state.read (zeroReg n pF) = 0 := by
    have := loopPrologue_preserves_zeroReg n pF s c_prologue hsteps_prologue hhalted_prologue
    rw [this, hs_zero]
  have hsaved_after_prologue : ∀ i : Fin n, c_prologue.state.read (savedInputsStart n pF + i) = inputs i := by
    intro i
    have := loopPrologue_preserves_savedInputs n pF s c_prologue hsteps_prologue hhalted_prologue i
    rw [this]
    exact hs_saved i
  -- Lift prologue steps to minimizeProgram
  have hembed_prologue := loopPrologue_embed n pF
  have hsteps_prologue_lifted : Steps (minimizeProgram n pF) ⟨loopStartPC n, s⟩
      ⟨loopStartPC n + c_prologue.pc, c_prologue.state⟩ :=
    Steps.straightLine_at_offset (loopStartPC n) hsl_prologue hembed_prologue hsteps_prologue
  -- After prologue, PC = loopStartPC n + loopPrologue.length = pFOffset n pF
  have hpc_after_prologue : loopStartPC n + c_prologue.pc = pFOffset n pF := by
    simp only [loopStartPC, pFOffset, setupPhaseLength, loopPrologueLength]
    rw [hpc_prologue, loopPrologue_length, loopPrologueLength]
  rw [hpc_after_prologue] at hsteps_prologue_lifted

  -- Phase 2: Execute pF
  -- c_prologue.state has the correct inputs for pF: R[0..n-1] = inputs, R[n] = k
  -- States agree on registers 0..pF.maxRegister since:
  -- - R[0..n-1] = inputs (from loopPrologue_restores_inputs)
  -- - R[n] = k (from loopPrologue_sets_counter_input)
  -- - R[n+1..maxReg] = 0 (cleared by loopPrologue, and initState also has 0)
  let initState := (Config.init (List.ofFn (extendInputs inputs k))).state
  have hagree_pF : c_prologue.state.agreeOn initState 0 pF.maxRegister := by
    intro r _ hr_hi
    -- Case split: r < n, r = n, or r > n
    by_cases hr_lt_n : r < n
    · -- Case r < n: both sides equal inputs r
      have hleft : c_prologue.state.read r = inputs ⟨r, hr_lt_n⟩ := hR_after_prologue ⟨r, hr_lt_n⟩
      have hright : initState.read r = inputs ⟨r, hr_lt_n⟩ := by
        unfold initState Config.init State.fromInputs State.read
        have hr_lt_n1 : r < n + 1 := Nat.lt_add_right 1 hr_lt_n
        simp only [List.getD, List.getElem?_ofFn, List.length_ofFn, hr_lt_n1, dite_true]
        simp only [Option.getD_some, extendInputs, Fin.snoc, hr_lt_n, dite_true]
        rfl
      rw [hleft, hright]
    · by_cases hr_eq_n : r = n
      · -- Case r = n: both sides equal k
        subst hr_eq_n
        have hleft : c_prologue.state.read r = k := hRn_after_prologue
        have hright : initState.read r = k := by
          unfold initState Config.init State.fromInputs State.read
          have hr_lt_r1 : r < r + 1 := Nat.lt_succ_self r
          simp only [List.getD, List.getElem?_ofFn, List.length_ofFn, hr_lt_r1, dite_true]
          simp only [Option.getD_some, extendInputs, Fin.snoc, Nat.lt_irrefl, dite_false]
          simp [Fin.last]
        rw [hleft, hright]
      · -- Case r > n: both sides equal 0
        have hr_gt_n : n < r := Nat.lt_of_le_of_ne (Nat.not_lt.mp hr_lt_n) (Ne.symm hr_eq_n)
        -- Right side: initState.read r = 0 (beyond List.ofFn length)
        have hright : initState.read r = 0 := by
          unfold initState Config.init State.fromInputs State.read
          have hr_ge_n1 : ¬ r < n + 1 := by omega
          simp only [List.getD, List.getElem?_ofFn, List.length_ofFn, hr_ge_n1, dite_false]
          simp only [Option.getD_none]
        -- Left side: c_prologue.state.read r = 0 (cleared by loopPrologue, then not touched)
        have hleft : c_prologue.state.read r = 0 := by
          have hr_le_base : r ≤ minimizationBase n pF := Nat.le_trans hr_hi (minimizationBase_ge_pF n pF)
          -- Register r is in clearRegisters range (0..base) but not touched by copy (0..n-1) or T (n)
          -- Use straight-line analysis: Z r at position r, no later writes to r
          have hk : r < (loopPrologue n pF).length := by
            simp only [loopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
              List.length]; omega
          have hwrite : (loopPrologue n pF)[r] = Instr.Z r := by
            simp only [loopPrologue]
            have h_in_clear : r < (clearRegisters (minimizationBase n pF)).length := by
              simp only [clearRegisters_length]; exact Nat.lt_succ_of_le hr_le_base
            have h_in_clear_ext : r < (clearRegisters (minimizationBase n pF) ++
                copyRegisterRange (savedInputsStart n pF) 0 n).length := by
              simp only [List.length_append, clearRegisters_length, copyRegisterRange_length]; omega
            rw [List.getElem_append_left h_in_clear_ext, List.getElem_append_left h_in_clear]
            simp only [Program.clearRegisters, List.getElem_map, List.getElem_range]
          have hnowrite : ∀ j (hj : j < (loopPrologue n pF).length), r < j →
              ((loopPrologue n pF)[j]).writesTo ≠ some r := by
            intro j hj hjr
            simp only [loopPrologue, List.length_append, clearRegisters_length, copyRegisterRange_length,
              List.length] at hj
            -- Simplify the goal by reducing the nested appends
            have h1 : j < (clearRegisters (minimizationBase n pF) ++ copyRegisterRange (savedInputsStart n pF) 0 n ++
                [Instr.T (counterReg n pF) n]).length := by
              simp only [List.length_append, clearRegisters_length, copyRegisterRange_length, List.length]; omega
            simp only [loopPrologue, List.getElem_append' h1]
            by_cases hj_clear1 : j < (clearRegisters (minimizationBase n pF) ++
                copyRegisterRange (savedInputsStart n pF) 0 n).length
            · simp only [hj_clear1, dite_true]
              by_cases hj_clear : j < minimizationBase n pF + 1
              · -- In clearRegisters: writes to j ≠ r since j > r
                have h2 : j < (clearRegisters (minimizationBase n pF)).length := by
                  simp only [clearRegisters_length]; exact hj_clear
                simp only [List.getElem_append_left h2, Program.clearRegisters, List.getElem_map,
                  List.getElem_range, Instr.writesTo, ne_eq, Option.some.injEq]
                intro heq; exact Nat.ne_of_lt hjr heq.symm
              · -- In copyRegisterRange
                have h2 : ¬ j < (clearRegisters (minimizationBase n pF)).length := by
                  simp only [clearRegisters_length]; exact hj_clear
                simp only [List.getElem_append_right h2, clearRegisters_length, Program.copyRegisterRange,
                  List.getElem_map, List.getElem_range, Nat.zero_add, Instr.writesTo, ne_eq, Option.some.injEq]
                intro heq; have : r < n := by omega; exact absurd this hr_lt_n
            · simp only [hj_clear1, dite_false]
              -- In [T counter n]: writes to n, but r > n
              have hidx : j - (clearRegisters (minimizationBase n pF) ++
                  copyRegisterRange (savedInputsStart n pF) 0 n).length = 0 := by
                simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear1 ⊢; omega
              simp only [hidx, List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
              intro heq; have : r = n := heq; exact hr_eq_n this.symm
          exact straightLine_zeros_register hsl_prologue s r r hk hwrite hnowrite
        rw [hleft, hright]

  -- Get pF execution from Config.init
  let c_pF := Classical.choose hf_halts
  have hspec_pF := Classical.choose_spec hf_halts
  let hsteps_pF := hspec_pF.1
  let hhalted_pF := hspec_pF.2
  -- Define c₂ explicitly to avoid rfl unification issues
  let c₂ : Config := ⟨0, c_prologue.state⟩
  have hpc_c2 : (Config.init (List.ofFn (extendInputs inputs k))).pc = c₂.pc := rfl
  -- Use Steps.agreeOn to get execution from c_prologue.state
  have hagree_pF_symm : initState.agreeOn c₂.state 0 pF.maxRegister := State.agreeOn_symm hagree_pF
  let hagree_result := Steps.agreeOn hsteps_pF hpc_c2 hagree_pF_symm
  let c_pF' := Classical.choose hagree_result
  have hspec_pF' := Classical.choose_spec hagree_result
  let hsteps_pF' := hspec_pF'.1
  let hpc_pF' := hspec_pF'.2.1

  -- Lift pF steps to minimizeProgram using shiftJumps_at_offset
  have hembed_pF := pF_shiftJumps_embed n pF
  have hsteps_pF_lifted := Steps.shiftJumps_at_offset (pFOffset n pF) hembed_pF hsteps_pF'

  -- Show that c_pF'.pc = pF.length (since pF is standard form)
  have hhalted_pF' : c_pF'.isHalted pF := by
    unfold Config.isHalted; rw [← hpc_pF']; exact hhalted_pF
  have hpc_pF'_length : c_pF'.pc = pF.length := by
    exact hpF_sf.pc_eq_length_of_halted hsteps_pF' (Nat.zero_le _) hhalted_pF'

  -- Simplify the lifted steps: we go from pFOffset to pFOffset + pF.length
  -- Note: c₂.state = c_prologue.state by definition
  have hsteps_pF_lifted' : Steps (minimizeProgram n pF) ⟨pFOffset n pF, c_prologue.state⟩
      ⟨pFOffset n pF + pF.length, c_pF'.state⟩ := by
    have h1 : pFOffset n pF + c₂.pc = pFOffset n pF := by simp only [Nat.add_zero]
    have h2 : pFOffset n pF + c_pF'.pc = pFOffset n pF + pF.length := by rw [hpc_pF'_length]
    rw [h1, h2] at hsteps_pF_lifted
    exact hsteps_pF_lifted

  -- Combined steps: from loopStartPC to pFOffset + pF.length
  have hsteps_to_epilogue : Steps (minimizeProgram n pF) ⟨loopStartPC n, s⟩
      ⟨pFOffset n pF + pF.length, c_pF'.state⟩ :=
    Relation.ReflTransGen.trans hsteps_prologue_lifted hsteps_pF_lifted'

  -- Phase 3: Execute loopEpilogue
  -- loopEpilogue = [J 0 zeroReg outputPC, S counter, J zeroReg zeroReg loopStartPC]

  -- Preservation: zeroReg and counter are unchanged by pF
  have hpF_max : pF.maxRegister ≤ minimizationBase n pF := minimizationBase_ge_pF n pF
  have hzero_after_pF : c_pF'.state.read (zeroReg n pF) = 0 := by
    have h := pF_preserves_zeroReg n pF c_prologue.state c_pF'.state hpF_max c_pF' hsteps_pF' hhalted_pF' rfl
    rw [h, hzero_after_prologue]
  have hcounter_after_pF : c_pF'.state.read (counterReg n pF) = k := by
    have h := pF_preserves_counter n pF c_prologue.state c_pF'.state hpF_max c_pF' hsteps_pF' hhalted_pF' rfl
    rw [h, hcounter_after_prologue]
  have hsaved_after_pF : ∀ i : Fin n, c_pF'.state.read (savedInputsStart n pF + i) = inputs i := by
    intro i
    have h := pF_preserves_savedInputs n pF c_prologue.state c_pF'.state hpF_max c_pF' hsteps_pF' hhalted_pF' rfl i
    rw [h, hsaved_after_prologue]

  -- The pF result is in R[0]
  let pF_result := c_pF'.state.read 0

  -- loopEpilogue starts at PC = pFOffset + pF.length
  let epilogueStartPC := pFOffset n pF + pF.length

  -- Verify the instruction at epilogueStartPC is J 0 zeroReg outputPC
  have hJ0_instr : (minimizeProgram n pF).getInstr epilogueStartPC =
      some (Instr.J 0 (zeroReg n pF) (outputPC n pF)) := by
    simp only [minimizeProgram, getInstr, epilogueStartPC, pFOffset, setupPhaseLength, loopPrologueLength]
    simp only [List.getElem?_append, List.length_append, setupPhase_length, loopPrologue_length,
      shiftJumps_length, loopEpilogue_length, outputPhase_length, setupPhaseLength, loopPrologueLength]
    -- The position is past setup, prologue, and pF, so it's in loopEpilogue at index 0
    simp only [show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length <
        n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 3 + 1 from by omega,
      show n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length <
        n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 3 from by omega,
      show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length <
        n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length from by omega,
      show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length < n + 2 from by omega,
      show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length - (n + 2) <
        minimizationBase n pF + 1 + n + 1 from by omega,
      show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length - (n + 2) -
        (minimizationBase n pF + 1 + n + 1) < pF.length from by omega,
      ite_true, ite_false, dite_true, dite_false,
      show n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length - (n + 2) -
        (minimizationBase n pF + 1 + n + 1) - pF.length = 0 from by omega,
      loopEpilogue, List.getElem?_cons_zero]

  -- Case split on whether pF returned 0
  by_cases hresult : pF_result = 0
  · -- Case: pF returned 0, exit loop via J 0 zeroReg outputPC
    -- R[0] = 0 = R[zeroReg], so the jump is taken
    have heq_zero : c_pF'.state.read 0 = c_pF'.state.read (zeroReg n pF) := by
      simp only [pF_result] at hresult
      rw [hresult, hzero_after_pF]
    have hstep_J0 : Step (minimizeProgram n pF) ⟨epilogueStartPC, c_pF'.state⟩
        ⟨outputPC n pF, c_pF'.state⟩ := Step.jump_eq hJ0_instr heq_zero
    have hsteps_exit := Relation.ReflTransGen.single hstep_J0
    have hsteps_total := Relation.ReflTransGen.trans hsteps_to_epilogue hsteps_exit
    exact ⟨⟨outputPC n pF, c_pF'.state⟩, hsteps_total, pF_result, Or.inl ⟨rfl, hresult⟩⟩

  · -- Case: pF returned non-zero, continue loop
    -- Execute J 0 zeroReg outputPC (doesn't jump since R[0] ≠ R[zeroReg])
    have hne_zero : c_pF'.state.read 0 ≠ c_pF'.state.read (zeroReg n pF) := by
      simp only [pF_result] at hresult
      rw [hzero_after_pF]; exact hresult
    have hstep_J0 : Step (minimizeProgram n pF) ⟨epilogueStartPC, c_pF'.state⟩
        ⟨epilogueStartPC + 1, c_pF'.state⟩ := Step.jump_ne hJ0_instr hne_zero

    -- Execute S counter
    have hS_instr : (minimizeProgram n pF).getInstr (epilogueStartPC + 1) =
        some (Instr.S (counterReg n pF)) := by
      simp only [minimizeProgram, getInstr, epilogueStartPC, pFOffset, setupPhaseLength, loopPrologueLength]
      simp only [List.getElem?_append, List.length_append, setupPhase_length, loopPrologue_length,
        shiftJumps_length, loopEpilogue_length, outputPhase_length, setupPhaseLength, loopPrologueLength]
      simp only [show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 1 <
          n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 3 + 1 from by omega,
        show n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 1 <
          n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 3 from by omega,
        show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 1 <
          n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length from by omega,
        show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 1 < n + 2 from by omega,
        show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 1 - (n + 2) <
          minimizationBase n pF + 1 + n + 1 from by omega,
        show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 1 - (n + 2) -
          (minimizationBase n pF + 1 + n + 1) < pF.length from by omega,
        ite_true, ite_false, dite_true, dite_false,
        show n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 1 - (n + 2) -
          (minimizationBase n pF + 1 + n + 1) - pF.length = 1 from by omega,
        loopEpilogue, List.getElem?_cons_succ, List.getElem?_cons_zero]
    let state_after_S := c_pF'.state.write (counterReg n pF) (c_pF'.state.read (counterReg n pF) + 1)
    have hstep_S : Step (minimizeProgram n pF) ⟨epilogueStartPC + 1, c_pF'.state⟩
        ⟨epilogueStartPC + 2, state_after_S⟩ := Step.succ hS_instr

    -- Execute J zeroReg zeroReg loopStartPC (unconditional jump)
    have hJ1_instr : (minimizeProgram n pF).getInstr (epilogueStartPC + 2) =
        some (Instr.J (zeroReg n pF) (zeroReg n pF) (loopStartPC n)) := by
      simp only [minimizeProgram, getInstr, epilogueStartPC, pFOffset, setupPhaseLength, loopPrologueLength]
      simp only [List.getElem?_append, List.length_append, setupPhase_length, loopPrologue_length,
        shiftJumps_length, loopEpilogue_length, outputPhase_length, setupPhaseLength, loopPrologueLength]
      simp only [show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 2 <
          n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 3 + 1 from by omega,
        show n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 2 <
          n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 3 from by omega,
        show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 2 <
          n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length from by omega,
        show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 2 < n + 2 from by omega,
        show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 2 - (n + 2) <
          minimizationBase n pF + 1 + n + 1 from by omega,
        show ¬ n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 2 - (n + 2) -
          (minimizationBase n pF + 1 + n + 1) < pF.length from by omega,
        ite_true, ite_false, dite_true, dite_false,
        show n + 2 + (minimizationBase n pF + 1 + n + 1) + pF.length + 2 - (n + 2) -
          (minimizationBase n pF + 1 + n + 1) - pF.length = 2 from by omega,
        loopEpilogue, List.getElem?_cons_succ, List.getElem?_cons_zero]
    have heq_self : state_after_S.read (zeroReg n pF) = state_after_S.read (zeroReg n pF) := rfl
    have hstep_J1 : Step (minimizeProgram n pF) ⟨epilogueStartPC + 2, state_after_S⟩
        ⟨loopStartPC n, state_after_S⟩ := Step.jump_eq hJ1_instr heq_self

    -- Combine all steps
    have hsteps_continue := Relation.ReflTransGen.head hstep_J0
        (Relation.ReflTransGen.head hstep_S (Relation.ReflTransGen.single hstep_J1))
    have hsteps_total := Relation.ReflTransGen.trans hsteps_to_epilogue hsteps_continue

    -- The counter is now k + 1
    have hcounter_k1 : state_after_S.read (counterReg n pF) = k + 1 := by
      simp only [state_after_S, State.write, State.read, Function.update_self, hcounter_after_pF]

    exact ⟨⟨loopStartPC n, state_after_S⟩, hsteps_total, pF_result, Or.inr ⟨rfl, hcounter_k1, hresult⟩⟩

/-! ## Main Halting Theorem -/

/-- After k loop iterations starting from loopStart, we reach loopStart with counter = k
    (if f hasn't returned 0 on any earlier iteration). -/
theorem loop_k_iterations (n : ℕ) (pF : Program) (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (s : State) (k : ℕ)
    (hs_counter : s.read (counterReg n pF) = 0)
    (hs_zero : s.read (zeroReg n pF) = 0)
    (hs_saved : ∀ i : Fin n, s.read (savedInputsStart n pF + i) = inputs i)
    (hf_halts_below : ∀ j < k, Halts pF (List.ofFn (extendInputs inputs j)))
    (hf_nonzero_below : ∀ j (hj : j < k), Result pF (List.ofFn (extendInputs inputs j))
        (hf_halts_below j hj) ≠ 0) :
    ∃ c, Steps (minimizeProgram n pF) ⟨loopStartPC n, s⟩ c ∧
         c.pc = loopStartPC n ∧
         c.state.read (counterReg n pF) = k := by
  sorry

/-- If μ f is defined, then minimizeProgram halts. -/
theorem minimizeProgram_halts (n : ℕ) (pF : Program)
    (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ)
    (hμ_dom : (μ f inputs).Dom) :
    Halts (minimizeProgram n pF) (List.ofFn inputs) := by
  sorry

/-! ## Converse: Halts → Dom -/

/-- If minimizeProgram halts, then μ f is defined. -/
theorem minimizeProgram_halts_imp_dom (n : ℕ) (pF : Program)
    (hpF_sf : pF.IsStandardForm)
    (f : (Fin (n + 1) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
        ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (minimizeProgram n pF) (List.ofFn inputs)) :
    (μ f inputs).Dom := by
  sorry

end Urm
