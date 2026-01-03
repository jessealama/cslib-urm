/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.PrimitiveRecursion.Preservation
import Urm.Embeddings
import Urm.Shift

/-! # Halting Proofs for Primitive Recursion

This file proves the halting properties of the primitive recursion witness program.

## Main results

- `primitiveRecursionProgram_halts`: If Pr domain, program halts
- `primitiveRecursionProgram_halts_imp_dom`: If program halts, Pr domain
-/

namespace Urm

open Program

/-! ## Embedding lemmas -/

/-- Setup phase is embedded at the start of the program. -/
theorem prSetupPhase_embed (n : ℕ) (pF pG : Program) :
    ∀ i, i < (prSetupPhase n pF pG).length →
    (primitiveRecursionProgram n pF pG).getInstr i = (prSetupPhase n pF pG).getInstr i := by
  intro i hi
  simp only [primitiveRecursionProgram, getInstr, List.getElem?_append, prSetupPhase_length,
    List.length_append, prBaseCasePhase_length, prLoopCheck_length, prLoopBody_length,
    prOutputPhase_length] at *
  -- i < setup length, so i is in the first chunk
  split_ifs with h1 h2 h3 h4 <;> try omega
  rfl

/-- Base case prologue is embedded after setup phase. -/
theorem prBaseCasePrologue_embed (n : ℕ) (pF pG : Program) :
    ∀ i, i < (prBaseCasePrologue n pF pG).length →
    (primitiveRecursionProgram n pF pG).getInstr (prBaseCasePC n + i) =
      (prBaseCasePrologue n pF pG).getInstr i := by
  intro i hi
  simp only [primitiveRecursionProgram, prBaseCasePC, prBaseCasePhase, getInstr, List.getElem?_append,
    prSetupPhase_length, prSetupPhaseLength, prBaseCasePrologue_length, prBaseCasePrologueLength,
    List.length_append, prBaseCasePhase_length, prLoopCheck_length, prLoopBody_length,
    prOutputPhase_length, shiftJumps_length] at *
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> try omega
  congr 1; omega

/-- Shifted pF is embedded in the base case phase. -/
theorem prPF_shiftJumps_embed (n : ℕ) (pF pG : Program) :
    ∀ i, i < pF.length →
    (primitiveRecursionProgram n pF pG).getInstr (prPFOffset n pF pG + i) =
      (pF.shiftJumps (prPFOffset n pF pG)).getInstr i := by
  intro i hi
  simp only [primitiveRecursionProgram, prPFOffset, prBaseCasePhase, getInstr, List.getElem?_append,
    prSetupPhase_length, prSetupPhaseLength, prBaseCasePrologueLength, prBaseCasePrologue_length,
    shiftJumps_length, List.length_append, prBaseCasePhase_length, prLoopCheck_length,
    prLoopBody_length, prOutputPhase_length]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 <;> try omega
  simp only [shiftJumps, getInstr, List.getElem?_map]
  -- The index calculation: after subtracting setup and prologue lengths, we get i
  have hsetup : n + 1 + 2 + (primitiveRecursionBase n pF pG + 1 + n) + i - (n + 1 + 2) =
      primitiveRecursionBase n pF pG + 1 + n + i := by omega
  have hprol : primitiveRecursionBase n pF pG + 1 + n + i - (primitiveRecursionBase n pF pG + 1 + n) = i := by
    omega
  simp only [hsetup, hprol]

/-- Loop check instruction embedding. -/
theorem prLoopCheck_embed (n : ℕ) (pF pG : Program) :
    (primitiveRecursionProgram n pF pG).getInstr (prLoopCheckPC n pF pG) =
      some (Instr.J (prCounterReg n pF pG) (prSavedYReg n pF pG) (prOutputPC n pF pG)) :=
  instr_at_loopCheck n pF pG

/-- Loop prologue is embedded at the start of loop body. -/
theorem prLoopPrologue_embed (n : ℕ) (pF pG : Program) :
    ∀ i, i < (prLoopPrologue n pF pG).length →
    (primitiveRecursionProgram n pF pG).getInstr (prLoopBodyPC n pF pG + i) =
      (prLoopPrologue n pF pG).getInstr i := by
  intro i hi
  simp only [primitiveRecursionProgram, prLoopBodyPC_eq, prLoopBody, getInstr, List.getElem?_append,
    prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length, prLoopPrologue_length,
    List.length_append, prLoopBody_length, prOutputPhase_length, shiftJumps_length,
    prLoopEpilogue_length] at *
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 <;> try omega
  congr 1; omega

/-- Shifted pG is embedded in the loop body. -/
theorem prPG_shiftJumps_embed (n : ℕ) (pF pG : Program) :
    ∀ i, i < pG.length →
    (primitiveRecursionProgram n pF pG).getInstr (prPGOffset n pF pG + i) =
      (pG.shiftJumps (prPGOffset n pF pG)).getInstr i := by
  intro i hi
  simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody, getInstr,
    List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length,
    prLoopPrologue_length, shiftJumps_length, List.length_append, prLoopBody_length,
    prOutputPhase_length, prLoopEpilogue_length]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 <;> try omega
  simp only [shiftJumps, getInstr, List.getElem?_map]
  -- Index calculation: subtract each segment length to get i
  simp only [prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength,
    prLoopPrologueLength, prLoopBodyLength, prLoopEpilogueLength] at *
  grind

/-- Output phase is at outputPC. -/
theorem prOutputPhase_embed (n : ℕ) (pF pG : Program) :
    (primitiveRecursionProgram n pF pG).getInstr (prOutputPC n pF pG) =
      some (Instr.T (prAccumulatorReg n pF pG) 0) :=
  instr_at_output n pF pG

/-! ## Setup Phase Execution -/

/-- Result of executing the setup phase. -/
structure SetupPhaseResult (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ) where
  config : Config
  steps : Steps (primitiveRecursionProgram n pF pG) (Config.init (List.ofFn (Fin.snoc inputs y))) config
  pc_eq : config.pc = prBaseCasePC n
  savedInputs_eq : ∀ i : Fin n, config.state.read (prSavedInputsStart n pF pG + i) = inputs i
  savedY_eq : config.state.read (prSavedYReg n pF pG) = y
  counter_eq : config.state.read (prCounterReg n pF pG) = 0
  zero_eq : config.state.read (prZeroReg n pF pG) = 0

/-- Execute the setup phase. -/
noncomputable def executeSetupPhase (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ) :
    SetupPhaseResult n pF pG inputs y :=
  let hsl_setup := prSetupPhase_isStraightLine n pF pG
  let initState := State.fromInputs (List.ofFn (Fin.snoc inputs y))
  let hExists := straightLine_halts_from_state hsl_setup initState
  let cSetup := Classical.choose hExists
  let hSpec := Classical.choose_spec hExists
  let hSetup_steps := hSpec.1
  let hSetup_halted := hSpec.2.1
  let hSetup_pc := hSpec.2.2

  -- Lift setup steps to primitiveRecursionProgram
  let hSetup_steps_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨0, initState⟩
      ⟨(prSetupPhase n pF pG).length, cSetup.state⟩ := by
    have hembed : ∀ i, i < (prSetupPhase n pF pG).length →
        (primitiveRecursionProgram n pF pG).getInstr (0 + i) =
        (prSetupPhase n pF pG).getInstr i := by
      intro i hi
      simp only [Nat.zero_add]
      exact prSetupPhase_embed n pF pG i hi
    have h := Steps.straightLine_at_offset 0 hsl_setup hembed hSetup_steps
    simp only [Nat.zero_add] at h
    rw [hSetup_pc] at h; exact h

  -- Establish invariants using Preservation lemmas
  let hSavedInputs : ∀ i : Fin n, cSetup.state.read (prSavedInputsStart n pF pG + i) = inputs i :=
    fun i => prSetupPhase_saves_inputs n pF pG inputs y initState rfl cSetup hSetup_steps hSetup_halted i
  let hSavedY : cSetup.state.read (prSavedYReg n pF pG) = y :=
    prSetupPhase_saves_y n pF pG inputs y initState rfl cSetup hSetup_steps hSetup_halted
  let hCounter : cSetup.state.read (prCounterReg n pF pG) = 0 :=
    prSetupPhase_counter_zero n pF pG inputs y initState rfl cSetup hSetup_steps hSetup_halted
  let hZero : cSetup.state.read (prZeroReg n pF pG) = 0 :=
    prSetupPhase_zero_zero n pF pG inputs y initState rfl cSetup hSetup_steps hSetup_halted

  -- PC after setup = prBaseCasePC
  let hSetup_pc_basecase : (prSetupPhase n pF pG).length = prBaseCasePC n := by
    simp only [prBaseCasePC, prSetupPhase_length]

  { config := ⟨prBaseCasePC n, cSetup.state⟩
    steps := by rw [← hSetup_pc_basecase]; exact hSetup_steps_lifted
    pc_eq := rfl
    savedInputs_eq := hSavedInputs
    savedY_eq := hSavedY
    counter_eq := hCounter
    zero_eq := hZero }

/-! ## Base Case Phase Execution -/

/-- Result of executing the base case phase. -/
structure BaseCasePhaseResult (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (hpF_halts : Halts pF (List.ofFn inputs)) where
  config : Config
  steps : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩ config
  pc_eq : config.pc = prLoopCheckPC n pF pG
  accumulator_eq : config.state.read (prAccumulatorReg n pF pG) = Result pF (List.ofFn inputs) hpF_halts
  savedInputs_preserved : ∀ i : Fin n, config.state.read (prSavedInputsStart n pF pG + i) =
    s.read (prSavedInputsStart n pF pG + i)
  savedY_preserved : config.state.read (prSavedYReg n pF pG) = s.read (prSavedYReg n pF pG)
  counter_preserved : config.state.read (prCounterReg n pF pG) = s.read (prCounterReg n pF pG)
  zero_preserved : config.state.read (prZeroReg n pF pG) = s.read (prZeroReg n pF pG)

/-- Execute the base case phase. -/
noncomputable def executeBaseCasePhase (n : ℕ) (pF pG : Program) (hpF_sf : pF.IsStandardForm)
    (inputs : Fin n → ℕ) (y : ℕ) (s : State)
    (hs_saved : ∀ i : Fin n, s.read (prSavedInputsStart n pF pG + i) = inputs i)
    (hpF_halts : Halts pF (List.ofFn inputs)) :
    BaseCasePhaseResult n pF pG inputs y s hpF_halts := by
  -- Phase 1: Execute prBaseCasePrologue (straight-line)
  have hsl_prologue := prBaseCasePrologue_isStraightLine n pF pG
  let hPrologue := straightLine_halts_from_state hsl_prologue s
  let c_prologue := Classical.choose hPrologue
  have hspec_prologue := Classical.choose_spec hPrologue
  let hsteps_prologue := hspec_prologue.1
  let hhalted_prologue := hspec_prologue.2.1
  let hpc_prologue := hspec_prologue.2.2

  -- Lift prologue steps to primitiveRecursionProgram
  have hembed_prologue : ∀ i, i < (prBaseCasePrologue n pF pG).length →
      (primitiveRecursionProgram n pF pG).getInstr (prBaseCasePC n + i) =
      (prBaseCasePrologue n pF pG).getInstr i := prBaseCasePrologue_embed n pF pG
  have hsteps_prologue_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩
      ⟨prBaseCasePC n + c_prologue.pc, c_prologue.state⟩ :=
    Steps.straightLine_at_offset (prBaseCasePC n) hsl_prologue hembed_prologue hsteps_prologue

  -- After prologue, PC is at prPFOffset
  have hpc_after_prologue : prBaseCasePC n + c_prologue.pc = prPFOffset n pF pG := by
    simp only [prBaseCasePC, prPFOffset, prSetupPhaseLength, prBaseCasePrologueLength]
    rw [hpc_prologue, prBaseCasePrologue_length, prBaseCasePrologueLength]
  rw [hpc_after_prologue] at hsteps_prologue_lifted

  -- Phase 2: Execute pF (shifted)
  -- After prologue, R[0..n-1] = inputs (restored from saved copies)
  -- pF executes and produces result in R[0]

  -- Get pF halting configuration
  let cpF := Classical.choose hpF_halts
  have hspec_pF := Classical.choose_spec hpF_halts
  let hsteps_pF := hspec_pF.1
  let hhalted_pF := hspec_pF.2

  -- After prologue, R[0..n-1] = inputs (restored from saved copies) and R[n..base] = 0
  have hR_after_prologue : ∀ i : Fin n, c_prologue.state.read i = inputs i :=
    fun i => prBaseCasePrologue_restores_inputs n pF pG s c_prologue hsteps_prologue hhalted_prologue i hs_saved

  -- State agreement: c_prologue.state agrees with initState on 0..pF.maxRegister
  let initState := (Config.init (List.ofFn inputs)).state
  have hagree_pF : c_prologue.state.agreeOn initState 0 pF.maxRegister := by
    intro r _ hr_hi
    by_cases hr_lt_n : r < n
    · -- Case r < n: both sides equal inputs r
      have hleft : c_prologue.state.read r = inputs ⟨r, hr_lt_n⟩ := hR_after_prologue ⟨r, hr_lt_n⟩
      have hright : initState.read r = inputs ⟨r, hr_lt_n⟩ := by
        unfold initState Config.init State.fromInputs State.read
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr_lt_n, dite_true]
        simp only [Option.getD_some]; rfl
      rw [hleft, hright]
    · -- Case r >= n: both sides equal 0
      have hr_ge_n : n ≤ r := Nat.not_lt.mp hr_lt_n
      -- Right side: initState.read r = 0 (beyond List.ofFn length)
      have hright : initState.read r = 0 := by
        unfold initState Config.init State.fromInputs State.read
        have hr_ge_n' : ¬ r < n := hr_lt_n
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr_ge_n', dite_false, Option.getD_none]
      -- Left side: c_prologue.state.read r = 0 (cleared by prologue, not overwritten)
      have hleft : c_prologue.state.read r = 0 := by
        have hr_le_base : r ≤ primitiveRecursionBase n pF pG :=
          Nat.le_trans hr_hi (primitiveRecursionBase_ge_pF n pF pG)
        -- Use straightLine_zeros_register: Z r at position r, no later writes to r
        have hk : r < (prBaseCasePrologue n pF pG).length := by
          simp only [prBaseCasePrologue, List.length_append, clearRegisters_length, copyRegisterRange_length]
          omega
        have hwrite : (prBaseCasePrologue n pF pG)[r] = Instr.Z r := by
          simp only [prBaseCasePrologue]
          have h_in_clear : r < (clearRegisters (primitiveRecursionBase n pF pG)).length := by
            simp only [clearRegisters_length]; exact Nat.lt_succ_of_le hr_le_base
          have h_in_clear_ext : r < (clearRegisters (primitiveRecursionBase n pF pG) ++
              copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length := by
            simp only [List.length_append, clearRegisters_length, copyRegisterRange_length]; omega
          rw [List.getElem_append_left h_in_clear_ext, List.getElem_append_left h_in_clear]
          simp only [Program.clearRegisters, List.getElem_map, List.getElem_range]
        have hnowrite : ∀ j (hj : j < (prBaseCasePrologue n pF pG).length), r < j →
            ((prBaseCasePrologue n pF pG)[j]).writesTo ≠ some r := by
          intro j hj hjr
          simp only [prBaseCasePrologue, List.length_append, clearRegisters_length,
            copyRegisterRange_length] at hj
          simp only [prBaseCasePrologue]
          by_cases hj_clear1 : j < (clearRegisters (primitiveRecursionBase n pF pG) ++
              copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length
          · rw [List.getElem_append_left hj_clear1]
            by_cases hj_clear : j < primitiveRecursionBase n pF pG + 1
            · -- In clearRegisters: writes to j ≠ r since j > r
              have h2 : j < (clearRegisters (primitiveRecursionBase n pF pG)).length := by
                simp only [clearRegisters_length]; exact hj_clear
              rw [List.getElem_append_left h2]
              simp only [Program.clearRegisters, List.getElem_map, List.getElem_range,
                Instr.writesTo, ne_eq, Option.some.injEq]
              intro heq; exact Nat.ne_of_lt hjr heq.symm
            · -- In copyRegisterRange: writes to 0 + (j - base - 1) < n ≤ r
              have h2 : ¬ j < (clearRegisters (primitiveRecursionBase n pF pG)).length := by
                simp only [clearRegisters_length]; omega
              have h2' : (clearRegisters (primitiveRecursionBase n pF pG)).length ≤ j := Nat.not_lt.mp h2
              rw [List.getElem_append_right h2']
              simp only [clearRegisters_length, Program.copyRegisterRange,
                List.getElem_map, List.getElem_range, Nat.zero_add, Instr.writesTo, ne_eq, Option.some.injEq]
              simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear1
              omega
          · -- Past prBaseCasePrologue - no more instructions
            simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear1
            omega
        exact straightLine_zeros_register hsl_prologue s r r hk hwrite hnowrite
      rw [hleft, hright]

  -- Define c₂ to use agreeOn
  let c₂ : Config := ⟨0, c_prologue.state⟩
  have hpc_c2 : (Config.init (List.ofFn inputs)).pc = c₂.pc := rfl

  -- Use Steps.agreeOn to get execution from c_prologue.state
  have hagree_pF_symm : initState.agreeOn c₂.state 0 pF.maxRegister := State.agreeOn_symm hagree_pF
  let hagree_result := Steps.agreeOn hsteps_pF hpc_c2 hagree_pF_symm
  let c_pF' := Classical.choose hagree_result
  have hspec_pF' := Classical.choose_spec hagree_result
  let hsteps_pF' := hspec_pF'.1
  let hpc_pF' := hspec_pF'.2.1
  have hagree_pF' : cpF.state.agreeOn c_pF'.state 0 pF.maxRegister := hspec_pF'.2.2

  -- pF_result_eq: c_pF'.state.read 0 = Result pF ... hpF_halts
  have hpF_result_eq : c_pF'.state.read 0 = Result pF (List.ofFn inputs) hpF_halts := by
    have h_agree_at_0 := hagree_pF' 0 (Nat.zero_le 0) (Nat.zero_le _)
    simp only [Result, State.output]
    exact h_agree_at_0.symm

  -- Lift pF steps to primitiveRecursionProgram using shiftJumps_at_offset
  have hembed_pF := prPF_shiftJumps_embed n pF pG
  have hsteps_pF_lifted := Steps.shiftJumps_at_offset (prPFOffset n pF pG) hembed_pF hsteps_pF'

  -- Show that c_pF'.pc = pF.length (since pF is standard form)
  have hhalted_pF' : c_pF'.isHalted pF := by
    unfold Config.isHalted; rw [← hpc_pF']; exact hhalted_pF
  have hpc_pF'_length : c_pF'.pc = pF.length :=
    hpF_sf.pc_eq_length_of_halted hsteps_pF' (Nat.zero_le _) hhalted_pF'

  -- Simplify the lifted steps: from prPFOffset to prPFOffset + pF.length
  have hsteps_pF_lifted' : Steps (primitiveRecursionProgram n pF pG) ⟨prPFOffset n pF pG, c_prologue.state⟩
      ⟨prPFOffset n pF pG + pF.length, c_pF'.state⟩ := by
    have h1 : prPFOffset n pF pG + c₂.pc = prPFOffset n pF pG := by simp
    have h2 : prPFOffset n pF pG + c_pF'.pc = prPFOffset n pF pG + pF.length := by rw [hpc_pF'_length]
    rw [h1, h2] at hsteps_pF_lifted
    exact hsteps_pF_lifted

  -- Combined steps: from prBaseCasePC to prPFOffset + pF.length
  have hsteps_to_T : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩
      ⟨prPFOffset n pF pG + pF.length, c_pF'.state⟩ :=
    Relation.ReflTransGen.trans hsteps_prologue_lifted hsteps_pF_lifted'

  -- Phase 3: Execute T instruction (copy R[0] to accumulator)
  -- prPFOffset + pF.length = prBaseCasePC + prBaseCasePrologueLength + pF.length
  -- which is where the T instruction is located

  have hT_pc : prPFOffset n pF pG + pF.length = prLoopCheckPC n pF pG - 1 := by
    simp only [prPFOffset, prLoopCheckPC, prSetupPhaseLength, prBaseCasePrologueLength,
      prBaseCasePhaseLength]
    omega

  -- The T instruction copies R[0] to accumulator
  have hT_instr : (primitiveRecursionProgram n pF pG).getInstr (prPFOffset n pF pG + pF.length) =
      some (Instr.T 0 (prAccumulatorReg n pF pG)) := by
    -- Position is prSetupPhaseLength + prBaseCasePrologueLength + pF.length
    -- which is in prBaseCasePhase at index prBaseCasePrologueLength + pF.length
    -- prBaseCasePhase = prBaseCasePrologue ++ pF.shiftJumps ++ [T 0 acc]
    -- At index prBaseCasePrologueLength + pF.length, we access [T 0 acc][0]
    simp only [primitiveRecursionProgram, getInstr, prPFOffset, prBaseCasePhase]
    have h_not_in_setup : ¬(prSetupPhaseLength n + prBaseCasePrologueLength n pF pG + pF.length <
        (prSetupPhase n pF pG).length) := by
      simp only [prSetupPhase_length, prSetupPhaseLength]; omega
    have h_in_basecase : prSetupPhaseLength n + prBaseCasePrologueLength n pF pG + pF.length <
        (prSetupPhase n pF pG ++ (prBaseCasePrologue n pF pG ++
          pF.shiftJumps (prSetupPhaseLength n + prBaseCasePrologueLength n pF pG) ++
          [Instr.T 0 (prAccumulatorReg n pF pG)])).length := by
      simp only [List.length_append, prSetupPhase_length, prBaseCasePrologue_length,
        shiftJumps_length, List.length, prSetupPhaseLength, prBaseCasePrologueLength]
      omega
    rw [List.getElem?_append h_in_basecase, List.getElem?_append_right (Nat.not_lt.mp h_not_in_setup)]
    simp only [prSetupPhase_length, prSetupPhaseLength]
    -- Now index is prBaseCasePrologueLength + pF.length within prBaseCasePrologue ++ pF.shiftJumps ++ [T]
    have h_not_in_prologue_pf : ¬(prBaseCasePrologueLength n pF pG + pF.length <
        (prBaseCasePrologue n pF pG ++ pF.shiftJumps (prSetupPhaseLength n + prBaseCasePrologueLength n pF pG)).length) := by
      simp only [List.length_append, prBaseCasePrologue_length, shiftJumps_length,
        prBaseCasePrologueLength]; omega
    have h_in_T : prBaseCasePrologueLength n pF pG + pF.length <
        (prBaseCasePrologue n pF pG ++ pF.shiftJumps (prSetupPhaseLength n + prBaseCasePrologueLength n pF pG) ++
          [Instr.T 0 (prAccumulatorReg n pF pG)]).length := by
      simp only [List.length_append, prBaseCasePrologue_length, shiftJumps_length,
        List.length, prBaseCasePrologueLength]; omega
    rw [List.getElem?_append h_in_T, List.getElem?_append_right (Nat.not_lt.mp h_not_in_prologue_pf)]
    simp only [List.length_append, prBaseCasePrologue_length, shiftJumps_length, prBaseCasePrologueLength]
    have hidx : prBaseCasePrologueLength n pF pG + pF.length -
        (prBaseCasePrologueLength n pF pG + pF.length) = 0 := by omega
    simp only [hidx, List.getElem?_cons_zero]

  -- Execute the T step
  have hstep_T : Step (primitiveRecursionProgram n pF pG) ⟨prPFOffset n pF pG + pF.length, c_pF'.state⟩
      ⟨prPFOffset n pF pG + pF.length + 1, c_pF'.state.write (prAccumulatorReg n pF pG) (c_pF'.state.read 0)⟩ :=
    Step.transfer hT_instr

  have hT_pc_eq : prPFOffset n pF pG + pF.length + 1 = prLoopCheckPC n pF pG := by
    simp only [prPFOffset, prLoopCheckPC, prSetupPhaseLength, prBaseCasePrologueLength,
      prBaseCasePhaseLength]
    omega

  -- Final state
  let finalState := c_pF'.state.write (prAccumulatorReg n pF pG) (c_pF'.state.read 0)

  -- Combined steps to loop check
  have hsteps_final : Steps (primitiveRecursionProgram n pF pG) ⟨prBaseCasePC n, s⟩
      ⟨prLoopCheckPC n pF pG, finalState⟩ := by
    have h := Relation.ReflTransGen.trans hsteps_to_T (Relation.ReflTransGen.single hstep_T)
    rw [hT_pc_eq] at h
    exact h

  -- Preservation lemmas for high registers through pF execution
  have hpF_preserves_high : ∀ r, pF.maxRegister < r → c_pF'.state.read r = c_prologue.state.read r := by
    intro r hr
    exact pF_preserves_high_reg pF c_prologue.state c_pF'.state c_pF' hsteps_pF' rfl r hr

  have hprologue_preserves : ∀ r, primitiveRecursionBase n pF pG < r → c_prologue.state.read r = s.read r :=
    fun r hr => prBaseCasePrologue_preserves_high_register n pF pG s c_prologue hsteps_prologue hhalted_prologue r hr

  -- Build the result
  { config := ⟨prLoopCheckPC n pF pG, finalState⟩
    steps := hsteps_final
    pc_eq := rfl
    accumulator_eq := by
      simp only [finalState, State.write, State.read]
      split_ifs with heq
      · exact hpF_result_eq
      · exact (heq rfl).elim
    savedInputs_preserved := fun i => by
      simp only [finalState, State.write, State.read]
      split_ifs with heq
      · have := prSavedInputsStart_gt_base n pF pG
        have := prAccumulatorReg_gt_base n pF pG
        simp only [prSavedInputsStart, prAccumulatorReg] at this heq ⊢
        omega
      · have h1 := pF_preserves_prSavedInputs n pF pG c_prologue.state c_pF'.state c_pF' hsteps_pF' rfl i
        have h2 := hprologue_preserves (prSavedInputsStart n pF pG + i) (prSavedInputsStart_gt_base n pF pG)
        rw [h1, h2]
    savedY_preserved := by
      simp only [finalState, State.write, State.read]
      split_ifs with heq
      · have := prSavedYReg_gt_base n pF pG
        have := prAccumulatorReg_gt_base n pF pG
        simp only [prSavedYReg, prAccumulatorReg] at this heq ⊢
        omega
      · have h1 := pF_preserves_prSavedYReg n pF pG c_prologue.state c_pF'.state c_pF' hsteps_pF' rfl
        have h2 := hprologue_preserves (prSavedYReg n pF pG) (prSavedYReg_gt_base n pF pG)
        rw [h1, h2]
    counter_preserved := by
      simp only [finalState, State.write, State.read]
      split_ifs with heq
      · have := prCounterReg_gt_base n pF pG
        have := prAccumulatorReg_gt_base n pF pG
        simp only [prCounterReg, prAccumulatorReg] at this heq ⊢
        omega
      · have h1 := pF_preserves_prCounterReg n pF pG c_prologue.state c_pF'.state c_pF' hsteps_pF' rfl
        have h2 := hprologue_preserves (prCounterReg n pF pG) (prCounterReg_gt_base n pF pG)
        rw [h1, h2]
    zero_preserved := by
      simp only [finalState, State.write, State.read]
      split_ifs with heq
      · have := prZeroReg_gt_base n pF pG
        have := prAccumulatorReg_gt_base n pF pG
        simp only [prZeroReg, prAccumulatorReg] at this heq ⊢
        omega
      · have h1 := pF_preserves_prZeroReg n pF pG c_prologue.state c_pF'.state c_pF' hsteps_pF' rfl
        have h2 := hprologue_preserves (prZeroReg n pF pG) (prZeroReg_gt_base n pF pG)
        rw [h1, h2] }

/-! ## Loop Iteration -/

/-- Result of a single loop iteration from loopCheckPC.
    Tracks whether we exited (counter = savedY) or continued (counter < savedY). -/
structure LoopIterationResult (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (k : ℕ) (accBefore : ℕ) (hpG_halts : Halts pG (List.ofFn (extendInputsForG inputs k accBefore))) where
  config : Config
  steps : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩ config
  /-- Either we exited to output (k = y) or we're back at loop check with counter = k+1 -/
  outcome : (config.pc = prOutputPC n pF pG ∧ k = y) ∨
            (config.pc = prLoopCheckPC n pF pG ∧ k < y)
  /-- In continue case, counter is k+1 -/
  counter_next : config.pc = prLoopCheckPC n pF pG →
    config.state.read (prCounterReg n pF pG) = k + 1
  /-- In continue case, accumulator updated -/
  accumulator_updated : config.pc = prLoopCheckPC n pF pG →
    config.state.read (prAccumulatorReg n pF pG) =
      Result pG (List.ofFn (extendInputsForG inputs k accBefore)) hpG_halts
  /-- Saved inputs preserved -/
  savedInputs_preserved : ∀ i : Fin n,
    config.state.read (prSavedInputsStart n pF pG + i) = s.read (prSavedInputsStart n pF pG + i)
  /-- SavedY preserved -/
  savedY_preserved : config.state.read (prSavedYReg n pF pG) = s.read (prSavedYReg n pF pG)
  /-- Zero register preserved -/
  zero_preserved : config.state.read (prZeroReg n pF pG) = s.read (prZeroReg n pF pG)

/-- Execute a single loop iteration. -/
noncomputable def loop_iteration (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (inputs : Fin n → ℕ) (y : ℕ) (s : State) (k : ℕ) (accBefore : ℕ)
    (hs_counter : s.read (prCounterReg n pF pG) = k)
    (hs_savedY : s.read (prSavedYReg n pF pG) = y)
    (hs_acc : s.read (prAccumulatorReg n pF pG) = accBefore)
    (hs_zero : s.read (prZeroReg n pF pG) = 0)
    (hs_saved : ∀ i : Fin n, s.read (prSavedInputsStart n pF pG + i) = inputs i)
    (hpG_halts : Halts pG (List.ofFn (extendInputsForG inputs k accBefore))) :
    LoopIterationResult n pF pG inputs y s k accBefore hpG_halts := by
  -- The loop check instruction: J counter savedY outputPC
  have hJ_instr := loopCheck_embed n pF pG

  -- Branch on whether k = y or k < y
  by_cases hky : k = y
  · -- Case k = y: counter = savedY, so J instruction jumps to outputPC
    have heq : s.read (prCounterReg n pF pG) = s.read (prSavedYReg n pF pG) := by
      rw [hs_counter, hs_savedY, hky]
    have hstep_J : Step (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prOutputPC n pF pG, s⟩ := Step.jump_eq hJ_instr heq

    exact {
      config := ⟨prOutputPC n pF pG, s⟩
      steps := Relation.ReflTransGen.single hstep_J
      outcome := Or.inl ⟨rfl, hky⟩
      counter_next := fun hpc => by simp only [hpc] at *; omega
      accumulator_updated := fun hpc => by simp only [hpc] at *; omega
      savedInputs_preserved := fun i => rfl
      savedY_preserved := rfl
      zero_preserved := rfl
    }

  · -- Case k ≠ y: counter ≠ savedY, so J instruction doesn't jump, proceed to loop body
    have hne : s.read (prCounterReg n pF pG) ≠ s.read (prSavedYReg n pF pG) := by
      rw [hs_counter, hs_savedY]; exact hky
    have hstep_J : Step (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prLoopCheckPC n pF pG + 1, s⟩ := Step.jump_ne hJ_instr hne

    have hLoopBodyPC_eq : prLoopCheckPC n pF pG + 1 = prLoopBodyPC n pF pG := by
      simp only [prLoopBodyPC]; omega

    -- Execute prLoopPrologue (straight-line)
    have hsl_prologue := prLoopPrologue_isStraightLine n pF pG
    let hPrologue := straightLine_halts_from_state hsl_prologue s
    let c_prologue := Classical.choose hPrologue
    have hspec_prologue := Classical.choose_spec hPrologue
    let hsteps_prologue := hspec_prologue.1
    let hhalted_prologue := hspec_prologue.2.1
    let hpc_prologue := hspec_prologue.2.2

    -- Lift prologue steps to primitiveRecursionProgram
    have hembed_prologue := prLoopPrologue_embed n pF pG
    have hsteps_prologue_lifted : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopBodyPC n pF pG, s⟩
        ⟨prLoopBodyPC n pF pG + c_prologue.pc, c_prologue.state⟩ :=
      Steps.straightLine_at_offset (prLoopBodyPC n pF pG) hsl_prologue hembed_prologue hsteps_prologue

    -- After prologue, PC is at prPGOffset
    have hpc_after_prologue : prLoopBodyPC n pF pG + c_prologue.pc = prPGOffset n pF pG := by
      simp only [prLoopBodyPC, prPGOffset, prLoopCheckPC, prLoopPrologueLength]
      rw [hpc_prologue, prLoopPrologue_length, prLoopPrologueLength]
    rw [hpc_after_prologue] at hsteps_prologue_lifted

    -- Steps from J to end of prologue
    have hsteps_to_prologue_end : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prPGOffset n pF pG, c_prologue.state⟩ := by
      have h1 := Relation.ReflTransGen.single hstep_J
      rw [hLoopBodyPC_eq] at h1
      exact Relation.ReflTransGen.trans h1 hsteps_prologue_lifted

    -- TODO: Similar to executeBaseCasePhase - need to show state agreement and lift pG
    sorry

/-! ## K Iterations -/

/-- Result of k loop iterations. -/
structure LoopKIterationsResult (n : ℕ) (pF pG : Program) (inputs : Fin n → ℕ) (y : ℕ)
    (s : State) (k : ℕ) where
  config : Config
  steps : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩ config
  pc_eq : config.pc = prLoopCheckPC n pF pG
  counter_eq : config.state.read (prCounterReg n pF pG) = k
  savedInputs_eq : ∀ i : Fin n, config.state.read (prSavedInputsStart n pF pG + i) = inputs i
  savedY_eq : config.state.read (prSavedYReg n pF pG) = y
  zero_eq : config.state.read (prZeroReg n pF pG) = 0

/-- Execute k loop iterations. -/
noncomputable def loop_k_iterations (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ) (s : State) (k : ℕ)
    (hk_le_y : k ≤ y)
    (hs_counter : s.read (prCounterReg n pF pG) = 0)
    (hs_savedY : s.read (prSavedYReg n pF pG) = y)
    (hs_zero : s.read (prZeroReg n pF pG) = 0)
    (hs_saved : ∀ i : Fin n, s.read (prSavedInputsStart n pF pG + i) = inputs i)
    (hPr_dom_k : (Pr f g (Fin.snoc inputs k)).Dom)
    (hs_acc : s.read (prAccumulatorReg n pF pG) = (Pr f g (Fin.snoc inputs 0)).get (Pr_dom_of_dom_le inputs hPr_dom_k (Nat.zero_le k))) :
    LoopKIterationsResult n pF pG inputs y s k := by
  sorry

/-! ## Output Phase -/

/-- Output phase halts and copies accumulator to R[0]. -/
theorem outputPhase_halts (n : ℕ) (pF pG : Program) (s : State) :
    ∃ c, Steps (primitiveRecursionProgram n pF pG) ⟨prOutputPC n pF pG, s⟩ c ∧
         c.isHalted (primitiveRecursionProgram n pF pG) ∧
         c.state.read 0 = s.read (prAccumulatorReg n pF pG) := by
  use ⟨prOutputPC n pF pG + 1, s.write 0 (s.read (prAccumulatorReg n pF pG))⟩
  constructor
  · apply Steps.single
    apply Step.trans
    exact prOutputPhase_embed n pF pG
  · constructor
    · simp only [Config.isHalted, primitiveRecursionProgram_length]
      omega
    · simp only [State.read, State.write, Function.update_self]

/-! ## Main Halting Theorems -/

/-- If Pr is defined, the primitive recursion program halts. -/
theorem primitiveRecursionProgram_halts (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ)
    (hPr_dom : (Pr f g (Fin.snoc inputs y)).Dom) :
    Halts (primitiveRecursionProgram n pF pG) (List.ofFn (Fin.snoc inputs y)) := by
  sorry

/-- If the primitive recursion program halts, Pr is defined. -/
theorem primitiveRecursionProgram_halts_imp_dom (n : ℕ) (pF pG : Program)
    (hpF_sf : pF.IsStandardForm) (hpG_sf : pG.IsStandardForm)
    (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (hpF_spec : ∀ args, (Halts pF (List.ofFn args) ↔ (f args).Dom) ∧
      ∀ hH hD, Result pF (List.ofFn args) hH = (f args).get hD)
    (hpG_spec : ∀ args, (Halts pG (List.ofFn args) ↔ (g args).Dom) ∧
      ∀ hH hD, Result pG (List.ofFn args) hH = (g args).get hD)
    (inputs : Fin n → ℕ) (y : ℕ)
    (hHalts : Halts (primitiveRecursionProgram n pF pG) (List.ofFn (Fin.snoc inputs y))) :
    (Pr f g (Fin.snoc inputs y)).Dom := by
  sorry

end Urm
