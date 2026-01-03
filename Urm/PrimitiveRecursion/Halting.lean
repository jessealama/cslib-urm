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

    -- Phase 2: Execute pG (shifted)
    -- Get pG halting configuration
    let cpG := Classical.choose hpG_halts
    have hspec_pG := Classical.choose_spec hpG_halts
    let hsteps_pG := hspec_pG.1
    let hhalted_pG := hspec_pG.2

    -- After prologue, R[0..n-1] = inputs, R[n] = k, R[n+1] = accBefore
    have hR_after_prologue : ∀ i : Fin n, c_prologue.state.read i = inputs i :=
      fun i => prLoopPrologue_restores_inputs n pF pG s c_prologue hsteps_prologue hhalted_prologue i hs_saved

    have hRn_after_prologue : c_prologue.state.read n = k :=
      prLoopPrologue_sets_Rn n pF pG s c_prologue hsteps_prologue hhalted_prologue hs_counter

    have hRn1_after_prologue : c_prologue.state.read (n + 1) = accBefore :=
      prLoopPrologue_sets_Rn1 n pF pG s c_prologue hsteps_prologue hhalted_prologue hs_acc

    -- State agreement: c_prologue.state agrees with initStateG on 0..pG.maxRegister
    let initStateG := (Config.init (List.ofFn (extendInputsForG inputs k accBefore))).state
    have hagree_pG : c_prologue.state.agreeOn initStateG 0 pG.maxRegister := by
      intro r _ hr_hi
      by_cases hr_lt_n : r < n
      · -- Case r < n: both sides equal inputs r
        have hleft : c_prologue.state.read r = inputs ⟨r, hr_lt_n⟩ := hR_after_prologue ⟨r, hr_lt_n⟩
        have hright : initStateG.read r = inputs ⟨r, hr_lt_n⟩ := by
          unfold initStateG Config.init State.fromInputs State.read extendInputsForG
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          have hlen : r < (n + 2) := by omega
          simp only [hlen, dite_true]
          simp only [Fin.snoc, Fin.castSucc]
          have hr_ne_n1 : r ≠ n + 1 := by omega
          have hr_ne_n : r ≠ n := by omega
          simp only [hr_ne_n1, if_false, hr_ne_n, if_false]
          simp only [Fin.val_mk, hr_lt_n, dite_true]
          rfl
        rw [hleft, hright]
      · by_cases hr_eq_n : r = n
        · -- Case r = n: both sides equal k
          have hleft : c_prologue.state.read r = k := by rw [hr_eq_n]; exact hRn_after_prologue
          have hright : initStateG.read r = k := by
            unfold initStateG Config.init State.fromInputs State.read extendInputsForG
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            have hlen : r < (n + 2) := by omega
            simp only [hlen, dite_true]
            simp only [Fin.snoc, Fin.castSucc, hr_eq_n]
            have hn_ne_n1 : n ≠ n + 1 := by omega
            simp only [hn_ne_n1, if_false]
            simp only [Nat.lt_irrefl, dite_false]
          rw [hleft, hright]
        · by_cases hr_eq_n1 : r = n + 1
          · -- Case r = n+1: both sides equal accBefore
            have hleft : c_prologue.state.read r = accBefore := by rw [hr_eq_n1]; exact hRn1_after_prologue
            have hright : initStateG.read r = accBefore := by
              unfold initStateG Config.init State.fromInputs State.read extendInputsForG
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
              have hlen : r < (n + 2) := by omega
              simp only [hlen, dite_true, hr_eq_n1]
              simp only [Fin.snoc, Fin.val_last]
            rw [hleft, hright]
          · -- Case r > n+1: both sides equal 0
            have hr_gt_n1 : n + 1 < r := by omega
            have hleft : c_prologue.state.read r = 0 := by
              have hr_le_pG_max : r ≤ pG.maxRegister := hr_hi
              have hpG_le_base : pG.maxRegister ≤ primitiveRecursionBase n pF pG :=
                primitiveRecursionBase_ge_pG n pF pG
              have hr_le_base : r ≤ primitiveRecursionBase n pF pG := Nat.le_trans hr_le_pG_max hpG_le_base
              -- Cleared by prologue
              have hk : r < (prLoopPrologue n pF pG).length := by
                simp only [prLoopPrologue, List.length_append, clearRegisters_length,
                  copyRegisterRange_length, List.length]
                omega
              have hwrite : (prLoopPrologue n pF pG)[r] = Instr.Z r := by
                simp only [prLoopPrologue]
                have h_in_clear : r < (clearRegisters (primitiveRecursionBase n pF pG)).length := by
                  simp only [clearRegisters_length]; exact Nat.lt_succ_of_le hr_le_base
                have h_in_ext : r < (clearRegisters (primitiveRecursionBase n pF pG) ++
                    copyRegisterRange (prSavedInputsStart n pF pG) 0 n ++
                    [Instr.T (prCounterReg n pF pG) n, Instr.T (prAccumulatorReg n pF pG) (n + 1)]).length := by
                  simp only [List.length_append, clearRegisters_length, copyRegisterRange_length, List.length]
                  omega
                rw [List.getElem_append_left h_in_ext]
                have h_in_ext2 : r < (clearRegisters (primitiveRecursionBase n pF pG) ++
                    copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length := by
                  simp only [List.length_append, clearRegisters_length, copyRegisterRange_length]; omega
                rw [List.getElem_append_left h_in_ext2, List.getElem_append_left h_in_clear]
                simp only [Program.clearRegisters, List.getElem_map, List.getElem_range]
              have hnowrite : ∀ j (hj : j < (prLoopPrologue n pF pG).length), r < j →
                  ((prLoopPrologue n pF pG)[j]).writesTo ≠ some r := by
                intro j hj hjr
                simp only [prLoopPrologue, List.length_append, clearRegisters_length,
                  copyRegisterRange_length, List.length] at hj
                simp only [prLoopPrologue]
                by_cases hj_clear : j < (clearRegisters (primitiveRecursionBase n pF pG) ++
                    copyRegisterRange (prSavedInputsStart n pF pG) 0 n ++
                    [Instr.T (prCounterReg n pF pG) n, Instr.T (prAccumulatorReg n pF pG) (n + 1)]).length
                · rw [List.getElem_append_left hj_clear]
                  by_cases hj_clear2 : j < (clearRegisters (primitiveRecursionBase n pF pG) ++
                      copyRegisterRange (prSavedInputsStart n pF pG) 0 n).length
                  · rw [List.getElem_append_left hj_clear2]
                    by_cases hj_in_clear : j < (clearRegisters (primitiveRecursionBase n pF pG)).length
                    · rw [List.getElem_append_left hj_in_clear]
                      simp only [Program.clearRegisters, List.getElem_map, List.getElem_range,
                        Instr.writesTo, ne_eq, Option.some.injEq]
                      omega
                    · rw [List.getElem_append_right (Nat.not_lt.mp hj_in_clear)]
                      simp only [clearRegisters_length, Program.copyRegisterRange, List.getElem_map,
                        List.getElem_range, Nat.zero_add, Instr.writesTo, ne_eq, Option.some.injEq]
                      simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear2
                      simp only [clearRegisters_length] at hj_in_clear
                      omega
                  · rw [List.getElem_append_right (Nat.not_lt.mp hj_clear2)]
                    simp only [List.length_append, clearRegisters_length, copyRegisterRange_length,
                      List.length] at hj_clear
                    simp only [List.length_append, clearRegisters_length, copyRegisterRange_length] at hj_clear2
                    simp only [List.length_append, clearRegisters_length, copyRegisterRange_length]
                    have hidx : j - (primitiveRecursionBase n pF pG + 1 + n) < 2 := by omega
                    interval_cases j - (primitiveRecursionBase n pF pG + 1 + n)
                    · simp only [List.getElem_cons_zero, Instr.writesTo, ne_eq, Option.some.injEq]
                      intro heq
                      have := prCounterReg_gt_n n pF pG
                      omega
                    · simp only [List.getElem_cons_succ, List.getElem_cons_zero, Instr.writesTo,
                        ne_eq, Option.some.injEq]
                      intro heq
                      have := prAccumulatorReg_gt_n n pF pG
                      omega
                · simp only [List.length_append, clearRegisters_length, copyRegisterRange_length,
                    List.length] at hj_clear
                  omega
              exact straightLine_zeros_register (prLoopPrologue_isStraightLine n pF pG) s r r hk hwrite hnowrite
            have hright : initStateG.read r = 0 := by
              unfold initStateG Config.init State.fromInputs State.read
              have hr_ge : ¬ r < n + 2 := by omega
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr_ge, dite_false, Option.getD_none]
            rw [hleft, hright]

    -- Define c₂ to use agreeOn
    let c₂ : Config := ⟨0, c_prologue.state⟩
    have hpc_c2 : (Config.init (List.ofFn (extendInputsForG inputs k accBefore))).pc = c₂.pc := rfl

    -- Use Steps.agreeOn to get execution from c_prologue.state
    have hagree_pG_symm : initStateG.agreeOn c₂.state 0 pG.maxRegister := State.agreeOn_symm hagree_pG
    let hagree_result := Steps.agreeOn hsteps_pG hpc_c2 hagree_pG_symm
    let c_pG' := Classical.choose hagree_result
    have hspec_pG' := Classical.choose_spec hagree_result
    let hsteps_pG' := hspec_pG'.1
    let hpc_pG' := hspec_pG'.2.1
    have hagree_pG' : cpG.state.agreeOn c_pG'.state 0 pG.maxRegister := hspec_pG'.2.2

    -- pG_result_eq: c_pG'.state.read 0 = Result pG ... hpG_halts
    have hpG_result_eq : c_pG'.state.read 0 = Result pG (List.ofFn (extendInputsForG inputs k accBefore)) hpG_halts := by
      have h_agree_at_0 := hagree_pG' 0 (Nat.zero_le 0) (Nat.zero_le _)
      simp only [Result, State.output]
      exact h_agree_at_0.symm

    -- Lift pG steps to primitiveRecursionProgram using shiftJumps_at_offset
    have hembed_pG := prPG_shiftJumps_embed n pF pG
    have hsteps_pG_lifted := Steps.shiftJumps_at_offset (prPGOffset n pF pG) hembed_pG hsteps_pG'

    -- Show that c_pG'.pc = pG.length (since pG is standard form)
    have hhalted_pG' : c_pG'.isHalted pG := by
      unfold Config.isHalted; rw [← hpc_pG']; exact hhalted_pG
    have hpc_pG'_length : c_pG'.pc = pG.length :=
      hpG_sf.pc_eq_length_of_halted hsteps_pG' (Nat.zero_le _) hhalted_pG'

    -- Simplify the lifted steps: from prPGOffset to prPGOffset + pG.length
    have hsteps_pG_lifted' : Steps (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG, c_prologue.state⟩
        ⟨prPGOffset n pF pG + pG.length, c_pG'.state⟩ := by
      have h1 : prPGOffset n pF pG + c₂.pc = prPGOffset n pF pG := by simp
      have h2 : prPGOffset n pF pG + c_pG'.pc = prPGOffset n pF pG + pG.length := by rw [hpc_pG'_length]
      rw [h1, h2] at hsteps_pG_lifted
      exact hsteps_pG_lifted

    -- Combined steps to end of pG
    have hsteps_to_pG_end : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prPGOffset n pF pG + pG.length, c_pG'.state⟩ :=
      Relation.ReflTransGen.trans hsteps_to_prologue_end hsteps_pG_lifted'

    -- Phase 3: Execute loop epilogue (T, S, J)
    -- Epilogue PC positions
    have hT_pc : prPGOffset n pF pG + pG.length = prPGOffset n pF pG + pG.length := rfl
    have hS_pc : prPGOffset n pF pG + pG.length + 1 = prPGOffset n pF pG + pG.length + 1 := rfl

    -- Epilogue instruction embeddings (inline proofs)
    have hT_instr : (primitiveRecursionProgram n pF pG).getInstr (prPGOffset n pF pG + pG.length) =
        some (Instr.T 0 (prAccumulatorReg n pF pG)) := by
      simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody, prLoopEpilogue,
        getInstr, List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length,
        prLoopPrologue_length, shiftJumps_length, List.length_append, prLoopBody_length,
        prOutputPhase_length, prLoopPrologueLength, prLoopEpilogueLength, prLoopBodyLength,
        prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength, List.length]
      split_ifs <;> try omega
      simp only [Nat.add_sub_cancel_left, List.getElem?_cons_zero]

    have hS_instr : (primitiveRecursionProgram n pF pG).getInstr (prPGOffset n pF pG + pG.length + 1) =
        some (Instr.S (prCounterReg n pF pG)) := by
      simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody, prLoopEpilogue,
        getInstr, List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length,
        prLoopPrologue_length, shiftJumps_length, List.length_append, prLoopBody_length,
        prOutputPhase_length, prLoopPrologueLength, prLoopEpilogueLength, prLoopBodyLength,
        prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength, List.length]
      split_ifs <;> try omega
      simp only [Nat.add_sub_cancel_left]
      have hidx : pG.length + 1 - pG.length = 1 := by omega
      simp only [hidx, List.getElem?_cons_succ, List.getElem?_cons_zero]

    have hJ_instr_epilogue : (primitiveRecursionProgram n pF pG).getInstr (prPGOffset n pF pG + pG.length + 2) =
        some (Instr.J (prZeroReg n pF pG) (prZeroReg n pF pG) (prLoopCheckPC n pF pG)) := by
      simp only [primitiveRecursionProgram, prPGOffset, prLoopBodyPC, prLoopCheckPC, prLoopBody, prLoopEpilogue,
        getInstr, List.getElem?_append, prSetupPhase_length, prBaseCasePhase_length, prLoopCheck_length,
        prLoopPrologue_length, shiftJumps_length, List.length_append, prLoopBody_length,
        prOutputPhase_length, prLoopPrologueLength, prLoopEpilogueLength, prLoopBodyLength,
        prSetupPhaseLength, prBaseCasePhaseLength, prBaseCasePrologueLength, List.length]
      split_ifs <;> try omega
      simp only [Nat.add_sub_cancel_left]
      have hidx : pG.length + 2 - pG.length = 2 := by omega
      simp only [hidx, List.getElem?_cons_succ, List.getElem?_cons_zero]

    -- Execute T instruction
    let state_after_T := c_pG'.state.write (prAccumulatorReg n pF pG) (c_pG'.state.read 0)
    have hstep_T : Step (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length, c_pG'.state⟩
        ⟨prPGOffset n pF pG + pG.length + 1, state_after_T⟩ :=
      Step.transfer hT_instr

    -- Execute S instruction
    let state_after_S := state_after_T.write (prCounterReg n pF pG) (state_after_T.read (prCounterReg n pF pG) + 1)
    have hstep_S : Step (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length + 1, state_after_T⟩
        ⟨prPGOffset n pF pG + pG.length + 2, state_after_S⟩ :=
      Step.succ hS_instr

    -- Execute J instruction (unconditional jump since zeroReg = zeroReg)
    have hzero_eq : state_after_S.read (prZeroReg n pF pG) = state_after_S.read (prZeroReg n pF pG) := rfl
    have hstep_J_back : Step (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length + 2, state_after_S⟩
        ⟨prLoopCheckPC n pF pG, state_after_S⟩ :=
      Step.jump_eq hJ_instr_epilogue hzero_eq

    -- Combined epilogue steps
    have hsteps_epilogue : Steps (primitiveRecursionProgram n pF pG) ⟨prPGOffset n pF pG + pG.length, c_pG'.state⟩
        ⟨prLoopCheckPC n pF pG, state_after_S⟩ := by
      apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep_T)
      apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep_S)
      exact Relation.ReflTransGen.single hstep_J_back

    -- Full steps from loopCheckPC back to loopCheckPC
    have hsteps_full : Steps (primitiveRecursionProgram n pF pG) ⟨prLoopCheckPC n pF pG, s⟩
        ⟨prLoopCheckPC n pF pG, state_after_S⟩ :=
      Relation.ReflTransGen.trans hsteps_to_pG_end hsteps_epilogue

    -- Preservation lemmas
    have hpG_preserves_high : ∀ r, pG.maxRegister < r → c_pG'.state.read r = c_prologue.state.read r := by
      intro r hr
      exact pG_preserves_high_reg pG c_prologue.state c_pG'.state c_pG' hsteps_pG' rfl r hr

    have hprologue_preserves : ∀ r, primitiveRecursionBase n pF pG < r → c_prologue.state.read r = s.read r :=
      fun r hr => prLoopPrologue_preserves_high_register n pF pG s c_prologue hsteps_prologue hhalted_prologue r hr

    -- Counter value in state_after_S
    have hcounter_after_S : state_after_S.read (prCounterReg n pF pG) = k + 1 := by
      simp only [state_after_S, state_after_T, State.write, State.read, Function.update_self]
      -- Need to show state_after_T.read counter = k
      -- pG doesn't touch counter (above pG.maxRegister), prologue sets counter via T
      have hcounter_after_T : state_after_T.read (prCounterReg n pF pG) = k := by
        simp only [state_after_T, State.write, State.read]
        split_ifs with heq
        · have := prCounterReg_gt_base n pF pG
          have := prAccumulatorReg_gt_base n pF pG
          simp only [prCounterReg, prAccumulatorReg] at this heq; omega
        · have hpG_preserves_counter := pG_preserves_prCounterReg n pF pG c_prologue.state c_pG'.state c_pG' hsteps_pG' rfl
          rw [hpG_preserves_counter]
          -- After prologue, counter = k (from T instruction)
          have := prLoopPrologue_preserves_high_register n pF pG s c_prologue hsteps_prologue hhalted_prologue
            (prCounterReg n pF pG) (prCounterReg_gt_base n pF pG)
          rw [this, hs_counter]
      rw [hcounter_after_T]

    -- Build the result
    have hk_lt_y : k < y := by
      by_contra h
      have hk_ge_y : k ≥ y := Nat.not_lt.mp h
      have hk_eq_y : k = y := Nat.le_antisymm hk_ge_y (Nat.le_of_not_lt (fun hlt => hky (Nat.le_antisymm (Nat.le_of_lt hlt) hk_ge_y)))
      exact hky hk_eq_y

    exact {
      config := ⟨prLoopCheckPC n pF pG, state_after_S⟩
      steps := hsteps_full
      outcome := Or.inr ⟨rfl, hk_lt_y⟩
      counter_next := fun _ => hcounter_after_S
      accumulator_updated := fun _ => by
        simp only [state_after_S, state_after_T, State.write, State.read]
        split_ifs with heq1
        · -- counterReg = accumulatorReg? No, they're different
          have := prCounterReg_gt_base n pF pG
          have := prAccumulatorReg_gt_base n pF pG
          simp only [prCounterReg, prAccumulatorReg] at this heq1; omega
        · split_ifs with heq2
          · exact hpG_result_eq
          · exact (heq2 rfl).elim
      savedInputs_preserved := fun i => by
        simp only [state_after_S, state_after_T, State.write, State.read]
        split_ifs with heq1
        · have := prSavedInputsStart_gt_base n pF pG
          have := prCounterReg_gt_base n pF pG
          simp only [prSavedInputsStart, prCounterReg] at this heq1 ⊢; omega
        · split_ifs with heq2
          · have := prSavedInputsStart_gt_base n pF pG
            have := prAccumulatorReg_gt_base n pF pG
            simp only [prSavedInputsStart, prAccumulatorReg] at this heq2 ⊢; omega
          · have h1 := pG_preserves_prSavedInputs n pF pG c_prologue.state c_pG'.state c_pG' hsteps_pG' rfl i
            have h2 := hprologue_preserves (prSavedInputsStart n pF pG + i) (prSavedInputsStart_gt_base n pF pG)
            rw [h1, h2]
      savedY_preserved := by
        simp only [state_after_S, state_after_T, State.write, State.read]
        split_ifs with heq1
        · have := prSavedYReg_gt_base n pF pG
          have := prCounterReg_gt_base n pF pG
          simp only [prSavedYReg, prCounterReg] at this heq1 ⊢; omega
        · split_ifs with heq2
          · have := prSavedYReg_gt_base n pF pG
            have := prAccumulatorReg_gt_base n pF pG
            simp only [prSavedYReg, prAccumulatorReg] at this heq2 ⊢; omega
          · have h1 := pG_preserves_prSavedYReg n pF pG c_prologue.state c_pG'.state c_pG' hsteps_pG' rfl
            have h2 := hprologue_preserves (prSavedYReg n pF pG) (prSavedYReg_gt_base n pF pG)
            rw [h1, h2]
      zero_preserved := by
        simp only [state_after_S, state_after_T, State.write, State.read]
        split_ifs with heq1
        · have := prZeroReg_gt_base n pF pG
          have := prCounterReg_gt_base n pF pG
          simp only [prZeroReg, prCounterReg] at this heq1 ⊢; omega
        · split_ifs with heq2
          · have := prZeroReg_gt_base n pF pG
            have := prAccumulatorReg_gt_base n pF pG
            simp only [prZeroReg, prAccumulatorReg] at this heq2 ⊢; omega
          · have h1 := pG_preserves_prZeroReg n pF pG c_prologue.state c_pG'.state c_pG' hsteps_pG' rfl
            have h2 := hprologue_preserves (prZeroReg n pF pG) (prZeroReg_gt_base n pF pG)
            rw [h1, h2]
    }

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
  induction k generalizing s with
  | zero =>
    -- Base case: 0 iterations, just return the initial state
    exact {
      config := ⟨prLoopCheckPC n pF pG, s⟩
      steps := Relation.ReflTransGen.refl
      pc_eq := rfl
      counter_eq := hs_counter
      savedInputs_eq := hs_saved
      savedY_eq := hs_savedY
      zero_eq := hs_zero
    }
  | succ m ih =>
    -- Inductive case: do m iterations, then one more
    -- First, get domain proofs for m
    have hPr_dom_m : (Pr f g (Fin.snoc inputs m)).Dom :=
      Pr_dom_of_dom_le inputs hPr_dom_k (Nat.le_of_lt (Nat.lt_of_succ_le hk_le_y))

    -- Get result after m iterations
    have hm_le_y : m ≤ y := Nat.le_of_lt (Nat.lt_of_succ_le hk_le_y)
    let result_m := ih hm_le_y hs_counter hs_savedY hs_zero hs_saved hPr_dom_m hs_acc

    -- After m iterations, we're at loopCheckPC with counter = m
    let s_m := result_m.config.state
    have hcounter_m : s_m.read (prCounterReg n pF pG) = m := result_m.counter_eq
    have hsavedY_m : s_m.read (prSavedYReg n pF pG) = y := result_m.savedY_eq
    have hzero_m : s_m.read (prZeroReg n pF pG) = 0 := result_m.zero_eq
    have hsaved_m : ∀ i : Fin n, s_m.read (prSavedInputsStart n pF pG + i) = inputs i := result_m.savedInputs_eq

    -- The accumulator after m iterations equals Pr(inputs, m)
    -- We need to track this through the iterations
    -- For now, we'll derive it from the invariant
    have hacc_m : s_m.read (prAccumulatorReg n pF pG) = (Pr f g (Fin.snoc inputs m)).get hPr_dom_m := by
      -- This follows from the fact that loop maintains the invariant:
      -- after j iterations, acc = Pr(inputs, j)
      -- We prove this by strong induction implicitly through the structure
      sorry -- TODO: Need to add acc_eq field to LoopKIterationsResult or prove separately

    -- pG halts for the m-th iteration inputs
    have hpG_halts_m : Halts pG (List.ofFn (extendInputsForG inputs m (s_m.read (prAccumulatorReg n pF pG)))) := by
      rw [hacc_m]
      -- Pr(inputs, m+1) is defined means g(inputs, m, Pr(inputs, m)) is defined
      have h := (Pr_dom_succ inputs m).mp hPr_dom_k
      have hg_dom := h.2 h.1
      rw [(hpG_spec (extendInputsForG inputs m ((Pr f g (Fin.snoc inputs m)).get hPr_dom_m))).1]
      exact hg_dom

    -- Do one more iteration
    let one_iter := loop_iteration n pF pG hpF_sf hpG_sf inputs y s_m m
      (s_m.read (prAccumulatorReg n pF pG)) hcounter_m hsavedY_m
      rfl hzero_m hsaved_m hpG_halts_m

    -- Get the outcome - it should be Or.inr (continue case) since m < y
    have hm_lt_y : m < y := Nat.lt_of_succ_le hk_le_y
    have houtcome := one_iter.outcome
    -- In the continue case, we're back at loopCheckPC with counter = m + 1
    cases houtcome with
    | inl hexit =>
      -- Exit case: m = y, but we have m < y, contradiction
      exfalso
      exact Nat.lt_irrefl y (hexit.2 ▸ hm_lt_y)
    | inr hcontinue =>
      -- Continue case: back at loopCheckPC with counter = m + 1
      exact {
        config := one_iter.config
        steps := Relation.ReflTransGen.trans result_m.steps one_iter.steps
        pc_eq := hcontinue.1
        counter_eq := one_iter.counter_next hcontinue.1
        savedInputs_eq := fun i => by
          rw [one_iter.savedInputs_preserved i, hsaved_m i]
        savedY_eq := by rw [one_iter.savedY_preserved, hsavedY_m]
        zero_eq := by rw [one_iter.zero_preserved, hzero_m]
      }

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
