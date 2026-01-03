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
    (inputs : Fin n → ℕ) (y : ℕ) (s : State) (hpF_halts : Halts pF (List.ofFn inputs)) :
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

  -- Phase 3: Execute T instruction (copy R[0] to accumulator)
  -- This is a single instruction

  -- TODO: Complete the proof by:
  -- 1. Showing c_prologue.state agrees with (Config.init (List.ofFn inputs)).state on pF's working registers
  -- 2. Lifting pF execution to primitiveRecursionProgram using shiftJumps embedding
  -- 3. Executing the final T instruction
  -- 4. Establishing all invariants (accumulator, preservation of high registers)
  sorry

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
