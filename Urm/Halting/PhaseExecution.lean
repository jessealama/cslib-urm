/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Halting.Common

/-! # Phase Execution Infrastructure

This module provides enhanced infrastructure for executing phases within larger programs,
specifically designed to reduce boilerplate in halting proofs.

## Design Goals

The existing `LiftedPhaseResult` in `Halting/Common.lean` loses access to the original
`StraightLineResult`, which is needed for invariant proofs that use lemmas like
`loopPrologue_preserves_high_register`. This module provides:

1. `PhaseExecutionResult`: Preserves both local and lifted execution information
2. `execPhaseInHost`: Convenient function to execute and lift a phase
3. `PhaseExecutionResult.chain`: Chain multiple phase executions together

## Example Usage

Instead of:
```lean
let prologueResult := straightLineExec hsl_prologue s
let c_prologue := prologueResult.config
let hsteps_prologue := prologueResult.steps
let hhalted_prologue := prologueResult.halted
-- ... establish invariants using helper lemmas with hsteps_prologue, hhalted_prologue ...
have hsteps_prologue_lifted := Steps.straightLine_at_offset offset hsl hembed hsteps_prologue
```

You can write:
```lean
let phaseResult := execPhaseInHost hsl_prologue offset hembed s
-- Access local result for invariant lemmas: phaseResult.local.steps, phaseResult.local.halted
-- Access lifted steps for chaining: phaseResult.hostSteps
```
-/

namespace Urm

open Program

/-! ## Phase Execution Result -/

/-- Result of executing a straight-line phase within a host program.

This structure preserves both:
- The local execution result (for invariant proofs using phase-specific lemmas)
- The lifted steps in the host program (for chaining with subsequent phases)

This addresses the limitation of `LiftedPhaseResult` which loses the local execution
information needed for invariant proofs. -/
structure PhaseExecutionResult (host phase : Program) (offset : ℕ) (s : State) where
  /-- The result of executing the phase in isolation (starting at PC 0) -/
  phaseResult : StraightLineResult phase s
  /-- Steps in the host program from ⟨offset, s⟩ to ⟨offset + phase.length, finalState⟩ -/
  liftedSteps : Steps host ⟨offset, s⟩ ⟨offset + phase.length, phaseResult.config.state⟩

/-- The final state after phase execution. -/
abbrev PhaseExecutionResult.finalState {host phase : Program} {offset : ℕ} {s : State}
    (r : PhaseExecutionResult host phase offset s) : State :=
  r.phaseResult.config.state

/-- Execute a straight-line phase and lift to the host program.

This is the primary entry point for phase execution. It combines:
1. `straightLineExec` to run the phase locally
2. `Steps.straightLine_at_offset` to lift the execution to the host

Usage:
```lean
let result := execPhaseInHost hsl_prologue offset hembed s
-- Use result.phaseResult.steps, result.phaseResult.halted for invariant lemmas
-- Use result.liftedSteps for chaining
```
-/
noncomputable def execPhaseInHost
    {phase host : Program} (hsl : phase.isStraightLine = true) (offset : ℕ)
    (hembed : ∀ i, i < phase.length → host.getInstr (offset + i) = phase.getInstr i)
    (s : State) : PhaseExecutionResult host phase offset s :=
  let localResult := straightLineExec hsl s
  let lifted := Steps.straightLine_at_offset offset hsl hembed localResult.steps
  -- Rewrite to get the correct form: ⟨offset + phase.length, state⟩
  have hpc_rewrite : offset + localResult.config.pc = offset + phase.length := by
    rw [localResult.pc_eq]
  ⟨localResult, hpc_rewrite ▸ lifted⟩

/-! ## Phase Chaining -/

/-- Chain two phase execution results together.

Given phases executed sequentially:
- Phase 1 from offset to offset + phase1.length
- Phase 2 from offset + phase1.length to offset + phase1.length + phase2.length

Produces steps from offset to offset + phase1.length + phase2.length.

Note: The second phase must start from `r1.finalState` for the chain to be valid.
-/
theorem PhaseExecutionResult.andThen
    {host phase1 phase2 : Program} {offset : ℕ} {s : State}
    (r1 : PhaseExecutionResult host phase1 offset s)
    (r2 : PhaseExecutionResult host phase2 (offset + phase1.length) r1.finalState) :
    Steps host ⟨offset, s⟩ ⟨offset + phase1.length + phase2.length, r2.finalState⟩ :=
  r1.liftedSteps.trans r2.liftedSteps

/-- Chain a phase execution result with arbitrary subsequent steps.

This is useful when the next phase is not straight-line (e.g., contains jumps)
or when you need to chain with custom step sequences.
-/
theorem PhaseExecutionResult.andThenSteps
    {host phase : Program} {offset : ℕ} {s : State} {c : Config}
    (r : PhaseExecutionResult host phase offset s)
    (hs : Steps host ⟨offset + phase.length, r.finalState⟩ c) :
    Steps host ⟨offset, s⟩ c :=
  r.liftedSteps.trans hs

/-! ## Convenience Accessors -/

/-- Access the local steps (for use with invariant lemmas). -/
theorem PhaseExecutionResult.localSteps {host phase : Program} {offset : ℕ} {s : State}
    (r : PhaseExecutionResult host phase offset s) : Steps phase ⟨0, s⟩ r.phaseResult.config :=
  r.phaseResult.steps

/-- Access the local halted proof (for use with invariant lemmas). -/
theorem PhaseExecutionResult.localHalted {host phase : Program} {offset : ℕ} {s : State}
    (r : PhaseExecutionResult host phase offset s) : r.phaseResult.config.isHalted phase :=
  r.phaseResult.halted

/-- Access the final config of the local execution. -/
abbrev PhaseExecutionResult.localConfig {host phase : Program} {offset : ℕ} {s : State}
    (r : PhaseExecutionResult host phase offset s) : Config :=
  r.phaseResult.config

/-! ## Subprogram Execution Infrastructure

This section provides infrastructure for executing embedded subprograms (like pF or pG)
within a host program. The key challenge is handling:

1. State agreement: The current state may differ from the init state, but agrees on
   registers 0..maxRegister
2. Lifting via `Steps.shiftJumps_at_offset`: The subprogram is embedded with shifted jumps
3. Standard form: The subprogram's PC ends at its length when halted
4. Result extraction: The result is in R[0]
-/

/-- Result of executing a subprogram embedded within a host program.

This captures the common pattern for "Phase 2" execution where:
- A subprogram `sub` is embedded at `offset` in `host` via `shiftJumps`
- The subprogram executes from a state that agrees with its init state
- The result is extracted from R[0]
- High registers (above sub.maxRegister) are preserved

Usage: After executing a prologue phase, use this to execute the embedded subprogram. -/
structure SubprogramExecResult (host sub : Program) (offset : ℕ) (s : State) where
  /-- The final state after subprogram execution -/
  finalState : State
  /-- Steps in the host program from ⟨offset, s⟩ to ⟨offset + sub.length, finalState⟩ -/
  liftedSteps : Steps host ⟨offset, s⟩ ⟨offset + sub.length, finalState⟩
  /-- The result value in R[0] -/
  result : ℕ
  /-- The result equals what's in R[0] -/
  result_eq : finalState.read 0 = result
  /-- Registers above sub.maxRegister are preserved -/
  highPreserved : ∀ r, sub.maxRegister < r → finalState.read r = s.read r

/-- Execute an embedded subprogram and lift to the host program.

This handles the common "Phase 2" pattern where a standard form subprogram is
embedded at an offset via shiftJumps. It combines:
1. `Steps.agreeOn` to transfer execution from the agreeing state
2. `Steps.shiftJumps_at_offset` to lift the execution to the host
3. Standard form to establish PC ends at sub.length

Parameters:
- `hsf`: The subprogram must be standard form (so PC = length when halted)
- `hembed`: Embedding lemma (host.getInstr (offset + i) = sub.shiftJumps.getInstr i)
- `hHalts`: Proof that sub halts on the original inputs
- `hagree`: State agreement (s agrees with init state on 0..sub.maxRegister)
- `inputs`: The original inputs (used for Result definition)

Returns a `SubprogramExecResult` with:
- `finalState`: State after execution
- `liftedSteps`: Steps from ⟨offset, s⟩ to ⟨offset + sub.length, finalState⟩
- `result`: The value in R[0], equal to `Result sub inputs hHalts`
- `highPreserved`: Registers above sub.maxRegister unchanged
-/
noncomputable def execSubprogramInHost
    {sub host : Program} {inputs : List ℕ}
    (hsf : sub.IsStandardForm) (offset : ℕ)
    (hembed : ∀ i, i < sub.length → host.getInstr (offset + i) = (sub.shiftJumps offset).getInstr i)
    (hHalts : Halts sub inputs)
    (s : State)
    (hagree : s.agreeOn (Config.init inputs).state 0 sub.maxRegister) :
    SubprogramExecResult host sub offset s := by
  -- Get the halting configuration from the original execution
  let cSub := Classical.choose hHalts
  have hspec := Classical.choose_spec hHalts
  let hsteps := hspec.1
  let hhalted := hspec.2

  -- Use Steps.agreeOn to transfer execution to our state
  let initState := (Config.init inputs).state
  let c₂ : Config := ⟨0, s⟩
  have hpc_c2 : (Config.init inputs).pc = c₂.pc := rfl
  have hagree_symm : initState.agreeOn c₂.state 0 sub.maxRegister := State.agreeOn_symm hagree
  let hagree_result := Steps.agreeOn hsteps hpc_c2 hagree_symm
  let cSub' := Classical.choose hagree_result
  have hspec' := Classical.choose_spec hagree_result
  let hsteps' := hspec'.1
  let hpc' := hspec'.2.1
  have hagree' : cSub.state.agreeOn cSub'.state 0 sub.maxRegister := hspec'.2.2

  -- Show PC ends at sub.length (standard form)
  have hhalted' : cSub'.isHalted sub := by
    unfold Config.isHalted; rw [← hpc']; exact hhalted
  have hpc_length : cSub'.pc = sub.length :=
    hsf.pc_eq_length_of_halted hsteps' (Nat.zero_le _) hhalted'

  -- Lift steps using shiftJumps_at_offset
  have hsteps_lifted := Steps.shiftJumps_at_offset offset hembed hsteps'

  -- Simplify lifted steps to use sub.length
  have hsteps_lifted' : Steps host ⟨offset, s⟩ ⟨offset + sub.length, cSub'.state⟩ := by
    have h1 : offset + c₂.pc = offset := by rfl
    have h2 : offset + cSub'.pc = offset + sub.length := by rw [hpc_length]
    rw [h1, h2] at hsteps_lifted
    exact hsteps_lifted

  -- The result equals what's in R[0]
  have hresult_eq : cSub'.state.read 0 = Result sub inputs hHalts := by
    let h_agree_at_0 := hagree' 0 (Nat.zero_le 0) (Nat.zero_le _)
    simp only [Result, State.output]
    exact h_agree_at_0.symm

  -- High registers are preserved
  have hhigh : ∀ r, sub.maxRegister < r → cSub'.state.read r = s.read r := by
    intro r hr
    exact Steps.preserves_high_register hsteps' r hr

  exact {
    finalState := cSub'.state
    liftedSteps := hsteps_lifted'
    result := Result sub inputs hHalts
    result_eq := hresult_eq
    highPreserved := hhigh
  }

/-- Chain a phase execution with a subprogram execution.

This is the common pattern where a straight-line prologue phase is followed
by an embedded subprogram execution. -/
theorem PhaseExecutionResult.andThenSubprogram
    {host phase sub : Program} {offset : ℕ} {s : State}
    (phaseResult : PhaseExecutionResult host phase offset s)
    (subResult : SubprogramExecResult host sub (offset + phase.length) phaseResult.finalState) :
    Steps host ⟨offset, s⟩ ⟨offset + phase.length + sub.length, subResult.finalState⟩ :=
  phaseResult.liftedSteps.trans subResult.liftedSteps

end Urm
