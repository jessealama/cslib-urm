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
def PhaseExecutionResult.andThen
    {host phase1 phase2 : Program} {offset : ℕ} {s : State}
    (r1 : PhaseExecutionResult host phase1 offset s)
    (r2 : PhaseExecutionResult host phase2 (offset + phase1.length) r1.finalState) :
    Steps host ⟨offset, s⟩ ⟨offset + phase1.length + phase2.length, r2.finalState⟩ :=
  r1.liftedSteps.trans r2.liftedSteps

/-- Chain a phase execution result with arbitrary subsequent steps.

This is useful when the next phase is not straight-line (e.g., contains jumps)
or when you need to chain with custom step sequences.
-/
def PhaseExecutionResult.andThenSteps
    {host phase : Program} {offset : ℕ} {s : State} {c : Config}
    (r : PhaseExecutionResult host phase offset s)
    (hs : Steps host ⟨offset + phase.length, r.finalState⟩ c) :
    Steps host ⟨offset, s⟩ c :=
  r.liftedSteps.trans hs

/-! ## Convenience Accessors -/

/-- Access the local steps (for use with invariant lemmas). -/
abbrev PhaseExecutionResult.localSteps {host phase : Program} {offset : ℕ} {s : State}
    (r : PhaseExecutionResult host phase offset s) : Steps phase ⟨0, s⟩ r.phaseResult.config :=
  r.phaseResult.steps

/-- Access the local halted proof (for use with invariant lemmas). -/
abbrev PhaseExecutionResult.localHalted {host phase : Program} {offset : ℕ} {s : State}
    (r : PhaseExecutionResult host phase offset s) : r.phaseResult.config.isHalted phase :=
  r.phaseResult.halted

/-- Access the final config of the local execution. -/
abbrev PhaseExecutionResult.localConfig {host phase : Program} {offset : ℕ} {s : State}
    (r : PhaseExecutionResult host phase offset s) : Config :=
  r.phaseResult.config

end Urm
