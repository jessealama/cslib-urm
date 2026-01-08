/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Embeddings
import Urm.StraightLine
import Urm.Shift
import Urm.StandardForm



/-! # Common Infrastructure for Halting Proofs

This module provides shared infrastructure for halting proofs used by both
primitive recursion and minimization constructions.

## Main definitions

- `StraightLineResult`: Bundled result of executing a straight-line program
- `straightLineExec`: Execute a straight-line program and extract the result
- `liftStraightLinePhase`: Lift straight-line execution to an embedded phase

## Main theorems

- `halts_of_exits_embedded_region`: Extract subprocess halting from full program
  execution that exits the embedded region
-/

namespace Urm

open Program

/-! ## Straight-Line Execution Infrastructure -/

/-- Result of executing a straight-line program. Bundles the final config with proofs. -/
structure StraightLineResult (p : Program) (s : State) where
  /-- Final configuration after execution -/
  config : Config
  /-- Steps from initial state to final config -/
  steps : Steps p ⟨0, s⟩ config
  /-- The program halted -/
  halted : config.isHalted p
  /-- PC equals program length at halt -/
  pc_eq : config.pc = p.length

/-- Execute a straight-line program and extract the result as a bundled structure.
    This eliminates the common boilerplate of Classical.choose + spec extraction. -/
noncomputable def straightLineExec {p : Program} (hsl : p.isStraightLine = true) (s : State) :
    StraightLineResult p s :=
  let hExists := straightLine_halts_from_state hsl s
  let c := Classical.choose hExists
  let hspec := Classical.choose_spec hExists
  ⟨c, hspec.1, hspec.2.1, hspec.2.2⟩

/-! ## Phase Lifting Infrastructure -/

/-- Result of lifting a straight-line phase execution to a larger program. -/
structure LiftedPhaseResult (host : Program) (offset : ℕ) (s : State) (phaseLen : ℕ) where
  /-- Final configuration after lifted execution -/
  config : Config
  /-- Steps in the host program -/
  steps : Steps host ⟨offset, s⟩ config
  /-- PC equals offset + phase length -/
  pc_eq : config.pc = offset + phaseLen

/-- Lift straight-line execution to an embedded phase in a larger program.
    Combines straightLineExec with Steps.straightLine_at_offset. -/
noncomputable def liftStraightLinePhase
    {phase host : Program} (hsl : phase.isStraightLine = true) (offset : ℕ)
    (hembed : ∀ i, i < phase.length → host.getInstr (offset + i) = phase.getInstr i)
    (s : State) : LiftedPhaseResult host offset s phase.length :=
  let result := straightLineExec hsl s
  let hsteps_lifted := Steps.straightLine_at_offset offset hsl hembed result.steps
  -- After lifting: pc goes from offset + 0 to offset + phase.length
  have hpc_start : offset + (0 : ℕ) = offset := by omega
  have hpc_end : offset + result.config.pc = offset + phase.length := by rw [result.pc_eq]
  ⟨⟨offset + result.config.pc, result.config.state⟩,
   by rw [hpc_start] at hsteps_lifted; exact hsteps_lifted,
   hpc_end⟩

/-- Access the final state from a lifted phase result. -/
abbrev LiftedPhaseResult.finalState {host : Program} {offset : ℕ} {s : State} {phaseLen : ℕ}
    (r : LiftedPhaseResult host offset s phaseLen) : State :=
  r.config.state

/-! ## Subprocess Halting Extraction -/

/-- Extract subprocess halting from host program execution exiting the embedded region.

If a subprogram `sub` is embedded (via shiftJumps) at offset `offset` in a host program,
and execution in the host starting at `offset + k` eventually reaches a PC ≥ `offset + sub.length`,
then the subprogram itself halts when started at PC `k`.

This is the core strong induction theorem used by both primitive recursion and minimization
to extract halting of pF/pG from halting of the composite program.

The proof uses strong induction on step count, with case analysis on each instruction type.
-/
theorem halts_of_exits_embedded_region
    {host sub : Program} {offset : ℕ}
    (hembed : ∀ i, i < sub.length → host.getInstr (offset + i) = (sub.shiftJumps offset).getInstr i)
    (hsub_sf : Program.IsStandardForm sub)
    (k : ℕ) (state : State) (c : Config)
    (hk_le : k ≤ sub.length)
    (hsteps : Steps host ⟨offset + k, state⟩ c)
    (hpc_ge : c.pc ≥ offset + sub.length) :
    ∃ c_sub, Steps sub ⟨k, state⟩ c_sub ∧ c_sub.pc = sub.length := by
  obtain ⟨numSteps, hstepsN⟩ := StepsN.fromSteps hsteps
  induction numSteps using Nat.strong_induction_on generalizing k state c with
  | _ numSteps ih =>
    by_cases hk_eq : k = sub.length
    · -- Base case: already at exit point
      subst hk_eq
      exact ⟨⟨sub.length, state⟩, Relation.ReflTransGen.refl, rfl⟩
    · -- Inductive case: k < sub.length, need to take a step
      have hk_lt : k < sub.length := Nat.lt_of_le_of_ne hk_le hk_eq
      -- numSteps must be > 0 (otherwise c = start, contradicting hpc_ge)
      have hnum_pos : numSteps > 0 := by
        by_contra hnum_zero
        push_neg at hnum_zero
        simp only [StepsN.zero_inv ((Nat.le_zero.mp hnum_zero) ▸ hstepsN)] at hpc_ge
        omega
      -- Decompose into first step + rest
      obtain ⟨c_mid, m, hfirst_step, hrest_steps, hm_eq⟩ := StepsN.succ_inv (Nat.pos_iff_ne_zero.mp hnum_pos) hstepsN
      -- Get the embedding at position k
      have hembed_k := hembed k hk_lt
      -- Get subprogram instruction at k
      have hsub_instr_exists : ∃ instr, sub.getInstr k = some instr := by
        simp only [Program.getInstr]
        exact ⟨sub[k], List.getElem?_eq_getElem hk_lt⟩
      obtain ⟨instr, hsub_instr⟩ := hsub_instr_exists
      -- The shifted instruction in the host program
      have hhost_instr : host.getInstr (offset + k) = some (instr.shiftJumps offset) := by
        rw [hembed_k, Program.getInstr_shiftJumps, hsub_instr]; rfl
      have hm_lt : m < numSteps := by omega
      have hk1_le : k + 1 ≤ sub.length := Nat.succ_le_of_lt hk_lt
      match instr with
      | Instr.Z r =>
        have hsub_step : Step sub ⟨k, state⟩ ⟨k + 1, state.write r 0⟩ := Step.zero hsub_instr
        have hhost_instr' : host.getInstr (offset + k) = some (Instr.Z r) := by rw [hhost_instr]; rfl
        have hexpected : Step host ⟨offset + k, state⟩ ⟨offset + k + 1, state.write r 0⟩ := Step.zero hhost_instr'
        have hc_mid_eq := Step.deterministic hfirst_step hexpected
        have hrest_steps' : StepsN host m ⟨offset + (k + 1), state.write r 0⟩ c := by
          rw [hc_mid_eq] at hrest_steps; convert hrest_steps using 2
        obtain ⟨c_sub, hsub_steps, hsub_pc⟩ := ih m hm_lt (k + 1) (state.write r 0) c hk1_le
            hrest_steps'.toSteps hpc_ge hrest_steps'
        exact ⟨c_sub, Relation.ReflTransGen.head hsub_step hsub_steps, hsub_pc⟩
      | Instr.S r =>
        have hsub_step : Step sub ⟨k, state⟩ ⟨k + 1, state.write r (state.read r + 1)⟩ := Step.succ hsub_instr
        have hhost_instr' : host.getInstr (offset + k) = some (Instr.S r) := by rw [hhost_instr]; rfl
        have hexpected : Step host ⟨offset + k, state⟩ ⟨offset + k + 1, state.write r (state.read r + 1)⟩ := Step.succ hhost_instr'
        have hc_mid_eq := Step.deterministic hfirst_step hexpected
        have hrest_steps' : StepsN host m ⟨offset + (k + 1), state.write r (state.read r + 1)⟩ c := by
          rw [hc_mid_eq] at hrest_steps; convert hrest_steps using 2
        obtain ⟨c_sub, hsub_steps, hsub_pc⟩ := ih m hm_lt (k + 1) (state.write r (state.read r + 1)) c hk1_le
            hrest_steps'.toSteps hpc_ge hrest_steps'
        exact ⟨c_sub, Relation.ReflTransGen.head hsub_step hsub_steps, hsub_pc⟩
      | Instr.T m' r =>
        have hsub_step : Step sub ⟨k, state⟩ ⟨k + 1, state.write r (state.read m')⟩ := Step.trans hsub_instr
        have hhost_instr' : host.getInstr (offset + k) = some (Instr.T m' r) := by rw [hhost_instr]; rfl
        have hexpected : Step host ⟨offset + k, state⟩ ⟨offset + k + 1, state.write r (state.read m')⟩ := Step.trans hhost_instr'
        have hc_mid_eq := Step.deterministic hfirst_step hexpected
        have hrest_steps' : StepsN host m ⟨offset + (k + 1), state.write r (state.read m')⟩ c := by
          rw [hc_mid_eq] at hrest_steps; convert hrest_steps using 2
        obtain ⟨c_sub, hsub_steps, hsub_pc⟩ := ih m hm_lt (k + 1) (state.write r (state.read m')) c hk1_le
            hrest_steps'.toSteps hpc_ge hrest_steps'
        exact ⟨c_sub, Relation.ReflTransGen.head hsub_step hsub_steps, hsub_pc⟩
      | Instr.J m' r' q =>
        have hhost_instr' : host.getInstr (offset + k) = some (Instr.J m' r' (q + offset)) := by
          rw [hhost_instr]; rfl
        have hq_le : q ≤ sub.length := by
          simpa [Instr.hasBoundedJump] using hsub_sf.getInstr_hasBoundedJump hsub_instr
        by_cases heq : state.read m' = state.read r'
        · -- Equal: jump to q
          have hsub_step : Step sub ⟨k, state⟩ ⟨q, state⟩ := Step.jump_eq hsub_instr heq
          have hexpected : Step host ⟨offset + k, state⟩ ⟨q + offset, state⟩ := Step.jump_eq hhost_instr' heq
          have hc_mid_eq := Step.deterministic hfirst_step hexpected
          have hrest_steps' : StepsN host m ⟨offset + q, state⟩ c := by
            rw [hc_mid_eq] at hrest_steps; convert hrest_steps using 2; omega
          obtain ⟨c_sub, hsub_steps, hsub_pc⟩ := ih m hm_lt q state c hq_le
              hrest_steps'.toSteps hpc_ge hrest_steps'
          exact ⟨c_sub, Relation.ReflTransGen.head hsub_step hsub_steps, hsub_pc⟩
        · -- Not equal: proceed to k + 1
          have hsub_step : Step sub ⟨k, state⟩ ⟨k + 1, state⟩ := Step.jump_ne hsub_instr heq
          have hexpected : Step host ⟨offset + k, state⟩ ⟨offset + k + 1, state⟩ := Step.jump_ne hhost_instr' heq
          have hc_mid_eq := Step.deterministic hfirst_step hexpected
          have hrest_steps' : StepsN host m ⟨offset + (k + 1), state⟩ c := by
            rw [hc_mid_eq] at hrest_steps; convert hrest_steps using 2
          obtain ⟨c_sub, hsub_steps, hsub_pc⟩ := ih m hm_lt (k + 1) state c hk1_le
              hrest_steps'.toSteps hpc_ge hrest_steps'
          exact ⟨c_sub, Relation.ReflTransGen.head hsub_step hsub_steps, hsub_pc⟩

end Urm
