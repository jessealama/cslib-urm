/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Core

/-! # Composition Helper Lemmas -/

namespace Urm

/-! ## HaltingExecution Structure -/

/-- Bundle for a halting execution with all its properties. -/
structure HaltingExecution (p : Program) (inputs : List ℕ) where
  /-- The final configuration after execution -/
  config : Config
  halts : Halts p inputs
  steps : Steps p (Config.init inputs) config
  halted : config.isHalted p

/-- Convert a halting proof into a full execution bundle. -/
noncomputable def Halts.toExecution {p : Program} {inputs : List ℕ} (h : Halts p inputs) :
    HaltingExecution p inputs where
  config := Classical.choose h
  halts := h
  steps := (Classical.choose_spec h).1
  halted := (Classical.choose_spec h).2

theorem HaltingExecution.pc_eq_length {p : Program} {inputs : List ℕ}
    (e : HaltingExecution p inputs) (hsf : p.IsStandardForm) : e.config.pc = p.length :=
  hsf.halts_at_length inputs e.config e.steps e.halted

/-! ## Program Chaining Lemmas -/

/-- Chain two programs: given p1 execution ending at c1, and p2 execution from c1.state,
build the combined execution in p1.concat p2. -/
theorem Steps.chain_concat {p1 p2 : Program} {s : State} {c1 c2 : Config}
    (h1_steps : Steps p1 ⟨0, s⟩ c1) (h1_pc : c1.pc = p1.length)
    (h2_steps : Steps p2 ⟨0, c1.state⟩ c2) (h2_halted : c2.isHalted p2) :
    Steps (p1.concat p2) ⟨0, s⟩ ⟨c2.pc + p1.length, c2.state⟩ ∧
    (⟨c2.pc + p1.length, c2.state⟩ : Config).isHalted (p1.concat p2) := by
  have h1' := Steps.concat_left_prefix (p2 := p2) h1_steps
  have h2' := Steps.concat_right (p1 := p1) h2_steps
  have hstart_eq : (⟨0 + p1.length, c1.state⟩ : Config) = ⟨c1.pc, c1.state⟩ := by simp [← h1_pc]
  rw [hstart_eq] at h2'
  exact ⟨h1'.trans h2', by simp only [Config.isHalted, Program.concat_length] at h2_halted ⊢; omega⟩

/-- Chain two programs where p1 is standard form: derives pc equality from halted. -/
theorem Steps.chain_concat_sf {p1 p2 : Program} {s : State} {c1 c2 : Config}
    (h1_sf : p1.IsStandardForm)
    (h1_steps : Steps p1 ⟨0, s⟩ c1) (h1_halted : c1.isHalted p1)
    (h2_steps : Steps p2 ⟨0, c1.state⟩ c2) (h2_halted : c2.isHalted p2) :
    Steps (p1.concat p2) ⟨0, s⟩ ⟨c2.pc + p1.length, c2.state⟩ ∧
    (⟨c2.pc + p1.length, c2.state⟩ : Config).isHalted (p1.concat p2) :=
  chain_concat h1_steps (h1_sf.pc_eq_length_of_halted h1_steps (Nat.zero_le _) h1_halted) h2_steps h2_halted

/-! ## Agreeing State Execution -/

/-- Bundle for an execution from an agreeing state. -/
structure AgreeingExecution (p : Program) (inputs : List ℕ) (s : State) where
  /-- The final configuration after execution -/
  config : Config
  steps : Steps p ⟨0, s⟩ config
  halted : config.isHalted p
  pc_eq : config.pc = p.length
  originalHalts : Halts p inputs
  state_agrees : config.state.agreeOn (Classical.choose originalHalts).state 0 p.maxRegister

/-- Execute a program from a state that agrees with the init state on relevant registers. -/
noncomputable def Halts.executeFromAgreeingState {p : Program} {inputs : List ℕ} {s : State}
    (hHalts : Halts p inputs) (hsf : p.IsStandardForm)
    (hagree : s.agreeOn (State.fromInputs inputs) 0 p.maxRegister) :
    AgreeingExecution p inputs s :=
  let e := hHalts.toExecution
  let hex := Steps.agreeOn (c₂ := ⟨0, s⟩) e.steps rfl (State.agreeOn_symm hagree)
  let c' := Classical.choose hex
  let hspec := Classical.choose_spec hex
  let hhalted' : c'.isHalted p := by
    have he := e.halted; have hpc := hspec.2.1
    simp only [Config.isHalted, show c' = Classical.choose hex from rfl] at he ⊢; omega
  ⟨c', hspec.1, hhalted', hspec.2.1.symm.trans (e.pc_eq_length hsf), hHalts, State.agreeOn_symm hspec.2.2⟩

/-- The final state's R[0] (output) matches the original execution. -/
theorem AgreeingExecution.output_eq {p : Program} {inputs : List ℕ} {s : State}
    (e : AgreeingExecution p inputs s) (hmax : 0 ≤ p.maxRegister) :
    e.config.state.read 0 = (Classical.choose e.originalHalts).state.read 0 :=
  e.state_agrees 0 (Nat.zero_le 0) hmax

/-! ## State Agreement Lemmas -/

/-- State agreement after clear+transfer: R[i]=inputs[i] for i<len, R[r]=0 for len≤r≤m. -/
theorem agrees_list_inputs_after_clear_transfer {m : ℕ} {p : Program} {s : State} {inputs : List ℕ}
    (hp : p.maxRegister ≤ m) (hs_inputs : ∀ i, i < inputs.length → s.read i = inputs.getD i 0)
    (hs_zeros : ∀ r, inputs.length ≤ r → r ≤ m → s.read r = 0) :
    s.agreeOn (State.fromInputs inputs) 0 p.maxRegister := fun r _ hhi => by
  simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD] at hs_inputs hs_zeros ⊢
  by_cases hr_in : r < inputs.length
  · rw [hs_inputs r hr_in, List.getElem?_eq_getElem hr_in]
  · simp only [hs_zeros r (Nat.le_of_not_lt hr_in) (Nat.le_trans hhi hp),
        List.getElem?_eq_none (Nat.le_of_not_lt hr_in), Option.getD_none]

/-- Result register value from agreeing state equals result from standard inputs. -/
theorem AgreeingExecution.result_matches_original {p : Program} {inputs : List ℕ} {s : State}
    (e : AgreeingExecution p inputs s) :
    e.config.state.read 0 = Result p inputs e.originalHalts := by
  simp only [Result]; exact e.output_eq (by omega)

/-! ## Transfer Instruction Properties -/

/-- Bundle single transfer execution with all properties. -/
structure SingleTransferResult (src dst : ℕ) (s : State) where
  /-- The state after the transfer instruction -/
  finalState : State
  steps : Steps [Instr.T src dst] ⟨0, s⟩ ⟨1, finalState⟩
  halted : (⟨1, finalState⟩ : Config).isHalted [Instr.T src dst]
  dst_eq : finalState.read dst = s.read src
  preserved : ∀ r, r ≠ dst → finalState.read r = s.read r

/-- Execute a single transfer and get bundled result. -/
noncomputable def executeSingleTransfer (src dst : ℕ) (s : State) : SingleTransferResult src dst s where
  finalState := s.write dst (s.read src)
  steps := .single (by apply Step.trans; simp [Program.getInstr])
  halted := by simp
  dst_eq := State.write_read_same s dst (s.read src)
  preserved := fun r hr => State.write_read_diff s r dst (s.read src) hr

/-- The final configuration after the single transfer. -/
def SingleTransferResult.config {src dst : ℕ} {s : State} (tr : SingleTransferResult src dst s) : Config :=
  ⟨1, tr.finalState⟩

/-! ## Clear Program Properties -/

theorem clearRegisters_eq_clearRegistersFrom' (maxReg : ℕ) :
    Program.clearRegisters maxReg = Program.clearRegistersFrom 0 (maxReg + 1) := by
  simp only [Program.clearRegisters, Program.clearRegistersFrom]; congr 1; funext i; simp

theorem clearRegisters_isStraightLine' (maxReg : ℕ) :
    Program.isStraightLine (Program.clearRegisters maxReg) = true := by
  simp only [Program.clearRegisters, Program.isStraightLine, List.all_map, List.all_eq_true]
  intro i _; simp [Instr.isNonJumping]

private theorem clearRegisters_finalState_eq (maxReg : ℕ) (s : State) :
    straightLineFinalState (clearRegisters_isStraightLine' maxReg) s =
    straightLineFinalState (Program.clearRegistersFrom_isStraightLine 0 (maxReg + 1)) s := by
  have ⟨hsteps1, hhalted1, _⟩ := straightLineFinalState_spec (clearRegisters_isStraightLine' maxReg) s
  have ⟨hsteps2, hhalted2, _⟩ := straightLineFinalState_spec (Program.clearRegistersFrom_isStraightLine 0 (maxReg + 1)) s
  have hsteps1' : Steps (Program.clearRegistersFrom 0 (maxReg + 1)) ⟨0, s⟩
      (Classical.choose (straightLine_halts_from_state (clearRegisters_isStraightLine' maxReg) s)) := by
    simp only [← clearRegisters_eq_clearRegistersFrom' maxReg]; exact hsteps1
  have hhalted1' : (Classical.choose (straightLine_halts_from_state
      (clearRegisters_isStraightLine' maxReg) s)).isHalted (Program.clearRegistersFrom 0 (maxReg + 1)) := by
    simp only [Config.isHalted, ← clearRegisters_eq_clearRegistersFrom' maxReg] at hhalted1 ⊢; exact hhalted1
  simp only [straightLineFinalState, Steps.halts_unique hsteps1' hhalted1' hsteps2 hhalted2]

theorem clearRegisters_preserves_above' (maxReg : ℕ) (s : State) (r : ℕ) (hr : maxReg < r) :
    (straightLineFinalState (clearRegisters_isStraightLine' maxReg) s).read r = s.read r := by
  rw [clearRegisters_finalState_eq]; exact clearRegistersFrom_preserves 0 (maxReg + 1) s r (Or.inr (by omega))

theorem clearRegisters_zeros' (maxReg : ℕ) (s : State) (r : ℕ) (hr : r ≤ maxReg) :
    (straightLineFinalState (clearRegisters_isStraightLine' maxReg) s).read r = 0 := by
  rw [clearRegisters_finalState_eq]; exact clearRegistersFrom_zeros 0 (maxReg + 1) s r ⟨Nat.zero_le r, by omega⟩

/-- For a straight-line program, c.state equals straightLineFinalState if halted from s. -/
theorem straightLineFinalState_eq_of_halted {p : Program} (hsl : p.isStraightLine = true) (s : State)
    (c : Config) (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.isHalted p) :
    c.state = straightLineFinalState hsl s :=
  Steps.halts_unique hsteps hhalted (straightLineFinalState_spec hsl s).1 (straightLineFinalState_spec hsl s).2.1 ▸ rfl

/-- When p1 is straight-line, the intermediate state equals straightLineFinalState.
    This combines suffix_of_concat_state with straightLineFinalState_eq_of_halted. -/
theorem straightLine_suffix_of_concat_state {p1 p2 : Program} {s : State} {c : Config}
    (hsl : p1.isStraightLine = true)
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.isHalted (p1.concat p2))
    (h1 : p1.IsStandardForm) :
    suffix_of_concat_state hsteps hhalted h1 = straightLineFinalState hsl s := by
  have hsteps_left := suffix_of_concat_steps_left hsteps hhalted h1
  exact straightLineFinalState_eq_of_halted hsl s ⟨p1.length, suffix_of_concat_state hsteps hhalted h1⟩
    hsteps_left (by simp)

/-- Simp lemma: decompose_concat.state equals straightLineFinalState for straight-line programs. -/
@[simp]
theorem decompose_concat_state_straightLine {p1 p2 : Program} {s : State} {c : Config}
    (hsl : p1.isStraightLine = true)
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.isHalted (p1.concat p2))
    (h1 : p1.IsStandardForm) :
    (decompose_concat hsteps hhalted h1).state = straightLineFinalState hsl s :=
  straightLine_suffix_of_concat_state hsl hsteps hhalted h1

theorem clearRegisters_exec (maxReg : ℕ) (s : State) :
    ∃ c, Steps (Program.clearRegisters maxReg) ⟨0, s⟩ c ∧
         c.isHalted (Program.clearRegisters maxReg) ∧
         c.pc = (Program.clearRegisters maxReg).length ∧
         (∀ r, r ≤ maxReg → c.state.read r = 0) ∧
         (∀ r, maxReg < r → c.state.read r = s.read r) := by
  obtain ⟨c, hsteps, hhalted, hpc⟩ := straightLine_halts_from_state (clearRegisters_isStraightLine maxReg) s
  have hstate_eq := straightLineFinalState_eq_of_halted (clearRegisters_isStraightLine maxReg) s c hsteps hhalted
  exact ⟨c, hsteps, hhalted, hpc, fun r hr => hstate_eq ▸ clearRegisters_zeros' maxReg s r hr,
    fun r hr => hstate_eq ▸ clearRegisters_preserves_above' maxReg s r hr⟩

/-! ## State Agreement Helpers -/

/-- Build agreeOn proof for state after copying inputs and clearing higher registers.
    This abstracts the common `by_cases hr_n : r < n` pattern used in gPhase proofs. -/
theorem agreeOn_after_copy_inputs {n base : ℕ} {s : State} {inputs : Fin n → ℕ}
    (hInputs : ∀ j : ℕ, (hj : j < n) → s.read j = inputs ⟨j, hj⟩)
    (hZeros : ∀ r, n ≤ r → r ≤ base → s.read r = 0) {p : Program}
    (hp_max : p.maxRegister ≤ base) :
    s.agreeOn (State.fromInputs (List.ofFn inputs)) 0 p.maxRegister := by
  intro r _hr0 hr_max
  by_cases hr_n : r < n
  · rw [hInputs r hr_n]; simp [State.fromInputs, State.read, hr_n]
  · rw [hZeros r (Nat.le_of_not_lt hr_n) (Nat.le_trans hr_max hp_max)]
    simp [State.fromInputs, State.read, hr_n]

end Urm
