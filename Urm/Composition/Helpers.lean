/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Core

/-! # Composition Helper Lemmas

Infrastructure for proving composition theorems, extracting common patterns
from composition proofs.

## Main definitions

- `AgreeingExecution`: Bundle for execution from a state that agrees with inputs
- `Halts.executeFromAgreeingState`: Run a program from an agreeing state

## Main results

- `Steps.chain_concat`: Chain two program executions in a concatenation
- `agrees_list_inputs_after_clear_transfer`: State agreement after clear+transfer
-/

namespace Urm

/-! ## HaltingExecution Structure

Bundles a halting execution with all commonly-needed properties to avoid
repeated Classical.choose unpacking. -/

/-- Bundle for a halting execution with all its properties.
This avoids the repeated pattern of unpacking Classical.choose_spec. -/
structure HaltingExecution (p : Program) (inputs : List ℕ) where
  /-- The halted configuration -/
  config : Config
  /-- Proof that the program halts -/
  halts : Halts p inputs
  /-- Steps from initial config to halted config -/
  steps : Steps p (Config.init inputs) config
  /-- The config is halted -/
  halted : config.isHalted p

/-- Extract HaltingExecution from Halts witness. -/
noncomputable def Halts.toExecution {p : Program} {inputs : List ℕ} (h : Halts p inputs) :
    HaltingExecution p inputs where
  config := Classical.choose h
  halts := h
  steps := (Classical.choose_spec h).1
  halted := (Classical.choose_spec h).2

/-- For standard-form programs, the halted PC equals program length. -/
theorem HaltingExecution.pc_eq_length {p : Program} {inputs : List ℕ}
    (e : HaltingExecution p inputs) (hsf : p.IsStandardForm) :
    e.config.pc = p.length :=
  hsf.halts_at_length inputs e.config e.steps e.halted

/-! ## Program Chaining Lemmas

These lemmas simplify the common pattern of chaining executions through
concatenated programs. -/

/-- Chain two programs: given p1 execution ending at c1, and p2 execution from c1.state,
build the combined execution in p1.concat p2.

This is the key lemma for composing program executions. -/
theorem Steps.chain_concat {p1 p2 : Program} {s : State} {c1 c2 : Config}
    (h1_steps : Steps p1 ⟨0, s⟩ c1) (h1_halted : c1.isHalted p1)
    (h1_pc : c1.pc = p1.length)
    (h2_steps : Steps p2 ⟨0, c1.state⟩ c2) (h2_halted : c2.isHalted p2) :
    Steps (p1.concat p2) ⟨0, s⟩ ⟨c2.pc + p1.length, c2.state⟩ ∧
    (⟨c2.pc + p1.length, c2.state⟩ : Config).isHalted (p1.concat p2) := by
  constructor
  · -- Build the combined steps
    have h1' := Steps.concat_left_prefix (p2 := p2) h1_steps h1_halted
    have h2' := Steps.concat_right (p1 := p1) h2_steps h2_halted
    -- Adjust the starting point of h2'
    have hstart_eq : (⟨0 + p1.length, c1.state⟩ : Config) = ⟨c1.pc, c1.state⟩ := by
      simp only [Nat.zero_add, ← h1_pc]
    rw [hstart_eq] at h2'
    exact Relation.ReflTransGen.trans h1' h2'
  · -- Show the combined config is halted
    simp only [Config.isHalted, Program.concat_length] at h2_halted ⊢
    omega

/-! ## Agreeing State Execution

This section provides infrastructure for running a program from a state that agrees with
the standard input state. This is the key pattern used in composition proofs where we
need to run a program (like G1 or G2) from an intermediate state rather than Config.init. -/

/-- Bundle for an execution from an agreeing state.
This captures the common pattern of running a program from a state that agrees
with its original input state on the relevant registers. -/
structure AgreeingExecution (p : Program) (inputs : List ℕ) (s : State) where
  /-- The halted configuration from the agreeing state -/
  config : Config
  /-- Steps from ⟨0, s⟩ to the halted config -/
  steps : Steps p ⟨0, s⟩ config
  /-- The config is halted -/
  halted : config.isHalted p
  /-- The pc equals program length (for SF programs) -/
  pc_eq : config.pc = p.length
  /-- The original Halts witness -/
  originalHalts : Halts p inputs
  /-- Final state agrees with original final state on relevant registers -/
  state_agrees : config.state.agreeOn (Classical.choose originalHalts).state 0 p.maxRegister

/-- Run a standard form program from a state that agrees with its original input state.

This is the key helper for composition proofs. It encapsulates the common pattern of:
1. Getting the original execution from a Halts witness
2. Using Steps.agreeOn to construct parallel execution from agreeing state
3. Deriving halted and pc properties for the new execution
4. Getting state agreement between the two final states

This replaces the repeated ~10 lines of boilerplate in composition proofs. -/
noncomputable def Halts.executeFromAgreeingState {p : Program} {inputs : List ℕ} {s : State}
    (hHalts : Halts p inputs) (hsf : p.IsStandardForm)
    (hagree : s.agreeOn (State.fromInputs inputs) 0 p.maxRegister) :
    AgreeingExecution p inputs s :=
  let e := hHalts.toExecution
  let hpc_eq : (Config.init inputs).pc = (⟨0, s⟩ : Config).pc := rfl
  let hex := Steps.agreeOn e.steps hpc_eq (State.agreeOn_symm hagree)
  let c' := Classical.choose hex
  let hspec := Classical.choose_spec hex
  let hsteps' := hspec.1
  let hpc_eq' := hspec.2.1
  let hagree_final := hspec.2.2
  let hhalted' : c'.isHalted p := by
    have he : e.config.isHalted p := e.halted
    simp only [Config.isHalted] at he ⊢
    have hpc_rel : e.config.pc = c'.pc := hpc_eq'
    omega
  let hpc' : c'.pc = p.length := hpc_eq'.symm.trans (e.pc_eq_length hsf)
  ⟨c', hsteps', hhalted', hpc', hHalts, State.agreeOn_symm hagree_final⟩

/-- The final state's R[0] (output) matches the original execution. -/
theorem AgreeingExecution.output_eq {p : Program} {inputs : List ℕ} {s : State}
    (e : AgreeingExecution p inputs s) (hmax : 0 ≤ p.maxRegister) :
    e.config.state.read 0 = (Classical.choose e.originalHalts).state.read 0 :=
  e.state_agrees 0 (Nat.zero_le 0) hmax

/-! ## State Agreement Lemmas

These lemmas handle the common pattern of proving state agreement after
clear and transfer operations. -/

/-- General case: after clearing registers and setting R[0..n-1] to match inputs,
agreement holds for programs with maxRegister ≤ m.

This is the key lemma for general composition: it shows that if a state has:
- R[i] = inputs[i] for i < inputs.length
- R[r] = 0 for inputs.length ≤ r ≤ m

Then the state agrees with State.fromInputs inputs on registers 0..p.maxRegister.

Use this when setting up inputs for running gᵢ from a prepared state. -/
theorem agrees_list_inputs_after_clear_transfer {m : ℕ} {p : Program} {s : State} {inputs : List ℕ}
    (hp : p.maxRegister ≤ m)
    (hs_inputs : ∀ i, i < inputs.length → s.read i = inputs.getD i 0)
    (hs_zeros : ∀ r, inputs.length ≤ r → r ≤ m → s.read r = 0) :
    s.agreeOn (State.fromInputs inputs) 0 p.maxRegister := fun r _ hhi => by
  simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD] at hs_inputs hs_zeros ⊢
  by_cases hr_in : r < inputs.length
  · rw [hs_inputs r hr_in, List.getElem?_eq_getElem hr_in]
  · simp only [hs_zeros r (Nat.le_of_not_lt hr_in) (Nat.le_trans hhi hp),
        List.getElem?_eq_none (Nat.le_of_not_lt hr_in), Option.getD_none]

/-! ## General Composition Infrastructure

This section provides the building blocks for the general composition theorem.

### General Composition Pattern

Given:
- f : n-ary computable function (takes n inputs)
- g₁, ..., gₙ : k-ary computable functions (all take k inputs)

We want to prove h(x₁,...,xₖ) = f(g₁(xs), ..., gₙ(xs)) is computable.

The proof structure involves n+1 phases:
1. **Setup phase**: Copy k inputs to high registers m+1, ..., m+k
2. **Phases 1..n**: For each i, clear → restore inputs → run gᵢ → store result in m+k+i
3. **Final phase**: Clear → transfer n results to R[0..n-1] → run f

The key abstractions are:
- `SubprogramPhase`: Run a subprogram gᵢ from a prepared state, store result
- `agrees_list_inputs_after_clear_transfer`: State agreement for k inputs
- `AgreeingExecution`: Run program from state that agrees with inputs

### Register Layout for General Composition

For composing f (n-ary) with g₁,...,gₙ (all k-ary):
- R[0..k-1]: Working registers for running gᵢ (set up with inputs)
- R[k..m]: Additional working registers (cleared between phases)
- R[m+1..m+k]: Preserved original inputs x₁,...,xₖ
- R[m+k+1..m+k+n]: Stored results g₁(xs),...,gₙ(xs)

Where m = max(maxRegister(f), maxRegister(g₁), ..., maxRegister(gₙ)).
-/

/-- The result register value after running a subprogram from an agreeing state
equals the result from running from standard inputs.

This is the key lemma for composition: it shows that running gᵢ from a prepared
state (after clear+transfer) gives the same result as running gᵢ from Config.init. -/
theorem AgreeingExecution.result_matches_original {p : Program} {inputs : List ℕ} {s : State}
    (e : AgreeingExecution p inputs s) :
    e.config.state.read 0 = Result p inputs e.originalHalts := by
  simp only [Result]
  exact e.output_eq (by omega : 0 ≤ p.maxRegister)

/-! ## Transfer Instruction Properties -/

/-! ## SingleTransferResult Structure

Bundles single transfer execution with all commonly-needed properties to avoid
repeated unpacking and State.write_read_same/diff calls. -/

/-- Bundle single transfer execution with commonly-needed properties:
steps, halted, destination value, and register preservation. -/
structure SingleTransferResult (src dst : ℕ) (s : State) where
  /-- The final state after the transfer -/
  finalState : State
  /-- Steps from initial config to halted config -/
  steps : Steps [Instr.T src dst] ⟨0, s⟩ ⟨1, finalState⟩
  /-- The config is halted -/
  halted : (⟨1, finalState⟩ : Config).isHalted [Instr.T src dst]
  /-- The destination register has the source value -/
  dst_eq : finalState.read dst = s.read src
  /-- All other registers are preserved -/
  preserved : ∀ r, r ≠ dst → finalState.read r = s.read r

/-- Execute a single transfer and get bundled result with all properties. -/
noncomputable def executeSingleTransfer (src dst : ℕ) (s : State) :
    SingleTransferResult src dst s where
  finalState := s.write dst (s.read src)
  steps := Relation.ReflTransGen.single (by
    apply Step.trans
    simp [Program.getInstr])
  halted := by simp [Config.isHalted]
  dst_eq := State.write_read_same s dst (s.read src)
  preserved := fun r hr => State.write_read_diff s r dst (s.read src) hr

/-- The final config of a SingleTransferResult. -/
def SingleTransferResult.config {src dst : ℕ} {s : State}
    (tr : SingleTransferResult src dst s) : Config :=
  ⟨1, tr.finalState⟩

/-! ## Clear Program Properties -/

/-- clearRegisters is the same as clearRegistersFrom 0 (maxReg + 1). -/
theorem clearRegisters_eq_clearRegistersFrom' (maxReg : ℕ) :
    Program.clearRegisters maxReg = Program.clearRegistersFrom 0 (maxReg + 1) := by
  simp only [Program.clearRegisters, Program.clearRegistersFrom]
  congr 1
  funext i
  simp only [Nat.zero_add]

/-- clearRegisters is a straight-line program. -/
theorem clearRegisters_isStraightLine' (maxReg : ℕ) :
    Program.isStraightLine (Program.clearRegisters maxReg) = true := by
  simp only [Program.clearRegisters, Program.isStraightLine, List.all_map, List.all_eq_true]
  intro i _
  simp [Instr.isNonJumping]

/-- Helper: clearRegisters and clearRegistersFrom 0 (maxReg + 1) produce the same final state. -/
private theorem clearRegisters_finalState_eq (maxReg : ℕ) (s : State) :
    straightLineFinalState (clearRegisters_isStraightLine' maxReg) s =
    straightLineFinalState (Program.clearRegistersFrom_isStraightLine 0 (maxReg + 1)) s := by
  have ⟨hsteps1, hhalted1, _⟩ := straightLineFinalState_spec (clearRegisters_isStraightLine' maxReg) s
  have ⟨hsteps2, hhalted2, _⟩ :=
    straightLineFinalState_spec (Program.clearRegistersFrom_isStraightLine 0 (maxReg + 1)) s
  have hsteps1' : Steps (Program.clearRegistersFrom 0 (maxReg + 1)) ⟨0, s⟩
      (Classical.choose (straightLine_halts_from_state (clearRegisters_isStraightLine' maxReg) s)) := by
    simp only [← clearRegisters_eq_clearRegistersFrom' maxReg]; exact hsteps1
  have hhalted1' : (Classical.choose (straightLine_halts_from_state
      (clearRegisters_isStraightLine' maxReg) s)).isHalted
      (Program.clearRegistersFrom 0 (maxReg + 1)) := by
    simp only [Config.isHalted, ← clearRegisters_eq_clearRegistersFrom' maxReg] at hhalted1 ⊢
    exact hhalted1
  simp only [straightLineFinalState, Steps.halts_unique hsteps1' hhalted1' hsteps2 hhalted2]

/-- clearRegisters preserves registers above maxReg. -/
theorem clearRegisters_preserves_above' (maxReg : ℕ) (s : State) (r : ℕ) (hr : maxReg < r) :
    (straightLineFinalState (clearRegisters_isStraightLine' maxReg) s).read r = s.read r := by
  rw [clearRegisters_finalState_eq]
  exact clearRegistersFrom_preserves 0 (maxReg + 1) s r (Or.inr (by omega))

/-- clearRegisters zeros all registers up to and including maxReg. -/
theorem clearRegisters_zeros' (maxReg : ℕ) (s : State) (r : ℕ) (hr : r ≤ maxReg) :
    (straightLineFinalState (clearRegisters_isStraightLine' maxReg) s).read r = 0 := by
  rw [clearRegisters_finalState_eq]
  exact clearRegistersFrom_zeros 0 (maxReg + 1) s r ⟨Nat.zero_le r, by omega⟩

/-! ## Straight Line State Equality -/

/-- For a straight-line program, if c is the halted configuration from state s,
then c.state equals straightLineFinalState. This is a common pattern for
proving state equality after straight-line execution. -/
theorem straightLineFinalState_eq_of_halted {p : Program} (hsl : p.isStraightLine = true) (s : State)
    (c : Config) (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.isHalted p) :
    c.state = straightLineFinalState hsl s := by
  have hspec := straightLineFinalState_spec hsl s
  exact Steps.halts_unique hsteps hhalted hspec.1 hspec.2.1 ▸ rfl

/-- Execution result for clearRegisters: halts, zeros registers 0..maxReg, preserves above. -/
theorem clearRegisters_exec (maxReg : ℕ) (s : State) :
    ∃ c, Steps (Program.clearRegisters maxReg) ⟨0, s⟩ c ∧
         c.isHalted (Program.clearRegisters maxReg) ∧
         c.pc = (Program.clearRegisters maxReg).length ∧
         (∀ r, r ≤ maxReg → c.state.read r = 0) ∧
         (∀ r, maxReg < r → c.state.read r = s.read r) := by
  have hsl := clearRegisters_isStraightLine maxReg
  have hhalts := straightLine_halts_from_state hsl s
  obtain ⟨c, hsteps, hhalted, hpc⟩ := hhalts
  have hstate_eq := straightLineFinalState_eq_of_halted hsl s c hsteps hhalted
  refine ⟨c, hsteps, hhalted, hpc, ?_, ?_⟩
  · intro r hr; rw [hstate_eq]; exact clearRegisters_zeros' maxReg s r hr
  · intro r hr; rw [hstate_eq]; exact clearRegisters_preserves_above' maxReg s r hr

end Urm
