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
- `agrees_single_input_after_clear_transfer`: State agreement after clear+transfer
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

/-- The config in HaltingExecution equals Classical.choose of the halts proof. -/
theorem HaltingExecution.config_eq {p : Program} {inputs : List ℕ}
    (e : HaltingExecution p inputs) :
    e.config = Classical.choose e.halts :=
  Steps.halts_unique e.steps e.halted
    (Classical.choose_spec e.halts).1 (Classical.choose_spec e.halts).2

/-- For standard-form programs, the halted PC equals program length. -/
theorem HaltingExecution.pc_eq_length {p : Program} {inputs : List ℕ}
    (e : HaltingExecution p inputs) (hsf : p.IsStandardForm) :
    e.config.pc = p.length :=
  hsf.halts_at_length inputs e.config e.steps e.halted

/-- The output of a HaltingExecution equals the Result. -/
theorem HaltingExecution.output_eq_result {p : Program} {inputs : List ℕ}
    (e : HaltingExecution p inputs) :
    e.config.state.output = Result p inputs e.halts := by
  simp only [Result]
  rw [e.config_eq]

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

/-- Variant of chain_concat that returns existence of the final config. -/
theorem Steps.chain_concat_halts {p1 p2 : Program} {s : State} {c1 : Config}
    (h1_steps : Steps p1 ⟨0, s⟩ c1) (h1_halted : c1.isHalted p1)
    (h1_pc : c1.pc = p1.length)
    (h2_halts : ∃ c2, Steps p2 ⟨0, c1.state⟩ c2 ∧ c2.isHalted p2) :
    ∃ c, Steps (p1.concat p2) ⟨0, s⟩ c ∧ c.isHalted (p1.concat p2) := by
  obtain ⟨c2, h2_steps, h2_halted⟩ := h2_halts
  exact ⟨⟨c2.pc + p1.length, c2.state⟩, (Steps.chain_concat h1_steps h1_halted h1_pc h2_steps h2_halted).1,
         (Steps.chain_concat h1_steps h1_halted h1_pc h2_steps h2_halted).2⟩

/-- Chain from HaltingExecution: given p1's execution and p2 halts from final state. -/
theorem HaltingExecution.chain {p1 p2 : Program} {inputs : List ℕ}
    (e1 : HaltingExecution p1 inputs) (hsf1 : p1.IsStandardForm)
    (h2_halts : ∃ c2, Steps p2 ⟨0, e1.config.state⟩ c2 ∧ c2.isHalted p2) :
    Halts (p1.concat p2) inputs := by
  obtain ⟨c2, h2_steps, h2_halted⟩ := h2_halts
  have hpc := e1.pc_eq_length hsf1
  have ⟨hsteps, hhalted⟩ := Steps.chain_concat e1.steps e1.halted hpc h2_steps h2_halted
  exact ⟨⟨c2.pc + p1.length, c2.state⟩, hsteps, hhalted⟩

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

/-- High registers (above p.maxRegister) are preserved from the starting state. -/
theorem AgreeingExecution.preserves_high_register {p : Program} {inputs : List ℕ} {s : State}
    (e : AgreeingExecution p inputs s) (r : ℕ) (hr : p.maxRegister < r) :
    e.config.state.read r = s.read r :=
  Steps.preserves_high_register e.steps r hr

/-! ## State Agreement Lemmas

These lemmas handle the common pattern of proving state agreement after
clear and transfer operations. -/

/-- After clearing registers and a single transfer setting R[0], agreement holds
for programs with maxRegister ≤ m. -/
theorem agrees_single_input_after_clear_transfer {m : ℕ} {p : Program} {s : State} {x : ℕ}
    (hp : p.maxRegister ≤ m)
    (hs0 : s.read 0 = x)
    (hs_zeros : ∀ r, 1 ≤ r → r ≤ m → s.read r = 0) :
    s.agreeOn (State.fromInputs [x]) 0 p.maxRegister := by
  intro r _ hhi
  by_cases hr0 : r = 0
  · rw [hr0, hs0]
    simp only [State.fromInputs, State.read, List.getD_cons_zero]
  · have hr_pos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    have hr_le_m : r ≤ m := Nat.le_trans hhi hp
    rw [hs_zeros r hr_pos hr_le_m]
    simp only [State.fromInputs, State.read]
    have hr_ge : r ≥ [x].length := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr_ge, Option.getD_none]

/-- After clearing registers and two transfers setting R[0] and R[1], agreement holds
for programs with maxRegister ≤ m. -/
theorem agrees_two_inputs_after_clear_transfer {m : ℕ} {p : Program} {s : State} {v1 v2 : ℕ}
    (hp : p.maxRegister ≤ m)
    (hs0 : s.read 0 = v1)
    (hs1 : s.read 1 = v2)
    (hs_zeros : ∀ r, 2 ≤ r → r ≤ m → s.read r = 0) :
    s.agreeOn (State.fromInputs [v1, v2]) 0 p.maxRegister := by
  intro r _ hhi
  by_cases hr0 : r = 0
  · rw [hr0, hs0]
    simp only [State.fromInputs, State.read, List.getD_cons_zero]
  · by_cases hr1 : r = 1
    · rw [hr1, hs1]
      simp only [State.fromInputs, State.read, List.getD]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    · have hr_ge_2 : 2 ≤ r := by omega
      have hr_le_m : r ≤ m := Nat.le_trans hhi hp
      rw [hs_zeros r hr_ge_2 hr_le_m]
      simp only [State.fromInputs, State.read]
      have hr_ge : r ≥ [v1, v2].length := by simp; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr_ge, Option.getD_none]

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
    s.agreeOn (State.fromInputs inputs) 0 p.maxRegister := by
  intro r _ hhi
  simp only [State.fromInputs, State.read]
  by_cases hr_in : r < inputs.length
  · -- r < inputs.length: s.read r = inputs[r]
    have heq := hs_inputs r hr_in
    simp only [State.read] at heq
    rw [heq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr_in]
  · -- r ≥ inputs.length: both are 0
    have hr_ge : inputs.length ≤ r := Nat.le_of_not_lt hr_in
    have hr_le_m : r ≤ m := Nat.le_trans hhi hp
    have heq := hs_zeros r hr_ge hr_le_m
    simp only [State.read] at heq
    rw [heq, List.getD_eq_getElem?_getD, List.getElem?_eq_none hr_ge, Option.getD_none]

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

/-- Single transfer is a straight-line program. -/
theorem single_transfer_isStraightLine' (src dst : ℕ) :
    Program.isStraightLine [Instr.T src dst] = true := by
  simp [Program.isStraightLine, Instr.isNonJumping]

/-- Double transfer is a straight-line program. -/
theorem double_transfer_isStraightLine' (s1 d1 s2 d2 : ℕ) :
    Program.isStraightLine [Instr.T s1 d1, Instr.T s2 d2] = true := by
  simp [Program.isStraightLine, Instr.isNonJumping]

/-- Single transfer is standard form. -/
theorem single_transfer_isStandardForm (src dst : ℕ) :
    Program.IsStandardForm [Instr.T src dst] :=
  straightLine_isStandardForm (single_transfer_isStraightLine' src dst)

/-- Double transfer is standard form. -/
theorem double_transfer_isStandardForm (s1 d1 s2 d2 : ℕ) :
    Program.IsStandardForm [Instr.T s1 d1, Instr.T s2 d2] :=
  straightLine_isStandardForm (double_transfer_isStraightLine' s1 d1 s2 d2)

/-! ## SingleTransferResult Structure

Bundles single transfer execution with all commonly-needed properties to avoid
repeated unpacking and State.write_read_same/diff calls. -/

/-- Bundle single transfer execution with commonly-needed properties.
This eliminates the repeated pattern of:
```
have hex := single_transfer_halts src dst s
obtain ⟨c', hsteps', hhalted', hpc', hstate'⟩ := hex
-- then State.write_read_same/diff calls
```
-/
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

/-- The PC of the final config is 1. -/
theorem SingleTransferResult.pc_eq {src dst : ℕ} {s : State}
    (tr : SingleTransferResult src dst s) : tr.config.pc = 1 := rfl

/-- Halting execution exists for single transfer (for compatibility). -/
theorem SingleTransferResult.halts_exists {src dst : ℕ} {s : State}
    (tr : SingleTransferResult src dst s) :
    ∃ c, Steps [Instr.T src dst] ⟨0, s⟩ c ∧ c.isHalted [Instr.T src dst] :=
  ⟨tr.config, tr.steps, tr.halted⟩

/-- Execute a double transfer and get the final state. -/
theorem double_transfer_halts (s1 d1 s2 d2 : ℕ) (s : State) :
    ∃ c, Steps [Instr.T s1 d1, Instr.T s2 d2] ⟨0, s⟩ c ∧
         c.isHalted [Instr.T s1 d1, Instr.T s2 d2] ∧
         c.pc = 2 ∧
         c.state = (s.write d1 (s.read s1)).write d2 ((s.write d1 (s.read s1)).read s2) := by
  let s1' := s.write d1 (s.read s1)
  have hstep1 : Step [Instr.T s1 d1, Instr.T s2 d2] ⟨0, s⟩ ⟨1, s1'⟩ := by
    apply Step.trans
    simp [Program.getInstr]
  have hstep2 : Step [Instr.T s1 d1, Instr.T s2 d2] ⟨1, s1'⟩ ⟨2, s1'.write d2 (s1'.read s2)⟩ := by
    apply Step.trans
    simp [Program.getInstr]
  refine ⟨⟨2, s1'.write d2 (s1'.read s2)⟩, ?_, ?_, rfl, rfl⟩
  · exact Relation.ReflTransGen.head hstep1 (Relation.ReflTransGen.single hstep2)
  · simp [Config.isHalted]

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

/-- clearRegisters is standard form. -/
theorem clearRegisters_isStandardForm' (maxReg : ℕ) :
    Program.IsStandardForm (Program.clearRegisters maxReg) :=
  straightLine_isStandardForm (clearRegisters_isStraightLine' maxReg)

/-- clearRegisters preserves registers above maxReg. -/
theorem clearRegisters_preserves_above' (maxReg : ℕ) (s : State) (r : ℕ) (hr : maxReg < r) :
    (straightLineFinalState (clearRegisters_isStraightLine' maxReg) s).read r = s.read r := by
  have hsl := clearRegisters_isStraightLine' maxReg
  have heq := clearRegisters_eq_clearRegistersFrom' maxReg
  have hstate_eq : straightLineFinalState hsl s =
      straightLineFinalState (Program.clearRegistersFrom_isStraightLine 0 (maxReg + 1)) s := by
    have ⟨hsteps1, hhalted1, _⟩ := straightLineFinalState_spec hsl s
    have ⟨hsteps2, hhalted2, _⟩ :=
      straightLineFinalState_spec (Program.clearRegistersFrom_isStraightLine 0 (maxReg + 1)) s
    have hsteps1' : Steps (Program.clearRegistersFrom 0 (maxReg + 1)) ⟨0, s⟩
        (Classical.choose (straightLine_halts_from_state hsl s)) := by
      simp only [← heq]; exact hsteps1
    have hlen_eq : (Program.clearRegisters maxReg).length =
        (Program.clearRegistersFrom 0 (maxReg + 1)).length := by simp only [heq]
    have hhalted1' : (Classical.choose (straightLine_halts_from_state hsl s)).isHalted
        (Program.clearRegistersFrom 0 (maxReg + 1)) := by
      simp only [Config.isHalted] at hhalted1 ⊢
      rw [← hlen_eq]; exact hhalted1
    have huniq := Steps.halts_unique hsteps1' hhalted1' hsteps2 hhalted2
    simp only [straightLineFinalState]; rw [huniq]
  rw [hstate_eq]
  have hr_range : r < 0 ∨ 0 + (maxReg + 1) ≤ r := Or.inr (by omega)
  exact clearRegistersFrom_preserves 0 (maxReg + 1) s r hr_range

/-- clearRegisters zeros all registers up to and including maxReg. -/
theorem clearRegisters_zeros' (maxReg : ℕ) (s : State) (r : ℕ) (hr : r ≤ maxReg) :
    (straightLineFinalState (clearRegisters_isStraightLine' maxReg) s).read r = 0 := by
  have heq := clearRegisters_eq_clearRegistersFrom' maxReg
  have hsl := clearRegisters_isStraightLine' maxReg
  have hstate_eq : straightLineFinalState hsl s =
      straightLineFinalState (Program.clearRegistersFrom_isStraightLine 0 (maxReg + 1)) s := by
    have ⟨hsteps1, hhalted1, _⟩ := straightLineFinalState_spec hsl s
    have ⟨hsteps2, hhalted2, _⟩ :=
      straightLineFinalState_spec (Program.clearRegistersFrom_isStraightLine 0 (maxReg + 1)) s
    have hsteps1' : Steps (Program.clearRegistersFrom 0 (maxReg + 1)) ⟨0, s⟩
        (Classical.choose (straightLine_halts_from_state hsl s)) := by
      simp only [← heq]; exact hsteps1
    have hlen_eq : (Program.clearRegisters maxReg).length =
        (Program.clearRegistersFrom 0 (maxReg + 1)).length := by simp only [heq]
    have hhalted1' : (Classical.choose (straightLine_halts_from_state hsl s)).isHalted
        (Program.clearRegistersFrom 0 (maxReg + 1)) := by
      simp only [Config.isHalted] at hhalted1 ⊢
      rw [← hlen_eq]; exact hhalted1
    have huniq := Steps.halts_unique hsteps1' hhalted1' hsteps2 hhalted2
    simp only [straightLineFinalState]; rw [huniq]
  rw [hstate_eq]
  have hr_range : 0 ≤ r ∧ r < 0 + (maxReg + 1) := ⟨Nat.zero_le r, by omega⟩
  exact clearRegistersFrom_zeros 0 (maxReg + 1) s r hr_range

/-- Clear followed by transfer(s) from high registers sets up state correctly.
This is the key setup lemma for composition. -/
theorem clear_and_setup_single {m x : ℕ} {s : State}
    (hs_high : s.read (m + 1) = x) :
    ∃ s' : State,
      (∃ c, Steps (Program.clearRegisters m) ⟨0, s⟩ c ∧
            c.isHalted (Program.clearRegisters m) ∧
            Steps [Instr.T (m + 1) 0] ⟨0, c.state⟩ ⟨1, s'⟩) ∧
      s'.read 0 = x ∧
      (∀ r, 1 ≤ r → r ≤ m → s'.read r = 0) ∧
      s'.read (m + 1) = x := by
  -- Clear halts
  have hClear_sl := clearRegisters_isStraightLine' m
  have hClear_halts := straightLine_halts_from_state hClear_sl s
  obtain ⟨cClear, hClear_steps, hClear_halted, _⟩ := hClear_halts
  -- Clear preserves R[m+1]
  have hClear_state_eq : cClear.state = straightLineFinalState hClear_sl s := by
    have hspec := straightLineFinalState_spec hClear_sl s
    exact Steps.halts_unique hClear_steps hClear_halted hspec.1 hspec.2.1 ▸ rfl
  have hClear_preserves : cClear.state.read (m + 1) = s.read (m + 1) := by
    rw [hClear_state_eq]
    exact clearRegisters_preserves_above' m s (m + 1) (by omega)
  -- Transfer sets R[0]
  let s' := cClear.state.write 0 (cClear.state.read (m + 1))
  have hT_step : Step [Instr.T (m + 1) 0] ⟨0, cClear.state⟩ ⟨1, s'⟩ := by
    apply Step.trans
    simp [Program.getInstr]
  refine ⟨s', ⟨cClear, hClear_steps, hClear_halted, Relation.ReflTransGen.single hT_step⟩, ?_, ?_, ?_⟩
  · -- s'.read 0 = x
    simp only [s', State.write_read_same, hClear_preserves, hs_high]
  · -- ∀ r, 1 ≤ r → r ≤ m → s'.read r = 0
    intro r hr1 hrm
    simp only [s']
    rw [State.write_read_diff _ _ _ _ (by omega : r ≠ 0)]
    rw [hClear_state_eq]
    exact clearRegisters_zeros' m s r hrm
  · -- s'.read (m + 1) = x
    simp only [s']
    rw [State.write_read_diff _ _ _ _ (by omega : m + 1 ≠ 0)]
    rw [hClear_preserves, hs_high]

/-! ## Binary-Unary Composition Components

Structure bundling the program components used in binary-unary composition.
This eliminates the repeated ~15-line setup block in each composition theorem. -/

/-- The base register for safe storage in binary-unary composition.
This is at least 1 (to avoid collision with R[1] used for binary input) and
above all registers used by F, G₁, and G₂. -/
def compositionBaseBU (pF pG1 pG2 : Program) : ℕ :=
  max 1 (max pF.maxRegister (max pG1.maxRegister pG2.maxRegister))

/-- Components of a binary-unary composition program.
Bundles all the sub-programs and phases used in composeBU. -/
structure ComposeBUComponents (pF pG1 pG2 : Program) where
  /-- The base register for safe storage -/
  m : ℕ := compositionBaseBU pF pG1 pG2
  /-- T01: Copy input to safe storage R[m+1] -/
  T01 : Program := [Instr.T 0 (m + 1)]
  /-- T02: Save g1 result to R[m+2] -/
  T02 : Program := [Instr.T 0 (m + 2)]
  /-- Clear program: zeros R[0..m] -/
  clearProg : Program := Program.clearRegisters m
  /-- T10: Restore input from R[m+1] to R[0] -/
  T10 : Program := [Instr.T (m + 1) 0]
  /-- T03: Save g2 result to R[m+3] -/
  T03 : Program := [Instr.T 0 (m + 3)]
  /-- Tsetup: Set up F's inputs from saved results -/
  Tsetup : Program := [Instr.T (m + 2) 0, Instr.T (m + 3) 1]
  /-- Phase 1: Run G1 and save result -/
  phase1 : Program := T01.concat (pG1.concat T02)
  /-- Phase 2: Restore input, run G2, save result -/
  phase2 : Program := clearProg.concat (T10.concat (pG2.concat T03))
  /-- Phase 3: Set up F's inputs and run F -/
  phase3 : Program := clearProg.concat (Tsetup.concat pF)

/-- The default (canonical) components for a binary-unary composition. -/
def ComposeBUComponents.mk' (pF pG1 pG2 : Program) : ComposeBUComponents pF pG1 pG2 := {}

namespace ComposeBUComponents

variable {pF pG1 pG2 : Program}

/-- m is at least 1 (for the default components). -/
theorem m_ge_1' : 1 ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU]
  exact Nat.le_max_left _ _

/-- m is at least pF.maxRegister (for the default components). -/
theorem m_ge_F' : pF.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU, le_max_iff]; omega

/-- m is at least pG1.maxRegister (for the default components). -/
theorem m_ge_G1' : pG1.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU, le_max_iff]; omega

/-- m is at least pG2.maxRegister (for the default components). -/
theorem m_ge_G2' : pG2.maxRegister ≤ compositionBaseBU pF pG1 pG2 := by
  simp only [compositionBaseBU, le_max_iff]; omega

/-- Single transfer [T src dst] is straight-line. -/
private theorem single_T_isStraightLine (src dst : ℕ) :
    Program.isStraightLine [Instr.T src dst] = true := rfl

/-- Double transfer is straight-line. -/
private theorem double_T_isStraightLine (s1 d1 s2 d2 : ℕ) :
    Program.isStraightLine [Instr.T s1 d1, Instr.T s2 d2] = true := rfl

/-- T01 is straight-line for any m. -/
theorem T01_isStraightLine' (m : ℕ) : Program.isStraightLine [Instr.T 0 (m + 1)] = true := rfl

/-- T02 is straight-line for any m. -/
theorem T02_isStraightLine' (m : ℕ) : Program.isStraightLine [Instr.T 0 (m + 2)] = true := rfl

/-- T10 is straight-line for any m. -/
theorem T10_isStraightLine' (m : ℕ) : Program.isStraightLine [Instr.T (m + 1) 0] = true := rfl

/-- T03 is straight-line for any m. -/
theorem T03_isStraightLine' (m : ℕ) : Program.isStraightLine [Instr.T 0 (m + 3)] = true := rfl

/-- Tsetup is straight-line for any m. -/
theorem Tsetup_isStraightLine' (m : ℕ) :
    Program.isStraightLine [Instr.T (m + 2) 0, Instr.T (m + 3) 1] = true := rfl

/-- clearProg is straight-line. -/
theorem clearProg_isStraightLine' (m : ℕ) :
    (Program.clearRegisters m).isStraightLine = true :=
  clearRegisters_isStraightLine' m

/-- T01 is standard form for any m. -/
theorem T01_sf' (m : ℕ) : Program.IsStandardForm [Instr.T 0 (m + 1)] :=
  straightLine_isStandardForm (T01_isStraightLine' m)

/-- T02 is standard form for any m. -/
theorem T02_sf' (m : ℕ) : Program.IsStandardForm [Instr.T 0 (m + 2)] :=
  straightLine_isStandardForm (T02_isStraightLine' m)

/-- T10 is standard form for any m. -/
theorem T10_sf' (m : ℕ) : Program.IsStandardForm [Instr.T (m + 1) 0] :=
  straightLine_isStandardForm (T10_isStraightLine' m)

/-- T03 is standard form for any m. -/
theorem T03_sf' (m : ℕ) : Program.IsStandardForm [Instr.T 0 (m + 3)] :=
  straightLine_isStandardForm (T03_isStraightLine' m)

/-- Tsetup is standard form for any m. -/
theorem Tsetup_sf' (m : ℕ) : Program.IsStandardForm [Instr.T (m + 2) 0, Instr.T (m + 3) 1] :=
  straightLine_isStandardForm (Tsetup_isStraightLine' m)

/-- clearProg is standard form for any m. -/
theorem clearProg_sf' (m : ℕ) : (Program.clearRegisters m).IsStandardForm :=
  straightLine_isStandardForm (clearProg_isStraightLine' m)

/-- Phase 1 (T01 ++ G1 ++ T02) is standard form if pG1 is. -/
theorem phase1_sf' (m : ℕ) (hG1 : pG1.IsStandardForm) :
    (Program.concat [Instr.T 0 (m + 1)] (Program.concat pG1 [Instr.T 0 (m + 2)])).IsStandardForm :=
  (T01_sf' m).concat (hG1.concat (T02_sf' m))

/-- Phase 2 (Clear ++ T10 ++ G2 ++ T03) is standard form if pG2 is. -/
theorem phase2_sf' (m : ℕ) (hG2 : pG2.IsStandardForm) :
    (Program.concat (Program.clearRegisters m)
      (Program.concat [Instr.T (m + 1) 0] (Program.concat pG2 [Instr.T 0 (m + 3)]))).IsStandardForm :=
  (clearProg_sf' m).concat ((T10_sf' m).concat (hG2.concat (T03_sf' m)))

/-- Phase 3 (Clear ++ Tsetup ++ F) is standard form if pF is. -/
theorem phase3_sf' (m : ℕ) (hF : pF.IsStandardForm) :
    (Program.concat (Program.clearRegisters m)
      (Program.concat [Instr.T (m + 2) 0, Instr.T (m + 3) 1] pF)).IsStandardForm :=
  (clearProg_sf' m).concat ((Tsetup_sf' m).concat hF)

end ComposeBUComponents

/-! ## Single Transfer Instruction Execution -/

/-- A single Transfer instruction takes exactly one step and halts. -/
theorem single_transfer_step (src dst : ℕ) (s : State) :
    Step [Instr.T src dst] ⟨0, s⟩ ⟨1, s.write dst (s.read src)⟩ := by
  apply Step.trans
  simp [Program.getInstr]

/-- A single Transfer instruction halts at pc = 1 with the copied value. -/
theorem single_transfer_halts (src dst : ℕ) (s : State) :
    ∃ c', Steps [Instr.T src dst] ⟨0, s⟩ c' ∧
          c'.isHalted [Instr.T src dst] ∧
          c'.pc = 1 ∧
          c'.state = s.write dst (s.read src) := by
  refine ⟨⟨1, s.write dst (s.read src)⟩, ?_, ?_, rfl, rfl⟩
  · exact Relation.ReflTransGen.single (single_transfer_step src dst s)
  · simp [Config.isHalted]

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
