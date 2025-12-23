/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.UnaryComposition

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

end Urm
