/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Extended.Eval
import Urm.Extended.Compile
import Urm.StraightLine
import Urm.Shift
import Urm.Embeddings

/-! # Extended URM: Compiler Correctness

This module proves the correctness of the ExtendedURM to base URM compiler:
running the compiled program produces the same result as the ExtendedURM semantics.

## Main Theorems

- `compileBlock_correct`: Compiled Block behaves like `runBlock`
- `compileMu_correct`: Compiled Mu behaves like `runMu`
- `compile_correct`: Full program correctness

## Proof Strategy

The correctness proof follows the structure of compilation:

### Block Correctness
1. **copyIn phase**: Straight-line, copies host registers to body workspace
2. **body phase**: Body executes with shifted registers, producing same result
3. **copyOut phase**: Straight-line, copies result back to host register

### Mu Correctness
1. **setup phase**: Straight-line, saves inputs and initializes counter
2. **loop prologue**: Straight-line, restores inputs for body execution
3. **body phase**: Body executes with shifted registers
4. **epilogue**: Checks exit condition, increments counter, loops back
5. **output phase**: Straight-line, copies result to host register

Key insight: We use `Steps`/`Halts` relations directly (not `eval`) to track
full state evolution. The `Halts.shift_from_state` lemma allows us to prove
body execution correctness by showing register agreement on R[0..maxReg].

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

namespace Extended

open Urm (Program Instr State Config Steps Step Halts Result)

/-! ## State Agreement -/

/-- Two states agree on a range of registers [lo, hi]. -/
def State.agreeOnRange (s₁ s₂ : State) (lo hi : ℕ) : Prop :=
  ∀ r, lo ≤ r → r ≤ hi → s₁ r = s₂ r

theorem State.agreeOnRange_refl (s : State) (lo hi : ℕ) : State.agreeOnRange s s lo hi :=
  fun _ _ _ => rfl

theorem State.agreeOnRange_symm {s₁ s₂ : State} {lo hi : ℕ}
    (h : State.agreeOnRange s₁ s₂ lo hi) : State.agreeOnRange s₂ s₁ lo hi :=
  fun r hlo hhi => (h r hlo hhi).symm

/-- States agree on the registers that matter for body execution. -/
def bodyStateAgrees (hostState bodyState : State) (regs : List ℕ) : Prop :=
  ∀ i : Fin regs.length, bodyState i = hostState (regs[i])

/-! ## Straight-Line Phase Execution -/

/-- Execute a straight-line phase embedded in a larger program.
Returns the configuration after the phase completes. -/
structure StraightLinePhaseResult (p : Program) (startPC : ℕ) (phase : Program) (s : State) where
  /-- Final configuration after phase -/
  finalConfig : Config
  /-- Steps from start to final -/
  steps : Steps p ⟨startPC, s⟩ finalConfig
  /-- PC after phase equals start + phase length -/
  pc_eq : finalConfig.pc = startPC + phase.length
  /-- Phase halted (at the end of the phase, not end of whole program) -/
  halted_at_phase_end : finalConfig.pc = startPC + phase.length

/-! ## Helper Lemmas for copyToBody -/

/-- After copyToBody executes, the target registers contain the source values. -/
theorem copyToBody_effect (regs : List ℕ) (base : ℕ) (s : State) :
    ∀ i : Fin regs.length,
      (straightLineFinalState (copyToBody_isStraightLine regs base) s) (base + i) = s (regs[i]) := by
  intro i
  -- copyToBody is a sequence of T instructions: T regs[j] (base + j) for each j
  -- After execution, R[base + i] = original R[regs[i]]
  sorry

/-- copyToBody preserves registers outside its write range. -/
theorem copyToBody_preserves (regs : List ℕ) (base : ℕ) (s : State) (r : ℕ)
    (hr : ∀ i : Fin regs.length, r ≠ base + i) :
    (straightLineFinalState (copyToBody_isStraightLine regs base) s) r = s r := by
  sorry

/-! ## Helper Lemmas for copyFromBody -/

/-- After copyFromBody executes, the target register contains the source value. -/
theorem copyFromBody_effect (regs : List ℕ) (base : ℕ) (s : State)
    (hregs : regs ≠ []) :
    let h0 : 0 < regs.length := List.length_pos_of_ne_nil hregs
    (straightLineFinalState (copyFromBody_isStraightLine regs base) s) (regs[0]'h0) = s base := by
  sorry

/-- copyFromBody preserves registers other than the first mapped register. -/
theorem copyFromBody_preserves (regs : List ℕ) (base : ℕ) (s : State) (r : ℕ)
    (hr : regs.head? ≠ some r) :
    (straightLineFinalState (copyFromBody_isStraightLine regs base) s) r = s r := by
  sorry

/-! ## Block Correctness -/

/-- Compiled Block is semantically equivalent to runBlock.

Given:
- A host state `s`
- A register mapping `regs`
- A body program `body` in standard form

The compiled block executes as follows:
1. Copy inputs from host registers to body workspace
2. Execute body with shifted registers
3. Copy result back to first host register

The final state agrees with runBlock semantics. -/
theorem compileBlock_correct (regs : List ℕ) (body : FlatProgram)
    (hbody_sf : body.IsStandardForm) (s : State)
    (hbody_halts : Halts body (List.ofFn fun i : Fin regs.length => s (regs[i]))) :
    Halts (compileBlock regs body) [s 0] ∧
    ∃ hH, (runBlock s regs body).Dom ∧
      ∀ hD, Result (compileBlock regs body) [s 0] hH =
        (((runBlock s regs body).get hD) 0) := by
  sorry

/-! ## Mu Setup Phase -/

/-- After muSetupPhase executes:
1. Counter register is 0
2. Zero register is 0
3. Saved inputs contain the original input values -/
theorem muSetupPhase_effect (layout : MuLayout) (regs : List ℕ) (s : State) :
    let s' := straightLineFinalState (muSetupPhase_isStraightLine layout regs) s
    s' layout.counterReg = 0 ∧
    s' layout.zeroReg = 0 ∧
    ∀ i : Fin regs.length, s' (layout.savedStart + i) = s (regs[i]) := by
  sorry

/-! ## Mu Prologue -/

/-- After muPrologue executes from state with counter = k:
1. Body input registers contain saved input values
2. Body counter input (at position n) contains k
3. Counter and zero registers are preserved -/
theorem muPrologue_effect (layout : MuLayout) (s : State) (k : ℕ)
    (hs_counter : s layout.counterReg = k)
    (hs_zero : s layout.zeroReg = 0)
    (hs_saved : ∀ i : Fin layout.n, s (layout.savedStart + i) = s (layout.savedStart + i)) :
    let s' := straightLineFinalState (muPrologue_isStraightLine layout) s
    (∀ i : Fin layout.n, s' (layout.base + i) = s (layout.savedStart + i)) ∧
    s' (layout.base + layout.n) = k ∧
    s' layout.counterReg = k ∧
    s' layout.zeroReg = 0 := by
  sorry

/-! ## Mu Loop Iteration -/

/-- Result of one Mu loop iteration. -/
structure MuIterationResult (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ)
    (s : State) (k : ℕ) where
  /-- Final configuration after iteration -/
  finalConfig : Config
  /-- Steps taken during iteration -/
  steps : Steps (compileMu regs body resultReg) ⟨(mkMuLayout regs body).n + 2, s⟩ finalConfig
  /-- Body's result in R[0] -/
  bodyResult : ℕ
  /-- Either exited (result = 0) or continued (result ≠ 0) -/
  outcome : (bodyResult = 0 ∧ finalConfig.pc = (compileMu regs body resultReg).length - 1) ∨
            (bodyResult ≠ 0 ∧ finalConfig.pc = regs.length + 2)

/-! ## Mu Correctness -/

/-- Compiled Mu is semantically equivalent to runMu.

Given:
- A host state `s`
- A register mapping `regs`
- A body program `body` in standard form
- A result register `resultReg`

The compiled Mu executes the loop until body returns 0, then writes
the result register value back to the first host register.

The final state agrees with runMu semantics. -/
theorem compileMu_correct (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ)
    (hbody_sf : body.IsStandardForm) (s : State)
    (hmu_dom : (runMu s regs body resultReg).Dom) :
    Halts (compileMu regs body resultReg) [s 0] ∧
    ∃ hH, ∀ hD, Result (compileMu regs body resultReg) [s 0] hH =
      (((runMu s regs body resultReg).get hD) 0) := by
  sorry

/-! ## Single-Instruction Execution -/

/-- For a single Z instruction, the final state writes 0 to the target register. -/
theorem single_Z_state (n : ℕ) (s : State) :
    let hsl : Program.isStraightLine [Instr.Z n] = true := rfl
    (straightLineFinalState hsl s) = s.write n 0 := by
  -- We construct the exact execution and show it's the unique halted config
  have hsl : Program.isStraightLine [Instr.Z n] = true := rfl
  have hinstr : Program.getInstr [Instr.Z n] 0 = some (Instr.Z n) := rfl
  have hstep : Step [Instr.Z n] ⟨0, s⟩ ⟨1, s.write n 0⟩ := Step.zero hinstr
  have hhalted : (⟨1, s.write n 0⟩ : Config).isHalted [Instr.Z n] := by simp [Config.isHalted]
  have hsteps : Steps [Instr.Z n] ⟨0, s⟩ ⟨1, s.write n 0⟩ := Steps.single hstep
  -- straightLineFinalState uses Classical.choose
  have hspec := straightLineFinalState_spec hsl s
  have heq : Classical.choose (straightLine_halts_from_state hsl s) = ⟨1, s.write n 0⟩ :=
    Steps.halts_unique hspec.1 hspec.2.1 hsteps hhalted
  simp only [straightLineFinalState, heq]

/-- For a single S instruction, the final state increments the target register. -/
theorem single_S_state (n : ℕ) (s : State) :
    let hsl : Program.isStraightLine [Instr.S n] = true := rfl
    (straightLineFinalState hsl s) = s.write n (s n + 1) := by
  have hsl : Program.isStraightLine [Instr.S n] = true := rfl
  have hinstr : Program.getInstr [Instr.S n] 0 = some (Instr.S n) := rfl
  have hstep : Step [Instr.S n] ⟨0, s⟩ ⟨1, s.write n (s.read n + 1)⟩ := Step.succ hinstr
  have hhalted : (⟨1, s.write n (s.read n + 1)⟩ : Config).isHalted [Instr.S n] := by simp [Config.isHalted]
  have hsteps : Steps [Instr.S n] ⟨0, s⟩ ⟨1, s.write n (s.read n + 1)⟩ := Steps.single hstep
  have hspec := straightLineFinalState_spec hsl s
  have heq : Classical.choose (straightLine_halts_from_state hsl s) = ⟨1, s.write n (s.read n + 1)⟩ :=
    Steps.halts_unique hspec.1 hspec.2.1 hsteps hhalted
  simp only [straightLineFinalState, heq, State.read]

/-- For a single T instruction, the final state copies the source to target register. -/
theorem single_T_state (m n : ℕ) (s : State) :
    let hsl : Program.isStraightLine [Instr.T m n] = true := rfl
    (straightLineFinalState hsl s) = s.write n (s m) := by
  have hsl : Program.isStraightLine [Instr.T m n] = true := rfl
  have hinstr : Program.getInstr [Instr.T m n] 0 = some (Instr.T m n) := rfl
  have hstep : Step [Instr.T m n] ⟨0, s⟩ ⟨1, s.write n (s.read m)⟩ := Step.trans hinstr
  have hhalted : (⟨1, s.write n (s.read m)⟩ : Config).isHalted [Instr.T m n] := by simp [Config.isHalted]
  have hsteps : Steps [Instr.T m n] ⟨0, s⟩ ⟨1, s.write n (s.read m)⟩ := Steps.single hstep
  have hspec := straightLineFinalState_spec hsl s
  have heq : Classical.choose (straightLine_halts_from_state hsl s) = ⟨1, s.write n (s.read m)⟩ :=
    Steps.halts_unique hspec.1 hspec.2.1 hsteps hhalted
  simp only [straightLineFinalState, heq, State.read]

/-! ## Full Compiler Correctness -/

/-- Execute a compiled instruction starting from a given state.
Returns the final configuration after the instruction halts. -/
structure InstrExecResult (p : Program) (s : State) where
  /-- Final configuration -/
  finalConfig : Config
  /-- Steps from (0, s) to finalConfig -/
  steps : Steps p ⟨0, s⟩ finalConfig
  /-- Program halted -/
  halted : finalConfig.isHalted p

/-- Each compiled instruction produces the correct result when run from a state.

This is the key correctness lemma: running the compiled instruction from
state s produces the same final state (in the relevant registers) as
evalInstr i s. -/
theorem compileInstr_correct' (i : ExtendedInstr) (s : State)
    (hwf : i.WellFormed)
    (hdom : (evalInstr i s).Dom) :
    ∃ (result : InstrExecResult (compileInstr i) s),
      result.finalConfig.state 0 = ((evalInstr i s).get hdom) 0 := by
  cases i with
  | Z n =>
    -- Z n compiles to [Z n], which halts immediately and sets R[n] to 0
    simp only [compileInstr, evalInstr]
    have hsl : Program.isStraightLine [Instr.Z n] = true := rfl
    obtain ⟨c, hsteps, hhalted, _⟩ := straightLine_halts_from_state hsl s
    refine ⟨⟨c, hsteps, hhalted⟩, ?_⟩
    -- c.state = straightLineFinalState hsl s = s.write n 0
    have hspec := straightLineFinalState_spec hsl s
    have hc_eq : c = Classical.choose (straightLine_halts_from_state hsl s) :=
      Steps.halts_unique hsteps hhalted hspec.1 hspec.2.1
    have hstate_eq : c.state = straightLineFinalState hsl s := by simp [straightLineFinalState, hc_eq]
    rw [hstate_eq, single_Z_state]
    simp only [Part.get_some]
  | S n =>
    -- S n compiles to [S n], which halts immediately and increments R[n]
    simp only [compileInstr, evalInstr]
    have hsl : Program.isStraightLine [Instr.S n] = true := rfl
    obtain ⟨c, hsteps, hhalted, _⟩ := straightLine_halts_from_state hsl s
    refine ⟨⟨c, hsteps, hhalted⟩, ?_⟩
    have hspec := straightLineFinalState_spec hsl s
    have hc_eq : c = Classical.choose (straightLine_halts_from_state hsl s) :=
      Steps.halts_unique hsteps hhalted hspec.1 hspec.2.1
    have hstate_eq : c.state = straightLineFinalState hsl s := by simp [straightLineFinalState, hc_eq]
    rw [hstate_eq, single_S_state]
    simp only [Part.get_some]
  | T m n =>
    -- T m n compiles to [T m n], which copies R[m] to R[n]
    simp only [compileInstr, evalInstr]
    have hsl : Program.isStraightLine [Instr.T m n] = true := rfl
    obtain ⟨c, hsteps, hhalted, _⟩ := straightLine_halts_from_state hsl s
    refine ⟨⟨c, hsteps, hhalted⟩, ?_⟩
    have hspec := straightLineFinalState_spec hsl s
    have hc_eq : c = Classical.choose (straightLine_halts_from_state hsl s) :=
      Steps.halts_unique hsteps hhalted hspec.1 hspec.2.1
    have hstate_eq : c.state = straightLineFinalState hsl s := by simp [straightLineFinalState, hc_eq]
    rw [hstate_eq, single_T_state]
    simp only [Part.get_some]
  | J m n q =>
    -- J is not directly evaluable in ExtendedURM context
    simp only [evalInstr] at hdom
    exact False.elim hdom
  | Block regs body =>
    -- Use compileBlock_correct
    simp only [compileInstr, evalInstr] at hdom ⊢
    sorry
  | Mu regs body resultReg =>
    -- Use compileMu_correct
    simp only [compileInstr, evalInstr] at hdom ⊢
    sorry

/-- The full compiler is correct: compiling and running an extended program
produces the same result as the extended evaluation semantics. -/
theorem compile_correct (p : ExtendedProgram) (inputs : List ℕ)
    (hwf : ExtendedProgram.WellFormed p)
    (hdom : (evalFromInputs p inputs).Dom) :
    Halts (compile p) inputs ∧
    ∃ hH, ∀ hD, Result (compile p) inputs hH = (evalFromInputs p inputs).get hD := by
  sorry

/-! ## Standard Form (Deferred) -/

/-- The compiled extended program is in standard form.
We defer this to the standardization theorem if needed. -/
theorem compile_isStandardForm' (p : ExtendedProgram)
    (hwf : ExtendedProgram.WellFormed p) :
    (compile p).IsStandardForm := by
  -- For now, we use the existing proof or defer to standardization
  sorry

end Extended

end Urm
