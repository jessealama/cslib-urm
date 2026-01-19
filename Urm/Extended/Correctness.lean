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
import Urm.Halting.PhaseExecution

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
theorem copyToBody_effect (regs : List ℕ) (base : ℕ) (s : State)
    (hbase : ∀ r ∈ regs, r < base) :
    ∀ i : Fin regs.length,
      (straightLineFinalState (copyToBody_isStraightLine regs base) s) (base + i) = s (regs[i]) := by
  intro ⟨i, hi⟩
  have hsl := copyToBody_isStraightLine regs base
  -- copyToBody is a sequence of T instructions: T regs[j] (base + j) for each j
  -- The instruction at position i is T (regs[i]) (base + i)
  have hcopy_len : (copyToBody regs base).length = regs.length := by
    simp only [copyToBody, List.length_mapIdx]
  have hi_lt : i < (copyToBody regs base).length := hcopy_len ▸ hi
  have hwrite : (copyToBody regs base)[i]'hi_lt = Instr.T (regs[i]) (base + i) := by
    simp only [copyToBody, List.getElem_mapIdx]
  -- No later instruction writes to (base + i)
  have hnowrite : ∀ j (hj : j < (copyToBody regs base).length),
      i < j → ((copyToBody regs base)[j]'hj).writesTo ≠ some (base + i) := by
    intro j hj hij
    simp only [copyToBody, List.getElem_mapIdx, Instr.writesTo, ne_eq, Option.some.injEq]
    omega
  -- By straightLine_transfer_result, final state has the transfer result
  obtain ⟨s_before, ⟨c_i, hsteps_i, hpc_i, hs_before⟩, hresult⟩ :=
    straightLine_transfer_result hsl s i (regs[i]) (base + i) hi_lt hwrite hnowrite
  simp only [State.read] at hresult ⊢
  rw [hresult, ← hs_before]
  -- Now show that c_i.state (regs[i]) = s (regs[i])
  -- This is because earlier T instructions write to base+0, base+1, ..., base+(i-1)
  -- and regs[i] < base, so they don't overwrite regs[i]
  have hregs_i_lt : regs[i] < base := hbase (regs[i]) (List.getElem_mem hi)
  have hpreserved : ∀ j (hj : j < i), ((copyToBody regs base)[j]'(Nat.lt_trans hj hi_lt)).writesTo ≠ some (regs[i]) := by
    intro j hj
    simp only [copyToBody, List.getElem_mapIdx, Instr.writesTo, ne_eq, Option.some.injEq]
    omega
  -- Use Steps.straightLine_preserves_partial to show regs[i] is unchanged
  have hpres := Steps.straightLine_preserves_partial hsl (Nat.le_of_lt hi_lt) hpreserved c_i hsteps_i hpc_i
  simp only [State.read] at hpres
  exact hpres

/-- copyToBody preserves registers outside its write range. -/
theorem copyToBody_preserves (regs : List ℕ) (base : ℕ) (s : State) (r : ℕ)
    (hr : ∀ i : Fin regs.length, r ≠ base + i) :
    (straightLineFinalState (copyToBody_isStraightLine regs base) s) r = s r := by
  have hsl := copyToBody_isStraightLine regs base
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  apply Steps.straightLine_preserves hsl hsteps
  intro instr hmem
  simp only [copyToBody, List.mem_mapIdx] at hmem
  obtain ⟨i, hi, rfl⟩ := hmem
  simp only [Instr.writesTo, ne_eq, Option.some.injEq]
  exact Ne.symm (hr ⟨i, hi⟩)

/-! ## Helper Lemmas for copyFromBody -/

/-- After copyFromBody executes, the target register contains the source value. -/
theorem copyFromBody_effect (regs : List ℕ) (base : ℕ) (s : State)
    (hregs : regs ≠ []) :
    let h0 : 0 < regs.length := List.length_pos_of_ne_nil hregs
    (straightLineFinalState (copyFromBody_isStraightLine regs base) s) (regs[0]'h0) = s base := by
  match regs with
  | [] => exact absurd rfl hregs
  | r :: rs =>
    -- copyFromBody (r :: rs) base = [T base r]
    -- This is a single T instruction that copies base to r
    have hsl : Program.isStraightLine [Instr.T base r] = true := rfl
    have hspec := straightLineFinalState_spec hsl s
    have hinstr : Program.getInstr [Instr.T base r] 0 = some (Instr.T base r) := rfl
    have hstep : Step [Instr.T base r] ⟨0, s⟩ ⟨1, s.write r (s.read base)⟩ := Step.trans hinstr
    have hhalted : (⟨1, s.write r (s.read base)⟩ : Config).isHalted [Instr.T base r] := by simp [Config.isHalted]
    have hsteps : Steps [Instr.T base r] ⟨0, s⟩ ⟨1, s.write r (s.read base)⟩ := Steps.single hstep
    have heq : Classical.choose (straightLine_halts_from_state hsl s) = ⟨1, s.write r (s.read base)⟩ :=
      Steps.halts_unique hspec.1 hspec.2.1 hsteps hhalted
    -- Goal: straightLineFinalState ... s (r :: rs)[0] = s base
    -- (r :: rs)[0] = r, and the final state writes (s base) to r
    simp only [straightLineFinalState, heq, State.write, State.read, List.getElem_cons_zero,
               Function.update_self]

/-- copyFromBody preserves registers other than the first mapped register. -/
theorem copyFromBody_preserves (regs : List ℕ) (base : ℕ) (s : State) (r : ℕ)
    (hr : regs.head? ≠ some r) :
    (straightLineFinalState (copyFromBody_isStraightLine regs base) s) r = s r := by
  match regs with
  | [] =>
    -- copyFromBody [] base = [], empty program, state unchanged
    have hsl : Program.isStraightLine ([] : Program) = true := rfl
    have hspec := straightLineFinalState_spec hsl s
    have hsteps : Steps [] ⟨0, s⟩ ⟨0, s⟩ := Steps.refl ⟨0, s⟩
    have hhalted : (⟨0, s⟩ : Config).isHalted [] := by simp [Config.isHalted]
    have heq : Classical.choose (straightLine_halts_from_state hsl s) = ⟨0, s⟩ :=
      Steps.halts_unique hspec.1 hspec.2.1 hsteps hhalted
    simp only [straightLineFinalState, heq]
  | r0 :: rs =>
    -- copyFromBody (r0 :: rs) base = [T base r0]
    -- The T instruction writes to r0, so r ≠ r0 means r is preserved
    have hr0 : r ≠ r0 := by
      simp only [List.head?] at hr
      intro heq
      exact hr (heq ▸ rfl)
    have hsl : Program.isStraightLine [Instr.T base r0] = true := rfl
    have hspec := straightLineFinalState_spec hsl s
    have hinstr : Program.getInstr [Instr.T base r0] 0 = some (Instr.T base r0) := rfl
    have hstep : Step [Instr.T base r0] ⟨0, s⟩ ⟨1, s.write r0 (s.read base)⟩ := Step.trans hinstr
    have hhalted : (⟨1, s.write r0 (s.read base)⟩ : Config).isHalted [Instr.T base r0] := by simp [Config.isHalted]
    have hsteps : Steps [Instr.T base r0] ⟨0, s⟩ ⟨1, s.write r0 (s.read base)⟩ := Steps.single hstep
    have heq : Classical.choose (straightLine_halts_from_state hsl s) = ⟨1, s.write r0 (s.read base)⟩ :=
      Steps.halts_unique hspec.1 hspec.2.1 hsteps hhalted
    simp only [straightLineFinalState, heq, State.write, State.read]
    exact Function.update_of_ne hr0 (s base) s

/-! ## Block Correctness -/

/-- Compiled Block is semantically equivalent to runBlock.

Given:
- A host state `s`
- A register mapping `regs`
- A body program `body` in standard form
- Workspace registers are zeroed

The compiled block executes as follows:
1. Copy inputs from host registers to body workspace
2. Execute body with shifted registers
3. Copy result back to first host register

The final state agrees with runBlock semantics.

Note: We use Steps directly from state `s` (not Halts from Config.init) because
compileBlock needs to read from all registers in `regs`, not just R[0].

The `hworkspace_zero` hypothesis requires that workspace registers beyond the
input region are zeroed. This is automatically satisfied when running from
a fresh Config.init state or when properly set up by an outer compilation. -/
theorem compileBlock_correct (regs : List ℕ) (body : FlatProgram)
    (hbody_sf : body.IsStandardForm) (s : State) (hregs : regs ≠ [])
    (hbody_halts : Halts body (List.ofFn fun i : Fin regs.length => s (regs[i])))
    (hworkspace_zero : ∀ r, regs.length ≤ r → r ≤ body.maxRegister →
        s (r + registerBase regs) = 0) :
    ∃ c, Steps (compileBlock regs body) ⟨0, s⟩ c ∧
         c.isHalted (compileBlock regs body) ∧
         c.state (regs[0]'(List.length_pos_of_ne_nil hregs)) =
           Result body (List.ofFn fun i : Fin regs.length => s (regs[i])) hbody_halts := by
  -- compileBlock = copyIn ++ shiftedBody ++ copyOut
  -- Phase 1: Execute copyIn (straight-line)
  let base := registerBase regs
  have hbase : ∀ r ∈ regs, r < base := registerBase_gt_all regs

  -- Execute copyIn phase
  have hsl_copyIn := copyToBody_isStraightLine regs base
  have ⟨c_copyIn, hsteps_copyIn, hhalted_copyIn, hpc_copyIn⟩ :=
    straightLine_halts_from_state hsl_copyIn s

  -- After copyIn: R[base + i] = s(regs[i])
  have h_copyIn_effect : ∀ i : Fin regs.length,
      c_copyIn.state (base + i) = s (regs[i]) := by
    intro i
    have hspec := straightLineFinalState_spec hsl_copyIn s
    have hc_eq : c_copyIn = Classical.choose (straightLine_halts_from_state hsl_copyIn s) :=
      Steps.halts_unique hsteps_copyIn hhalted_copyIn hspec.1 hspec.2.1
    rw [show c_copyIn.state = straightLineFinalState hsl_copyIn s by simp [straightLineFinalState, hc_eq]]
    exact copyToBody_effect regs base s hbase i

  -- The inputs for body are exactly what copyIn produced
  let bodyInputs := List.ofFn fun i : Fin regs.length => s (regs[i])

  -- copyIn preserves registers outside [base, base + regs.length - 1]
  have h_copyIn_preserves : ∀ r, (∀ i : Fin regs.length, r ≠ base + i) →
      c_copyIn.state r = s r := by
    intro r hr
    have hspec := straightLineFinalState_spec hsl_copyIn s
    have hc_eq : c_copyIn = Classical.choose (straightLine_halts_from_state hsl_copyIn s) :=
      Steps.halts_unique hsteps_copyIn hhalted_copyIn hspec.1 hspec.2.1
    rw [show c_copyIn.state = straightLineFinalState hsl_copyIn s by simp [straightLineFinalState, hc_eq]]
    exact copyToBody_preserves regs base s r hr

  -- Phase 2: Execute shifted body using Halts.shift_from_state
  -- The agreement condition: for r ≤ body.maxRegister, c_copyIn.state(r + base) = bodyInputs.getD r 0
  have h_agreement : ∀ r, r ≤ body.maxRegister →
      c_copyIn.state.read (r + base) = bodyInputs.getD r 0 := by
    intro r hr
    simp only [State.read]
    by_cases hr_lt : r < regs.length
    · -- r < regs.length: use h_copyIn_effect
      have heq : (base + r) = (r + base) := Nat.add_comm base r
      rw [← heq]
      -- bodyInputs.getD r 0 = bodyInputs[r] when r < length
      have hlen : bodyInputs.length = regs.length := List.length_ofFn
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hr_lt)]
      simp only [Option.getD_some, bodyInputs, List.getElem_ofFn]
      exact h_copyIn_effect ⟨r, hr_lt⟩
    · -- r ≥ regs.length: register is 0 in bodyInputs, wasn't written by copyIn
      -- bodyInputs.getD r 0 = 0 when r ≥ length
      have hlen : bodyInputs.length = regs.length := List.length_ofFn
      have hge : regs.length ≤ r := Nat.not_lt.mp hr_lt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hlen ▸ hge)]
      simp only [Option.getD_none]
      -- Show copyIn preserves this register
      have hne : ∀ i : Fin regs.length, r + base ≠ base + i := by
        intro ⟨i, hi⟩
        omega
      rw [h_copyIn_preserves (r + base) hne]
      exact hworkspace_zero r hge hr

  -- Apply Halts.shift_from_state to get body execution
  have ⟨c_body, hsteps_body, hhalted_body, hresult_body⟩ :=
    Halts.shift_from_state base hbody_halts h_agreement

  -- Lift body steps to the full program using Steps.shiftJumps_at_offset
  let copyIn := copyToBody regs base
  let shiftedBody := (body.shiftRegisters base).shiftJumps copyIn.length
  let copyOut := copyFromBody regs base
  have hcompile : compileBlock regs body = copyIn ++ shiftedBody ++ copyOut := by
    simp only [compileBlock, copyIn, shiftedBody, copyOut, base]

  -- Embedding condition: instructions at offset copyIn.length match shiftedBody
  have hbody_embed : ∀ i, i < (body.shiftRegisters base).length →
      (compileBlock regs body).getInstr (copyIn.length + i) =
      ((body.shiftRegisters base).shiftJumps copyIn.length).getInstr i := by
    intro i hi
    simp only [Program.shiftRegisters_length] at hi
    have hlen_copyIn : copyIn.length = regs.length := by
      simp only [copyIn, copyToBody, List.length_mapIdx]
    have hlen_shifted : shiftedBody.length = body.length := by
      simp only [shiftedBody, Program.shiftJumps_length, Program.shiftRegisters_length]
    -- compileBlock = copyIn ++ shiftedBody ++ copyOut
    -- We need (copyIn ++ shiftedBody ++ copyOut)[copyIn.length + i]?
    --       = shiftedBody[i]?
    simp only [compileBlock, Program.getInstr]
    -- First, show copyIn.length + i < copyIn.length + shiftedBody.length
    have hlt1 : copyIn.length + i < (copyIn ++ shiftedBody).length := by
      simp only [List.length_append, hlen_shifted]; omega
    rw [List.getElem?_append_left hlt1]
    -- Now show copyIn.length + i ≥ copyIn.length to get into shiftedBody
    rw [List.getElem?_append_right (by omega : copyIn.length ≤ copyIn.length + i)]
    simp only [Nat.add_sub_cancel_left, shiftedBody, Program.shiftJumps, Program.shiftRegisters,
      List.getElem?_map]

  -- Lift body steps
  have hsteps_body_lifted := Steps.shiftJumps_at_offset copyIn.length hbody_embed hsteps_body

  -- copyIn.length = regs.length
  have hlen_copyIn : copyIn.length = regs.length := by
    simp only [copyIn, copyToBody, List.length_mapIdx]

  -- Lift copyIn steps to full program
  have hcopyIn_embed : ∀ i, i < copyIn.length →
      (compileBlock regs body).getInstr (0 + i) = copyIn.getInstr i := by
    intro i hi
    simp only [copyIn, hlen_copyIn] at hi
    simp only [compileBlock, Program.getInstr, Nat.zero_add]
    -- compileBlock = copyToBody ++ shifted ++ copyFromBody
    -- We need (copyToBody ++ shifted ++ copyFromBody)[i]? = copyToBody[i]?
    have hlen_copyIn' : (copyToBody regs (registerBase regs)).length = regs.length := by
      simp only [copyToBody, List.length_mapIdx]
    have hlen_sh : (Program.shiftJumps (copyToBody regs (registerBase regs)).length
        (Program.shiftRegisters (registerBase regs) body)).length = body.length := by
      simp only [Program.shiftJumps_length, Program.shiftRegisters_length]
    rw [List.getElem?_append_left]
    · rw [List.getElem?_append_left (by rw [hlen_copyIn']; exact hi)]
    · simp only [List.length_append, hlen_copyIn']; omega
  have hsteps_copyIn_lifted : Steps (compileBlock regs body) ⟨0, s⟩ ⟨copyIn.length, c_copyIn.state⟩ := by
    have h := Steps.straightLine_at_offset 0 hsl_copyIn hcopyIn_embed hsteps_copyIn
    simp only [Nat.zero_add, Nat.add_zero] at h
    convert h using 2
    simp only [copyIn, hpc_copyIn]

  -- Chain copyIn and body steps
  have hsteps_body_from_copyIn : Steps (compileBlock regs body)
      ⟨copyIn.length, c_copyIn.state⟩
      ⟨copyIn.length + c_body.pc, c_body.state⟩ := by
    convert hsteps_body_lifted using 2

  have hsteps_copyIn_body := Relation.ReflTransGen.trans hsteps_copyIn_lifted hsteps_body_from_copyIn

  -- Body halts at PC = body.length (standard form property)
  have hbody_sf_shifted := shiftRegisters_isStandardForm hbody_sf base
  have hbody_pc : c_body.pc = body.length := by
    have h := Program.IsStandardForm.pc_eq_length_of_halted hbody_sf_shifted hsteps_body (Nat.zero_le _) hhalted_body
    simp only [Program.shiftRegisters_length] at h
    exact h

  -- After body: PC = copyIn.length + body.length = start of copyOut
  have hpc_after_body : copyIn.length + c_body.pc = copyIn.length + body.length := by
    rw [hbody_pc]

  -- Phase 3: Execute copyOut (single T instruction if regs ≠ [])
  have hsl_copyOut := copyFromBody_isStraightLine regs base
  have ⟨c_copyOut, hsteps_copyOut, hhalted_copyOut_local, hpc_copyOut⟩ :=
    straightLine_halts_from_state hsl_copyOut c_body.state

  -- copyOut is at offset copyIn.length + body.length in the full program
  let copyOutOffset := copyIn.length + body.length
  have hcopyOut_embed : ∀ i, i < copyOut.length →
      (compileBlock regs body).getInstr (copyOutOffset + i) = copyOut.getInstr i := by
    intro i hi
    have hlen_copyIn' : copyIn.length = regs.length := by
      simp only [copyIn, copyToBody, List.length_mapIdx]
    have hlen_sh : shiftedBody.length = body.length := by
      simp only [shiftedBody, Program.shiftJumps_length, Program.shiftRegisters_length]
    have hlen_out : copyOut.length = if regs = [] then 0 else 1 := by
      simp only [copyOut, copyFromBody]; cases regs with | nil => rfl | cons _ _ => rfl
    -- compileBlock = copyIn ++ shiftedBody ++ copyOut
    rw [hcompile]
    simp only [Program.getInstr]
    -- Need: (copyIn ++ shiftedBody ++ copyOut)[copyOutOffset + i]? = copyOut[i]?
    -- copyOutOffset = copyIn.length + body.length = copyIn.length + shiftedBody.length
    have hoff : copyOutOffset = copyIn.length + shiftedBody.length := by
      simp only [copyOutOffset, hlen_sh]
    have h1 : copyOutOffset + i ≥ (copyIn ++ shiftedBody).length := by
      simp only [List.length_append, hlen_sh, copyOutOffset]; omega
    rw [List.getElem?_append_right h1]
    simp only [List.length_append, hoff, Nat.add_sub_cancel_left]

  have hsteps_copyOut_lifted := Steps.straightLine_at_offset copyOutOffset hsl_copyOut
    hcopyOut_embed hsteps_copyOut

  -- Rewrite to chain with body steps
  have hsteps_copyOut_from_body : Steps (compileBlock regs body)
      ⟨copyIn.length + c_body.pc, c_body.state⟩
      ⟨copyOutOffset + c_copyOut.pc, c_copyOut.state⟩ := by
    convert hsteps_copyOut_lifted using 2

  -- Chain all steps
  have hsteps_all := Relation.ReflTransGen.trans hsteps_copyIn_body hsteps_copyOut_from_body

  -- Final configuration
  let c_final : Config := ⟨copyOutOffset + c_copyOut.pc, c_copyOut.state⟩

  -- Show final PC = program length (halted)
  have hfinal_halted : c_final.isHalted (compileBlock regs body) := by
    simp only [Config.isHalted, compileBlock_length, c_final, copyOutOffset, hpc_copyOut]
    simp only [copyFromBody]
    cases regs with
    | nil => exact absurd rfl hregs
    | cons h t =>
      simp only [List.length_cons, List.cons_ne_nil, if_false, copyIn, copyToBody,
        List.length_mapIdx, List.length_nil, Nat.zero_add, le_refl]

  -- Show result: c_final.state (regs[0]) = Result body bodyInputs
  have hresult : c_final.state (regs[0]'(List.length_pos_of_ne_nil hregs)) =
      Result body bodyInputs hbody_halts := by
    -- c_final.state = c_copyOut.state
    -- copyFromBody copies base to regs[0]
    -- base in c_body.state = Result (by hresult_body)
    have hcopyOut_spec := straightLineFinalState_spec hsl_copyOut c_body.state
    have hc_copyOut_eq : c_copyOut = Classical.choose (straightLine_halts_from_state hsl_copyOut c_body.state) :=
      Steps.halts_unique hsteps_copyOut hhalted_copyOut_local hcopyOut_spec.1 hcopyOut_spec.2.1
    have hstate_eq : c_copyOut.state = straightLineFinalState hsl_copyOut c_body.state := by
      simp [straightLineFinalState, hc_copyOut_eq]
    simp only [c_final, hstate_eq]
    rw [copyFromBody_effect regs base c_body.state hregs]
    -- c_body.state base = Result body bodyInputs hbody_halts
    simp only [State.read] at hresult_body
    exact hresult_body

  exact ⟨c_final, hsteps_all, hfinal_halted, hresult⟩

/-! ## Mu Setup Phase -/

/-- After muSetupPhase executes with mkMuLayout:
1. Counter register is 0
2. Zero register is 0
3. Saved inputs contain the original input values -/
theorem muSetupPhase_effect' (regs : List ℕ) (body : FlatProgram) (s : State) :
    let layout := mkMuLayout regs body
    let s' := straightLineFinalState (muSetupPhase_isStraightLine layout regs) s
    s' layout.counterReg = 0 ∧
    s' layout.zeroReg = 0 ∧
    ∀ i : Fin regs.length, s' (layout.savedStart + i) = s (regs[i]) := by
  -- muSetupPhase = saveInputs ++ [Z counterReg, Z zeroReg]
  -- saveInputs = [T regs[0] (savedStart+0), T regs[1] (savedStart+1), ...]
  let layout := mkMuLayout regs body
  let hsl := muSetupPhase_isStraightLine layout regs

  -- muSetupPhase structure
  have hsetup_eq : muSetupPhase layout regs =
      regs.mapIdx (fun i r => Instr.T r (layout.savedStart + i)) ++
      [Instr.Z layout.counterReg, Instr.Z layout.zeroReg] := rfl
  have hsetup_len : (muSetupPhase layout regs).length = regs.length + 2 := by
    simp only [muSetupPhase, List.length_append, List.length_mapIdx, List.length_cons,
               List.length_nil]

  -- Position of Z counterReg is regs.length
  have hcounter_pos : regs.length < (muSetupPhase layout regs).length := by omega
  have hcounter_instr : (muSetupPhase layout regs)[regs.length]'hcounter_pos =
      Instr.Z layout.counterReg := by
    simp only [muSetupPhase]
    rw [List.getElem_append_right (by simp : regs.length ≥ (regs.mapIdx _).length)]
    simp

  -- Position of Z zeroReg is regs.length + 1
  have hzero_pos : regs.length + 1 < (muSetupPhase layout regs).length := by omega
  have hzero_instr : (muSetupPhase layout regs)[regs.length + 1]'hzero_pos =
      Instr.Z layout.zeroReg := by
    simp only [muSetupPhase]
    rw [List.getElem_append_right (by simp : regs.length + 1 ≥ (regs.mapIdx _).length)]
    simp

  -- Part 1: counterReg = 0
  have h1 : (straightLineFinalState hsl s) layout.counterReg = 0 := by
    -- Z counterReg is at position regs.length, and only Z zeroReg comes after
    -- Z zeroReg writes to zeroReg ≠ counterReg
    have hnowrite : ∀ j (hj : j < (muSetupPhase layout regs).length),
        regs.length < j → ((muSetupPhase layout regs)[j]'hj).writesTo ≠ some layout.counterReg := by
      intro j hj hgt
      -- Only j = regs.length + 1 is possible
      have hj_eq : j = regs.length + 1 := by omega
      subst hj_eq
      rw [hzero_instr]
      simp only [Instr.writesTo, ne_eq, Option.some.injEq]
      exact Ne.symm (mkMuLayout_counterReg_ne_zeroReg regs body)
    exact straightLine_zeros_register hsl s layout.counterReg regs.length hcounter_pos
      hcounter_instr hnowrite

  -- Part 2: zeroReg = 0
  have h2 : (straightLineFinalState hsl s) layout.zeroReg = 0 := by
    -- Z zeroReg is the last instruction
    have hnowrite : ∀ j (hj : j < (muSetupPhase layout regs).length),
        regs.length + 1 < j → ((muSetupPhase layout regs)[j]'hj).writesTo ≠ some layout.zeroReg := by
      intro j hj hgt
      omega  -- No such j exists
    exact straightLine_zeros_register hsl s layout.zeroReg (regs.length + 1) hzero_pos
      hzero_instr hnowrite

  -- Part 3: saved inputs are preserved
  have h3 : ∀ i : Fin regs.length, (straightLineFinalState hsl s) (layout.savedStart + i) = s (regs[i]) := by
    intro i
    -- Convert to ℕ for easier reasoning
    let iv := (i : ℕ)
    have hiv : iv < regs.length := i.isLt
    -- T regs[iv] (savedStart + iv) is at position iv
    have hi_lt : iv < (muSetupPhase layout regs).length := by omega
    have hinstr_i : (muSetupPhase layout regs)[iv]'hi_lt = Instr.T (regs[iv]'hiv) (layout.savedStart + iv) := by
      simp only [muSetupPhase, iv]
      rw [List.getElem_append_left (by simp)]
      simp only [List.getElem_mapIdx]
    -- No later instruction writes to (savedStart + iv)
    have hnowrite : ∀ j (hj : j < (muSetupPhase layout regs).length),
        iv < j → ((muSetupPhase layout regs)[j]'hj).writesTo ≠ some (layout.savedStart + iv) := by
      intro j hj hij
      by_cases hj_in_save : j < regs.length
      · -- j is in saveInputs: T regs[j] (savedStart + j), writes to savedStart + j ≠ savedStart + iv
        simp only [muSetupPhase]
        rw [List.getElem_append_left (by simp; exact hj_in_save)]
        simp only [List.getElem_mapIdx, Instr.writesTo, ne_eq, Option.some.injEq]
        omega
      · -- j is in [Z counterReg, Z zeroReg]
        by_cases hj_counter : j = regs.length
        · -- j = regs.length: Z counterReg
          subst hj_counter
          rw [hcounter_instr]
          simp only [Instr.writesTo, ne_eq, Option.some.injEq, layout, iv] at *
          have hne := mkMuLayout_counterReg_ne_saved regs body i
          omega
        · -- j = regs.length + 1: Z zeroReg
          have hj_eq : j = regs.length + 1 := by omega
          subst hj_eq
          rw [hzero_instr]
          simp only [Instr.writesTo, ne_eq, Option.some.injEq, layout, iv] at *
          have hne := mkMuLayout_zeroReg_ne_saved regs body i
          omega
    -- Use straightLine_transfer_result
    -- Need to show regs[i] = regs[iv]'hiv for the types to match
    have hregs_eq : regs[i] = regs[iv]'hiv := rfl
    have hoff_eq : layout.savedStart + (i : ℕ) = layout.savedStart + iv := rfl
    obtain ⟨s_before, ⟨c_i, hsteps_i, hpc_i, hs_before⟩, hresult⟩ :=
      straightLine_transfer_result hsl s iv (regs[iv]'hiv) (layout.savedStart + iv) hi_lt hinstr_i hnowrite
    simp only [State.read] at hresult ⊢
    rw [hoff_eq, hresult, ← hs_before]
    -- Show that s_before (regs[iv]) = s (regs[iv])
    -- Earlier instructions write to savedStart + 0, ..., savedStart + (iv-1)
    -- and regs[iv] < savedStart (by mkMuLayout_regs_lt_saved)
    have hregs_i_lt_saved : regs[iv]'hiv < layout.savedStart :=
      mkMuLayout_regs_lt_saved regs body i
    have hpreserved : ∀ j (hj : j < iv), ((muSetupPhase layout regs)[j]'(Nat.lt_trans hj hi_lt)).writesTo ≠ some (regs[iv]'hiv) := by
      intro j hj
      simp only [muSetupPhase]
      rw [List.getElem_append_left (by simp; exact Nat.lt_trans hj hiv)]
      simp only [List.getElem_mapIdx, Instr.writesTo, ne_eq, Option.some.injEq]
      omega
    have hpres := Steps.straightLine_preserves_partial hsl (Nat.le_of_lt hi_lt) hpreserved c_i hsteps_i hpc_i
    simp only [State.read, hregs_eq] at hpres ⊢
    exact hpres

  exact ⟨h1, h2, h3⟩

/-! ## Mu Prologue -/

/-- After muPrologue executes from state with counter = k:
1. Body input registers contain saved input values
2. Body counter input (at position n) contains k
3. Counter and zero registers are preserved

This version uses mkMuLayout directly to get the necessary register disjointness properties. -/
theorem muPrologue_effect' (regs : List ℕ) (body : FlatProgram) (s : State) (k : ℕ)
    (hs_counter : s (mkMuLayout regs body).counterReg = k)
    (hs_zero : s (mkMuLayout regs body).zeroReg = 0) :
    let layout := mkMuLayout regs body
    let s' := straightLineFinalState (muPrologue_isStraightLine layout) s
    (∀ i : Fin regs.length, s' (layout.base + i) = s (layout.savedStart + i)) ∧
    s' (layout.base + layout.n) = k ∧
    s' layout.counterReg = k ∧
    s' layout.zeroReg = 0 := by
  -- muPrologue = clearWorkspace ++ restoreInputs ++ setCounter
  let layout := mkMuLayout regs body
  let hsl := muPrologue_isStraightLine layout

  -- Part 4: zeroReg is preserved (no instruction writes to it)
  have h4 : (straightLineFinalState hsl s) layout.zeroReg = 0 := by
    rw [← hs_zero]
    apply Urm.straightLineFinalState_preserves hsl s
    intro instr hmem
    simp only [muPrologue, clearBodyRegs, List.mem_append, List.mem_map, List.mem_range, layout] at hmem
    rcases hmem with (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | hmem
    · -- Z (base + j) doesn't write to zeroReg
      simp only [Instr.writesTo, ne_eq, Option.some.injEq, layout]
      have := mkMuLayout_zeroReg_gt_workspace regs body
      omega
    · -- T (savedStart + j) (base + j) doesn't write to zeroReg
      simp only [Instr.writesTo, ne_eq, Option.some.injEq, layout]
      have := mkMuLayout_zeroReg_gt_base_n regs body
      omega
    · -- T counterReg (base + n) doesn't write to zeroReg
      simp only [List.mem_singleton] at hmem; rw [hmem]
      simp only [Instr.writesTo, ne_eq, Option.some.injEq]
      have := mkMuLayout_zeroReg_gt_base_n regs body
      simp only [layout] at *; omega

  -- Part 3: counterReg is preserved (no instruction writes to it)
  have h3 : (straightLineFinalState hsl s) layout.counterReg = k := by
    rw [← hs_counter]
    apply Urm.straightLineFinalState_preserves hsl s
    intro instr hmem
    simp only [muPrologue, clearBodyRegs, List.mem_append, List.mem_map, List.mem_range] at hmem
    rcases hmem with (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | hmem
    · -- Z (base + j) doesn't write to counterReg
      simp only [Instr.writesTo, ne_eq, Option.some.injEq]
      have := mkMuLayout_counterReg_gt_workspace regs body
      simp only [layout] at *; omega
    · -- T (savedStart + j) (base + j) doesn't write to counterReg
      simp only [Instr.writesTo, ne_eq, Option.some.injEq]
      have := mkMuLayout_counterReg_gt_base_n regs body
      simp only [layout] at *; omega
    · -- T counterReg (base + n) doesn't write to counterReg
      simp only [List.mem_singleton] at hmem; rw [hmem]
      simp only [Instr.writesTo, ne_eq, Option.some.injEq]
      have := mkMuLayout_counterReg_gt_base_n regs body
      simp only [layout] at *; omega

  -- Part 2: setCounter transfers counterReg (= k) to base + n
  -- setCounter = [T counterReg (base + n)] is the last instruction in muPrologue
  have h2 : (straightLineFinalState hsl s) (layout.base + layout.n) = k := by
    -- muPrologue = clearWorkspace ++ restoreInputs ++ setCounter
    -- setCounter is at the very end, so no instruction writes to (base + n) after it
    have hpro_eq : muPrologue layout =
        clearBodyRegs layout.base (layout.bodyMaxReg + 1) ++
        (List.range layout.n |>.map fun i => Instr.T (layout.savedStart + i) (layout.base + i)) ++
        [Instr.T layout.counterReg (layout.base + layout.n)] := rfl

    -- Length calculations
    have hclear_len : (clearBodyRegs layout.base (layout.bodyMaxReg + 1)).length = layout.bodyMaxReg + 1 := by
      simp only [clearBodyRegs, List.length_map, List.length_range]
    have hrestore_len : (List.range layout.n |>.map fun i => Instr.T (layout.savedStart + i) (layout.base + i)).length = layout.n := by
      simp only [List.length_map, List.length_range]
    have hpro_len : (muPrologue layout).length = layout.bodyMaxReg + 1 + layout.n + 1 := by
      simp only [muPrologue, clearBodyRegs, List.length_append, List.length_map, List.length_range,
                 List.length_singleton]

    -- Index of setCounter T instruction is at position (clearWorkspace.len + restoreInputs.len)
    let setCounterIdx := layout.bodyMaxReg + 1 + layout.n
    have hsc_idx_lt : setCounterIdx < (muPrologue layout).length := by
      simp only [hpro_len, setCounterIdx]; omega
    have hsc_instr : (muPrologue layout)[setCounterIdx]'hsc_idx_lt =
        Instr.T layout.counterReg (layout.base + layout.n) := by
      simp only [muPrologue, clearBodyRegs, setCounterIdx]
      -- (clear ++ restore ++ [T ...]) at index (clear.len + restore.len) = T ...
      have hclear_len' : (List.range (layout.bodyMaxReg + 1) |>.map fun i => Instr.Z (layout.base + i)).length = layout.bodyMaxReg + 1 := by simp
      have hrestore_len' : (List.range layout.n |>.map fun i => Instr.T (layout.savedStart + i) (layout.base + i)).length = layout.n := by simp
      rw [List.getElem_append_right (by simp only [List.length_append, hclear_len', hrestore_len']; omega)]
      simp only [List.length_append, hclear_len', hrestore_len', List.getElem_singleton]

    -- No instruction after setCounter (it's the last one)
    have hnowrite : ∀ j (hj : j < (muPrologue layout).length),
        setCounterIdx < j → ((muPrologue layout)[j]'hj).writesTo ≠ some (layout.base + layout.n) := by
      intro j hj hgt
      simp only [hpro_len, setCounterIdx] at hgt hj
      omega  -- No such j exists

    -- Use straightLine_transfer_result
    obtain ⟨s_before, ⟨c_i, hsteps_i, hpc_i, hs_before⟩, hresult⟩ :=
      straightLine_transfer_result hsl s setCounterIdx layout.counterReg (layout.base + layout.n)
        hsc_idx_lt hsc_instr hnowrite
    simp only [State.read] at hresult ⊢
    rw [hresult, ← hs_before]

    -- Now show c_i.state counterReg = s counterReg = k
    -- counterReg is preserved by all earlier instructions (clearWorkspace and restoreInputs)
    have hcounter_preserved : ∀ j (hj : j < setCounterIdx),
        ((muPrologue layout)[j]'(Nat.lt_trans hj hsc_idx_lt)).writesTo ≠ some layout.counterReg := by
      intro j hj
      -- Establish equalities for omega
      have hbase_eq : layout.base = (mkMuLayout regs body).base := rfl
      have hbmr_eq : layout.bodyMaxReg = (mkMuLayout regs body).bodyMaxReg := rfl
      have hn_eq : layout.n = (mkMuLayout regs body).n := rfl
      have hcr_eq : layout.counterReg = (mkMuLayout regs body).counterReg := rfl
      have hss_eq : layout.savedStart = (mkMuLayout regs body).savedStart := rfl
      simp only [setCounterIdx, hbmr_eq, hn_eq] at hj
      simp only [muPrologue, clearBodyRegs, hbase_eq, hbmr_eq, hn_eq, hcr_eq, hss_eq]
      have hclear_len' : (List.range ((mkMuLayout regs body).bodyMaxReg + 1) |>.map fun i => Instr.Z ((mkMuLayout regs body).base + i)).length = (mkMuLayout regs body).bodyMaxReg + 1 := by simp
      have hrestore_len' : (List.range (mkMuLayout regs body).n |>.map fun i => Instr.T ((mkMuLayout regs body).savedStart + i) ((mkMuLayout regs body).base + i)).length = (mkMuLayout regs body).n := by simp
      by_cases hj_clear : j < (mkMuLayout regs body).bodyMaxReg + 1
      · -- j in clearWorkspace: Z (base + j) writes to base + j
        rw [List.getElem_append_left (by simp; omega)]
        rw [List.getElem_append_left (by simp; exact hj_clear)]
        simp only [List.getElem_map, List.getElem_range, Instr.writesTo, ne_eq, Option.some.injEq]
        have hgt := mkMuLayout_counterReg_gt_workspace regs body
        omega
      · -- j in restoreInputs: T (savedStart + (j - clear.len)) (base + (j - clear.len))
        have hj_restore : j - ((mkMuLayout regs body).bodyMaxReg + 1) < (mkMuLayout regs body).n := by omega
        rw [List.getElem_append_left (by simp; omega)]
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range,
                   Instr.writesTo, ne_eq, Option.some.injEq]
        have hgt := mkMuLayout_counterReg_gt_base_n regs body
        omega

    have hpres := Steps.straightLine_preserves_partial hsl (Nat.le_of_lt hsc_idx_lt) hcounter_preserved c_i hsteps_i hpc_i
    simp only [State.read] at hpres
    rw [hpres, hs_counter]

  have h1 : ∀ i : Fin regs.length, (straightLineFinalState hsl s) (layout.base + i) = s (layout.savedStart + i) := by
    intro ⟨i, hi⟩
    -- Establish equalities for omega
    have hbase_eq : layout.base = (mkMuLayout regs body).base := rfl
    have hbmr_eq : layout.bodyMaxReg = (mkMuLayout regs body).bodyMaxReg := rfl
    have hn_eq : layout.n = (mkMuLayout regs body).n := rfl
    have hcr_eq : layout.counterReg = (mkMuLayout regs body).counterReg := rfl
    have hss_eq : layout.savedStart = (mkMuLayout regs body).savedStart := rfl

    -- muPrologue = clearWorkspace ++ restoreInputs ++ setCounter
    -- restoreInputs[i] = T (savedStart + i) (base + i)
    have hpro_len : (muPrologue layout).length = layout.bodyMaxReg + 1 + layout.n + 1 := by
      simp only [muPrologue, clearBodyRegs, List.length_append, List.length_map, List.length_range,
                 List.length_singleton]

    -- The T instruction for register i is at position (bodyMaxReg + 1 + i)
    let restoreIdx := layout.bodyMaxReg + 1 + i
    have hri_lt : restoreIdx < (muPrologue layout).length := by
      simp only [hpro_len, restoreIdx, hn_eq]
      have hn_eq' : (mkMuLayout regs body).n = regs.length := mkMuLayout_n_eq regs body
      omega
    have hri_instr : (muPrologue layout)[restoreIdx]'hri_lt =
        Instr.T (layout.savedStart + i) (layout.base + i) := by
      simp only [muPrologue, clearBodyRegs, restoreIdx, hbase_eq, hbmr_eq, hn_eq, hss_eq]
      have hclear_len' : (List.range ((mkMuLayout regs body).bodyMaxReg + 1) |>.map fun i =>
          Instr.Z ((mkMuLayout regs body).base + i)).length = (mkMuLayout regs body).bodyMaxReg + 1 := by simp
      have hrestore_len' : (List.range (mkMuLayout regs body).n |>.map fun i =>
          Instr.T ((mkMuLayout regs body).savedStart + i) ((mkMuLayout regs body).base + i)).length =
          (mkMuLayout regs body).n := by simp
      have hn_eq' : (mkMuLayout regs body).n = regs.length := mkMuLayout_n_eq regs body
      rw [List.getElem_append_left (by simp only [List.length_append, hclear_len', hrestore_len']; omega)]
      rw [List.getElem_append_right (by simp only [hclear_len']; omega)]
      simp only [hclear_len', List.getElem_map, List.getElem_range, Nat.add_sub_cancel_left]

    -- No later instruction writes to (base + i)
    -- - restoreInputs[j] for j > i writes to (base + j) ≠ (base + i)
    -- - setCounter writes to (base + n) and i < n
    have hnowrite : ∀ j (hj : j < (muPrologue layout).length),
        restoreIdx < j → ((muPrologue layout)[j]'hj).writesTo ≠ some (layout.base + i) := by
      intro j hj hgt
      simp only [muPrologue, clearBodyRegs, restoreIdx, hbase_eq, hbmr_eq, hn_eq, hss_eq, hcr_eq] at hgt hj ⊢
      have hn_eq' : (mkMuLayout regs body).n = regs.length := mkMuLayout_n_eq regs body
      by_cases hj_in_restore : j < (mkMuLayout regs body).bodyMaxReg + 1 + (mkMuLayout regs body).n
      · -- j in clearWorkspace ++ restoreInputs
        rw [List.getElem_append_left (by simp; omega)]
        by_cases hj_in_clear : j < (mkMuLayout regs body).bodyMaxReg + 1
        · -- j in clearWorkspace - but restoreIdx >= bodyMaxReg + 1, so this case is impossible
          omega
        · -- j in restoreInputs: writes to base + (j - (bodyMaxReg + 1))
          rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range,
                     Instr.writesTo, ne_eq, Option.some.injEq]
          omega
      · -- j is setCounter: writes to (base + n)
        have hj_eq : j = (mkMuLayout regs body).bodyMaxReg + 1 + (mkMuLayout regs body).n := by omega
        subst hj_eq
        rw [List.getElem_append_right (by simp)]
        simp only [List.length_append, List.length_map, List.length_range,
                   List.getElem_singleton, Instr.writesTo, ne_eq, Option.some.injEq]
        omega

    -- Use straightLine_transfer_result
    obtain ⟨s_before, ⟨c_i, hsteps_i, hpc_i, hs_before⟩, hresult⟩ :=
      straightLine_transfer_result hsl s restoreIdx (layout.savedStart + i) (layout.base + i)
        hri_lt hri_instr hnowrite
    simp only [State.read] at hresult ⊢
    rw [hresult, ← hs_before]

    -- Show savedStart + i is preserved by all earlier instructions
    -- clearWorkspace writes to base + j for j < bodyMaxReg + 1
    -- earlier restoreInputs write to base + j for j < i
    -- savedStart > base + bodyMaxReg >= base + j for all writes
    have hsaved_preserved : ∀ j (hj : j < restoreIdx),
        ((muPrologue layout)[j]'(Nat.lt_trans hj hri_lt)).writesTo ≠ some (layout.savedStart + i) := by
      intro j hj
      simp only [muPrologue, clearBodyRegs, restoreIdx, hbase_eq, hbmr_eq, hn_eq, hss_eq] at hj ⊢
      have hclear_len' : (List.range ((mkMuLayout regs body).bodyMaxReg + 1) |>.map fun i =>
          Instr.Z ((mkMuLayout regs body).base + i)).length = (mkMuLayout regs body).bodyMaxReg + 1 := by simp
      have hrestore_len' : (List.range (mkMuLayout regs body).n |>.map fun i =>
          Instr.T ((mkMuLayout regs body).savedStart + i) ((mkMuLayout regs body).base + i)).length =
          (mkMuLayout regs body).n := by simp
      have hn_eq' : (mkMuLayout regs body).n = regs.length := mkMuLayout_n_eq regs body
      by_cases hj_in_clear : j < (mkMuLayout regs body).bodyMaxReg + 1
      · -- j in clearWorkspace: Z (base + j) writes to base + j
        rw [List.getElem_append_left (by simp only [List.length_append, hclear_len', hrestore_len']; omega)]
        rw [List.getElem_append_left (by simp only [hclear_len']; exact hj_in_clear)]
        simp only [List.getElem_map, List.getElem_range, Instr.writesTo, ne_eq, Option.some.injEq]
        have hgt := mkMuLayout_savedStart_gt_workspace regs body
        omega
      · -- j in earlier restoreInputs: T (savedStart + (j - clear.len)) (base + (j - clear.len))
        have hj_in_restore : j - ((mkMuLayout regs body).bodyMaxReg + 1) < i := by omega
        rw [List.getElem_append_left (by simp only [List.length_append, hclear_len', hrestore_len']; omega)]
        rw [List.getElem_append_right (by simp only [hclear_len']; omega)]
        simp only [hclear_len', List.getElem_map, List.getElem_range, Instr.writesTo, ne_eq, Option.some.injEq]
        have hgt := mkMuLayout_savedStart_gt_base_n regs body
        omega

    have hpres := Steps.straightLine_preserves_partial hsl (Nat.le_of_lt hri_lt) hsaved_preserved c_i hsteps_i hpc_i
    simp only [State.read] at hpres
    exact hpres

  exact ⟨h1, h2, h3, h4⟩

/-! ## Mu Loop Infrastructure -/

/-- State invariant for Mu loop: tracks saved inputs, counter, and zero register. -/
structure MuLoopInvariant (regs : List ℕ) (body : FlatProgram) (s : State) (k : ℕ)
    (originalInputs : Fin regs.length → ℕ) : Prop where
  /-- Counter register holds current iteration count -/
  counter_eq : s (mkMuLayout regs body).counterReg = k
  /-- Zero register is always 0 -/
  zero_eq : s (mkMuLayout regs body).zeroReg = 0
  /-- Saved inputs preserve original values -/
  saved_eq : ∀ i : Fin regs.length, s ((mkMuLayout regs body).savedStart + i) = originalInputs i

/-- Result of executing Mu setup phase. -/
structure MuSetupResult (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ)
    (s : State) where
  /-- State after setup -/
  state : State
  /-- Steps from initial to loopStart -/
  steps : Steps (compileMu regs body resultReg) ⟨0, s⟩ ⟨regs.length + 2, state⟩
  /-- Counter is initialized to 0 -/
  counter_eq : state (mkMuLayout regs body).counterReg = 0
  /-- Zero register is initialized to 0 -/
  zero_eq : state (mkMuLayout regs body).zeroReg = 0
  /-- Original saved inputs match host inputs -/
  saved_inputs : ∀ i : Fin regs.length, state ((mkMuLayout regs body).savedStart + i) = s (regs[i])

/-- PC positions in compileMu. -/
def muSetupStartPC : ℕ := 0

def muLoopStartPC (regs : List ℕ) : ℕ := regs.length + 2

def muBodyStartPC (regs : List ℕ) (body : FlatProgram) : ℕ :=
  let layout := mkMuLayout regs body
  regs.length + 2 + (layout.bodyMaxReg + 1 + layout.n + 1)

def muEpilogueStartPC (regs : List ℕ) (body : FlatProgram) : ℕ :=
  muBodyStartPC regs body + body.length

def muOutputPC (regs : List ℕ) (body : FlatProgram) : ℕ :=
  muEpilogueStartPC regs body + 3

/-! ## Mu Embedding Lemmas -/

/-- muSetupPhase is embedded in compileMu at offset 0. -/
theorem muSetupPhase_embed (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ) :
    ∀ i, i < (muSetupPhase (mkMuLayout regs body) regs).length →
    (compileMu regs body resultReg).getInstr (0 + i) =
      (muSetupPhase (mkMuLayout regs body) regs).getInstr i := by
  intro i hi
  simp only [compileMu, Nat.zero_add, Program.getInstr]
  have hsetup_len : (muSetupPhase (mkMuLayout regs body) regs).length = regs.length + 2 := by
    simp only [muSetupPhase, List.length_append, List.length_mapIdx, List.length_cons, List.length_nil]
  simp only [hsetup_len] at hi
  -- compileMu = setup ++ prologue ++ ... so getElem?_append_left applies
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp only [muSetupPhase, List.length_append, List.length_mapIdx,
    List.length_cons, List.length_nil]; omega)]

/-- muPrologue is embedded in compileMu at offset muLoopStartPC regs. -/
theorem muPrologue_embed (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ) :
    ∀ i, i < (muPrologue (mkMuLayout regs body)).length →
    (compileMu regs body resultReg).getInstr (muLoopStartPC regs + i) =
      (muPrologue (mkMuLayout regs body)).getInstr i := by
  intro i hi
  simp only [compileMu, muLoopStartPC, Program.getInstr]
  have hsetup_len : (muSetupPhase (mkMuLayout regs body) regs).length = regs.length + 2 := by
    simp only [muSetupPhase, List.length_append, List.length_mapIdx, List.length_cons, List.length_nil]
  have hprologue_len : (muPrologue (mkMuLayout regs body)).length =
      (mkMuLayout regs body).bodyMaxReg + 1 + (mkMuLayout regs body).n + 1 := by
    simp only [muPrologue, clearBodyRegs, List.length_append, List.length_map, List.length_range,
      List.length_singleton]
  simp only [hprologue_len] at hi
  -- Skip setup phase, then get from prologue
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by simp only [muSetupPhase, List.length_append, List.length_mapIdx,
    List.length_cons, List.length_nil]; omega)]
  simp only [muSetupPhase, List.length_append, List.length_mapIdx, List.length_cons, List.length_nil,
    Nat.add_sub_cancel_left]

/-- shiftedBody is embedded in compileMu at offset muBodyStartPC. -/
theorem muBody_embed (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ) :
    ∀ i, i < body.length →
    (compileMu regs body resultReg).getInstr (muBodyStartPC regs body + i) =
      ((body.shiftRegisters (mkMuLayout regs body).base).shiftJumps (muBodyStartPC regs body)).getInstr i := by
  intro i hi
  let layout := mkMuLayout regs body
  let setup := muSetupPhase layout regs
  let prologue := muPrologue layout
  let shiftedBody := (body.shiftRegisters layout.base).shiftJumps (muBodyStartPC regs body)
  let epilogue := muEpilogue layout (muOutputPC regs body) (muLoopStartPC regs)
  let output := muOutputPhase regs resultReg
  have hsetup_len : setup.length = regs.length + 2 := by
    simp only [setup, muSetupPhase, List.length_append, List.length_mapIdx, List.length_cons, List.length_nil]
  have hprologue_len : prologue.length = layout.bodyMaxReg + 1 + layout.n + 1 := by
    simp only [prologue, muPrologue, clearBodyRegs, List.length_append, List.length_map, List.length_range,
      List.length_singleton]
  have hbody_len : shiftedBody.length = body.length := by
    simp only [shiftedBody, Program.shiftJumps_length, Program.shiftRegisters_length]
  have hn_eq : layout.n = regs.length := mkMuLayout_n_eq regs body
  have hbodyStartPC : muBodyStartPC regs body = setup.length + prologue.length := by
    simp only [muBodyStartPC, hsetup_len, hprologue_len, layout, mkMuLayout]
  -- compileMu = setup ++ prologue ++ shiftedBody ++ epilogue ++ output
  have hcompile : compileMu regs body resultReg = setup ++ prologue ++ shiftedBody ++ epilogue ++ output := rfl
  rw [hbodyStartPC]
  simp only [Program.getInstr, hcompile]
  -- Index is setup.length + prologue.length + i, which is in shiftedBody
  have hi_lt : setup.length + prologue.length + i < (setup ++ prologue ++ shiftedBody ++ epilogue).length := by
    simp only [List.length_append, hbody_len]; omega
  rw [List.getElem?_append_left hi_lt]
  have hi_lt2 : setup.length + prologue.length + i < (setup ++ prologue ++ shiftedBody).length := by
    simp only [List.length_append, hbody_len]; omega
  rw [List.getElem?_append_left hi_lt2]
  have hi_ge : (setup ++ prologue).length ≤ setup.length + prologue.length + i := by
    simp only [List.length_append]; omega
  rw [List.getElem?_append_right hi_ge]
  simp only [List.length_append, Nat.add_sub_cancel_left, shiftedBody, hbodyStartPC]
  rfl

/-- muEpilogue is embedded in compileMu at offset muEpilogueStartPC. -/
theorem muEpilogue_embed (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ) :
    ∀ i, i < 3 →
    (compileMu regs body resultReg).getInstr (muEpilogueStartPC regs body + i) =
      (muEpilogue (mkMuLayout regs body) (muOutputPC regs body) (muLoopStartPC regs)).getInstr i := by
  intro i hi
  let layout := mkMuLayout regs body
  let setup := muSetupPhase layout regs
  let prologue := muPrologue layout
  let shiftedBody := (body.shiftRegisters layout.base).shiftJumps (muBodyStartPC regs body)
  let epilogue := muEpilogue layout (muOutputPC regs body) (muLoopStartPC regs)
  let output := muOutputPhase regs resultReg
  have hsetup_len : setup.length = regs.length + 2 := by
    simp only [setup, muSetupPhase, List.length_append, List.length_mapIdx, List.length_cons, List.length_nil]
  have hprologue_len : prologue.length = layout.bodyMaxReg + 1 + layout.n + 1 := by
    simp only [prologue, muPrologue, clearBodyRegs, List.length_append, List.length_map, List.length_range,
      List.length_singleton]
  have hbody_len : shiftedBody.length = body.length := by
    simp only [shiftedBody, Program.shiftJumps_length, Program.shiftRegisters_length]
  have hepilogue_len : epilogue.length = 3 := by
    simp only [epilogue, muEpilogue, List.length_cons, List.length_nil]
  have hn_eq : layout.n = regs.length := mkMuLayout_n_eq regs body
  have hepilogueStartPC : muEpilogueStartPC regs body = setup.length + prologue.length + body.length := by
    simp only [muEpilogueStartPC, muBodyStartPC, hsetup_len, hprologue_len, layout, mkMuLayout]
  have hcompile : compileMu regs body resultReg = setup ++ prologue ++ shiftedBody ++ epilogue ++ output := rfl
  rw [hepilogueStartPC]
  simp only [Program.getInstr, hcompile]
  -- Index is setup.length + prologue.length + body.length + i, which is in epilogue
  have hi_lt : setup.length + prologue.length + body.length + i < (setup ++ prologue ++ shiftedBody ++ epilogue).length := by
    simp only [List.length_append, hbody_len, hepilogue_len]; omega
  rw [List.getElem?_append_left hi_lt]
  have hi_ge : (setup ++ prologue ++ shiftedBody).length ≤ setup.length + prologue.length + body.length + i := by
    simp only [List.length_append, hbody_len]; omega
  rw [List.getElem?_append_right hi_ge]
  simp only [List.length_append, hbody_len, Nat.add_sub_cancel_left, epilogue]
  rfl

/-- First epilogue instruction: J base zeroReg outputPC -/
theorem instr_at_muEpilogue_J0 (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ) :
    (compileMu regs body resultReg).getInstr (muEpilogueStartPC regs body) =
      some (Instr.J (mkMuLayout regs body).base (mkMuLayout regs body).zeroReg (muOutputPC regs body)) := by
  have h := muEpilogue_embed regs body resultReg 0 (by omega : 0 < 3)
  simp only [Nat.add_zero] at h
  rw [h]
  simp only [muEpilogue, Program.getInstr, List.getElem?_cons_zero]

/-- Second epilogue instruction: S counterReg -/
theorem instr_at_muEpilogue_S (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ) :
    (compileMu regs body resultReg).getInstr (muEpilogueStartPC regs body + 1) =
      some (Instr.S (mkMuLayout regs body).counterReg) := by
  have h := muEpilogue_embed regs body resultReg 1 (by omega : 1 < 3)
  rw [h]
  simp only [muEpilogue, Program.getInstr, List.getElem?_cons_succ, List.getElem?_cons_zero]

/-- Third epilogue instruction: J zeroReg zeroReg loopStartPC -/
theorem instr_at_muEpilogue_J1 (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ) :
    (compileMu regs body resultReg).getInstr (muEpilogueStartPC regs body + 2) =
      some (Instr.J (mkMuLayout regs body).zeroReg (mkMuLayout regs body).zeroReg (muLoopStartPC regs)) := by
  have h := muEpilogue_embed regs body resultReg 2 (by omega : 2 < 3)
  rw [h]
  simp only [muEpilogue, Program.getInstr, List.getElem?_cons_succ, List.getElem?_cons_zero]

/-- Execute Mu setup phase and return the result. -/
noncomputable def executeMuSetup (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ)
    (s : State) : MuSetupResult regs body resultReg s :=
  let layout := mkMuLayout regs body
  let hsl := muSetupPhase_isStraightLine layout regs
  let hHalts := straightLine_halts_from_state hsl s
  let cSetup := Classical.choose hHalts
  let hspec := Classical.choose_spec hHalts
  let hsteps_local := hspec.1
  let hhalted_local := hspec.2.1
  let hpc_local := hspec.2.2
  have hlen : (muSetupPhase layout regs).length = regs.length + 2 := by
    simp only [muSetupPhase, List.length_append, List.length_mapIdx, List.length_cons, List.length_nil]
  let hsteps_lifted := Steps.straightLine_at_offset 0 hsl (muSetupPhase_embed regs body resultReg) hsteps_local
  have hsteps : Steps (compileMu regs body resultReg) ⟨0, s⟩ ⟨regs.length + 2, cSetup.state⟩ := by
    simp only [Nat.zero_add, Nat.add_zero] at hsteps_lifted
    have hcSetup_eq : cSetup = Classical.choose hHalts := rfl
    rw [hcSetup_eq]
    have hpc_eq : (Classical.choose hHalts).pc = regs.length + 2 := by
      rw [hpc_local, hlen]
    conv_rhs => rw [← hpc_eq]
    exact hsteps_lifted
  -- Get effect from muSetupPhase_effect'
  let heffect := muSetupPhase_effect' regs body s
  have hstate_eq : cSetup.state = straightLineFinalState hsl s := rfl
  {
    state := cSetup.state
    steps := hsteps
    counter_eq := by rw [hstate_eq]; exact heffect.1
    zero_eq := by rw [hstate_eq]; exact heffect.2.1
    saved_inputs := fun i => by rw [hstate_eq]; exact heffect.2.2 i
  }

/-- Result of one Mu loop iteration. -/
structure MuIterationResult (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ)
    (s : State) (k : ℕ) where
  /-- Final configuration after iteration -/
  finalConfig : Config
  /-- Steps taken during iteration -/
  steps : Steps (compileMu regs body resultReg) ⟨muLoopStartPC regs, s⟩ finalConfig
  /-- Body's result in R[0] (shifted by base) -/
  bodyResult : ℕ
  /-- Either exited (result = 0) or continued (result ≠ 0) -/
  outcome : (bodyResult = 0 ∧ finalConfig.pc = muOutputPC regs body) ∨
            (bodyResult ≠ 0 ∧ finalConfig.pc = muLoopStartPC regs ∧
             finalConfig.state (mkMuLayout regs body).counterReg = k + 1)
  /-- Zero register preserved -/
  zero_preserved : finalConfig.state (mkMuLayout regs body).zeroReg = 0
  /-- Saved inputs preserved -/
  saved_preserved : ∀ i : Fin regs.length,
    finalConfig.state ((mkMuLayout regs body).savedStart + i) = s ((mkMuLayout regs body).savedStart + i)

/-- Execute one Mu loop iteration.

Starting from PC = muLoopStartPC regs with state satisfying the loop invariant,
execute one iteration:
1. Prologue: restore inputs to body registers, copy counter
2. Body: execute shifted body program
3. Epilogue: check result, either exit to output or increment counter and loop

Returns a `MuIterationResult` with either:
- Exit: bodyResult = 0, PC = muOutputPC
- Continue: bodyResult ≠ 0, PC = muLoopStartPC, counter incremented
-/
noncomputable def muLoopIteration (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ)
    (hbody_sf : body.IsStandardForm) (s : State) (k : ℕ)
    (inputs : Fin regs.length → ℕ)
    (hs_counter : s (mkMuLayout regs body).counterReg = k)
    (hs_zero : s (mkMuLayout regs body).zeroReg = 0)
    (hs_saved : ∀ i : Fin regs.length, s ((mkMuLayout regs body).savedStart + i) = inputs i)
    (hf_halts : Halts body ((List.ofFn inputs) ++ [k])) :
    MuIterationResult regs body resultReg s k := by
  /-
  Proof structure (following the pattern from Urm.Minimization):

  1. **Prologue Phase**: Execute straight-line prologue
     - Clears body workspace registers
     - Copies saved inputs to body input registers (base + 0, ..., base + n-1)
     - Copies counter to body counter register (base + n)

  2. **Body Phase**: Execute shifted body using Halts.shift_from_state
     - Body runs on shifted registers (offset by base)
     - Halts and produces result in R[base] (which is body's R[0])

  3. **Epilogue Phase**: Branch based on result
     - J base zeroReg outputPC: if result = 0, jump to output
     - S counterReg: increment counter
     - J zeroReg zeroReg loopStart: unconditional jump back

  4. **Construct Result**: Either exit or continue case based on bodyResult
  -/

  -- Get the body result using Classical.choose (since we're noncomputable)
  let layout := mkMuLayout regs body
  let bodyInputs := (List.ofFn inputs) ++ [k]
  let bodyResult := Result body bodyInputs hf_halts

  -- The rest of the proof constructs the MuIterationResult
  -- For now, we use sorry placeholders for the complex step constructions
  exact {
    finalConfig := sorry
    steps := sorry
    bodyResult := bodyResult
    outcome := sorry
    zero_preserved := sorry
    saved_preserved := sorry
  }

/-! ## Mu Correctness -/

/-- Length of compileMu. -/
theorem compileMu_length (regs : List ℕ) (body : FlatProgram) (resultReg : ℕ) :
    (compileMu regs body resultReg).length =
      muOutputPC regs body + (if regs = [] then 0 else 1) := by
  simp only [compileMu, muOutputPC, muEpilogueStartPC, muBodyStartPC,
    List.length_append, muSetupPhase, muPrologue, muEpilogue, clearBodyRegs,
    List.length_mapIdx, List.length_map, List.length_range, List.length_cons, List.length_nil,
    Program.shiftRegisters_length, Program.shiftJumps_length, mkMuLayout]
  cases regs with
  | nil => rfl
  | cons h t =>
    simp only [List.cons_ne_nil, ↓reduceIte, List.length_cons, muOutputPhase, List.length_nil]

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
    (hbody_sf : body.IsStandardForm) (s : State) (hregs : regs ≠ [])
    (hmu_dom : (runMu s regs body resultReg).Dom) :
    ∃ c, Steps (compileMu regs body resultReg) ⟨0, s⟩ c ∧
         c.isHalted (compileMu regs body resultReg) ∧
         c.state (regs[0]'(List.length_pos_of_ne_nil hregs)) =
           ((runMu s regs body resultReg).get hmu_dom) (regs[0]'(List.length_pos_of_ne_nil hregs)) := by
  /-
  Proof structure (following the pattern from Urm.Minimization):

  1. **Domain Analysis**: From hmu_dom, we know:
     - findMuExit.Dom (there exists exit counter N)
     - runMuIteration halts at exit counter N
     - For k < N: body(inputs, k) halts with result ≠ 0
     - At k = N: body(inputs, N) halts with result = 0

  2. **Setup Phase** (muSetupPhase):
     - Executes straight-line program
     - Saves inputs to savedStart area
     - Zeros counter and zeroReg
     - State satisfies MuLoopInvariant with k = 0

  3. **Loop Iterations** (0 to N-1):
     For each k < N:
     a. Prologue: restore inputs, set counter to k
     b. Body: execute shifted body, get non-zero result
     c. Epilogue: since result ≠ 0, increment counter, jump to loop start
     After N iterations: at loopStart with counter = N

  4. **Final Iteration** (k = N):
     a. Prologue: restore inputs, set counter to N
     b. Body: execute shifted body, get result = 0
     c. Epilogue: since result = 0, jump to output

  5. **Output Phase**:
     - T resultReg (regs[0]): copy body's result register to output
     - Final state has correct result in regs[0]

  Key lemmas needed:
  - muSetupPhase_steps: Setup executes and establishes invariant
  - muLoopIteration_steps: One iteration either exits or continues
  - muOutputPhase_steps: Output phase copies result correctly
  -/
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
    -- Note: compileBlock_correct proves result is in regs[0], but this theorem asks about R[0].
    -- These match when regs[0] = 0, which is a reasonable assumption for top-level calls.
    -- For a fully general proof, we would need to track register mappings more carefully.
    simp only [compileInstr, evalInstr] at hdom ⊢
    -- The well-formedness condition ensures body is standard form and regs is non-empty
    -- BlockWellFormed for Block = regs ≠ [] ∧ body.IsStandardForm
    have hwf_block : regs ≠ [] ∧ body.IsStandardForm := hwf.1
    have hregs : regs ≠ [] := hwf_block.1
    have hbody_sf : body.IsStandardForm := hwf_block.2
    -- Extract halting from domain
    have hblock_dom := hdom
    simp only [runBlock] at hblock_dom
    -- TODO: Connect compileBlock_correct with evalInstr semantics
    -- This requires showing that the Urm.eval result matches the compiled execution
    sorry
  | Mu regs body resultReg =>
    -- Use compileMu_correct
    -- Note: Similar issue as Block - compileMu_correct proves result is in regs[0].
    simp only [compileInstr, evalInstr] at hdom ⊢
    -- The well-formedness condition ensures body is standard form
    -- MuWellFormed for Mu = regs ≠ [] ∧ body.IsStandardForm ∧ resultReg ≤ ...
    have hwf_mu : regs ≠ [] ∧ body.IsStandardForm ∧ resultReg ≤ regs.length + body.maxRegister := hwf.2
    have hregs : regs ≠ [] := hwf_mu.1
    have hbody_sf : body.IsStandardForm := hwf_mu.2.1
    -- TODO: Connect compileMu_correct with evalInstr semantics
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
