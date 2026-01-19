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
