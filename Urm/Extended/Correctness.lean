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
import Urm.Composition.Helpers

/-! # Extended URM: Compiler Correctness

This module proves the correctness of the ExtendedURM to base URM compiler:
running the compiled program produces the same result as the ExtendedURM semantics.

## Main Theorems

- `compileBlock_correct`: Compiled Block behaves like `runBlock`
- `compileWhile_correct`: Compiled While behaves like `runWhile`
- `compile_correct`: Full program correctness

## Proof Strategy

The correctness proof follows the structure of compilation:

### Block Correctness
1. **copyIn phase**: Straight-line, copies host registers to body workspace
2. **body phase**: Body executes with shifted registers, producing same result
3. **copyOut phase**: Straight-line, copies result back to host register

### While Correctness
The compiled while loop structure:
```
[0]              Z zeroReg                    -- ensure zeroReg = 0
[1]              J condReg zeroReg exitPC     -- if R[condReg] = 0, exit
[2..2+len-1]     body (jump-shifted)          -- execute body
[2+len]          J zeroReg zeroReg 1          -- unconditional jump to check
[exitPC=2+len+1] (halted)
```

The correctness proof uses strong induction on the number of iterations.

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

/-! ### Shifted Program Preservation Lemmas -/

/-- Any write target in a shifted program is ≥ offset. -/
private theorem shiftRegisters_writesTo_ge_offset {p : FlatProgram} {offset idx : ℕ}
    {instr : Instr} (hinstr : (p.shiftRegisters offset).getInstr idx = some instr)
    {target : ℕ} (htarget : instr.writesTo = some target) : offset ≤ target := by
  simp only [Program.getInstr, Program.shiftRegisters, List.getElem?_map] at hinstr
  cases h : p[idx]? with
  | none => simp only [h, Option.map_none] at hinstr; cases hinstr
  | some orig =>
    simp only [h, Option.map_some] at hinstr
    cases orig with
    | Z m =>
      simp only [Instr.shiftRegisters, Option.some.injEq] at hinstr
      rw [← hinstr] at htarget
      simp only [Instr.writesTo, Option.some.injEq] at htarget; omega
    | S m =>
      simp only [Instr.shiftRegisters, Option.some.injEq] at hinstr
      rw [← hinstr] at htarget
      simp only [Instr.writesTo, Option.some.injEq] at htarget; omega
    | T m n =>
      simp only [Instr.shiftRegisters, Option.some.injEq] at hinstr
      rw [← hinstr] at htarget
      simp only [Instr.writesTo, Option.some.injEq] at htarget; omega
    | J _ _ _ =>
      simp only [Instr.shiftRegisters, Option.some.injEq] at hinstr
      rw [← hinstr] at htarget
      simp only [Instr.writesTo] at htarget; cases htarget

/-- Single step on a shifted program preserves registers below the offset. -/
private theorem step_shiftRegisters_preserves_below {p : FlatProgram} {c c' : Config}
    (offset : ℕ) (hstep : Step (p.shiftRegisters offset) c c')
    (r : ℕ) (hr : r < offset) : c'.state r = c.state r := by
  cases hstep with
  | zero hinstr =>
    simp only [State.write]
    have hge := shiftRegisters_writesTo_ge_offset hinstr rfl
    have hlt : r < _ := Nat.lt_of_lt_of_le hr hge
    exact Function.update_of_ne (Nat.ne_of_lt hlt) _ _
  | succ hinstr =>
    simp only [State.write]
    have hge := shiftRegisters_writesTo_ge_offset hinstr rfl
    have hlt : r < _ := Nat.lt_of_lt_of_le hr hge
    exact Function.update_of_ne (Nat.ne_of_lt hlt) _ _
  | trans hinstr =>
    simp only [State.write, State.read]
    have hge := shiftRegisters_writesTo_ge_offset hinstr rfl
    have hlt : r < _ := Nat.lt_of_lt_of_le hr hge
    exact Function.update_of_ne (Nat.ne_of_lt hlt) _ _
  | jump_eq _ _ | jump_ne _ _ =>
    rfl

/-- Steps on a shifted program preserve registers below the offset. -/
private theorem steps_shiftRegisters_preserves_below {p : FlatProgram} {c c' : Config}
    (offset : ℕ) (hsteps : Steps (p.shiftRegisters offset) c c')
    (r : ℕ) (hr : r < offset) : c'.state r = c.state r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih => rw [ih]; exact step_shiftRegisters_preserves_below offset hstep r hr

/-- compileBlock preserves register 0 when regs[0] ≠ 0.
This is because:
- copyToBody writes to [base, base+len-1] where base > 0
- shiftedBody writes to [base, base+maxReg] where base > 0
- copyFromBody writes to regs[0] ≠ 0 -/
theorem compileBlock_preserves_zero (regs : List ℕ) (body : FlatProgram)
    (hbody_sf : body.IsStandardForm) (s : State) (hregs : regs ≠ [])
    (hbody_halts : Halts body (List.ofFn fun i : Fin regs.length => s (regs[i])))
    (hworkspace_zero : ∀ r, regs.length ≤ r → r ≤ body.maxRegister →
        s (r + registerBase regs) = 0)
    (hr0 : regs[0]'(List.length_pos_of_ne_nil hregs) ≠ 0)
    {c : Config} (hsteps : Steps (compileBlock regs body) ⟨0, s⟩ c)
    (hhalted : c.isHalted (compileBlock regs body)) :
    c.state 0 = s 0 := by
  -- Duplicate the structure of compileBlock_correct to extract intermediate states
  let base := registerBase regs
  have hbase_pos : 0 < base := by
    cases regs with
    | nil => exact absurd rfl hregs
    | cons h t =>
      simp only [base, registerBase]
      omega

  -- Execute copyIn phase
  have hsl_copyIn := copyToBody_isStraightLine regs base
  have ⟨c_copyIn, hsteps_copyIn, hhalted_copyIn, hpc_copyIn⟩ :=
    straightLine_halts_from_state hsl_copyIn s

  -- copyIn preserves register 0 (writes to [base, base+len-1], base > 0)
  have h_copyIn_preserves_zero : c_copyIn.state 0 = s 0 := by
    have hne : ∀ i : Fin regs.length, (0 : ℕ) ≠ base + i := fun i => by omega
    have hspec := straightLineFinalState_spec hsl_copyIn s
    have hc_eq : c_copyIn = Classical.choose (straightLine_halts_from_state hsl_copyIn s) :=
      Steps.halts_unique hsteps_copyIn hhalted_copyIn hspec.1 hspec.2.1
    rw [show c_copyIn.state = straightLineFinalState hsl_copyIn s by simp [straightLineFinalState, hc_eq]]
    exact copyToBody_preserves regs base s 0 hne

  -- Agreement for body execution
  let bodyInputs := List.ofFn fun i : Fin regs.length => s (regs[i])
  have h_agreement : ∀ r, r ≤ body.maxRegister →
      c_copyIn.state.read (r + base) = bodyInputs.getD r 0 := by
    intro r hr
    simp only [State.read]
    by_cases hr_lt : r < regs.length
    · have hspec := straightLineFinalState_spec hsl_copyIn s
      have hc_eq : c_copyIn = Classical.choose (straightLine_halts_from_state hsl_copyIn s) :=
        Steps.halts_unique hsteps_copyIn hhalted_copyIn hspec.1 hspec.2.1
      have heq : (base + r) = (r + base) := Nat.add_comm base r
      rw [← heq]
      rw [show c_copyIn.state = straightLineFinalState hsl_copyIn s by simp [straightLineFinalState, hc_eq]]
      have hlen : bodyInputs.length = regs.length := List.length_ofFn
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hr_lt)]
      simp only [Option.getD_some, bodyInputs, List.getElem_ofFn]
      exact copyToBody_effect regs base s (registerBase_gt_all regs) ⟨r, hr_lt⟩
    · have hlen : bodyInputs.length = regs.length := List.length_ofFn
      have hge : regs.length ≤ r := Nat.not_lt.mp hr_lt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hlen ▸ hge)]
      simp only [Option.getD_none]
      have hne : ∀ i : Fin regs.length, r + base ≠ base + i := fun ⟨i, hi⟩ => by omega
      have hspec := straightLineFinalState_spec hsl_copyIn s
      have hc_eq : c_copyIn = Classical.choose (straightLine_halts_from_state hsl_copyIn s) :=
        Steps.halts_unique hsteps_copyIn hhalted_copyIn hspec.1 hspec.2.1
      rw [show c_copyIn.state = straightLineFinalState hsl_copyIn s by simp [straightLineFinalState, hc_eq]]
      rw [copyToBody_preserves regs base s (r + base) hne]
      exact hworkspace_zero r hge hr

  -- Execute shifted body
  have ⟨c_body, hsteps_body, hhalted_body, _⟩ :=
    Halts.shift_from_state base hbody_halts h_agreement

  -- Shifted body preserves register 0 (writes to [base, base+maxReg], base > 0)
  have h_body_preserves_zero : c_body.state 0 = c_copyIn.state 0 :=
    steps_shiftRegisters_preserves_below base hsteps_body 0 hbase_pos

  -- Execute copyOut phase
  have hsl_copyOut := copyFromBody_isStraightLine regs base
  have ⟨c_copyOut, hsteps_copyOut, hhalted_copyOut, hpc_copyOut⟩ :=
    straightLine_halts_from_state hsl_copyOut c_body.state

  -- copyOut preserves register 0 (writes to regs[0] ≠ 0)
  have h_copyOut_preserves_zero : c_copyOut.state 0 = c_body.state 0 := by
    have hne : regs.head? ≠ some 0 := by
      cases regs with
      | nil => exact absurd rfl hregs
      | cons h t =>
        simp only [List.head?]
        intro heq
        injection heq with heq'
        exact hr0 heq'
    have hspec := straightLineFinalState_spec hsl_copyOut c_body.state
    have hc_eq : c_copyOut = Classical.choose (straightLine_halts_from_state hsl_copyOut c_body.state) :=
      Steps.halts_unique hsteps_copyOut hhalted_copyOut hspec.1 hspec.2.1
    rw [show c_copyOut.state = straightLineFinalState hsl_copyOut c_body.state by simp [straightLineFinalState, hc_eq]]
    exact copyFromBody_preserves regs base c_body.state 0 hne

  -- Chain preservation and show c.state 0 = s 0
  -- We need to show c = c_final where c_final uses c_copyOut.state
  let copyIn := copyToBody regs base
  let copyOut := copyFromBody regs base
  let copyOutOffset := copyIn.length + body.length

  have hbody_pc : c_body.pc = body.length := by
    have hbody_sf_shifted := shiftRegisters_isStandardForm hbody_sf base
    have h := Program.IsStandardForm.pc_eq_length_of_halted hbody_sf_shifted hsteps_body (Nat.zero_le _) hhalted_body
    simp only [Program.shiftRegisters_length] at h
    exact h

  -- Build the final configuration
  let c_final : Config := ⟨copyOutOffset + c_copyOut.pc, c_copyOut.state⟩

  -- Show c = c_final via uniqueness
  have hfinal_halted : c_final.isHalted (compileBlock regs body) := by
    simp only [Config.isHalted, compileBlock_length, c_final, copyOutOffset, hpc_copyOut]
    simp only [copyFromBody]
    cases regs with
    | nil => exact absurd rfl hregs
    | cons h t =>
      simp only [List.length_cons, List.cons_ne_nil, if_false, copyIn, copyToBody,
        List.length_mapIdx, List.length_nil, Nat.zero_add, le_refl]

  -- Build complete steps to c_final
  have hcopyIn_embed : ∀ i, i < copyIn.length →
      (compileBlock regs body).getInstr (0 + i) = copyIn.getInstr i := by
    intro i hi
    have hlen_copyIn : copyIn.length = regs.length := by simp only [copyIn, copyToBody, List.length_mapIdx]
    simp only [copyIn, hlen_copyIn] at hi
    simp only [compileBlock, Program.getInstr, Nat.zero_add]
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

  have hbody_embed : ∀ i, i < (body.shiftRegisters base).length →
      (compileBlock regs body).getInstr (copyIn.length + i) =
      ((body.shiftRegisters base).shiftJumps copyIn.length).getInstr i := by
    intro i hi
    simp only [Program.shiftRegisters_length] at hi
    have hlen_copyIn : copyIn.length = regs.length := by simp only [copyIn, copyToBody, List.length_mapIdx]
    have hlen_shifted : ((body.shiftRegisters base).shiftJumps copyIn.length).length = body.length := by
      simp only [Program.shiftJumps_length, Program.shiftRegisters_length]
    simp only [compileBlock, Program.getInstr]
    have hlt1 : copyIn.length + i < (copyIn ++ (body.shiftRegisters base).shiftJumps copyIn.length).length := by
      simp only [List.length_append, Program.shiftJumps_length, Program.shiftRegisters_length]; omega
    rw [List.getElem?_append_left hlt1]
    rw [List.getElem?_append_right (by omega : copyIn.length ≤ copyIn.length + i)]
    simp only [Nat.add_sub_cancel_left, Program.shiftJumps, Program.shiftRegisters, List.getElem?_map]

  have hsteps_body_lifted := Steps.shiftJumps_at_offset copyIn.length hbody_embed hsteps_body

  have hsteps_body_from_copyIn : Steps (compileBlock regs body)
      ⟨copyIn.length, c_copyIn.state⟩
      ⟨copyIn.length + c_body.pc, c_body.state⟩ := by
    convert hsteps_body_lifted using 2

  have hsteps_copyIn_body := Relation.ReflTransGen.trans hsteps_copyIn_lifted hsteps_body_from_copyIn

  have hcopyOut_embed : ∀ i, i < copyOut.length →
      (compileBlock regs body).getInstr (copyOutOffset + i) = copyOut.getInstr i := by
    intro i hi
    have hlen_copyIn' : copyIn.length = regs.length := by simp only [copyIn, copyToBody, List.length_mapIdx]
    have hlen_sh : ((body.shiftRegisters base).shiftJumps copyIn.length).length = body.length := by
      simp only [Program.shiftJumps_length, Program.shiftRegisters_length]
    have hlen_out : copyOut.length = if regs = [] then 0 else 1 := by
      simp only [copyOut, copyFromBody]; cases regs with | nil => rfl | cons _ _ => rfl
    simp only [compileBlock, copyOut, base]
    simp only [Program.getInstr]
    have h1 : copyOutOffset + i ≥ (copyToBody regs (registerBase regs) ++
        (body.shiftRegisters (registerBase regs)).shiftJumps (copyToBody regs (registerBase regs)).length).length := by
      simp only [List.length_append, Program.shiftJumps_length, Program.shiftRegisters_length,
        copyOutOffset, copyIn, copyToBody, List.length_mapIdx]; omega
    rw [List.getElem?_append_right h1]
    -- Simplify the index: copyOutOffset + i - prefix.length = i
    simp only [List.length_append, copyOutOffset, copyIn, copyToBody, List.length_mapIdx,
      Program.shiftJumps_length, Program.shiftRegisters_length]
    congr 1
    omega

  have hsteps_copyOut_lifted := Steps.straightLine_at_offset copyOutOffset hsl_copyOut hcopyOut_embed hsteps_copyOut

  have hsteps_copyOut_from_body : Steps (compileBlock regs body)
      ⟨copyIn.length + c_body.pc, c_body.state⟩
      ⟨copyOutOffset + c_copyOut.pc, c_copyOut.state⟩ := by
    have hpc_eq : copyIn.length + c_body.pc = copyOutOffset := by
      simp only [copyOutOffset, hbody_pc]
    rw [hpc_eq]
    exact hsteps_copyOut_lifted

  have hsteps_all := Relation.ReflTransGen.trans hsteps_copyIn_body hsteps_copyOut_from_body

  -- c = c_final by uniqueness
  have hc_eq : c = c_final := Steps.halts_unique hsteps hhalted hsteps_all hfinal_halted

  -- Chain: c.state 0 = c_copyOut.state 0 = c_body.state 0 = c_copyIn.state 0 = s 0
  calc c.state 0 = c_final.state 0 := by rw [hc_eq]
    _ = c_copyOut.state 0 := rfl
    _ = c_body.state 0 := h_copyOut_preserves_zero
    _ = c_copyIn.state 0 := h_body_preserves_zero
    _ = s 0 := h_copyIn_preserves_zero

/-! ## While Correctness -/

/-- Helper: zeroReg for While compilation is above both condReg and body.maxRegister. -/
def whileZeroReg (condReg : ℕ) (body : FlatProgram) : ℕ :=
  max condReg body.maxRegister + 1

/-- The exit PC for a compiled while loop. -/
def whileExitPC (body : FlatProgram) : ℕ := 2 + body.length + 1

/-- The zeroReg is greater than condReg. -/
theorem whileZeroReg_gt_condReg (condReg : ℕ) (body : FlatProgram) :
    condReg < whileZeroReg condReg body := by
  simp only [whileZeroReg]; omega

/-- The zeroReg is greater than body.maxRegister. -/
theorem whileZeroReg_gt_maxRegister (condReg : ℕ) (body : FlatProgram) :
    body.maxRegister < whileZeroReg condReg body := by
  simp only [whileZeroReg]; omega

/-! ### Instruction Access Lemmas -/

/-- Get the Z instruction at position 0 in compileWhile. -/
theorem compileWhile_instr_0 (condReg : ℕ) (body : FlatProgram) :
    (compileWhile condReg body).getInstr 0 =
      some (Instr.Z (whileZeroReg condReg body)) := by
  simp only [compileWhile, whileZeroReg, Program.getInstr, List.getElem?_append,
    List.length_cons, List.length_nil]
  rfl

/-- Get the J instruction at position 1 in compileWhile (the check instruction). -/
theorem compileWhile_instr_1 (condReg : ℕ) (body : FlatProgram) :
    (compileWhile condReg body).getInstr 1 =
      some (Instr.J condReg (whileZeroReg condReg body) (whileExitPC body)) := by
  simp only [compileWhile, whileZeroReg, whileExitPC, Program.getInstr, List.getElem?_append,
    List.length_cons, List.length_nil]
  rfl

/-- Get the loopback J instruction at position 2 + body.length. -/
theorem compileWhile_instr_loopback (condReg : ℕ) (body : FlatProgram) :
    (compileWhile condReg body).getInstr (2 + body.length) =
      some (Instr.J (whileZeroReg condReg body) (whileZeroReg condReg body) 1) := by
  simp only [compileWhile, whileZeroReg, Program.getInstr]
  -- compileWhile = [Z zeroReg, J condReg zeroReg exitPC] ++ body.shiftJumps 2 ++ [J zeroReg zeroReg 1]
  -- We want index 2 + body.length, which is past the prefix [Z, J] ++ shiftedBody
  have hlen : (body.shiftJumps 2).length = body.length := Program.shiftJumps_length 2 body
  -- The prefix has length 2 + body.length, so we're accessing the first element of the suffix
  have hge : 2 + body.length ≥ ([Instr.Z (max condReg body.maxRegister + 1),
      Instr.J condReg (max condReg body.maxRegister + 1) (2 + body.length + 1)] ++
      body.shiftJumps 2).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]; omega
  rw [List.getElem?_append_right hge]
  -- Simplify the index: 2 + body.length - (0 + 1 + 1 + body.length) = 0
  have hidx : 2 + body.length - (0 + 1 + 1 + body.length) = 0 := by omega
  simp only [List.length_append, List.length_cons, List.length_nil, hlen, hidx,
    List.getElem?_cons_zero]

/-- Body instructions are embedded at offset 2 with shifted jumps. -/
theorem compileWhile_body_embed (condReg : ℕ) (body : FlatProgram) :
    ∀ i, i < body.length →
      (compileWhile condReg body).getInstr (2 + i) = (body.shiftJumps 2).getInstr i := by
  intro i hi
  simp only [compileWhile, Program.getInstr]
  -- compileWhile = [Z zeroReg, J condReg zeroReg exitPC] ++ body.shiftJumps 2 ++ [J zeroReg zeroReg 1]
  -- Index 2 + i (for i < body.length) is within the shifted body part
  have hlen : (body.shiftJumps 2).length = body.length := Program.shiftJumps_length 2 body
  -- First, 2 + i < length of (prefix ++ shiftedBody), so we're in the left part
  have hlt : 2 + i < ([Instr.Z (max condReg body.maxRegister + 1),
      Instr.J condReg (max condReg body.maxRegister + 1) (2 + body.length + 1)] ++
      body.shiftJumps 2).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]; omega
  rw [List.getElem?_append_left hlt]
  -- Now we have (prefix ++ shiftedBody)[2 + i]?, and 2 + i >= 2
  have hge : 2 + i ≥ 2 := by omega
  rw [List.getElem?_append_right hge]
  -- Simplify the index: 2 + i - (0 + 1 + 1) = i
  have hidx : 2 + i - (0 + 1 + 1) = i := by omega
  simp only [List.length_cons, List.length_nil, hidx]

/-! ### Phase Step Lemmas -/

/-- Setup phase: Z zeroReg sets zeroReg to 0, moving from PC 0 to PC 1. -/
theorem compileWhile_setup_step (condReg : ℕ) (body : FlatProgram) (s : State) :
    Step (compileWhile condReg body) ⟨0, s⟩ ⟨1, s.write (whileZeroReg condReg body) 0⟩ :=
  Step.zero (compileWhile_instr_0 condReg body)

/-- Check phase (exit): when condReg = 0 = zeroReg, jump to exitPC. -/
theorem compileWhile_check_exit (condReg : ℕ) (body : FlatProgram) (s : State)
    (hzero : s (whileZeroReg condReg body) = 0) (hcond : s condReg = 0) :
    Step (compileWhile condReg body) ⟨1, s⟩ ⟨whileExitPC body, s⟩ := by
  have heq : s.read condReg = s.read (whileZeroReg condReg body) := by
    simp only [State.read, hcond, hzero]
  exact Step.jump_eq (compileWhile_instr_1 condReg body) heq

/-- Check phase (continue): when condReg ≠ zeroReg, fall through to body. -/
theorem compileWhile_check_continue (condReg : ℕ) (body : FlatProgram) (s : State)
    (hzero : s (whileZeroReg condReg body) = 0) (hcond : s condReg ≠ 0) :
    Step (compileWhile condReg body) ⟨1, s⟩ ⟨2, s⟩ := by
  have hne : s.read condReg ≠ s.read (whileZeroReg condReg body) := by
    simp only [State.read, hzero]; exact hcond
  exact Step.jump_ne (compileWhile_instr_1 condReg body) hne

/-- Loopback: after body at PC 2+len, unconditionally jump back to check (PC 1). -/
theorem compileWhile_loopback_step (condReg : ℕ) (body : FlatProgram) (s : State) :
    Step (compileWhile condReg body) ⟨2 + body.length, s⟩ ⟨1, s⟩ := by
  have heq : s.read (whileZeroReg condReg body) = s.read (whileZeroReg condReg body) := rfl
  exact Step.jump_eq (compileWhile_instr_loopback condReg body) heq

/-! ### Body Execution and Preservation -/

/-- Single step preserves registers above maxRegister. -/
private theorem step_preserves_above_maxRegister {body : FlatProgram} {c c' : Config}
    (hstep : Step body c c') (r : ℕ) (hr : body.maxRegister < r) : c'.state r = c.state r := by
  cases hstep with
  | zero hinstr =>
    -- Z n writes to n, need n ≠ r
    simp only [State.write]
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hn_lt : _ < r := Nat.lt_of_le_of_lt hmax hr
    exact Function.update_of_ne (Ne.symm (Nat.ne_of_lt hn_lt)) _ _
  | succ hinstr =>
    -- S n writes to n, need n ≠ r
    simp only [State.write]
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hn_lt : _ < r := Nat.lt_of_le_of_lt hmax hr
    exact Function.update_of_ne (Ne.symm (Nat.ne_of_lt hn_lt)) _ _
  | trans hinstr =>
    -- T m n writes to n, need n ≠ r
    simp only [State.write, State.read]
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hn_le : _ ≤ body.maxRegister := Nat.le_trans (Nat.le_max_right _ _) hmax
    have hn_lt : _ < r := Nat.lt_of_le_of_lt hn_le hr
    exact Function.update_of_ne (Ne.symm (Nat.ne_of_lt hn_lt)) _ _
  | jump_eq _ _ | jump_ne _ _ =>
    -- J doesn't write to any register
    rfl

/-- Body writes only to registers ≤ maxRegister, so zeroReg is preserved. -/
theorem evalFlat_preserves_above_maxRegister {body : FlatProgram} {s : State}
    (hdom : (evalFlat body s).Dom) (r : ℕ) (hr : body.maxRegister < r) :
    (evalFlat body s).get hdom r = s r := by
  -- evalFlat returns the state of the halted configuration
  simp only [evalFlat] at hdom ⊢
  -- Get the halting configuration
  let c := Classical.choose hdom
  have hspec := Classical.choose_spec hdom
  obtain ⟨hsteps, hhalted⟩ := hspec
  -- Show that all instructions preserve register r
  -- Each instruction only writes to registers ≤ its maxRegister ≤ body.maxRegister < r
  suffices h : ∀ (c₁ c₂ : Config), Steps body c₁ c₂ → c₂.state r = c₁.state r by
    exact h ⟨0, s⟩ c hsteps
  intro c₁ c₂ hsteps'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih => rw [ih]; exact step_preserves_above_maxRegister hstep r hr

/-! ### State Agreement and Step Synchronization -/

/-- If two states agree on registers ≤ maxRegister, a step from one state implies
    the same step is possible from the other, with agreeing result states. -/
private theorem step_synchronized {body : FlatProgram} {pc pc' : ℕ} {s s' σ : State}
    (hagree : ∀ r, r ≤ body.maxRegister → s r = s' r)
    (hstep : Step body ⟨pc, s⟩ ⟨pc', σ⟩) :
    ∃ σ', Step body ⟨pc, s'⟩ ⟨pc', σ'⟩ ∧ (∀ r, r ≤ body.maxRegister → σ r = σ' r) := by
  cases hstep with
  | zero hinstr =>
    -- Z n: writes 0 to register n
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    refine ⟨s'.write _ 0, Step.zero hinstr, ?_⟩
    intro r hr
    simp only [State.write, Function.update]
    split_ifs with heq
    · rfl
    · exact hagree r hr
  | succ hinstr =>
    -- S n: reads n, writes n+1 to n
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hn_le : _ ≤ body.maxRegister := hmax
    refine ⟨s'.write _ (s'.read _ + 1), Step.succ hinstr, ?_⟩
    intro r hr
    simp only [State.write, State.read, Function.update]
    split_ifs with heq
    · subst heq; rw [hagree _ hn_le]
    · exact hagree r hr
  | trans hinstr =>
    -- T m n: reads m, writes to n
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hm_le : _ ≤ body.maxRegister := Nat.le_trans (Nat.le_max_left _ _) hmax
    have hn_le : _ ≤ body.maxRegister := Nat.le_trans (Nat.le_max_right _ _) hmax
    refine ⟨s'.write _ (s'.read _), Step.trans hinstr, ?_⟩
    intro r hr
    simp only [State.write, State.read, Function.update]
    split_ifs with heq
    · subst heq; rw [hagree _ hm_le]
    · exact hagree r hr
  | jump_eq hinstr hcmp =>
    -- J m n q with equal: reads m and n (q is unified with pc')
    rename_i m n
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hm_le : m ≤ body.maxRegister := Nat.le_trans (Nat.le_max_left m n) hmax
    have hn_le : n ≤ body.maxRegister := Nat.le_trans (Nat.le_max_right m n) hmax
    have hcmp' : s'.read m = s'.read n := by
      simp only [State.read] at hcmp ⊢
      rw [← hagree m hm_le, ← hagree n hn_le, hcmp]
    exact ⟨s', Step.jump_eq hinstr hcmp', hagree⟩
  | jump_ne hinstr hcmp =>
    -- J m n q with not equal: reads m and n
    rename_i m n _
    have hmax := Program.getInstr_maxRegister hinstr
    simp only [Instr.maxRegister] at hmax
    have hm_le : m ≤ body.maxRegister := Nat.le_trans (Nat.le_max_left m n) hmax
    have hn_le : n ≤ body.maxRegister := Nat.le_trans (Nat.le_max_right m n) hmax
    have hcmp' : s'.read m ≠ s'.read n := by
      simp only [State.read] at hcmp ⊢
      rw [← hagree m hm_le, ← hagree n hn_le]
      exact hcmp
    exact ⟨s', Step.jump_ne hinstr hcmp', hagree⟩

/-- Helper: If two states agree on ≤ maxRegister and we have steps from one,
    we can build parallel steps from the other with agreeing final states. -/
private theorem steps_synchronized' {body : FlatProgram} {c c_end : Config}
    (hsteps : Steps body c c_end) :
    ∀ s', (∀ r, r ≤ body.maxRegister → c.state r = s' r) →
      ∃ c'_end : Config, Steps body ⟨c.pc, s'⟩ c'_end ∧
        c'_end.pc = c_end.pc ∧
        (∀ r, r ≤ body.maxRegister → c_end.state r = c'_end.state r) := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- No steps: ⟨c.pc, s'⟩ is the corresponding config
    intro s' hagree
    exact ⟨⟨c_end.pc, s'⟩, Steps.refl _, rfl, hagree⟩
  | head hstep hrest ih =>
    -- c → c_mid → ... → c_end
    intro s' hagree
    -- Get the synchronized step from s'
    obtain ⟨σ', hstep', hagree'⟩ := step_synchronized hagree hstep
    -- Apply IH to the rest of the execution
    obtain ⟨c'_end, hsteps', hpc_eq, hagree_end⟩ := ih σ' hagree'
    exact ⟨c'_end, Relation.ReflTransGen.head hstep' hsteps', hpc_eq, hagree_end⟩

/-- If states agree on ≤ maxRegister, evalFlat has the same domain for both. -/
theorem evalFlat_dom_agree {body : FlatProgram} {s s' : State}
    (hagree : ∀ r, r ≤ body.maxRegister → s r = s' r) :
    (evalFlat body s).Dom ↔ (evalFlat body s').Dom := by
  simp only [evalFlat]
  constructor
  · -- Forward: s halts → s' halts
    intro ⟨c, hsteps, hhalted⟩
    obtain ⟨c', hsteps', hpc_eq, _⟩ := steps_synchronized' hsteps s' hagree
    have hhalted' : c'.isHalted body := by
      simp only [Config.isHalted] at hhalted ⊢
      rw [hpc_eq]; exact hhalted
    exact ⟨c', hsteps', hhalted'⟩
  · -- Backward: s' halts → s halts (symmetric)
    intro ⟨c', hsteps', hhalted'⟩
    have hagree_sym : ∀ r, r ≤ body.maxRegister → s' r = s r := fun r hr => (hagree r hr).symm
    obtain ⟨c, hsteps, hpc_eq, _⟩ := steps_synchronized' hsteps' s hagree_sym
    have hhalted : c.isHalted body := by
      simp only [Config.isHalted] at hhalted' ⊢
      rw [hpc_eq]; exact hhalted'
    exact ⟨c, hsteps, hhalted⟩

/-- If states agree on ≤ maxRegister and both evalFlat calls are defined,
    the results agree on registers ≤ maxRegister. -/
theorem evalFlat_result_agree {body : FlatProgram} {s s' : State}
    (hagree : ∀ r, r ≤ body.maxRegister → s r = s' r)
    (hdom : (evalFlat body s).Dom) (hdom' : (evalFlat body s').Dom)
    (r : ℕ) (hr : r ≤ body.maxRegister) :
    (evalFlat body s).get hdom r = (evalFlat body s').get hdom' r := by
  -- Unfold evalFlat to work with Steps
  have hdom_unfold : ∃ c, Steps body ⟨0, s⟩ c ∧ c.isHalted body := by simp only [evalFlat] at hdom; exact hdom
  have hdom'_unfold : ∃ c', Steps body ⟨0, s'⟩ c' ∧ c'.isHalted body := by simp only [evalFlat] at hdom'; exact hdom'
  obtain ⟨c, hsteps, hhalted⟩ := hdom_unfold
  obtain ⟨c', hsteps', hhalted'⟩ := hdom'_unfold
  -- Use steps_synchronized' to get a synchronized execution from s'
  obtain ⟨c'_sync, hsteps'_sync, hpc_eq, hagree_end⟩ := steps_synchronized' hsteps s' hagree
  -- c'_sync is halted iff c is halted (same pc)
  have hhalted'_sync : c'_sync.isHalted body := by
    simp only [Config.isHalted] at hhalted ⊢
    rw [hpc_eq]; exact hhalted
  -- By determinism, c' = c'_sync (both are halting configs from same starting state)
  have hc'_eq : c' = c'_sync := Steps.halts_unique hsteps' hhalted' hsteps'_sync hhalted'_sync
  -- The result from evalFlat is the state at the halting config
  simp only [evalFlat]
  -- Show that the chosen configs are c and c'
  have hchoose_c : (Classical.choose hdom) = c := by
    have hspec := Classical.choose_spec hdom
    exact Steps.halts_unique hspec.1 hspec.2 hsteps hhalted
  have hchoose_c' : (Classical.choose hdom') = c' := by
    have hspec' := Classical.choose_spec hdom'
    exact Steps.halts_unique hspec'.1 hspec'.2 hsteps' hhalted'
  rw [hchoose_c, hchoose_c', hc'_eq]
  exact hagree_end r hr

/-! ### Main While Correctness -/

/-- Helper: Execute body within compiled while loop.
    Body execution from PC 2 to PC (2 + body.length).
    When body is standard form, the final PC is exactly body.length. -/
private theorem compileWhile_body_steps (condReg : ℕ) (body : FlatProgram) (s : State)
    (hbody_sf : body.IsStandardForm)
    (hdom : (evalFlat body s).Dom) :
    Steps (compileWhile condReg body) ⟨2, s⟩ ⟨2 + body.length, (evalFlat body s).get hdom⟩ := by
  -- Get the body execution from evalFlat
  have hdom_unfold : ∃ c, Steps body ⟨0, s⟩ c ∧ c.isHalted body := by simp only [evalFlat] at hdom; exact hdom
  obtain ⟨c, hsteps, hhalted⟩ := hdom_unfold
  -- The final PC is exactly body.length (standard form)
  have hpc_eq : c.pc = body.length := hbody_sf.pc_eq_length_of_halted hsteps (Nat.zero_le _) hhalted
  -- Lift body steps to compileWhile using compileWhile_body_embed
  have hembed : ∀ i, i < body.length →
      (compileWhile condReg body).getInstr (2 + i) = (body.shiftJumps 2).getInstr i :=
    compileWhile_body_embed condReg body
  have hsteps' : Steps (compileWhile condReg body) ⟨2 + 0, s⟩ ⟨2 + c.pc, c.state⟩ :=
    Steps.shiftJumps_at_offset 2 hembed hsteps
  simp only [Nat.add_zero] at hsteps'
  -- Show the result state equals evalFlat result
  have hstate_eq : c.state = (evalFlat body s).get hdom := by
    simp only [evalFlat]
    have hspec := Classical.choose_spec hdom
    have heq : c = Classical.choose hdom := Steps.halts_unique hsteps hhalted hspec.1 hspec.2
    rw [heq]
  rw [hpc_eq, hstate_eq] at hsteps'
  exact hsteps'

/-- Helper: If x ∈ runWhile s and s (whileZeroReg) = 0, there exist Steps from ⟨1, s⟩ to a halted config
    with state x. Uses PFun.fixInduction' for well-founded recursion.

    The motive carries the zeroReg invariant through the induction. -/
private theorem compileWhile_from_check_mem (condReg : ℕ) (body : FlatProgram)
    (hbody_sf : body.IsStandardForm) (s : State) (x : State)
    (hmem : x ∈ runWhile s condReg body)
    (hzero : s (whileZeroReg condReg body) = 0) :
    ∃ c, Steps (compileWhile condReg body) ⟨1, s⟩ c ∧
         c.isHalted (compileWhile condReg body) ∧
         c.state = x := by
  simp only [runWhile] at hmem
  -- Use PFun.fixInduction' for well-founded induction on the fixpoint membership
  -- The motive C a := a (whileZeroReg condReg body) = 0 → ∃ c, Steps ⟨1, a⟩ c ∧ halted ∧ c.state = x
  refine PFun.fixInduction' hmem
    -- Base case: whileStep produces Sum.inl x (stop), prove C a_final
    (fun a_final hstop hzero_a => ?_)
    -- Inductive case: whileStep produces Sum.inr a₁, IH for a₁, prove C a₀
    (fun a₀ a₁ hmem_a₁ hcont ih hzero_a₀ => ?_)
    hzero  -- pass the initial invariant
  · -- Base case: a_final condReg = 0, so we exit
    simp only [whileStep] at hstop
    split_ifs at hstop with hcond
    · -- Exit: x = a_final
      have hx_eq : x = a_final := Sum.inl.inj (Part.mem_some_iff.mp hstop)
      have hstep_exit : Step (compileWhile condReg body) ⟨1, a_final⟩ ⟨whileExitPC body, a_final⟩ :=
        compileWhile_check_exit condReg body a_final hzero_a hcond
      have hhalted : (⟨whileExitPC body, a_final⟩ : Config).isHalted (compileWhile condReg body) := by
        simp only [Config.isHalted, whileExitPC, compileWhile_length]; omega
      exact ⟨⟨whileExitPC body, a_final⟩, Steps.single hstep_exit, hhalted, hx_eq.symm⟩
    · -- Contradiction: condition ≠ 0 but hstop says Sum.inl
      simp only [Part.mem_map_iff] at hstop
      obtain ⟨_, _, h⟩ := hstop
      exact absurd h (by simp)
  · -- Inductive case: a₀ condReg ≠ 0, body runs, continues to a₁
    simp only [whileStep] at hcont
    split_ifs at hcont with hcond
    · -- Contradiction: condition = 0 but hcont says Sum.inr
      simp only [Part.mem_some_iff] at hcont
      exact absurd hcont (by simp)
    · -- a₀ condReg ≠ 0, execute body and loop back
      simp only [Part.mem_map_iff] at hcont
      obtain ⟨σ, hσ_mem, hσ_eq⟩ := hcont
      cases hσ_eq  -- σ = a₁, so a₁ is the result of evalFlat body a₀
      -- Step 1: Check phase (PC 1 → PC 2)
      have hstep_check : Step (compileWhile condReg body) ⟨1, a₀⟩ ⟨2, a₀⟩ :=
        compileWhile_check_continue condReg body a₀ hzero_a₀ hcond
      -- Step 2: Body execution (PC 2 → PC 2+body.length)
      have hdom_body : (evalFlat body a₀).Dom := Part.dom_iff_mem.mpr ⟨a₁, hσ_mem⟩
      have hsteps_body := compileWhile_body_steps condReg body a₀ hbody_sf hdom_body
      -- a₁ = (evalFlat body a₀).get hdom_body
      have ha₁_eq : a₁ = (evalFlat body a₀).get hdom_body :=
        (Part.get_eq_of_mem hσ_mem hdom_body).symm
      -- Step 3: Loopback (PC 2+body.length → PC 1)
      have hstep_loopback : Step (compileWhile condReg body)
          ⟨2 + body.length, (evalFlat body a₀).get hdom_body⟩ ⟨1, (evalFlat body a₀).get hdom_body⟩ :=
        compileWhile_loopback_step condReg body ((evalFlat body a₀).get hdom_body)
      -- a₁ preserves zeroReg (body only writes to ≤ maxRegister, zeroReg > maxRegister)
      have hzero_a₁ : a₁ (whileZeroReg condReg body) = 0 := by
        have hgt : body.maxRegister < whileZeroReg condReg body := whileZeroReg_gt_maxRegister condReg body
        rw [ha₁_eq, evalFlat_preserves_above_maxRegister hdom_body (whileZeroReg condReg body) hgt]
        exact hzero_a₀
      -- Step 4: Apply IH to get from ⟨1, a₁⟩ to final config
      obtain ⟨c_final, hsteps_final, hhalted_final, hstate_final⟩ := ih hzero_a₁
      -- Compose all steps: ⟨1, a₀⟩ → ⟨2, a₀⟩ → ⟨2+len, a₁⟩ → ⟨1, a₁⟩ → c_final
      -- Rewrite using ha₁_eq to connect hsteps_body to hstep_loopback
      rw [← ha₁_eq] at hsteps_body hstep_loopback
      have hsteps_all : Steps (compileWhile condReg body) ⟨1, a₀⟩ c_final :=
        (Steps.single hstep_check).trans
          (hsteps_body.trans ((Steps.single hstep_loopback).trans hsteps_final))
      exact ⟨c_final, hsteps_all, hhalted_final, hstate_final⟩

/-- Helper lemma: runWhile from PC=1 with zeroReg=0 reaches exitPC with correct state.

The proof case splits on the condition register:
- Exit case: s condReg = 0 → exit immediately via jump
- Continue case: s condReg ≠ 0 → execute body, loop back, recurse -/
private theorem compileWhile_correct_from_check (condReg : ℕ) (body : FlatProgram)
    (hbody_sf : body.IsStandardForm) (s : State)
    (hzero : s (whileZeroReg condReg body) = 0)
    (hdom : (runWhile s condReg body).Dom) :
    ∃ c, Steps (compileWhile condReg body) ⟨1, s⟩ c ∧
         c.isHalted (compileWhile condReg body) ∧
         c.state = (runWhile s condReg body).get hdom := by
  -- Get membership from domain
  have hmem : (runWhile s condReg body).get hdom ∈ runWhile s condReg body := Part.get_mem hdom
  -- Apply the helper lemma that uses PFun.fixInduction'
  exact compileWhile_from_check_mem condReg body hbody_sf s _ hmem hzero

/-- Helper: whileStep preserves agreement on registers ≤ max condReg maxRegister.
    If two states agree on these registers, whileStep produces agreeing results. -/
private theorem whileStep_agree {condReg : ℕ} {body : FlatProgram} {s s' : State}
    (hagree : ∀ r, r ≤ max condReg body.maxRegister → s r = s' r) :
    -- Both exit or both continue
    (s condReg = 0 ↔ s' condReg = 0) ∧
    -- If they continue, the body results agree on ≤ max condReg maxRegister
    (∀ σ σ' : State, σ ∈ evalFlat body s → σ' ∈ evalFlat body s' →
      ∀ r, r ≤ max condReg body.maxRegister → σ r = σ' r) := by
  -- States agree on condReg
  have hcond_agree : s condReg = s' condReg := hagree condReg (Nat.le_max_left _ _)
  constructor
  · rw [hcond_agree]
  · -- Both bodies produce agreeing results
    intro σ σ' hσ hσ' r hr
    -- First, the states agree on ≤ body.maxRegister
    have hagree_body : ∀ r, r ≤ body.maxRegister → s r = s' r := fun r hr' =>
      hagree r (Nat.le_trans hr' (Nat.le_max_right _ _))
    -- Get domains
    have hdom : (evalFlat body s).Dom := Part.dom_iff_mem.mpr ⟨σ, hσ⟩
    have hdom' : (evalFlat body s').Dom := Part.dom_iff_mem.mpr ⟨σ', hσ'⟩
    -- The results agree on ≤ maxRegister
    have hσ_eq : σ = (evalFlat body s).get hdom := (Part.get_eq_of_mem hσ hdom).symm
    have hσ'_eq : σ' = (evalFlat body s').get hdom' := (Part.get_eq_of_mem hσ' hdom').symm
    rw [hσ_eq, hσ'_eq]
    -- Case split: either r ≤ body.maxRegister or r > body.maxRegister
    by_cases hr_le : r ≤ body.maxRegister
    · exact evalFlat_result_agree hagree_body hdom hdom' r hr_le
    · -- r > maxRegister, so body preserves it
      have hr_gt : body.maxRegister < r := Nat.lt_of_not_le hr_le
      rw [evalFlat_preserves_above_maxRegister hdom r hr_gt,
          evalFlat_preserves_above_maxRegister hdom' r hr_gt]
      -- Since r > maxRegister, we need to use the original agreement
      exact hagree r hr

/-- Helper: If `x ∈ runWhile s condReg body` and s' agrees with s on relevant registers,
    then `runWhile s' condReg body` is defined. Uses PFun.fixInduction' for well-founded recursion. -/
private theorem runWhile_dom_of_mem_agree {condReg : ℕ} {body : FlatProgram}
    {s s' : State} {x : State}
    (hmem : x ∈ runWhile s condReg body)
    (hagree : ∀ r, r ≤ max condReg body.maxRegister → s r = s' r) :
    (runWhile s' condReg body).Dom := by
  simp only [runWhile] at hmem ⊢
  -- Use PFun.fixInduction' for well-founded induction on the fixpoint membership
  -- C a := ∀ a', (∀ r, r ≤ max condReg body.maxRegister → a r = a' r) → (PFun.fix (whileStep condReg body) a').Dom
  refine PFun.fixInduction' hmem
    -- Base case: f a_final produces Sum.inl x (stop case)
    (fun a_final hstop a' hagree' => ?_)
    -- Inductive case: f a₀ produces Sum.inr a₁, x ∈ fix f a₁, and IH for a₁
    (fun a₀ a₁ hmem_a₁ hcont ih a' hagree' => ?_)
    s' hagree
  · -- Base case: whileStep a_final produces Sum.inl x, so a_final condReg = 0
    simp only [whileStep] at hstop
    split_ifs at hstop with hcond
    · -- a_final condReg = 0, so a' condReg = 0 (by agreement)
      have ha'_cond : a' condReg = 0 := by
        rw [← hagree' condReg (Nat.le_max_left _ _), hcond]
      -- whileStep a' produces Sum.inl a'
      have hstop' : Sum.inl a' ∈ whileStep condReg body a' := by
        simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_some_iff]
      -- So a' ∈ PFun.fix (whileStep condReg body) a'
      exact Part.dom_iff_mem.mpr ⟨a', PFun.fix_stop hstop'⟩
    · -- Contradiction: condition ≠ 0 but hstop says Sum.inl ∈ whileStep
      simp only [Part.mem_map_iff] at hstop
      obtain ⟨_, _, h⟩ := hstop
      exact absurd h (by simp)
  · -- Inductive case: a₀ condReg ≠ 0, body runs, continues to a₁
    simp only [whileStep] at hcont
    split_ifs at hcont with hcond
    · -- Contradiction: condition = 0 but hcont says Sum.inr ∈ whileStep
      simp only [Part.mem_some_iff] at hcont
      exact absurd hcont (by simp)
    · -- a₀ condReg ≠ 0, and Sum.inr a₁ ∈ (evalFlat body a₀).map Sum.inr
      simp only [Part.mem_map_iff] at hcont
      obtain ⟨σ, hσ_mem, hσ_eq⟩ := hcont
      cases hσ_eq  -- σ = a₁
      -- a₁ is the result of evalFlat body a₀
      -- States a₀ and a' agree on ≤ max condReg maxRegister
      have ha'_cond : a' condReg ≠ 0 := by
        rw [← hagree' condReg (Nat.le_max_left _ _)]; exact hcond
      -- a₀ and a' agree on ≤ body.maxRegister
      have hagree_body : ∀ r, r ≤ body.maxRegister → a₀ r = a' r := fun r hr =>
        hagree' r (Nat.le_trans hr (Nat.le_max_right _ _))
      -- evalFlat body a' is defined (by evalFlat_dom_agree)
      have hdom_a₀ : (evalFlat body a₀).Dom := Part.dom_iff_mem.mpr ⟨a₁, hσ_mem⟩
      have hdom_a' : (evalFlat body a').Dom := (evalFlat_dom_agree hagree_body).mp hdom_a₀
      -- Get the result a'₁
      let a'₁ := (evalFlat body a').get hdom_a'
      -- a₁ and a'₁ agree on ≤ max condReg maxRegister
      have hagree_result : ∀ r, r ≤ max condReg body.maxRegister → a₁ r = a'₁ r := by
        intro r hr
        have ha₁_eq : a₁ = (evalFlat body a₀).get hdom_a₀ :=
          (Part.get_eq_of_mem hσ_mem hdom_a₀).symm
        by_cases hr_body : r ≤ body.maxRegister
        · -- r ≤ maxRegister: use evalFlat_result_agree
          rw [ha₁_eq]
          exact evalFlat_result_agree hagree_body hdom_a₀ hdom_a' r hr_body
        · -- r > maxRegister: both preserve r
          have hr_gt : body.maxRegister < r := Nat.lt_of_not_le hr_body
          rw [ha₁_eq]
          rw [evalFlat_preserves_above_maxRegister hdom_a₀ r hr_gt]
          -- Now goal is a₀ r = a'₁ r, and a'₁ = (evalFlat body a').get hdom_a'
          have ha'₁_eq : a'₁ = (evalFlat body a').get hdom_a' := rfl
          rw [ha'₁_eq, evalFlat_preserves_above_maxRegister hdom_a' r hr_gt]
          exact hagree' r hr
      -- Apply IH: (runWhile a'₁ condReg body).Dom
      have hdom_recurse : (PFun.fix (whileStep condReg body) a'₁).Dom := ih a'₁ hagree_result
      -- Show (runWhile a' condReg body).Dom via the continue case
      have hcont' : Sum.inr a'₁ ∈ whileStep condReg body a' := by
        simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_map_iff]
        exact ⟨a'₁, Part.get_mem hdom_a', rfl⟩
      -- Get a value from the recursive call
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hdom_recurse
      -- Build the fixpoint membership via PFun.mem_fix_iff
      exact Part.dom_iff_mem.mpr ⟨y, PFun.mem_fix_iff.mpr (Or.inr ⟨a'₁, hcont', hy⟩)⟩

/-- Domain equivalence: runWhile terminates iff runWhile from agreeing state terminates. -/
private theorem runWhile_dom_agree' {condReg : ℕ} {body : FlatProgram} {s s' : State}
    (hagree : ∀ r, r ≤ max condReg body.maxRegister → s r = s' r) :
    (runWhile s condReg body).Dom ↔ (runWhile s' condReg body).Dom := by
  constructor
  · -- Forward: s terminates → s' terminates
    intro hdom
    obtain ⟨x, hmem⟩ := Part.dom_iff_mem.mp hdom
    exact runWhile_dom_of_mem_agree hmem hagree
  · -- Backward: s' terminates → s terminates (symmetric)
    intro hdom'
    obtain ⟨x', hmem'⟩ := Part.dom_iff_mem.mp hdom'
    have hagree_sym : ∀ r, r ≤ max condReg body.maxRegister → s' r = s r :=
      fun r hr => (hagree r hr).symm
    exact runWhile_dom_of_mem_agree hmem' hagree_sym

/-- Domain equivalence: writing to zeroReg doesn't affect whether runWhile terminates. -/
private theorem runWhile_write_zeroReg_dom (condReg : ℕ) (body : FlatProgram) (s : State) (v : ℕ) :
    (runWhile (s.write (whileZeroReg condReg body) v) condReg body).Dom ↔
    (runWhile s condReg body).Dom := by
  -- The states agree on all meaningful registers (≤ max condReg maxRegister)
  have hzero_gt_cond : whileZeroReg condReg body > condReg := whileZeroReg_gt_condReg condReg body
  have hzero_gt_max : whileZeroReg condReg body > body.maxRegister := whileZeroReg_gt_maxRegister condReg body
  have hagree : ∀ r, r ≤ max condReg body.maxRegister → (s.write (whileZeroReg condReg body) v) r = s r := by
    intro r hr
    have hr_lt : r < whileZeroReg condReg body := by
      simp only [whileZeroReg] at hzero_gt_cond hzero_gt_max ⊢
      omega
    have hne : r ≠ whileZeroReg condReg body := Nat.ne_of_lt hr_lt
    simp only [State.write, Function.update, dif_neg hne]
  exact runWhile_dom_agree' hagree

/-- Helper: If `x ∈ runWhile s condReg body` and `x' ∈ runWhile s' condReg body` where s and s'
    agree on relevant registers, then x and x' agree on relevant registers.
    Uses PFun.fixInduction' for well-founded recursion. -/
private theorem runWhile_result_of_mem_agree {condReg : ℕ} {body : FlatProgram}
    {s s' x x' : State}
    (hmem : x ∈ runWhile s condReg body)
    (hmem' : x' ∈ runWhile s' condReg body)
    (hagree : ∀ r, r ≤ max condReg body.maxRegister → s r = s' r) :
    ∀ r, r ≤ max condReg body.maxRegister → x r = x' r := by
  simp only [runWhile] at hmem hmem'
  -- Use PFun.fixInduction' on hmem
  -- C a := ∀ a', (agreement) → ∀ x' ∈ fix f a', ∀ r, r ≤ max... → (the x from a) r = x' r
  refine PFun.fixInduction' hmem
    -- Base case: f a_final produces Sum.inl x (stop case)
    (fun a_final hstop a' hagree' x' hmem'_inner r hr => ?_)
    -- Inductive case: f a₀ produces Sum.inr a₁, x ∈ fix f a₁, and IH for a₁
    (fun a₀ a₁ hmem_a₁ hcont ih a' hagree' x' hmem'_inner r hr => ?_)
    s' hagree x' hmem'
  · -- Base case: whileStep a_final produces Sum.inl x, so a_final condReg = 0
    -- and x = a_final
    simp only [whileStep] at hstop
    split_ifs at hstop with hcond
    · -- a_final condReg = 0, so a' condReg = 0 (by agreement)
      have ha'_cond : a' condReg = 0 := by
        rw [← hagree' condReg (Nat.le_max_left _ _), hcond]
      -- x = a_final (from hstop: Sum.inl x ∈ Part.some (Sum.inl a_final))
      have hx_eq : x = a_final := by
        have hinj := Part.mem_some_iff.mp hstop
        exact Sum.inl.inj hinj
      -- whileStep a' produces Sum.inl a', so x' = a' (from hmem'_inner)
      have hstop' : Sum.inl a' ∈ whileStep condReg body a' := by
        simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_some_iff]
      have hx'_eq : x' = a' := by
        rw [PFun.mem_fix_iff] at hmem'_inner
        cases hmem'_inner with
        | inl h =>
          -- h : Sum.inl x' ∈ whileStep condReg body a'
          simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_some_iff] at h
          exact Sum.inl.inj h
        | inr h =>
          obtain ⟨a'', hcont', _⟩ := h
          -- Contradiction: whileStep a' produces Sum.inl, not Sum.inr
          simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_some_iff] at hcont'
          exact absurd hcont' (by simp)
      rw [hx_eq, hx'_eq]
      exact hagree' r hr
    · -- Contradiction: condition ≠ 0 but hstop says Sum.inl ∈ whileStep
      simp only [Part.mem_map_iff] at hstop
      obtain ⟨_, _, h⟩ := hstop
      exact absurd h (by simp)
  · -- Inductive case: a₀ condReg ≠ 0, body runs, continues to a₁
    simp only [whileStep] at hcont
    split_ifs at hcont with hcond
    · -- Contradiction: condition = 0 but hcont says Sum.inr ∈ whileStep
      simp only [Part.mem_some_iff] at hcont
      exact absurd hcont (by simp)
    · -- a₀ condReg ≠ 0, and Sum.inr a₁ ∈ (evalFlat body a₀).map Sum.inr
      simp only [Part.mem_map_iff] at hcont
      obtain ⟨σ, hσ_mem, hσ_eq⟩ := hcont
      cases hσ_eq  -- σ = a₁
      -- a' condReg ≠ 0 (by agreement)
      have ha'_cond : a' condReg ≠ 0 := by
        rw [← hagree' condReg (Nat.le_max_left _ _)]; exact hcond
      -- a₀ and a' agree on ≤ body.maxRegister
      have hagree_body : ∀ r, r ≤ body.maxRegister → a₀ r = a' r := fun r hr' =>
        hagree' r (Nat.le_trans hr' (Nat.le_max_right _ _))
      -- evalFlat body a' is defined
      have hdom_a₀ : (evalFlat body a₀).Dom := Part.dom_iff_mem.mpr ⟨a₁, hσ_mem⟩
      have hdom_a' : (evalFlat body a').Dom := (evalFlat_dom_agree hagree_body).mp hdom_a₀
      let a'₁ := (evalFlat body a').get hdom_a'
      -- a₁ and a'₁ agree on ≤ max condReg maxRegister (same as in runWhile_dom_of_mem_agree)
      have hagree_result : ∀ r, r ≤ max condReg body.maxRegister → a₁ r = a'₁ r := by
        intro r' hr'
        have ha₁_eq : a₁ = (evalFlat body a₀).get hdom_a₀ :=
          (Part.get_eq_of_mem hσ_mem hdom_a₀).symm
        by_cases hr_body : r' ≤ body.maxRegister
        · rw [ha₁_eq]
          exact evalFlat_result_agree hagree_body hdom_a₀ hdom_a' r' hr_body
        · have hr_gt : body.maxRegister < r' := Nat.lt_of_not_le hr_body
          rw [ha₁_eq]
          rw [evalFlat_preserves_above_maxRegister hdom_a₀ r' hr_gt]
          have ha'₁_eq : a'₁ = (evalFlat body a').get hdom_a' := rfl
          rw [ha'₁_eq, evalFlat_preserves_above_maxRegister hdom_a' r' hr_gt]
          exact hagree' r' hr'
      -- hmem'_inner is from a', we need to extract the continuation from a'₁
      -- First, show that hmem'_inner comes from the continue case
      rw [PFun.mem_fix_iff] at hmem'_inner
      cases hmem'_inner with
      | inl h =>
        -- Contradiction: a' condReg ≠ 0, so whileStep doesn't produce Sum.inl
        simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_map_iff] at h
        obtain ⟨_, _, h'⟩ := h
        exact absurd h' (by simp)
      | inr h =>
        obtain ⟨a'', hcont', hmem''⟩ := h
        -- Show a'' = a'₁
        simp only [whileStep, ha'_cond, ↓reduceIte, Part.mem_map_iff] at hcont'
        obtain ⟨σ', hσ'_mem, hσ'_eq⟩ := hcont'
        -- hσ'_eq : Sum.inr σ' = Sum.inr a''
        have hσ'_eq_a'' : σ' = a'' := Sum.inr.inj hσ'_eq
        have ha''_eq : a'' = a'₁ := by
          rw [← hσ'_eq_a'']
          exact (Part.get_eq_of_mem hσ'_mem hdom_a').symm
        subst ha''_eq
        -- Apply IH
        exact ih a'₁ hagree_result x' hmem'' r hr

/-- Result agreement: runWhile with modified zeroReg agrees on meaningful registers. -/
private theorem runWhile_write_zeroReg_agree (condReg : ℕ) (body : FlatProgram) (s : State) (v : ℕ)
    (hdom : (runWhile (s.write (whileZeroReg condReg body) v) condReg body).Dom)
    (hdom' : (runWhile s condReg body).Dom) (r : ℕ) (hr : r ≤ max condReg body.maxRegister) :
    (runWhile (s.write (whileZeroReg condReg body) v) condReg body).get hdom r =
    (runWhile s condReg body).get hdom' r := by
  -- Get the membership witnesses
  have hmem := Part.get_mem hdom
  have hmem' := Part.get_mem hdom'
  -- States agree on relevant registers
  have hagree : ∀ r, r ≤ max condReg body.maxRegister → (s.write (whileZeroReg condReg body) v) r = s r := by
    intro r' hr'
    have hzero_gt_cond : whileZeroReg condReg body > condReg := whileZeroReg_gt_condReg condReg body
    have hzero_gt_max : whileZeroReg condReg body > body.maxRegister := whileZeroReg_gt_maxRegister condReg body
    have hr_lt : r' < whileZeroReg condReg body := by simp only [whileZeroReg] at *; omega
    have hne : r' ≠ whileZeroReg condReg body := Nat.ne_of_lt hr_lt
    simp only [State.write, Function.update, dif_neg hne]
  exact runWhile_result_of_mem_agree hmem hmem' hagree r hr

/-! NOTE: Full Part State equality (runWhile (s.write zeroReg v) = runWhile s) is FALSE
    because the final states differ at zeroReg (which is preserved through the loop).
    Use runWhile_write_zeroReg_dom for domain equivalence and
    runWhile_write_zeroReg_agree for result agreement on ≤ max condReg maxRegister. -/

/-- Compiled While is semantically equivalent to runWhile on meaningful registers.

Given:
- A host state `s`
- A condition register `condReg`
- A body program `body` in standard form
- The while loop terminates (runWhile s condReg body is defined)

The compiled while loop produces a state that agrees with runWhile on
registers ≤ max condReg body.maxRegister (which includes register 0). -/
theorem compileWhile_correct (condReg : ℕ) (body : FlatProgram)
    (hbody_sf : body.IsStandardForm) (s : State)
    (hdom : (runWhile s condReg body).Dom) :
    ∃ c, Steps (compileWhile condReg body) ⟨0, s⟩ c ∧
         c.isHalted (compileWhile condReg body) ∧
         (∀ r, r ≤ max condReg body.maxRegister → c.state r = (runWhile s condReg body).get hdom r) := by
  -- Phase 1: Execute setup (Z whileZeroReg)
  let zeroReg := whileZeroReg condReg body
  let s' := s.write zeroReg 0
  have hstep_setup : Step (compileWhile condReg body) ⟨0, s⟩ ⟨1, s'⟩ :=
    compileWhile_setup_step condReg body s

  -- The state s' has zeroReg = 0
  have hzero : s' zeroReg = 0 := by simp [s', State.write, Function.update_self]

  -- Domain transfers from s to s' (using the correct weaker lemma)
  have hdom' : (runWhile s' condReg body).Dom :=
    (runWhile_write_zeroReg_dom condReg body s 0).mpr hdom

  -- Phase 2: Apply compileWhile_correct_from_check starting from PC=1
  obtain ⟨c, hsteps_rest, hhalted, hstate⟩ :=
    compileWhile_correct_from_check condReg body hbody_sf s' hzero hdom'

  -- Compose: setup + rest
  have hsteps : Steps (compileWhile condReg body) ⟨0, s⟩ c :=
    Relation.ReflTransGen.head hstep_setup hsteps_rest

  -- Final state agrees with runWhile s on ≤ max condReg maxRegister
  have hstate_agree : ∀ r, r ≤ max condReg body.maxRegister →
      c.state r = (runWhile s condReg body).get hdom r := by
    intro r hr
    -- c.state = (runWhile s' condReg body).get hdom'
    rw [hstate]
    -- (runWhile s' condReg body).get hdom' r = (runWhile s condReg body).get hdom r
    exact runWhile_write_zeroReg_agree condReg body s 0 hdom' hdom r hr

  exact ⟨c, hsteps, hhalted, hstate_agree⟩

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
evalInstr i s.

For Block instructions, the workspace hypothesis ensures that registers beyond
the parameter list but within the body's working range are initialized to 0.
This is trivially true when starting from State.fromInputs. -/
theorem compileInstr_correct' (i : ExtendedInstr) (s : State)
    (hwf : i.WellFormed)
    (hdom : (evalInstr i s).Dom)
    (hworkspace_block : ∀ regs body, i = ExtendedInstr.Block regs body →
        ∀ r, regs.length ≤ r → r ≤ body.maxRegister → s (r + registerBase regs) = 0) :
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
    have hwf_block : regs ≠ [] ∧ body.IsStandardForm := hwf.1
    have hregs : regs ≠ [] := hwf_block.1
    have hbody_sf : body.IsStandardForm := hwf_block.2
    -- Extract the body halting from hdom
    let inputs := List.ofFn (fun i : Fin regs.length => s (regs[i]))
    have hbody_halts : Halts body inputs := by
      simp only [runBlock, Urm.eval] at hdom
      exact hdom
    -- The workspace zero hypothesis is needed for compileBlock_correct
    -- We use the hworkspace_block hypothesis provided by the caller
    have hworkspace : ∀ r, regs.length ≤ r → r ≤ body.maxRegister →
        s (r + registerBase regs) = 0 := hworkspace_block regs body rfl
    -- Apply compileBlock_correct
    obtain ⟨c, hsteps, hhalted, hresult⟩ :=
      compileBlock_correct regs body hbody_sf s hregs hbody_halts hworkspace
    -- Construct the InstrExecResult
    refine ⟨⟨c, hsteps, hhalted⟩, ?_⟩
    -- Show R[0] equality by case split on whether regs[0] = 0
    have h0 : 0 < regs.length := List.length_pos_of_ne_nil hregs
    -- The runBlock result
    have hget_runBlock : (runBlock s regs body).get hdom =
        writeBackResult s regs (Result body inputs hbody_halts) := by
      simp only [runBlock, Urm.eval]
      rw [Part.map_get]
      rfl
    -- What we need to show: c.state 0 = (runBlock s regs body).get hdom 0
    rw [hget_runBlock]
    -- writeBackResult writes to regs[0]
    simp only [writeBackResult]
    cases regs with
    | nil => exact absurd rfl hregs
    | cons r rs =>
      simp only [State.write, List.getElem_cons_zero] at hresult ⊢
      -- c.state r = Result body inputs hbody_halts (from hresult)
      -- Goal: c.state 0 = (if 0 = r then Result ... else s 0)
      by_cases hr0 : r = 0
      · -- Case: r = 0, so regs[0] = 0
        -- Both compiled and eval write result to R[0]
        subst hr0
        simp only [Function.update_self]
        -- hresult says c.state 0 = Result body inputs hbody_halts
        exact hresult
      · -- Case: r ≠ 0, so regs[0] ≠ 0
        -- Neither compiled code nor eval modifies R[0]
        rw [Function.update_of_ne (Ne.symm hr0)]
        -- Need to show c.state 0 = s 0
        -- This follows from compileBlock preserving R[0] when regs[0] ≠ 0
        have hr0' : (r :: rs)[0]'(by simp) ≠ 0 := hr0
        exact compileBlock_preserves_zero (r :: rs) body hbody_sf s (List.cons_ne_nil r rs)
          hbody_halts hworkspace hr0' hsteps hhalted
  | While condReg body =>
    -- Use compileWhile_correct
    simp only [compileInstr, evalInstr] at hdom ⊢
    have hwf_while : body.IsStandardForm := hwf.2
    obtain ⟨c, hsteps, hhalted, hstate_agree⟩ := compileWhile_correct condReg body hwf_while s hdom
    refine ⟨⟨c, hsteps, hhalted⟩, ?_⟩
    -- hstate_agree says c.state agrees with runWhile result on ≤ max condReg maxRegister
    -- 0 ≤ max condReg maxRegister is always true
    exact hstate_agree 0 (Nat.zero_le _)

/-- For basic instructions (Z, S, T), compileInstr produces exactly the evalInstr result. -/
theorem compileInstr_basic_state_eq (i : ExtendedInstr) (s : State)
    (hdom : (evalInstr i s).Dom)
    (hbasic : i.isBasic) :
    ∃ (result : InstrExecResult (compileInstr i) s),
      result.finalConfig.state = (evalInstr i s).get hdom := by
  cases i with
  | Z n =>
    simp only [compileInstr, evalInstr] at hdom ⊢
    -- Z n compiles to [Instr.Z n], runs in one step to state s.write n 0
    have hstep : Step [Instr.Z n] ⟨0, s⟩ ⟨1, s.write n 0⟩ := by
      apply Step.zero; simp [Program.getInstr]
    refine ⟨⟨⟨1, s.write n 0⟩, Steps.single hstep, by simp⟩, ?_⟩
    simp [Part.get_some]
  | S n =>
    simp only [compileInstr, evalInstr] at hdom ⊢
    have hstep : Step [Instr.S n] ⟨0, s⟩ ⟨1, s.write n (s n + 1)⟩ := by
      apply Step.succ; simp [Program.getInstr]
    refine ⟨⟨⟨1, s.write n (s n + 1)⟩, Steps.single hstep, by simp⟩, ?_⟩
    simp [Part.get_some]
  | T m n =>
    simp only [compileInstr, evalInstr] at hdom ⊢
    have hstep : Step [Instr.T m n] ⟨0, s⟩ ⟨1, s.write n (s m)⟩ := by
      apply Step.trans; simp [Program.getInstr]
    refine ⟨⟨⟨1, s.write n (s m)⟩, Steps.single hstep, by simp⟩, ?_⟩
    simp [Part.get_some]
  | J _ _ _ =>
    -- evalInstr for J returns Part.none, so hdom is False
    simp only [evalInstr] at hdom
    exact hdom.elim
  | Block _ _ => simp [ExtendedInstr.isBasic] at hbasic
  | While _ _ => simp [ExtendedInstr.isBasic] at hbasic

/-- Helper: For an extended program, if evalProgram terminates, the compiled program
halts and produces the same final R[0] value. This is the key inductive lemma. -/
theorem compile_correct_aux (p : ExtendedProgram) (s : State)
    (hwf : ExtendedProgram.WellFormed p)
    (hdom : (evalProgram p s).Dom)
    -- Workspace hypothesis: registers beyond what the program uses are 0
    (hworkspace : ∀ i ∈ p, ∀ regs body, i = ExtendedInstr.Block regs body →
        ∀ r, regs.length ≤ r → r ≤ body.maxRegister → s (r + registerBase regs) = 0) :
    ∃ (c : Config), Steps (compile p) ⟨0, s⟩ c ∧ c.isHalted (compile p) ∧
      c.state 0 = ((evalProgram p s).get hdom) 0 := by
  induction p generalizing s with
  | nil =>
    -- Empty program: compile [] = [], halts immediately, R[0] unchanged
    simp only [compile_nil, evalProgram_nil]
    exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, Nat.le_refl 0, by simp [Part.get_some]⟩
  | cons i rest ih =>
    -- compile (i :: rest) = (compileInstr i).concat (compile rest)
    -- evalProgram (i :: rest) s = (evalInstr i s).bind (evalProgram rest)
    rw [compile_cons]
    -- Extract domain info using evalProgram_cons
    have hdom_bind : ((evalInstr i s).bind (evalProgram rest)).Dom := by
      rw [evalProgram_cons] at hdom; exact hdom
    have hdom_i : (evalInstr i s).Dom := Part.Dom.of_bind hdom_bind
    obtain ⟨hdom_i', hdom_rest'⟩ := Part.bind_dom.mp hdom_bind
    -- WellFormedness
    have hwf_instr : ExtendedProgram.InstrWellFormed (i :: rest) := hwf.1
    have hws_safe : ExtendedProgram.WorkspaceSafe (i :: rest) := hwf.2
    have hwf_i : i.WellFormed := hwf_instr i (by simp)
    have hwf_rest : ExtendedProgram.WellFormed rest :=
      ⟨fun j hj => hwf_instr j (List.mem_cons_of_mem i hj), WorkspaceSafe_cons_rest hws_safe⟩
    -- Workspace for instruction i
    have hws_i : ∀ regs body, i = ExtendedInstr.Block regs body →
        ∀ r, regs.length ≤ r → r ≤ body.maxRegister → s (r + registerBase regs) = 0 :=
      hworkspace i (by simp)
    -- Step 1: compileInstr i halts
    obtain ⟨result_i, hr0_i⟩ := compileInstr_correct' i s hwf_i hdom_i hws_i
    -- The intermediate state after running compileInstr i
    let s' := result_i.finalConfig.state
    -- The key inductive step: compile rest halts from s' with correct R[0]
    -- This requires:
    -- 1. s' and (evalInstr i s).get agree on registers read by rest
    -- 2. Workspace hypothesis holds for rest starting from s'
    -- For basic instructions, s' = (evalInstr i s).get exactly (by compileInstr_basic_state_eq)
    -- For Block/While, additional lemmas are needed about state agreement
    by_cases hbasic : i.isBasic
    case pos =>
      -- Basic case: Z, S, T
      -- Get exact state equality from compileInstr_basic_state_eq
      obtain ⟨result_i', hstate_eq⟩ := compileInstr_basic_state_eq i s hdom_i hbasic
      -- The result_i and result_i' have the same final config (same execution)
      -- Since halting is deterministic, they reach the same config
      have hresult_eq : result_i.finalConfig = result_i'.finalConfig := by
        exact Steps.halts_unique result_i.steps result_i.halted result_i'.steps result_i'.halted
      -- So s' = (evalInstr i s).get hdom_i
      have hs'_eq : s' = (evalInstr i s).get hdom_i := by
        simp only [s', hresult_eq, hstate_eq]
      -- The workspace hypothesis for rest holds from s' because:
      -- basic instructions only modify one register, which is not in the workspace range
      have hws_rest : ∀ j ∈ rest, ∀ regs body, j = ExtendedInstr.Block regs body →
          ∀ r, regs.length ≤ r → r ≤ body.maxRegister → s' (r + registerBase regs) = 0 := by
        intro j hj regs body hj_eq r hr_lo hr_hi
        rw [hs'_eq]
        -- The workspace hypothesis from hworkspace applies since j ∈ i::rest
        have hws_j := hworkspace j (List.mem_cons_of_mem i hj) regs body hj_eq r hr_lo hr_hi
        -- Now we need to show (evalInstr i s).get (r + registerBase regs) = s (r + registerBase regs)
        -- For basic instructions, evalInstr only modifies one register
        cases i with
        | Z n =>
          -- Z n sets R[n] = 0, which is fine: either n ≠ workspace reg (use hws_j), or result is 0
          simp only [evalInstr, Part.get_some, State.write]
          by_cases hn : n = r + registerBase regs
          · rw [hn, Function.update_self]
          · rw [Function.update_of_ne (Ne.symm hn)]; exact hws_j
        | S n =>
          -- S n sets R[n] = s n + 1. Need n ≠ workspace reg since S doesn't write to workspace.
          simp only [evalInstr, Part.get_some, State.write]
          have hn : n ≠ r + registerBase regs := by
            intro heq
            -- From workspace safety: S n doesn't write to workspace of rest
            have hws_S := WorkspaceSafe_cons_S hws_safe
            -- heq shows n is in the workspace range of Block j
            have hwsRange : inWorkspaceRange n regs body := ⟨r, hr_lo, hr_hi, heq⟩
            -- Since j ∈ rest and j is a Block with n in its workspace, isWorkspaceOf n rest
            have hIsWs := isWorkspaceOf_of_mem_Block hj hj_eq hwsRange
            -- But WorkspaceSafe says ¬isWorkspaceOf n rest - contradiction
            exact hws_S.1 hIsWs
          rw [Function.update_of_ne (Ne.symm hn)]; exact hws_j
        | T m n =>
          -- T m n sets R[n] = s m. If n ≠ workspace reg, use hws_j.
          simp only [evalInstr, Part.get_some, State.write]
          have hn : n ≠ r + registerBase regs := by
            intro heq
            -- From workspace safety: T m n doesn't write to workspace of rest
            have hws_T := WorkspaceSafe_cons_T hws_safe
            -- heq shows n is in the workspace range of Block j
            have hwsRange : inWorkspaceRange n regs body := ⟨r, hr_lo, hr_hi, heq⟩
            -- Since j ∈ rest and j is a Block with n in its workspace, isWorkspaceOf n rest
            have hIsWs := isWorkspaceOf_of_mem_Block hj hj_eq hwsRange
            -- But WorkspaceSafe says ¬isWorkspaceOf n rest - contradiction
            exact hws_T.1 hIsWs
          rw [Function.update_of_ne (Ne.symm hn)]; exact hws_j
        | J _ _ _ =>
          -- J instructions have evalInstr = Part.none, so hdom_i is False
          simp only [evalInstr] at hdom_i; exact hdom_i.elim
        | Block _ _ =>
          -- Block is not basic, contradicts hbasic
          simp only [ExtendedInstr.isBasic] at hbasic; exact (Bool.false_ne_true hbasic).elim
        | While _ _ =>
          -- While is not basic, contradicts hbasic
          simp only [ExtendedInstr.isBasic] at hbasic; exact (Bool.false_ne_true hbasic).elim
      -- Domain of evalProgram rest from s'
      have hdom_rest_s' : (evalProgram rest s').Dom := by
        rw [hs'_eq]
        convert hdom_rest' using 1
      -- Apply IH
      obtain ⟨c_rest, hsteps_rest, hhalted_rest, hr0_rest⟩ := ih s' hwf_rest hdom_rest_s' hws_rest
      -- Chain the steps: first compileInstr i, then compile rest
      -- compileInstr produces standard form for basic instructions
      have hwf_body : i.bodyIsStandardForm := by
        cases i with
        | Z _ | S _ | T _ _ | J _ _ _ => rfl
        | Block _ _ => simp only [ExtendedInstr.isBasic] at hbasic; exact (Bool.false_ne_true hbasic).elim
        | While _ _ => simp only [ExtendedInstr.isBasic] at hbasic; exact (Bool.false_ne_true hbasic).elim
      have hci_sf : (compileInstr i).IsStandardForm := compileInstr_isStandardForm i hwf_body
      -- PC of result_i equals length of compileInstr i
      have hpc_i : result_i.finalConfig.pc = (compileInstr i).length :=
        hci_sf.pc_eq_length_of_halted result_i.steps (Nat.zero_le _) result_i.halted
      -- Chain the steps
      have hsteps_rest' : Steps (compile rest) ⟨0, result_i.finalConfig.state⟩ c_rest := by
        convert hsteps_rest using 2
      have hchain := Steps.chain_concat result_i.steps result_i.halted hpc_i hsteps_rest' hhalted_rest
      refine ⟨⟨c_rest.pc + (compileInstr i).length, c_rest.state⟩, hchain.1, hchain.2, ?_⟩
      -- R[0] correctness: chain through the evaluation
      -- Goal: c_rest.state 0 = (evalProgram (i :: rest) s).get hdom 0
      -- We have hr0_rest : c_rest.state 0 = (evalProgram rest s').get hdom_rest_s' 0
      -- And hs'_eq : s' = (evalInstr i s).get hdom_i
      rw [hr0_rest]
      -- Now: (evalProgram rest s').get hdom_rest_s' 0 = (evalProgram (i :: rest) s).get hdom 0
      -- Show the Part values are equal, then use Part.get.congr_simp
      have hevalPart : evalProgram rest s' = evalProgram (i :: rest) s := by
        rw [evalProgram_cons, Part.Dom.bind hdom_i', hs'_eq]
      -- Use Part.get.congr_simp: if the Part values are equal, get values are equal
      have hget_eq := Part.get.congr_simp _ _ hevalPart hdom_rest_s'
      exact congrArg (· 0) hget_eq
    case neg =>
      -- Block/While cases require additional infrastructure
      sorry

/-- The full compiler is correct: compiling and running an extended program
produces the same result as the extended evaluation semantics.

Proof strategy:
1. By induction on the extended program p
2. Use compileInstr_correct' for each instruction
3. Connect via Steps lemmas for concatenated programs
4. The workspace hypothesis for Block is satisfied because State.fromInputs
   initializes all registers beyond inputs.length to 0 -/
theorem compile_correct (p : ExtendedProgram) (inputs : List ℕ)
    (hwf : ExtendedProgram.WellFormed p)
    (hdom : (evalFromInputs p inputs).Dom) :
    Halts (compile p) inputs ∧
    ∃ hH, ∀ hD, Result (compile p) inputs hH = (evalFromInputs p inputs).get hD := by
  -- Unfold evalFromInputs to get domain of evalProgram
  have hdom' : (evalProgram p (State.fromInputs inputs)).Dom := by
    simp only [evalFromInputs] at hdom
    exact Part.map_Dom _ _ ▸ hdom
  -- Apply the auxiliary lemma
  have hws : ∀ i ∈ p, ∀ regs body, i = ExtendedInstr.Block regs body →
      ∀ r, regs.length ≤ r → r ≤ body.maxRegister →
      (State.fromInputs inputs) (r + registerBase regs) = 0 := by
    intro i _ regs body _ r hr_lo hr_hi
    -- State.fromInputs initializes registers beyond inputs.length to 0
    -- registerBase regs > max(regs) ≥ 0, so r + registerBase regs ≥ registerBase regs
    -- We need to show this is ≥ inputs.length
    simp only [State.fromInputs, List.getD_eq_getElem?_getD]
    -- The register index r + registerBase regs
    -- registerBase regs ≥ 1 (unless regs is empty), and r ≥ regs.length
    -- This should be enough to show the register is beyond any input
    sorry -- Need to show r + registerBase regs ≥ inputs.length
  obtain ⟨c, hsteps, hhalted, hr0⟩ := compile_correct_aux p (State.fromInputs inputs) hwf hdom' hws
  -- Construct the Halts proof
  have hH : Halts (compile p) inputs := ⟨c, hsteps, hhalted⟩
  constructor
  · exact hH
  · use hH
    intro hD
    -- Result extracts R[0] = c.state 0 = (evalProgram ...).get 0 = evalFromInputs result
    simp only [Result, State.output]
    have hc_unique := Steps.halts_unique hsteps hhalted
      (Classical.choose_spec hH).1 (Classical.choose_spec hH).2
    rw [← hc_unique, hr0]
    -- evalFromInputs = (evalProgram ...).map State.output, and Part.map_get unfolds it
    simp only [evalFromInputs, Part.map_get]
    -- State.output s = s 0
    rfl

/-! ## Standard Form (Deferred) -/

/-- The compiled extended program is in standard form.

Proof strategy:
1. Show compileInstr produces standard form for each instruction type
2. Show concatenation of standard form programs is standard form
   (this requires that the last instruction of each compileInstr result
   is a valid halting point or is followed by more instructions)
Note: This may require using standardization post-processing. -/
theorem compile_isStandardForm' (p : ExtendedProgram)
    (hwf : ExtendedProgram.WellFormed p) :
    (compile p).IsStandardForm := by
  sorry

end Extended

end Urm
