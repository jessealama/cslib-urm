/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Simulate.Encoding
import Urm.Execution
import Urm.Shift



/-! # Encoded Step Function

This file defines the URM step function operating on encoded configurations and proves
its correctness with respect to the abstract `Step` relation.

## Main definitions

- `nthEncoded`: Extract the r-th element from an encoded list
- `updateNthEncoded`: Update the r-th element in an encoded list
- `encodedStep`: Single step on encoded configuration
- `encodedIsHalted`: Check if encoded configuration is halted

## Main results

- `encodedStep_correct`: `encodedStep` correctly simulates `Step`
- `encodedStep_not_halted`: If `Step` exists, configuration is not halted

The primitive recursiveness proofs for these functions are in `StepPrimrec.lean`.
-/

namespace Urm

open Nat (pair unpair)

/-! ## Encoded Register Operations

For a fixed bound k, reading register r (where r ≤ k) from an encoded
register list involves a fixed number of `unpair` operations.
-/

/-- Extract the r-th element from an encoded list of k elements.
    This involves r applications of unpair.2, then one unpair.1. -/
def nthEncoded (r : ℕ) (encoded : ℕ) : ℕ :=
  match r with
  | 0 => encoded.unpair.1
  | r + 1 => nthEncoded r encoded.unpair.2

@[simp]
theorem nthEncoded_zero (n : ℕ) : nthEncoded 0 n = n.unpair.1 := rfl

@[simp]
theorem nthEncoded_succ (r n : ℕ) : nthEncoded (r + 1) n = nthEncoded r n.unpair.2 := rfl

/-- Helper: getD of decodeRegs equals nthEncoded. -/
private theorem decodeRegs_getD_eq_nthEncoded (k n r : ℕ) (hr : r < k) :
    (decodeRegs k n).getD r 0 = nthEncoded r n := by
  induction r generalizing k n with
  | zero =>
    cases k with
    | zero => omega
    | succ k' =>
      simp only [decodeRegs_succ, nthEncoded_zero, List.getD_eq_getElem?_getD,
                 List.getElem?_cons_zero, Option.getD_some]
  | succ r' ih =>
    cases k with
    | zero => omega
    | succ k' =>
      simp only [decodeRegs_succ, nthEncoded_succ, List.getD_eq_getElem?_getD,
                 List.getElem?_cons_succ]
      rw [← List.getD_eq_getElem?_getD]
      have hr' : r' < k' := by omega
      exact ih k' n.unpair.2 hr'

/-- Reading encoded register r from regCode equals nthEncoded r regCode. -/
theorem readEncodedReg_eq_nthEncoded (bound : ℕ) (configCode : ℕ) (r : ℕ) (hr : r ≤ bound) :
    readEncodedReg bound configCode r = nthEncoded r configCode.unpair.2 := by
  simp only [readEncodedReg]
  exact decodeRegs_getD_eq_nthEncoded (bound + 1) configCode.unpair.2 r (Nat.lt_succ_of_le hr)

/-! ## Encoded Register Update

Updating register r in an encoded list involves:
1. Extract the first r values
2. Skip the old r-th value
3. Insert the new value
4. Re-encode
-/

/-- Update the r-th element in an encoded list.
    Returns pair(new0, pair(new1, ...)) with the r-th position updated. -/
def updateNthEncoded (r : ℕ) (encoded : ℕ) (newVal : ℕ) : ℕ :=
  match r with
  | 0 => pair newVal encoded.unpair.2
  | r + 1 => pair encoded.unpair.1 (updateNthEncoded r encoded.unpair.2 newVal)

@[simp]
theorem updateNthEncoded_zero (n v : ℕ) :
    updateNthEncoded 0 n v = pair v n.unpair.2 := rfl

@[simp]
theorem updateNthEncoded_succ (r n v : ℕ) :
    updateNthEncoded (r + 1) n v = pair n.unpair.1 (updateNthEncoded r n.unpair.2 v) := rfl

/-! ## Encoded Step Function -/

/-- Execute a single step on an encoded configuration for a fixed program.

    Parameters:
    - `progCode`: encoded program (fixed for primrec)
    - `bound`: register bound (fixed for primrec)
    - `configCode`: encoded (pc, registers)

    Returns the encoded next configuration, or the same config if halted.
-/
def encodedStep (progCode bound configCode : ℕ) : ℕ :=
  let pc := configCode.unpair.1
  let regsCode := configCode.unpair.2
  let progLen := progCode.unpair.1
  if pc < progLen then
    -- Not halted, execute instruction
    let instrCode := nthEncoded pc progCode.unpair.2
    let tag := instrCode.unpair.1
    let args := instrCode.unpair.2
    -- Use if-then-else instead of match for easier primrec proofs
    if tag = 0 then -- Z n: set register n to 0
      let n := args
      if n ≤ bound then
        pair (pc + 1) (updateNthEncoded n regsCode 0)
      else
        pair (pc + 1) regsCode  -- Register out of bounds, no-op on encoded state
    else if tag = 1 then -- S n: increment register n
      let n := args
      if n ≤ bound then
        let oldVal := nthEncoded n regsCode
        pair (pc + 1) (updateNthEncoded n regsCode (oldVal + 1))
      else
        pair (pc + 1) regsCode
    else if tag = 2 then -- T m n: copy register m to register n
      let m := args.unpair.1
      let n := args.unpair.2
      if n ≤ bound then
        let srcVal := if m ≤ bound then nthEncoded m regsCode else 0
        pair (pc + 1) (updateNthEncoded n regsCode srcVal)
      else
        pair (pc + 1) regsCode
    else if tag = 3 then -- J m n q: conditional jump
      let m := args.unpair.1
      let nReg := args.unpair.2.unpair.1
      let q := args.unpair.2.unpair.2
      let mVal := if m ≤ bound then nthEncoded m regsCode else 0
      let nVal := if nReg ≤ bound then nthEncoded nReg regsCode else 0
      if mVal = nVal then
        pair q regsCode
      else
        pair (pc + 1) regsCode
    else
      pair (pc + 1) regsCode  -- Invalid instruction tag
  else
    configCode  -- Halted, return unchanged

/-- Check if an encoded configuration is halted (pc ≥ program length). -/
def encodedIsHalted (progCode configCode : ℕ) : Bool :=
  progCode.unpair.1 ≤ configCode.unpair.1

/-- The halting check as a function to ℕ (1 if halted, 0 if not). -/
def encodedIsHaltedNat (progCode configCode : ℕ) : ℕ :=
  if encodedIsHalted progCode configCode then 1 else 0

/-! ## Helper Lemmas for Correctness -/

/-- nthEncoded on encoded config registers equals state read (for r ≤ bound). -/
theorem nthEncoded_encodeConfig_regs (bound : ℕ) (c : Config) (r : ℕ) (hr : r ≤ bound) :
    nthEncoded r (encodeConfig bound c).unpair.2 = c.state r := by
  have h1 := readEncodedReg_eq_nthEncoded bound (encodeConfig bound c) r hr
  have h2 := readEncodedReg_encodeConfig bound c r hr
  rw [← h2, h1]

/-- Helper: nthEncoded on encodeRegs gives the element at that position. -/
theorem nthEncoded_encodeRegs (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    nthEncoded i (encodeRegs l) = l[i] := by
  induction i generalizing l with
  | zero =>
    match l with
    | [] => simp at hi
    | hd :: tl => simp [encodeRegs_cons, nthEncoded_zero]
  | succ i' ih =>
    match l with
    | [] => simp at hi
    | hd :: tl =>
      simp only [encodeRegs_cons, nthEncoded_succ, Nat.unpair_pair,
                 List.length_cons, Nat.succ_lt_succ_iff, List.getElem_cons_succ] at hi ⊢
      exact ih tl hi

/-- nthEncoded on encoded program instructions gives the encoded instruction. -/
theorem nthEncoded_encodeRegs_map_encodeInstr (p : Program) (pc : ℕ) (hpc : pc < p.length) :
    nthEncoded pc (encodeRegs (p.map encodeInstr)) = encodeInstr p[pc] := by
  have hlen : pc < (p.map encodeInstr).length := by simp; exact hpc
  rw [nthEncoded_encodeRegs _ pc hlen, List.getElem_map]

/-- Helper: updateNthEncoded on encodeRegs gives encodeRegs of the updated list. -/
private theorem updateNthEncoded_encodeRegs (l : List ℕ) (i v : ℕ) (hi : i < l.length) :
    updateNthEncoded i (encodeRegs l) v = encodeRegs (l.set i v) := by
  induction i generalizing l with
  | zero =>
    match l with
    | [] => simp at hi
    | hd :: tl =>
      simp only [encodeRegs_cons, updateNthEncoded_zero, Nat.unpair_pair,
                 List.set_cons_zero]
  | succ i' ih =>
    match l with
    | [] => simp at hi
    | hd :: tl =>
      simp only [encodeRegs_cons, updateNthEncoded_succ, Nat.unpair_pair,
                 List.length_cons, Nat.succ_lt_succ_iff, List.set_cons_succ] at hi ⊢
      congr 1
      exact ih tl hi

/-! ## Correctness Lemmas -/

private theorem ofFn_set_eq_ofFn_write (bound : ℕ) (c : Config) (r v : ℕ) :
    (List.ofFn (fun i : Fin (bound + 1) => c.state i)).set r v =
    List.ofFn (fun i : Fin (bound + 1) => (c.state.write r v) i) := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.length_ofFn] at hi1 hi2
    simp only [List.getElem_set, List.getElem_ofFn]
    split_ifs with heq
    · subst heq; simp [State.write, Function.update]
    · simp only [State.write, Function.update]
      split_ifs with heq2
      · exact absurd heq2.symm heq
      · rfl

private theorem encodedStep_correct_zero (p : Program) (c : Config) (n : ℕ)
    (hpc : c.pc < p.length) (hinstr : p[c.pc] = Instr.Z n) :
    let bound := p.maxRegister
    let progCode := encodeProgram p
    let configCode := encodeConfig bound c
    encodedStep progCode bound configCode = encodeConfig bound ⟨c.pc + 1, c.state.write n 0⟩ := by
  simp only [encodedStep, encodeProgram, encodeConfig, Nat.unpair_pair, hpc, ↓reduceIte]
  rw [nthEncoded_encodeRegs_map_encodeInstr p c.pc hpc]
  simp only [hinstr, encodeInstr, Nat.unpair_pair]
  have hn : n ≤ p.maxRegister := by
    have hinstr' : p[c.pc]? = some (Instr.Z n) := by
      simp only [List.getElem?_eq_getElem hpc, hinstr]
    have h := Program.getElem?_maxRegister p hinstr'
    simp only [Instr.maxRegister] at h
    exact h
  simp only [hn, ↓reduceIte]
  rw [updateNthEncoded_encodeRegs _ _ _ (by simp; omega)]
  congr 1
  exact congrArg _ (ofFn_set_eq_ofFn_write p.maxRegister c n 0)

private theorem ofFn_getElem (bound : ℕ) (c : Config) (i : ℕ) (hi : i < bound + 1) :
    (List.ofFn (fun j : Fin (bound + 1) => c.state j))[i]'(by simp; exact hi) = c.state i :=
  List.getElem_ofFn ..

private theorem encodedStep_correct_succ (p : Program) (c : Config) (n : ℕ)
    (hpc : c.pc < p.length) (hinstr : p[c.pc] = Instr.S n) :
    let bound := p.maxRegister
    let progCode := encodeProgram p
    let configCode := encodeConfig bound c
    encodedStep progCode bound configCode =
      encodeConfig bound ⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩ := by
  simp only [encodedStep, encodeProgram, encodeConfig, Nat.unpair_pair, hpc, ↓reduceIte]
  rw [nthEncoded_encodeRegs_map_encodeInstr p c.pc hpc]
  simp only [hinstr, encodeInstr, Nat.unpair_pair]
  simp only [show (1 : ℕ) = 0 ↔ False from ⟨Nat.one_ne_zero, False.elim⟩, ↓reduceIte]
  have hn : n ≤ p.maxRegister := by
    have hinstr' : p[c.pc]? = some (Instr.S n) := by
      simp only [List.getElem?_eq_getElem hpc, hinstr]
    have h := Program.getElem?_maxRegister p hinstr'
    simp only [Instr.maxRegister] at h
    exact h
  simp only [hn, ↓reduceIte]
  rw [nthEncoded_encodeRegs _ n (by simp; omega)]
  rw [updateNthEncoded_encodeRegs _ _ _ (by simp; omega)]
  congr 1
  have heq1 : (List.ofFn (fun j : Fin (p.maxRegister + 1) => c.state j))[n]'(by simp; omega) =
      c.state n := ofFn_getElem p.maxRegister c n (by omega)
  rw [heq1]
  simp only [State.read]
  exact congrArg _ (ofFn_set_eq_ofFn_write p.maxRegister c n (c.state n + 1))

private theorem encodedStep_correct_trans (p : Program) (c : Config) (m n : ℕ)
    (hpc : c.pc < p.length) (hinstr : p[c.pc] = Instr.T m n) :
    let bound := p.maxRegister
    let progCode := encodeProgram p
    let configCode := encodeConfig bound c
    encodedStep progCode bound configCode =
      encodeConfig bound ⟨c.pc + 1, c.state.write n (c.state.read m)⟩ := by
  simp only [encodedStep, encodeProgram, encodeConfig, Nat.unpair_pair, hpc, ↓reduceIte]
  rw [nthEncoded_encodeRegs_map_encodeInstr p c.pc hpc]
  simp only [hinstr, encodeInstr, Nat.unpair_pair]
  simp only [show (2 : ℕ) = 0 ↔ False from ⟨by omega, False.elim⟩,
             show (2 : ℕ) = 1 ↔ False from ⟨by omega, False.elim⟩, ↓reduceIte]
  have hmn : max m n ≤ p.maxRegister := by
    have hinstr' : p[c.pc]? = some (Instr.T m n) := by
      simp only [List.getElem?_eq_getElem hpc, hinstr]
    have h := Program.getElem?_maxRegister p hinstr'
    simp only [Instr.maxRegister] at h
    exact h
  have hm : m ≤ p.maxRegister := le_of_max_le_left hmn
  have hn : n ≤ p.maxRegister := le_of_max_le_right hmn
  simp only [hn, hm, ↓reduceIte]
  rw [nthEncoded_encodeRegs _ m (by simp; omega)]
  rw [updateNthEncoded_encodeRegs _ _ _ (by simp; omega)]
  congr 1
  have heq1 : (List.ofFn (fun j : Fin (p.maxRegister + 1) => c.state j))[m]'(by simp; omega) =
      c.state m := ofFn_getElem p.maxRegister c m (by omega)
  rw [heq1]
  simp only [State.read]
  exact congrArg _ (ofFn_set_eq_ofFn_write p.maxRegister c n (c.state m))

private theorem encodedStep_correct_jump_eq (p : Program) (c : Config) (m n q : ℕ)
    (hpc : c.pc < p.length) (hinstr : p[c.pc] = Instr.J m n q)
    (heq : c.state.read m = c.state.read n) :
    let bound := p.maxRegister
    let progCode := encodeProgram p
    let configCode := encodeConfig bound c
    encodedStep progCode bound configCode = encodeConfig bound ⟨q, c.state⟩ := by
  simp only [encodedStep, encodeProgram, encodeConfig, Nat.unpair_pair, hpc, ↓reduceIte]
  rw [nthEncoded_encodeRegs_map_encodeInstr p c.pc hpc]
  simp only [hinstr, encodeInstr, Nat.unpair_pair]
  simp only [show (3 : ℕ) = 0 ↔ False from ⟨by omega, False.elim⟩,
             show (3 : ℕ) = 1 ↔ False from ⟨by omega, False.elim⟩,
             show (3 : ℕ) = 2 ↔ False from ⟨by omega, False.elim⟩, ↓reduceIte]
  have hmn : max m n ≤ p.maxRegister := by
    have hinstr' : p[c.pc]? = some (Instr.J m n q) := by
      simp only [List.getElem?_eq_getElem hpc, hinstr]
    have h := Program.getElem?_maxRegister p hinstr'
    simp only [Instr.maxRegister] at h
    exact h
  have hm : m ≤ p.maxRegister := le_of_max_le_left hmn
  have hn : n ≤ p.maxRegister := le_of_max_le_right hmn
  simp only [hm, hn, ↓reduceIte]
  rw [nthEncoded_encodeRegs _ m (by simp; omega)]
  rw [nthEncoded_encodeRegs _ n (by simp; omega)]
  have heqm : (List.ofFn (fun j : Fin (p.maxRegister + 1) => c.state j))[m]'(by simp; omega) =
      c.state m := ofFn_getElem p.maxRegister c m (by omega)
  have heqn : (List.ofFn (fun j : Fin (p.maxRegister + 1) => c.state j))[n]'(by simp; omega) =
      c.state n := ofFn_getElem p.maxRegister c n (by omega)
  rw [heqm, heqn]
  simp only [State.read] at heq
  simp only [heq, ↓reduceIte]

private theorem encodedStep_correct_jump_ne (p : Program) (c : Config) (m n q : ℕ)
    (hpc : c.pc < p.length) (hinstr : p[c.pc] = Instr.J m n q)
    (hne : c.state.read m ≠ c.state.read n) :
    let bound := p.maxRegister
    let progCode := encodeProgram p
    let configCode := encodeConfig bound c
    encodedStep progCode bound configCode = encodeConfig bound ⟨c.pc + 1, c.state⟩ := by
  simp only [encodedStep, encodeProgram, encodeConfig, Nat.unpair_pair, hpc, ↓reduceIte]
  rw [nthEncoded_encodeRegs_map_encodeInstr p c.pc hpc]
  simp only [hinstr, encodeInstr, Nat.unpair_pair]
  simp only [show (3 : ℕ) = 0 ↔ False from ⟨by omega, False.elim⟩,
             show (3 : ℕ) = 1 ↔ False from ⟨by omega, False.elim⟩,
             show (3 : ℕ) = 2 ↔ False from ⟨by omega, False.elim⟩, ↓reduceIte]
  have hmn : max m n ≤ p.maxRegister := by
    have hinstr' : p[c.pc]? = some (Instr.J m n q) := by
      simp only [List.getElem?_eq_getElem hpc, hinstr]
    have h := Program.getElem?_maxRegister p hinstr'
    simp only [Instr.maxRegister] at h
    exact h
  have hm : m ≤ p.maxRegister := le_of_max_le_left hmn
  have hn : n ≤ p.maxRegister := le_of_max_le_right hmn
  simp only [hm, hn, ↓reduceIte]
  rw [nthEncoded_encodeRegs _ m (by simp; omega)]
  rw [nthEncoded_encodeRegs _ n (by simp; omega)]
  have heqm : (List.ofFn (fun j : Fin (p.maxRegister + 1) => c.state j))[m]'(by simp; omega) =
      c.state m := ofFn_getElem p.maxRegister c m (by omega)
  have heqn : (List.ofFn (fun j : Fin (p.maxRegister + 1) => c.state j))[n]'(by simp; omega) =
      c.state n := ofFn_getElem p.maxRegister c n (by omega)
  rw [heqm, heqn]
  simp only [State.read] at hne
  simp only [hne, ↓reduceIte]

/-- Correctness: if Step p c c', then encodedStep produces the right encoded result. -/
theorem encodedStep_correct (p : Program) (c c' : Config)
    (hstep : Step p c c') :
    let bound := p.maxRegister
    let progCode := encodeProgram p
    let configCode := encodeConfig bound c
    encodedStep progCode bound configCode = encodeConfig bound c' := by
  have hpc := Step.pc_lt_length hstep
  cases hstep with
  | zero hinstr =>
    rename_i n
    simp only [List.getElem?_eq_getElem hpc, Option.some.injEq] at hinstr
    exact encodedStep_correct_zero p c n hpc hinstr
  | succ hinstr =>
    rename_i n
    simp only [List.getElem?_eq_getElem hpc, Option.some.injEq] at hinstr
    exact encodedStep_correct_succ p c n hpc hinstr
  | trans hinstr =>
    rename_i m n
    simp only [List.getElem?_eq_getElem hpc, Option.some.injEq] at hinstr
    exact encodedStep_correct_trans p c m n hpc hinstr
  | jump_eq hinstr heq =>
    rename_i m n q
    simp only [List.getElem?_eq_getElem hpc, Option.some.injEq] at hinstr
    exact encodedStep_correct_jump_eq p c m n q hpc hinstr heq
  | jump_ne hinstr hne =>
    rename_i m n q
    simp only [List.getElem?_eq_getElem hpc, Option.some.injEq] at hinstr
    exact encodedStep_correct_jump_ne p c m n q hpc hinstr hne

/-- If Step exists, configuration is not halted. -/
theorem encodedStep_not_halted (p : Program) (c c' : Config)
    (hstep : Step p c c') :
    let bound := p.maxRegister
    let progCode := encodeProgram p
    let configCode := encodeConfig bound c
    encodedIsHalted progCode configCode = false := by
  simp only [encodedIsHalted, encodeProgram, encodeConfig, Nat.unpair_pair]
  have hpc := Step.pc_lt_length hstep
  simp only [Nat.not_le, decide_eq_false_iff_not]
  omega

end Urm
