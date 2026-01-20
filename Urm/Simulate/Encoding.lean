/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Basic
import Mathlib.Computability.Primrec

/-! # Configuration Encoding for URM Simulation

This file provides encoding and decoding functions for URM configurations,
enabling simulation of URM execution using primitive recursive functions.

## Main definitions

- `encodeRegs`: Encode a list of register values as a natural number
- `decodeRegs`: Decode a natural number to a list of register values
- `encodeConfig`: Encode a configuration (pc, bounded registers) as a natural
- `decodeConfig`: Decode a natural to a configuration
- `encodeInstr`: Encode an instruction as a natural
- `encodeProgram`: Encode a program as a natural

## Strategy

We use Cantor pairing to encode lists and configurations:
- A list [a, b, c] is encoded as pair(a, pair(b, pair(c, 0)))
- A config (pc, regs) is encoded as pair(pc, encodeRegs regs)

The key insight is that we only need to encode registers up to `p.maxRegister`,
since `Steps.preserves_high_register` guarantees higher registers are unchanged.
-/

namespace Urm

open Nat (pair unpair)

/-! ## Register List Encoding -/

/-- Encode a list of natural numbers using iterated Cantor pairing.
    The encoding is: [] ↦ 0, [a] ↦ pair(a, 0), [a, b] ↦ pair(a, pair(b, 0)), etc. -/
def encodeRegs : List ℕ → ℕ
  | [] => 0
  | r :: rs => pair r (encodeRegs rs)

/-- Decode a natural number to a list of k register values.
    Extracts k values using iterated unpair.left/unpair.right. -/
def decodeRegs : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => n.unpair.1 :: decodeRegs k n.unpair.2

@[simp]
theorem encodeRegs_cons (r : ℕ) (rs : List ℕ) :
    encodeRegs (r :: rs) = pair r (encodeRegs rs) := rfl

@[simp]
theorem decodeRegs_succ (k n : ℕ) :
    decodeRegs (k + 1) n = n.unpair.1 :: decodeRegs k n.unpair.2 := rfl

/-- Decoding an encoded list recovers the original list. -/
theorem decodeRegs_encodeRegs (rs : List ℕ) :
    decodeRegs rs.length (encodeRegs rs) = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih]

/-- Length of decoded list equals k. -/
@[simp]
theorem decodeRegs_length (k n : ℕ) : (decodeRegs k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [decodeRegs_succ, List.length_cons, ih]

/-! ## Configuration Encoding -/

/-- Encode a configuration with a given register bound.
    We encode registers 0 through bound (inclusive), giving bound + 1 values. -/
def encodeConfig (bound : ℕ) (c : Config) : ℕ :=
  pair c.pc (encodeRegs (List.ofFn (fun i : Fin (bound + 1) => c.state i)))

/-- Decode a natural to a configuration with a given register bound. -/
def decodeConfig (bound : ℕ) (n : ℕ) : Config :=
  let pc := n.unpair.1
  let regs := decodeRegs (bound + 1) n.unpair.2
  ⟨pc, fun r => regs.getD r 0⟩

/-- Helper lemma: decodeRegs after encodeRegs of ofFn list. -/
private theorem decodeRegs_encodeRegs_ofFn (bound : ℕ) (f : Fin (bound + 1) → ℕ) :
    decodeRegs (bound + 1) (encodeRegs (List.ofFn f)) = List.ofFn f := by
  simpa using decodeRegs_encodeRegs (List.ofFn f)

/-! ## Instruction Encoding -/

/-- Encode an instruction as a natural number.
    - Z n     ↦ pair(0, n)
    - S n     ↦ pair(1, n)
    - T m n   ↦ pair(2, pair(m, n))
    - J m n q ↦ pair(3, pair(m, pair(n, q))) -/
def encodeInstr : Instr → ℕ
  | Instr.Z n => pair 0 n
  | Instr.S n => pair 1 n
  | Instr.T m n => pair 2 (pair m n)
  | Instr.J m n q => pair 3 (pair m (pair n q))

/-- Decode a natural to an instruction.
    Returns default (Z 0) for invalid encodings. -/
def decodeInstr (n : ℕ) : Instr :=
  let tag := n.unpair.1
  let args := n.unpair.2
  match tag with
  | 0 => Instr.Z args
  | 1 => Instr.S args
  | 2 => Instr.T args.unpair.1 args.unpair.2
  | 3 => Instr.J args.unpair.1 args.unpair.2.unpair.1 args.unpair.2.unpair.2
  | _ => Instr.Z 0  -- default for invalid

/-! ## Program Encoding -/

/-- Encode a program (list of instructions) as a natural number.
    Uses length-prefixed encoding: pair(length, encodeRegs(map encodeInstr p)) -/
def encodeProgram (p : Program) : ℕ :=
  pair p.length (encodeRegs (p.map encodeInstr))

/-- Decode a natural to a program. -/
def decodeProgram (n : ℕ) : Program :=
  let len := n.unpair.1
  let encodedInstrs := decodeRegs len n.unpair.2
  encodedInstrs.map decodeInstr

/-- Helper lemma: decodeRegs after encodeRegs of mapped list. -/
private theorem decodeRegs_encodeRegs_map (p : Program) :
    decodeRegs p.length (encodeRegs (p.map encodeInstr)) = p.map encodeInstr := by
  simpa using decodeRegs_encodeRegs (p.map encodeInstr)

/-- Get instruction at position from encoded program. -/
def getEncodedInstr (progCode : ℕ) (pc : ℕ) : Option Instr :=
  let p := decodeProgram progCode
  p[pc]?

/-! ## Helper: Update encoded registers -/

/-- Update a single register in a decoded register list. -/
def updateRegs (k : ℕ) (regCode : ℕ) (r v : ℕ) : ℕ :=
  let regs := decodeRegs k regCode
  encodeRegs (regs.set r v)

/-- Helper lemma: decodeRegs after encodeRegs of set list. -/
private theorem decodeRegs_encodeRegs_set (k : ℕ) (regCode r v : ℕ) :
    decodeRegs k (encodeRegs ((decodeRegs k regCode).set r v)) = (decodeRegs k regCode).set r v := by
  simpa using decodeRegs_encodeRegs ((decodeRegs k regCode).set r v)

/-! ## Encoded Configuration Operations -/

/-- Read a register from an encoded configuration. -/
def readEncodedReg (bound : ℕ) (configCode : ℕ) (r : ℕ) : ℕ :=
  (decodeRegs (bound + 1) configCode.unpair.2).getD r 0

/-- Write a register in an encoded configuration. -/
def writeEncodedReg (bound : ℕ) (configCode : ℕ) (r v : ℕ) : ℕ :=
  let pc := configCode.unpair.1
  let regs := decodeRegs (bound + 1) configCode.unpair.2
  pair pc (encodeRegs (regs.set r v))

/-- Get the PC from an encoded configuration. -/
def getEncodedPC (configCode : ℕ) : ℕ := configCode.unpair.1

/-- Set the PC in an encoded configuration. -/
def setEncodedPC (configCode : ℕ) (newPC : ℕ) : ℕ :=
  pair newPC configCode.unpair.2

theorem readEncodedReg_encodeConfig (bound : ℕ) (c : Config) (r : ℕ) (hr : r ≤ bound) :
    readEncodedReg bound (encodeConfig bound c) r = c.state r := by
  simp only [readEncodedReg, encodeConfig, Nat.unpair_pair]
  rw [decodeRegs_encodeRegs_ofFn]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  have hr' : r < bound + 1 := Nat.lt_succ_of_le hr
  simp only [hr', ↓reduceDIte, Option.getD_some]

end Urm
