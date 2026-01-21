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

- `encode_regs`: Encode a list of register values as a natural number
- `decode_regs`: Decode a natural number to a list of register values
- `encode_config`: Encode a configuration (pc, bounded registers) as a natural
- `decode_config`: Decode a natural to a configuration
- `encode_instr`: Encode an instruction as a natural
- `encode_program`: Encode a program as a natural

## Strategy

We use Cantor pairing to encode lists and configurations:
- A list [a, b, c] is encoded as pair(a, pair(b, pair(c, 0)))
- A config (pc, regs) is encoded as pair(pc, encode_regs regs)

The key insight is that we only need to encode registers up to `p.max_register`,
since `Steps.read_high_register_eq` guarantees higher registers are unchanged.
-/

namespace Urm

open Nat (pair unpair)

/-! ## Register List Encoding -/

/-- Encode a list of natural numbers using iterated Cantor pairing.
    The encoding is: [] ↦ 0, [a] ↦ pair(a, 0), [a, b] ↦ pair(a, pair(b, 0)), etc. -/
def encode_regs : List ℕ → ℕ
  | [] => 0
  | r :: rs => pair r (encode_regs rs)

/-- Decode a natural number to a list of k register values.
    Extracts k values using iterated unpair.left/unpair.right. -/
def decode_regs : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => n.unpair.1 :: decode_regs k n.unpair.2

@[simp]
theorem encode_regs_cons (r : ℕ) (rs : List ℕ) :
    encode_regs (r :: rs) = pair r (encode_regs rs) := rfl

@[simp]
theorem decode_regs_succ (k n : ℕ) :
    decode_regs (k + 1) n = n.unpair.1 :: decode_regs k n.unpair.2 := rfl

/-- Decoding an encoded list recovers the original list. -/
theorem decode_regs_encode_regs (rs : List ℕ) :
    decode_regs rs.length (encode_regs rs) = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih]

/-- Length of decoded list equals k. -/
@[simp]
theorem decode_regs_length (k n : ℕ) : (decode_regs k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [decode_regs_succ, List.length_cons, ih]

/-! ## Configuration Encoding -/

/-- Encode a configuration with a given register bound.
    We encode registers 0 through bound (inclusive), giving bound + 1 values. -/
def encode_config (bound : ℕ) (c : Config) : ℕ :=
  pair c.pc (encode_regs (List.ofFn (fun i : Fin (bound + 1) => c.state i)))

/-- Decode a natural to a configuration with a given register bound. -/
def decode_config (bound : ℕ) (n : ℕ) : Config :=
  let pc := n.unpair.1
  let regs := decode_regs (bound + 1) n.unpair.2
  ⟨pc, fun r => regs.getD r 0⟩

/-- Helper lemma: decode_regs after encode_regs of ofFn list. -/
private theorem decode_regs_encode_regs_ofFn (bound : ℕ) (f : Fin (bound + 1) → ℕ) :
    decode_regs (bound + 1) (encode_regs (List.ofFn f)) = List.ofFn f := by
  simpa using decode_regs_encode_regs (List.ofFn f)

/-! ## Instruction Encoding -/

/-- Encode an instruction as a natural number.
    - Z n     ↦ pair(0, n)
    - S n     ↦ pair(1, n)
    - T m n   ↦ pair(2, pair(m, n))
    - J m n q ↦ pair(3, pair(m, pair(n, q))) -/
def encode_instr : Instr → ℕ
  | Instr.Z n => pair 0 n
  | Instr.S n => pair 1 n
  | Instr.T m n => pair 2 (pair m n)
  | Instr.J m n q => pair 3 (pair m (pair n q))

/-- Decode a natural to an instruction.
    Returns default (Z 0) for invalid encodings. -/
def decode_instr (n : ℕ) : Instr :=
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
    Uses length-prefixed encoding: pair(length, encode_regs(map encode_instr p)) -/
def encode_program (p : Program) : ℕ :=
  pair p.length (encode_regs (p.map encode_instr))

/-- Decode a natural to a program. -/
def decode_program (n : ℕ) : Program :=
  let len := n.unpair.1
  let encodedInstrs := decode_regs len n.unpair.2
  encodedInstrs.map decode_instr

/-- Helper lemma: decode_regs after encode_regs of mapped list. -/
private theorem decode_regs_encode_regs_map (p : Program) :
    decode_regs p.length (encode_regs (p.map encode_instr)) = p.map encode_instr :=
  List.length_map .. ▸ decode_regs_encode_regs (p.map encode_instr)

/-- Get instruction at position from encoded program. -/
def get_encoded_instr (progCode : ℕ) (pc : ℕ) : Option Instr :=
  let p := decode_program progCode
  p[pc]?

/-! ## Helper: Update encoded registers -/

/-- Update a single register in a decoded register list. -/
def update_regs (k : ℕ) (regCode : ℕ) (r v : ℕ) : ℕ :=
  let regs := decode_regs k regCode
  encode_regs (regs.set r v)

/-- Helper lemma: decode_regs after encode_regs of set list. -/
private theorem decode_regs_encode_regs_set (k : ℕ) (regCode r v : ℕ) :
    decode_regs k (encode_regs ((decode_regs k regCode).set r v)) = (decode_regs k regCode).set r v := by
  simpa using decode_regs_encode_regs ((decode_regs k regCode).set r v)

/-! ## Encoded Configuration Operations -/

/-- Read a register from an encoded configuration. -/
def read_encoded_reg (bound : ℕ) (configCode : ℕ) (r : ℕ) : ℕ :=
  (decode_regs (bound + 1) configCode.unpair.2).getD r 0

/-- Write a register in an encoded configuration. -/
def write_encoded_reg (bound : ℕ) (configCode : ℕ) (r v : ℕ) : ℕ :=
  let pc := configCode.unpair.1
  let regs := decode_regs (bound + 1) configCode.unpair.2
  pair pc (encode_regs (regs.set r v))

/-- Get the PC from an encoded configuration. -/
def get_encoded_pc (configCode : ℕ) : ℕ := configCode.unpair.1

/-- Set the PC in an encoded configuration. -/
def set_encoded_pc (configCode : ℕ) (newPC : ℕ) : ℕ :=
  pair newPC configCode.unpair.2

theorem read_encoded_reg_encode_config (bound : ℕ) (c : Config) (r : ℕ) (hr : r ≤ bound) :
    read_encoded_reg bound (encode_config bound c) r = c.state r := by
  simp only [read_encoded_reg, encode_config, Nat.unpair_pair]
  rw [decode_regs_encode_regs_ofFn]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  have hr' : r < bound + 1 := Nat.lt_succ_of_le hr
  simp only [hr', ↓reduceDIte, Option.getD_some]

end Urm
