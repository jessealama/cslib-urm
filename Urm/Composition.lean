/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.CollectLoop

/-! # Composition of URM-Computable Functions

This module re-exports all composition-related definitions and theorems.
The content has been split into smaller files for faster incremental builds.

## Submodules

### Core definitions
- `Urm.Composition.Seq`: Sequential composition (`Program.seq`)
- `Urm.Composition.RegOps`: Register operations (copyReg, copyRegs, zeroReg)
- `Urm.Composition.PartialComp`: Partial function composition definitions

### Shift lemmas
- `Urm.Composition.ShiftLemmas`: Jump and register shifting lemmas

### Execution semantics
- `Urm.Composition.SeqExecution`: Sequential program execution properties

### JumpsBounded predicate and properties
- `Urm.Composition.JumpsBounded.Basic`: JumpsBounded definition
- `Urm.Composition.JumpsBounded.Seq`: Seq composition preserves JumpsBounded
- `Urm.Composition.JumpsBounded.Halting`: Halting at exact length
- `Urm.Composition.JumpsBounded.SeqFirst`: First program halts from seq
- `Urm.Composition.JumpsBounded.SeqSecond`: Second program halts from seq

### Register clearing
- `Urm.Composition.ClearRegs`: clearRegsFrom1, clearRegsRange

### Execution with register operations
- `Urm.Composition.CopyRegsExec`: copyRegs execution lemmas

### State agreement
- `Urm.Composition.StateAgreement`: State agreement and execution transfer
- `Urm.Composition.StateShift`: State shifting/unshifting operations
- `Urm.Composition.PrefixTransfer`: Prefix step transfer

### Composition theorems
- `Urm.Composition.CompUnary`: Unary composition theorem
- `Urm.Composition.CollectLoop`: Collection loop and general composition

## Main statements

- `Urm.URMComputable.comp_unary`: Unary composition closure
- `Urm.URMComputable.comp`: General composition closure (Cutland Theorem 2.1)

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980],
  Chapter 2, Theorem 2.1
-/

-- Re-exports everything through the final module in the chain
