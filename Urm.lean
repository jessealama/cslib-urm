-- This module serves as the root of the `Urm` library.
-- Import modules here that should be built as part of the library.
import Urm.PartSequence
import Urm.Basic
import Urm.Execution
import Urm.Shift
import Urm.Embeddings
import Urm.Computable
import Urm.Arithmetic
import Urm.Composition.Basic
import Urm.PrimitiveRecursion.Basic
import Urm.Minimization.Basic
import Urm.Partrec
import Urm.Simulate.Basic

/-! # Public API

Core types and main theorems for URM computability.

## Core Types
- `Urm.Instr` - URM instructions (Z, S, T, J)
- `Urm.Program` - Programs as lists of instructions
- `Urm.Config` - Machine configurations (pc + state)
- `Urm.Step` - Single-step execution relation
- `Urm.Steps` - Multi-step execution

## Computability
- `Urm.URMComputable` - n-ary URM-computability
- `Urm.URMComputable1` - Unary version for ℕ →. ℕ

## Main Theorems
- `Urm.URMComputable1.toPartrec` - URM-computable implies Partrec
- `Nat.Partrec.toURMComputable1` - Partrec implies URM-computable
-/

export Urm (Instr Program Config Step Steps)
export Urm (URMComputable URMComputable1)
export Urm (URMComputable1.toPartrec)
-- Note: Nat.Partrec.toURMComputable1 is in Nat namespace, auto-accessible
