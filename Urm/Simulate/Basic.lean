/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Simulate.Encoding
import Urm.Simulate.StepPrimrec
import Urm.Simulate.Simulate

/-! # URM Simulation via Primitive Recursive Functions

This module provides the infrastructure to prove that URM-computable functions
are partial recursive (`Nat.Partrec`), establishing the reverse direction of
the equivalence with Mathlib's computability hierarchy.

## Main Results

- `encode_config`, `decode_config`: Config ↔ ℕ encoding
- `encoded_step_primrec`: Single step is primitive recursive
- `URMComputable1.toPartrec`: Every URM-computable function is partial recursive

## Strategy

1. Encode configurations (pc + bounded registers) as natural numbers
2. Show the step function on encoded configs is `Nat.Primrec`
3. Use μ-recursion (`Nat.rfind`) to find the halting step
4. Extract output from register 0

The key insight is `Steps.read_high_register_eq`: registers above `max_register`
are unchanged, so we only need to encode finitely many registers.
-/
