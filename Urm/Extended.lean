/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Extended.Basic
import Urm.Extended.Eval
import Urm.Extended.Compile

/-! # Extended URM

This module provides a higher-level intermediate representation for URM programs
with structured control flow constructs (BLOCK and MU).

## Overview

The ExtendedURM IR separates concerns:
- **Semantics**: What does each construct mean? (clean, compositional)
- **Compilation**: How do we translate to base URM? (separate, mechanical)
- **Equivalence**: ExtendedURM ↔ Partrec (easier, maps directly)

## Modules

- `Basic`: Core types (`ExtendedInstr`, `ExtendedProgram`)
- `Eval`: Evaluation semantics (`evalInstr`, `evalProgram`)
- `Compile`: Compilation to base URM (`compile`, `compileInstr`)

## Main Constructs

### BLOCK [r₀, r₁, ...] { body }

Execute `body` with registers mapped through `regs`:
1. Create sub-state: body's R[i] ← host's R[rᵢ]
2. Run body (base URM) until halt
3. Write back: host's R[r₀] ← body's R[0]

### MU [r₀, r₁, ...] { body } resultReg

Execute `body` repeatedly with an incrementing counter until body's R[0] = 0:
- Body's R[0..n-1]: inputs from host's R[r₀, r₁, ...]
- Body's R[n]: counter (starts at 0, incremented each iteration)
- On exit: host's R[r₀] ← body's R[resultReg]

This directly models μ-recursion when resultReg = n (returns counter).

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/
