/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Block.Basic
import Urm.Block.Pseudo
import Urm.Block.Compile
import Urm.Block.Glue
import Urm.Block.Compose
import Urm.Block.Prec

/-! # URMBlock: Structured URM Programming

This module provides a structured approach to URM programming through the
`URMBlock` abstraction, which encapsulates programs with isolated register
namespaces and supports compositional construction.

## Main Components

- `Urm.Block.Basic`: Core `URMBlock` structure and `ComputesN` predicate
- `Urm.Block.Pseudo`: Pseudo-instructions (decrement, add, copy range, etc.)
- `Urm.Block.Compile`: Compilation with register offset preservation
- `Urm.Block.Glue`: Block sequencing lemmas
- `Urm.Block.Compose`: Composition combinator
- `Urm.Block.Prec`: Primitive recursion combinator

Note: Minimization (μ-recursion) is handled via the Extended URM module
(`Urm.Extended`), which provides a cleaner compilation approach.
-/
