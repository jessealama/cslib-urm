/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Mathlib.Data.Part
import Mathlib.Data.Fin.Tuple.Basic

/-! # Part.sequence: Collecting Partial Values into a Partial Tuple

This file defines `Part.sequence`, a combinator that collects a family of partial values
indexed by `Fin n` into a single partial tuple. This is analogous to `sequence` for monads,
specialized to the `Part` monad with `Fin`-indexed families.

## Main definitions

* `Part.sequence`: Given `f : Fin n → Part α`, produces `Part (Fin n → α)` that is defined
  iff all `f i` are defined, and whose value is the tuple of all values.

## Main results

* `Part.sequence_dom`: `(Part.sequence f).Dom ↔ ∀ i, (f i).Dom`
* `Part.sequence_get`: `(Part.sequence f).get hdom i = (f i).get _`
* `Part.sequence_succ`: Unfolding lemma for the successor case

## Potential Mathlib Contribution

This module contains general-purpose combinators for the `Part` monad that may be suitable
for contribution to Mathlib. The `Part.sequence` function fills a gap in `Mathlib.Data.Part`:
there is currently no standard way to collect multiple partial values into a partial tuple.

A natural generalization would be to define this for arbitrary `Traversable` functors,
but the `Fin`-indexed version is directly useful for computability theory where functions
of multiple arguments are represented as `Fin n → α`.

## References

* This combinator arises naturally in the formalization of composition for
  Unlimited Register Machines (URMs), where computing `f(g₁(x), ..., gₘ(x))` requires
  collecting the partial results of all `gᵢ` before applying `f`.
-/

namespace Part

variable {α : Type*}

/-- Collect a `Fin`-indexed family of partial values into a partial tuple.

Given `f : Fin n → Part α`, returns `Part (Fin n → α)` which is defined exactly when
all components are defined. This is the `Part` monad's analogue of `sequence` for
`Fin`-indexed families.

Examples:
* `Part.sequence (![Part.some 1, Part.some 2]) = Part.some ![1, 2]`
* `Part.sequence (![Part.some 1, Part.none]) = Part.none`
-/
def sequence : {n : ℕ} → (Fin n → Part α) → Part (Fin n → α)
  | 0, _ => Part.some Fin.elim0
  | _ + 1, f => (f 0).bind fun a0 =>
      (sequence (fun i => f i.succ)).map fun rest => Fin.cons a0 rest

/-- Unfolding lemma for `Part.sequence` at successor indices. -/
theorem sequence_succ {n : ℕ} (f : Fin (n + 1) → Part α) :
    sequence f = (f 0).bind fun a0 =>
      (sequence (fun i => f i.succ)).map fun rest => Fin.cons a0 rest := rfl

/-- The sequence is defined iff all components are defined. -/
theorem sequence_dom {n : ℕ} {f : Fin n → Part α} :
    (sequence f).Dom ↔ ∀ i, (f i).Dom := by
  induction n with
  | zero =>
    simp only [sequence, Part.some_dom]
    exact ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | succ n ih =>
    simp only [sequence, Part.bind_dom, Part.map_Dom]
    constructor
    · intro ⟨hdom0, hrest⟩ i
      match i with
      | ⟨0, _⟩ => exact hdom0
      | ⟨j + 1, hlt⟩ => exact ih.mp hrest ⟨j, Nat.lt_of_succ_lt_succ hlt⟩
    · intro hall
      exact ⟨hall 0, ih.mpr (fun i => hall i.succ)⟩

/-- Extracting a component from the sequence equals extracting from the original family. -/
theorem sequence_get {n : ℕ} {f : Fin n → Part α}
    (hdom : (sequence f).Dom) (i : Fin n) :
    (sequence f).get hdom i = (f i).get (sequence_dom.mp hdom i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    match i with
    | ⟨0, _⟩ =>
      simp only [sequence_succ, Part.bind, Part.map] at hdom ⊢
      rfl
    | ⟨j + 1, hlt⟩ =>
      simp only [sequence_succ, Part.bind, Part.map] at hdom ⊢
      exact ih _ ⟨j, Nat.lt_of_succ_lt_succ hlt⟩

end Part
