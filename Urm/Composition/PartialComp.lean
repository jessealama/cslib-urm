/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.RegOps

/-! # Composition of Partial Functions

This file defines composition of partial functions for URMs.

## Main definitions

- `Urm.collectOutputs`: Collect outputs from partial functions into a vector
- `Urm.composePartial`: Composition of partial functions
-/

namespace Urm

/-- Collect outputs from partial functions into a vector.
Returns `Part.some outputs` if all functions are defined, where `outputs i = (g i inputs).get _`.
Returns `Part.none` if any function is undefined. -/
def collectOutputs {m n : ℕ} (g : Fin m → (Fin n → ℕ) → Part ℕ) (inputs : Fin n → ℕ) :
    Part (Fin m → ℕ) :=
  Part.mk
    (∀ i, (g i inputs).Dom)
    (fun h => fun i => (g i inputs).get (h i))

/-- Composition of partial functions: `h(x) = f(g₀(x), ..., gₘ₋₁(x))`.

The composition is defined (has a value) iff:
- All `gᵢ(x)` are defined, and
- `f` is defined on the collected outputs `(g₀(x), ..., gₘ₋₁(x))`

This follows the standard definition of composition for partial functions. -/
def composePartial {m n : ℕ}
    (f : (Fin m → ℕ) → Part ℕ)
    (g : Fin m → (Fin n → ℕ) → Part ℕ) : (Fin n → ℕ) → Part ℕ :=
  fun inputs => (collectOutputs g inputs).bind f

theorem collectOutputs_dom {m n : ℕ}
    {g : Fin m → (Fin n → ℕ) → Part ℕ} {inputs : Fin n → ℕ} :
    (collectOutputs g inputs).Dom ↔ ∀ i, (g i inputs).Dom := by
  simp only [collectOutputs]

theorem collectOutputs_get {m n : ℕ}
    {g : Fin m → (Fin n → ℕ) → Part ℕ} {inputs : Fin n → ℕ}
    (h : (collectOutputs g inputs).Dom) (i : Fin m) :
    (collectOutputs g inputs).get h i = (g i inputs).get (collectOutputs_dom.mp h i) := by
  simp only [collectOutputs]

theorem composePartial_dom {m n : ℕ}
    {f : (Fin m → ℕ) → Part ℕ} {g : Fin m → (Fin n → ℕ) → Part ℕ}
    {inputs : Fin n → ℕ} :
    (composePartial f g inputs).Dom ↔
      (∀ i, (g i inputs).Dom) ∧
      ∃ (hg : ∀ i, (g i inputs).Dom), (f (fun i => (g i inputs).get (hg i))).Dom := by
  simp only [composePartial, Part.bind_dom, collectOutputs_dom]
  constructor
  · intro ⟨hg, hf⟩
    exact ⟨hg, hg, hf⟩
  · intro ⟨hg, _, hf⟩
    exact ⟨hg, hf⟩

end Urm
