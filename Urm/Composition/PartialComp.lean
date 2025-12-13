/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.RegOps
import Mathlib.Data.Fin.Tuple.Basic

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

/-- For m = 0, composition reduces to applying f to the empty tuple.
    Since Fin 0 is empty, collectOutputs is trivially defined. -/
theorem composePartial_zero {n : ℕ} (f : (Fin 0 → ℕ) → Part ℕ)
    (g : Fin 0 → (Fin n → ℕ) → Part ℕ) (inputs : Fin n → ℕ) :
    composePartial f g inputs = f (fun i => Fin.elim0 i) := by
  simp only [composePartial, collectOutputs]
  -- collectOutputs g inputs = Part.some (fun i : Fin 0 => ...) since Fin 0 is empty
  -- So we need: Part.mk (∀ i : Fin 0, ...) (...).bind f = f (fun i => Fin.elim0 i)
  -- The domain ∀ i : Fin 0, ... is vacuously true
  have heq : Part.mk (∀ i : Fin 0, (g i inputs).Dom) (fun h i => (g i inputs).get (h i)) =
             Part.some (fun i : Fin 0 => Fin.elim0 i) := by
    apply Part.ext'
    · simp only [Part.some_dom]
      exact ⟨fun _ => trivial, fun _ i => Fin.elim0 i⟩
    · intro h1 h2
      funext i
      exact Fin.elim0 i
  rw [heq, Part.bind_some]

/-- Helper: Fin.cons reconstructs the original function from g 0 and g ∘ succ -/
private theorem fin_cons_reconstruct {m n : ℕ} (g : Fin (m + 1) → (Fin n → ℕ) → Part ℕ)
    (inputs : Fin n → ℕ) (hall : ∀ i, (g i inputs).Dom) :
    (fun i => (g i inputs).get (hall i)) =
    Fin.cons ((g 0 inputs).get (hall 0)) (fun i => (g (Fin.succ i) inputs).get (hall (Fin.succ i))) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [Fin.cons]
  | succ j => simp [Fin.cons]

/-- Decomposition of composition for m + 1: peel off g 0 first.
    This is the key lemma for the inductive proof of composition closure. -/
theorem composePartial_succ {m n : ℕ} (f : (Fin (m + 1) → ℕ) → Part ℕ)
    (g : Fin (m + 1) → (Fin n → ℕ) → Part ℕ) (inputs : Fin n → ℕ) :
    composePartial f g inputs =
      (g 0 inputs).bind (fun y₀ =>
        composePartial (fun rest => f (Fin.cons y₀ rest))
                       (fun i => g (Fin.succ i)) inputs) := by
  simp only [composePartial, collectOutputs]
  -- Use Part.ext to show equality by showing membership coincides
  ext x
  simp only [Part.mem_bind_iff, Part.mem_mk_iff]
  constructor
  · intro ⟨outputs, ⟨hall, houtputs_eq⟩, hf_x⟩
    -- outputs = (fun i => (g i inputs).get (hall i)), need to show the RHS membership
    refine ⟨outputs 0, ⟨hall 0, ?_⟩, outputs ∘ Fin.succ, ⟨fun i => hall (Fin.succ i), ?_⟩, ?_⟩
    · -- (g 0 inputs).get (hall 0) = outputs 0
      rw [← houtputs_eq]
    · -- (fun i => (g (Fin.succ i) inputs).get ...) = outputs ∘ Fin.succ
      funext i
      rw [← houtputs_eq]
      rfl
    · -- x ∈ f (Fin.cons (outputs 0) (outputs ∘ Fin.succ))
      convert hf_x using 2
      rw [← houtputs_eq]
      funext i
      cases i using Fin.cases with
      | zero => simp [Fin.cons]
      | succ j => simp [Fin.cons]
  · intro ⟨y0, ⟨h0, hy0_eq⟩, rest, ⟨hrest, hrest_eq⟩, hf_x⟩
    -- Construct the full outputs function
    have hall : ∀ i, (g i inputs).Dom := fun i =>
      match i with
      | ⟨0, _⟩ => h0
      | ⟨k+1, hk⟩ => hrest ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    refine ⟨Fin.cons y0 rest, ⟨hall, ?_⟩, ?_⟩
    · -- (fun i => (g i inputs).get (hall i)) = Fin.cons y0 rest
      funext i
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        rw [← hy0_eq]
      | succ j =>
        simp only [Fin.cons_succ]
        rw [← hrest_eq]
    · -- x ∈ f (Fin.cons y0 rest)
      exact hf_x

end Urm
