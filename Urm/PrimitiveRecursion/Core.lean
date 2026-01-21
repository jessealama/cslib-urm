/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.StandardForm
import Mathlib.Computability.Partrec

/-! # Primitive Recursion Core Definitions

This file defines the primitive recursion operator `Pr` for partial functions and
provides basic lemmas about its domain and specification.

## Main definitions

- `Pr`: The primitive recursion operator combining base case f and step function g
- `PrFunction`: Wrapper for stating computability theorems

## Main results

- `Pr_dom_zero`: Domain characterization for y = 0
- `Pr_dom_succ`: Domain characterization for y + 1
- `Pr_zero_spec`: Specification for y = 0 (equals f)
- `Pr_succ_spec`: Specification for y + 1 (equals g applied to previous value)

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Helper functions for input manipulation -/

/-- Extract the first n inputs from a (n+1)-tuple.
    Given inputs : Fin (n+1) → ℕ, returns the first n values. -/
def init_inputs {n : ℕ} (inputs : Fin (n + 1) → ℕ) : Fin n → ℕ :=
  fun i => inputs (Fin.castSucc i)

/-- Extract the last input (recursion depth y) from a (n+1)-tuple. -/
def last_input {n : ℕ} (inputs : Fin (n + 1) → ℕ) : ℕ :=
  inputs (Fin.last n)

/-- Extend n inputs with two additional values (counter k and accumulator acc).
    Used for constructing inputs to g in primitive recursion. -/
def extend_inputs_for_g {n : ℕ} (x : Fin n → ℕ) (k : ℕ) (acc : ℕ) : Fin (n + 2) → ℕ :=
  Fin.snoc (Fin.snoc x k) acc

/-! ## Primitive Recursion Definition -/

/-- The primitive recursion operator.

    Pr f g (x₁, ..., xₙ, y) computes:
    - Pr f g (x, 0) = f(x)
    - Pr f g (x, y+1) = g(x, y, Pr f g (x, y))

    Returns Part.none if f or any intermediate g call diverges. -/
def Pr {n : ℕ} (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ)
    (inputs : Fin (n + 1) → ℕ) : Part ℕ :=
  let x := init_inputs inputs
  let y := last_input inputs
  Nat.rec
    (motive := fun _ => Part ℕ)
    (f x)                                              -- base case: f(x)
    (fun k ih => ih.bind (fun acc => g (extend_inputs_for_g x k acc)))  -- recursive: g(x, k, prev)
    y

/-- The function computed by Pr, for stating computability theorems. -/
def PrFunction {n : ℕ} (f : (Fin n → ℕ) → Part ℕ) (g : (Fin (n + 2) → ℕ) → Part ℕ) :
    (Fin (n + 1) → ℕ) → Part ℕ :=
  Pr f g

/-! ## Helper lemmas for input manipulation -/

@[simp] theorem init_inputs_apply {n : ℕ} (inputs : Fin (n + 1) → ℕ) (i : Fin n) :
    init_inputs inputs i = inputs (Fin.castSucc i) := rfl

@[simp] theorem last_input_apply {n : ℕ} (inputs : Fin (n + 1) → ℕ) :
    last_input inputs = inputs (Fin.last n) := rfl

theorem extend_inputs_for_g_castSucc_castSucc {n : ℕ} (x : Fin n → ℕ) (k acc : ℕ) (i : Fin n) :
    extend_inputs_for_g x k acc (Fin.castSucc (Fin.castSucc i)) = x i := by
  simp only [extend_inputs_for_g, Fin.snoc_castSucc, Fin.snoc_castSucc]

theorem extend_inputs_for_g_castSucc_last {n : ℕ} (x : Fin n → ℕ) (k acc : ℕ) :
    extend_inputs_for_g x k acc (Fin.castSucc (Fin.last n)) = k := by
  simp only [extend_inputs_for_g, Fin.snoc_castSucc, Fin.snoc_last]

theorem extend_inputs_for_g_last {n : ℕ} (x : Fin n → ℕ) (k acc : ℕ) :
    extend_inputs_for_g x k acc (Fin.last (n + 1)) = acc := by
  simp only [extend_inputs_for_g, Fin.snoc_last]

theorem init_inputs_snoc {n : ℕ} (x : Fin n → ℕ) (y : ℕ) :
    init_inputs (Fin.snoc x y) = x := by
  ext i
  simp only [init_inputs_apply, Fin.snoc_castSucc]

theorem last_input_snoc {n : ℕ} (x : Fin n → ℕ) (y : ℕ) :
    last_input (Fin.snoc x y) = y := by
  simp only [last_input_apply, Fin.snoc_last]

/-! ## Unfolding lemmas for Pr -/

/-- Alternative form: construct inputs with explicit y = 0. -/
theorem Pr_snoc_zero {n : ℕ} {f : (Fin n → ℕ) → Part ℕ} {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (x : Fin n → ℕ) :
    Pr f g (Fin.snoc x 0) = f x := by
  simp only [Pr, last_input_snoc, init_inputs_snoc, Nat.rec_zero]

/-- Alternative form: construct inputs with explicit y + 1. -/
theorem Pr_snoc_succ {n : ℕ} {f : (Fin n → ℕ) → Part ℕ} {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (x : Fin n → ℕ) (y : ℕ) :
    Pr f g (Fin.snoc x (y + 1)) = (Pr f g (Fin.snoc x y)).bind
      (fun acc => g (extend_inputs_for_g x y acc)) := by
  simp only [Pr, last_input_snoc, init_inputs_snoc]

/-! ## Domain Characterization -/

/-- Pr is defined at y = 0 iff f is defined on the initial inputs. -/
theorem Pr_dom_zero {n : ℕ} {f : (Fin n → ℕ) → Part ℕ} {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (x : Fin n → ℕ) :
    (Pr f g (Fin.snoc x 0)).Dom ↔ (f x).Dom := by
  rw [Pr_snoc_zero]

/-- Pr is defined at y + 1 iff Pr is defined at y AND g is defined on (x, y, Pr(x, y)). -/
theorem Pr_dom_succ {n : ℕ} {f : (Fin n → ℕ) → Part ℕ} {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (x : Fin n → ℕ) (y : ℕ) :
    (Pr f g (Fin.snoc x (y + 1))).Dom ↔
      (Pr f g (Fin.snoc x y)).Dom ∧
      ∀ h : (Pr f g (Fin.snoc x y)).Dom,
        (g (extend_inputs_for_g x y ((Pr f g (Fin.snoc x y)).get h))).Dom := by
  rw [Pr_snoc_succ, Part.bind_dom]
  constructor
  · intro ⟨hPr, hg⟩
    refine ⟨hPr, fun h => ?_⟩
    have : (Pr f g (Fin.snoc x y)).get hPr = (Pr f g (Fin.snoc x y)).get h := by
      congr 1
    rw [← this]
    exact hg
  · intro ⟨hPr, hg⟩
    exact ⟨hPr, hg hPr⟩

/-- Full domain characterization: Pr(x, y) is defined iff
    f(x) is defined AND g is defined at each intermediate step. -/
theorem Pr_dom_iff {n : ℕ} {f : (Fin n → ℕ) → Part ℕ} {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (x : Fin n → ℕ) (y : ℕ) :
    (Pr f g (Fin.snoc x y)).Dom ↔
      (f x).Dom ∧ ∀ k < y, ∀ h : (Pr f g (Fin.snoc x k)).Dom,
        (g (extend_inputs_for_g x k ((Pr f g (Fin.snoc x k)).get h))).Dom := by
  induction y with
  | zero =>
    rw [Pr_dom_zero]
    simp only [Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, and_true]
  | succ y ih =>
    rw [Pr_dom_succ]
    constructor
    · intro ⟨hPr, hg⟩
      rw [ih] at hPr
      obtain ⟨hf, hg_prev⟩ := hPr
      refine ⟨hf, fun k hk h => ?_⟩
      by_cases hky : k < y
      · exact hg_prev k hky h
      · have hkeq : k = y := Nat.eq_of_lt_succ_of_not_lt hk hky
        subst hkeq
        exact hg h
    · intro ⟨hf, hg_all⟩
      constructor
      · rw [ih]
        exact ⟨hf, fun k hk h => hg_all k (Nat.lt_succ_of_lt hk) h⟩
      · intro h
        exact hg_all y (Nat.lt_succ_self y) h

/-! ## Specification -/

/-- At y = 0, Pr returns f(x). -/
theorem Pr_zero_spec {n : ℕ} {f : (Fin n → ℕ) → Part ℕ} {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (x : Fin n → ℕ) (h : (Pr f g (Fin.snoc x 0)).Dom) :
    (Pr f g (Fin.snoc x 0)).get h = (f x).get (Pr_dom_zero x |>.mp h) := by
  simp only [Pr_snoc_zero]

/-- At y + 1, Pr returns g(x, y, Pr(x, y)). -/
theorem Pr_succ_spec {n : ℕ} {f : (Fin n → ℕ) → Part ℕ} {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (x : Fin n → ℕ) (y : ℕ) (h : (Pr f g (Fin.snoc x (y + 1))).Dom) :
    let hPr := (Pr_dom_succ x y).mp h |>.1
    let prev := (Pr f g (Fin.snoc x y)).get hPr
    let hg := (Pr_dom_succ x y).mp h |>.2 hPr
    (Pr f g (Fin.snoc x (y + 1))).get h = (g (extend_inputs_for_g x y prev)).get hg := by
  simp only [Pr_snoc_succ]
  rfl

/-- Domain at k implies domain at all j ≤ k. -/
theorem Pr_dom_of_dom_le {n : ℕ} {f : (Fin n → ℕ) → Part ℕ} {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (x : Fin n → ℕ) {k : ℕ} (h : (Pr f g (Fin.snoc x k)).Dom) {j : ℕ} (hj : j ≤ k) :
    (Pr f g (Fin.snoc x j)).Dom := by
  rw [Pr_dom_iff] at h ⊢
  obtain ⟨hf, hg⟩ := h
  refine ⟨hf, fun i hi h' => hg i (Nat.lt_of_lt_of_le hi hj) h'⟩

end Urm
