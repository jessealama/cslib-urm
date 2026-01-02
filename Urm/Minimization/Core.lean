/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.StandardForm
import Mathlib.Computability.Partrec

/-! # Minimization Core Definitions

This file defines the μ (minimization) operator for partial functions and
provides basic lemmas about its domain and specification.

## Main definitions

- `μ`: The minimization operator - finds the least y such that f(inputs, y) = 0

## Main results

- `μ_dom_iff`: Characterization of when μ is defined
- `μ_spec`: The result of μ satisfies f(inputs, y) = 0
- `μ_min`: The result of μ is minimal

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-- Extend inputs with an additional argument y at the end.
    Given inputs : Fin n → ℕ and y : ℕ, produces (inputs, y) : Fin (n+1) → ℕ -/
def extendInputs {n : ℕ} (inputs : Fin n → ℕ) (y : ℕ) : Fin (n + 1) → ℕ :=
  Fin.snoc inputs y

/-- The predicate that checks if f returns 0, as a partial Bool. -/
def checkZero {n : ℕ} (f : (Fin (n + 1) → ℕ) → Part ℕ) (inputs : Fin n → ℕ) (y : ℕ) : Part Bool :=
  Part.map (· = 0) (f (extendInputs inputs y))

/-- The μ (minimization) operator.
    μ f inputs = least y such that f(inputs, y) = 0.
    Returns Part.none if no such y exists or if f diverges on some y' < y. -/
def μ {n : ℕ} (f : (Fin (n + 1) → ℕ) → Part ℕ) (inputs : Fin n → ℕ) : Part ℕ :=
  Nat.rfind (checkZero f inputs)

/-- The function computed by μ, for stating computability theorems. -/
def μFunction {n : ℕ} (f : (Fin (n + 1) → ℕ) → Part ℕ) : (Fin n → ℕ) → Part ℕ :=
  μ f

/-! ## Helper lemmas for checkZero -/

theorem checkZero_true_iff {n : ℕ} {f : (Fin (n + 1) → ℕ) → Part ℕ} {inputs : Fin n → ℕ} {y : ℕ} :
    true ∈ checkZero f inputs y ↔ 0 ∈ f (extendInputs inputs y) := by
  simp only [checkZero, Part.mem_map_iff, eq_comm, true_eq_decide_iff]
  constructor
  · intro ⟨v, hv, hv0⟩; subst hv0; exact hv
  · intro h; exact ⟨0, h, rfl⟩

theorem checkZero_false_iff {n : ℕ} {f : (Fin (n + 1) → ℕ) → Part ℕ} {inputs : Fin n → ℕ} {y : ℕ} :
    false ∈ checkZero f inputs y ↔ ∃ v ≠ 0, v ∈ f (extendInputs inputs y) := by
  simp only [checkZero, Part.mem_map_iff, eq_comm, false_eq_decide_iff, ne_eq]
  constructor
  · intro ⟨v, hv, hv_ne0⟩; exact ⟨v, hv_ne0, hv⟩
  · intro ⟨v, hv_ne0, hv⟩; exact ⟨v, hv, hv_ne0⟩

theorem checkZero_dom_iff {n : ℕ} {f : (Fin (n + 1) → ℕ) → Part ℕ} {inputs : Fin n → ℕ} {y : ℕ} :
    (checkZero f inputs y).Dom ↔ (f (extendInputs inputs y)).Dom := by
  simp only [checkZero, Part.dom_iff_mem, Part.mem_map_iff]
  constructor
  · intro ⟨_, v, hv, _⟩; exact ⟨v, hv⟩
  · intro ⟨v, hv⟩; exact ⟨v = 0, v, hv, rfl⟩

/-! ## Domain Characterization -/

/-- μ f inputs is defined iff there exists a witness y where f returns 0,
    and f is defined on all smaller values. -/
theorem μ_dom_iff {n : ℕ} {f : (Fin (n + 1) → ℕ) → Part ℕ} {inputs : Fin n → ℕ} :
    (μ f inputs).Dom ↔
      ∃ y, (f (extendInputs inputs y) = Part.some 0) ∧
           ∀ y' < y, (f (extendInputs inputs y')).Dom := by
  unfold μ
  rw [Nat.rfind_dom]
  constructor
  · intro ⟨y, htrue, hdom⟩
    refine ⟨y, ?_, ?_⟩
    · rw [checkZero_true_iff] at htrue
      exact Part.eq_some_iff.mpr htrue
    · intro y' hy'
      rw [← checkZero_dom_iff]
      exact hdom hy'
  · intro ⟨y, hfy, hdom⟩
    refine ⟨y, ?_, ?_⟩
    · rw [checkZero_true_iff]
      rw [Part.eq_some_iff] at hfy
      exact hfy
    · intro y' hy'
      rw [checkZero_dom_iff]
      exact hdom y' hy'

/-- If μ f inputs is defined, there exists a witness y where f returns 0. -/
theorem μ_dom_exists_witness {n : ℕ} {f : (Fin (n + 1) → ℕ) → Part ℕ} {inputs : Fin n → ℕ}
    (h : (μ f inputs).Dom) : ∃ y, f (extendInputs inputs y) = Part.some 0 := by
  rw [μ_dom_iff] at h
  exact ⟨h.choose, h.choose_spec.1⟩

/-! ## Specification -/

/-- The value returned by μ satisfies f(inputs, y) = 0. -/
theorem μ_spec {n : ℕ} {f : (Fin (n + 1) → ℕ) → Part ℕ} {inputs : Fin n → ℕ}
    (h : (μ f inputs).Dom) : f (extendInputs inputs ((μ f inputs).get h)) = Part.some 0 := by
  unfold μ at h ⊢
  have hspec := Nat.rfind_spec (Part.get_mem h)
  rw [checkZero_true_iff] at hspec
  exact Part.eq_some_iff.mpr hspec

/-- For y' < μ result, f is defined and returns a non-zero value. -/
theorem μ_min {n : ℕ} {f : (Fin (n + 1) → ℕ) → Part ℕ} {inputs : Fin n → ℕ}
    (h : (μ f inputs).Dom) {y' : ℕ} (hy' : y' < (μ f inputs).get h) :
    ∃ v, f (extendInputs inputs y') = Part.some v ∧ v ≠ 0 := by
  unfold μ at h hy'
  have hmin := Nat.rfind_min (Part.get_mem h) hy'
  rw [checkZero_false_iff] at hmin
  obtain ⟨v, hv_ne0, hv_mem⟩ := hmin
  exact ⟨v, Part.eq_some_iff.mpr hv_mem, hv_ne0⟩

/-- For y' < μ result, f is defined. -/
theorem μ_dom_below {n : ℕ} {f : (Fin (n + 1) → ℕ) → Part ℕ} {inputs : Fin n → ℕ}
    (h : (μ f inputs).Dom) {y' : ℕ} (hy' : y' < (μ f inputs).get h) :
    (f (extendInputs inputs y')).Dom := by
  obtain ⟨v, hv, _⟩ := μ_min h hy'
  rw [Part.eq_some_iff] at hv
  exact Part.dom_iff_mem.mpr ⟨v, hv⟩

/-! ## Helper Lemmas -/

/-- extendInputs at index i < n returns the original input. -/
theorem extendInputs_castSucc {n : ℕ} (inputs : Fin n → ℕ) (y : ℕ) (i : Fin n) :
    extendInputs inputs y (Fin.castSucc i) = inputs i := by
  simp [extendInputs, Fin.snoc]

/-- extendInputs at index n returns y. -/
theorem extendInputs_last {n : ℕ} (inputs : Fin n → ℕ) (y : ℕ) :
    extendInputs inputs y (Fin.last n) = y := by
  simp [extendInputs, Fin.snoc]

end Urm
