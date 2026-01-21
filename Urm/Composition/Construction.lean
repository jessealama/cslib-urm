/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Base

/-! # Program Construction for Composition -/

namespace Urm

open Program

/-- One phase of composition: clears working registers, copies saved inputs,
    runs gᵢ, and saves the result to register `base + n + 1 + i`. -/
def g_phase (base n : ℕ) (pG : Program) (i : ℕ) : Program :=
  (clear_registers base).concat ((copy_register_range (base + 1) 0 n).concat (pG.concat [Instr.T 0 (base + n + 1 + i)]))

/-- Helper to map g_phase over a list of indices. -/
def g_phaseList (n base : ℕ) (pGs : Fin m → Program) (indices : List (Fin m)) : List Program :=
  indices.map (fun i => g_phase base n (pGs i) i.val)

/-- All m phases for computing g₀, g₁, ..., gₘ₋₁ in sequence. -/
def all_g_phases (m n base : ℕ) (pGs : Fin m → Program) : Program :=
  (g_phaseList n base pGs (List.finRange m)).prod

/-- First i phases (prefix) of all_g_phases. -/
def all_g_phases_prefix (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) : Program :=
  (g_phaseList n base pGs ((List.finRange m).take i)).prod

/-- Phases from i to m-1 (suffix) of all_g_phases. -/
def all_g_phases_suffix (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) : Program :=
  (g_phaseList n base pGs ((List.finRange m).drop i)).prod

theorem all_g_phases_split (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) :
    all_g_phases m n base pGs = (all_g_phases_prefix m n base pGs i).concat (all_g_phases_suffix m n base pGs i) := by
  simp only [all_g_phases, all_g_phases_prefix, all_g_phases_suffix, g_phaseList]
  rw [show (List.finRange m).map (fun i => g_phase base n (pGs i) i.val) =
      ((List.finRange m).take i).map (fun i => g_phase base n (pGs i) i.val) ++
      ((List.finRange m).drop i).map (fun i => g_phase base n (pGs i) i.val) by
    rw [← List.map_append, List.take_append_drop]]
  rw [List.prod_append]
  rfl

theorem all_g_phases_prefix_full (m n base : ℕ) (pGs : Fin m → Program) :
    all_g_phases_prefix m n base pGs m = all_g_phases m n base pGs := by
  simp only [all_g_phases_prefix, all_g_phases, g_phaseList]; congr 1; simp

/-- Decompose suffix when start < m: first g_phase followed by remaining suffix. -/
theorem all_g_phases_suffix_cons {m n base : ℕ} (pGs : Fin m → Program) (start : ℕ) (hstart : start < m) :
    all_g_phases_suffix m n base pGs start =
      (g_phase base n (pGs ⟨start, hstart⟩) start).concat (all_g_phases_suffix m n base pGs (start + 1)) := by
  simp only [all_g_phases_suffix, g_phaseList]
  rw [List.drop_eq_getElem_cons (by simp; exact hstart), List.map_cons, List.prod_cons]
  simp only [List.getElem_finRange]
  rfl

/-- Decompose prefix when taking one more: previous prefix followed by the next g_phase. -/
theorem all_g_phases_prefix_succ {m n base : ℕ} (pGs : Fin m → Program) (i : ℕ) (hi : i < m) :
    all_g_phases_prefix m n base pGs (i + 1) =
      (all_g_phases_prefix m n base pGs i).concat (g_phase base n (pGs ⟨i, hi⟩) i) := by
  simp only [all_g_phases_prefix, g_phaseList]
  rw [List.take_succ_eq_append_getElem (by simp; exact hi : i < (List.finRange m).length)]
  rw [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
  simp only [List.getElem_finRange]
  rfl

/-- Final phase: clears working registers, copies computed g values to inputs, and runs pF. -/
def final_phase (m n base : ℕ) (pF : Program) : Program :=
  (clear_registers base).concat ((transfer_results_to_inputs (base + n + 1) m).concat pF)

/-- Compose an m-ary function f with n-ary functions g₀,...,gₘ₋₁.
    Computes h(x) = f(g₀(x), g₁(x), ..., gₘ₋₁(x)). -/
def Program.compose_general (m n : ℕ) (pF : Program) (pGs : Fin m → Program) : Program :=
  let base := composition_base m n pF pGs
  (copy_register_range 0 (base + 1) n).concat ((all_g_phases m n base pGs).concat (final_phase m n base pF))

end Urm
