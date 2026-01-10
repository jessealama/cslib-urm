/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Base

/-! # Program Construction for Composition -/

namespace Urm

open Program

def gPhase (base n : ℕ) (pG : Program) (i : ℕ) : Program :=
  (clearRegisters base).concat ((copyRegisterRange (base + 1) 0 n).concat (pG.concat [Instr.T 0 (base + n + 1 + i)]))

/-- Helper to map gPhase over a list of indices. -/
def gPhaseList (n base : ℕ) (pGs : Fin m → Program) (indices : List (Fin m)) : List Program :=
  indices.map (fun i => gPhase base n (pGs i) i.val)

def allGPhases (m n base : ℕ) (pGs : Fin m → Program) : Program :=
  (gPhaseList n base pGs (List.finRange m)).prod

def allGPhases_prefix (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) : Program :=
  (gPhaseList n base pGs ((List.finRange m).take i)).prod

def allGPhases_suffix (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) : Program :=
  (gPhaseList n base pGs ((List.finRange m).drop i)).prod

theorem allGPhases_split (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) (_hi : i ≤ m) :
    allGPhases m n base pGs = (allGPhases_prefix m n base pGs i).concat (allGPhases_suffix m n base pGs i) := by
  simp only [allGPhases, allGPhases_prefix, allGPhases_suffix, gPhaseList]
  rw [show (List.finRange m).map (fun i => gPhase base n (pGs i) i.val) =
      ((List.finRange m).take i).map (fun i => gPhase base n (pGs i) i.val) ++
      ((List.finRange m).drop i).map (fun i => gPhase base n (pGs i) i.val) by
    rw [← List.map_append, List.take_append_drop]]
  rw [List.prod_append]
  rfl

theorem allGPhases_prefix_full (m n base : ℕ) (pGs : Fin m → Program) :
    allGPhases_prefix m n base pGs m = allGPhases m n base pGs := by
  simp only [allGPhases_prefix, allGPhases, gPhaseList]; congr 1; simp

/-- Decompose suffix when start < m: first gPhase followed by remaining suffix. -/
theorem allGPhases_suffix_cons {m n base : ℕ} (pGs : Fin m → Program) (start : ℕ) (hstart : start < m) :
    allGPhases_suffix m n base pGs start =
      (gPhase base n (pGs ⟨start, hstart⟩) start).concat (allGPhases_suffix m n base pGs (start + 1)) := by
  simp only [allGPhases_suffix, gPhaseList]
  rw [List.drop_eq_getElem_cons (by simp; exact hstart), List.map_cons, List.prod_cons]
  simp only [List.getElem_finRange]
  rfl

/-- Decompose prefix when taking one more: previous prefix followed by the next gPhase. -/
theorem allGPhases_prefix_succ {m n base : ℕ} (pGs : Fin m → Program) (i : ℕ) (hi : i < m) :
    allGPhases_prefix m n base pGs (i + 1) =
      (allGPhases_prefix m n base pGs i).concat (gPhase base n (pGs ⟨i, hi⟩) i) := by
  simp only [allGPhases_prefix, gPhaseList]
  rw [List.take_succ_eq_append_getElem (by simp; exact hi : i < (List.finRange m).length)]
  rw [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
  simp only [List.getElem_finRange]
  rfl

def finalPhase (m n base : ℕ) (pF : Program) : Program :=
  (clearRegisters base).concat ((transferResultsToInputs (base + n + 1) m).concat pF)

def Program.composeGeneral (m n : ℕ) (pF : Program) (pGs : Fin m → Program) : Program :=
  let base := compositionBase m n pF pGs
  (copyRegisterRange 0 (base + 1) n).concat ((allGPhases m n base pGs).concat (finalPhase m n base pF))

end Urm
