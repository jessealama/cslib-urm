/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Base

/-! # Program Construction

Defines the composite program structure for general composition.

## Main definitions

- `gPhase`: Phase for running Gᵢ (clear, restore inputs, run Gᵢ, save result)
- `allGPhases`: All G phases concatenated
- `finalPhase`: Final phase (clear, set up F inputs, run F)
- `Program.composeGeneral`: The full general composition program
-/

namespace Urm

open Program

/-! ## Program Construction -/

/-- Phase for running Gᵢ: clear, restore inputs, run Gᵢ, save result.
The result is saved to R[base + n + 1 + i]. -/
def gPhase (base n : ℕ) (pG : Program) (i : ℕ) : Program :=
  (clearRegisters base).concat
    ((copyRegisterRange (base + 1) 0 n).concat
      (pG.concat [Instr.T 0 (base + n + 1 + i)]))

/-- All G phases concatenated. -/
def allGPhases (m n : ℕ) (base : ℕ) (pGs : Fin m → Program) : Program :=
  (List.finRange m).foldl (fun acc i => acc.concat (gPhase base n (pGs i) i.val)) []

/-- First i phases of allGPhases (phases 0 through i-1). -/
def allGPhases_prefix (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) : Program :=
  (List.finRange m).take i |>.foldl (fun acc j => acc.concat (gPhase base n (pGs j) j.val)) []

/-- Suffix of allGPhases starting from phase i. -/
def allGPhases_suffix (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) : Program :=
  (List.finRange m).drop i |>.foldl (fun acc j => acc.concat (gPhase base n (pGs j) j.val)) []

/-- Helper: foldl with concat distributes - starting from acc equals acc.concat starting from []. -/
theorem foldl_concat_eq_acc_concat {α : Type*} (f : α → Program)
    (l : List α) (acc : Program) :
    l.foldl (fun a x => a.concat (f x)) acc =
    acc.concat (l.foldl (fun a x => a.concat (f x)) []) := by
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil, concat_nil_right]
  | cons x xs ih =>
    simp only [List.foldl_cons, concat_nil_left]
    rw [ih (acc.concat (f x)), ih (f x), concat_assoc]

/-- allGPhases splits into prefix and suffix. -/
theorem allGPhases_split (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) (_hi : i ≤ m) :
    allGPhases m n base pGs = (allGPhases_prefix m n base pGs i).concat (allGPhases_suffix m n base pGs i) := by
  simp only [allGPhases, allGPhases_prefix, allGPhases_suffix]
  have h : (List.finRange m) = (List.finRange m).take i ++ (List.finRange m).drop i :=
    (List.take_append_drop i (List.finRange m)).symm
  conv_lhs => rw [h]
  simp only [List.foldl_append]
  exact foldl_concat_eq_acc_concat (fun j => gPhase base n (pGs j) j.val) _ _

/-- Taking all m phases equals the full allGPhases. -/
theorem allGPhases_prefix_full (m n base : ℕ) (pGs : Fin m → Program) :
    allGPhases_prefix m n base pGs m = allGPhases m n base pGs := by
  simp only [allGPhases_prefix, allGPhases]
  have h : (List.finRange m).take m = List.finRange m := by simp
  rw [h]

/-- Final phase: clear, set up F inputs, run F. -/
def finalPhase (m n : ℕ) (base : ℕ) (pF : Program) : Program :=
  (clearRegisters base).concat
    ((transferResultsToInputs (base + n + 1) m).concat pF)

/-- General composition program: runs g₁,...,gₘ on inputs, then f on their results. -/
def Program.composeGeneral (m n : ℕ) (pF : Program) (pGs : Fin m → Program) : Program :=
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF
  saveInputs.concat (gPhases.concat final)

end Urm
