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

def allGPhases (m n base : ℕ) (pGs : Fin m → Program) : Program :=
  (List.finRange m).foldl (fun acc i => acc.concat (gPhase base n (pGs i) i.val)) []

def allGPhases_prefix (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) : Program :=
  (List.finRange m).take i |>.foldl (fun acc j => acc.concat (gPhase base n (pGs j) j.val)) []

def allGPhases_suffix (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) : Program :=
  (List.finRange m).drop i |>.foldl (fun acc j => acc.concat (gPhase base n (pGs j) j.val)) []

theorem foldl_concat_eq_acc_concat {α : Type*} (f : α → Program) (l : List α) (acc : Program) :
    l.foldl (fun a x => a.concat (f x)) acc = acc.concat (l.foldl (fun a x => a.concat (f x)) []) := by
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil, concat_nil_right]
  | cons x xs ih => simp only [List.foldl_cons, concat_nil_left]; rw [ih (acc.concat (f x)), ih (f x), concat_assoc]

theorem allGPhases_split (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) (_hi : i ≤ m) :
    allGPhases m n base pGs = (allGPhases_prefix m n base pGs i).concat (allGPhases_suffix m n base pGs i) := by
  simp only [allGPhases, allGPhases_prefix, allGPhases_suffix]
  conv_lhs => rw [(List.take_append_drop i (List.finRange m)).symm]
  simp only [List.foldl_append]
  exact foldl_concat_eq_acc_concat (fun j => gPhase base n (pGs j) j.val) _ _

theorem allGPhases_prefix_full (m n base : ℕ) (pGs : Fin m → Program) :
    allGPhases_prefix m n base pGs m = allGPhases m n base pGs := by
  simp only [allGPhases_prefix, allGPhases]; congr 1; simp

def finalPhase (m n base : ℕ) (pF : Program) : Program :=
  (clearRegisters base).concat ((transferResultsToInputs (base + n + 1) m).concat pF)

def Program.composeGeneral (m n : ℕ) (pF : Program) (pGs : Fin m → Program) : Program :=
  let base := compositionBase m n pF pGs
  (copyRegisterRange 0 (base + 1) n).concat ((allGPhases m n base pGs).concat (finalPhase m n base pF))

end Urm
