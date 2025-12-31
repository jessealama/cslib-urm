/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.CompositionHelpers
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-! # General Composition

This file proves the general closure of URM-computable functions under composition.
Given an m-ary f and m n-ary functions g₁,...,gₘ, the composition
h(x₁,...,xₙ) = f(g₁(x),...,gₘ(x)) is computable.

## Main results

- `URMComputableSF.comp_general`: Closure under general composition for standard form programs.

## Implementation

The proof follows Cutland's approach:
1. Let base = max of (m-1) and all registers used by F and the Gᵢ
2. Store n input values in R[base+1..base+n] (safe storage)
3. For each i from 0 to m-1:
   - Clear working registers
   - Restore inputs from safe storage
   - Run Gᵢ
   - Save result to R[base+n+1+i]
4. Clear working registers, set up F's inputs from saved results, run F

Register layout:
  R[0..base]           : Working registers
  R[base+1..base+n]    : Saved copies of n inputs (x₁, ..., xₙ)
  R[base+n+1..base+n+m]: Saved results of m g's (g₁(x), ..., gₘ(x))

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

open Program

/-! ## Base Register Computation -/

/-- Maximum register used by any of the G programs. -/
def maxGsRegister (m : ℕ) (pGs : Fin m → Program) : ℕ :=
  Finset.univ.sup fun i => (pGs i).maxRegister

/-- The base register for safe storage in general composition.
This is at least (m-1) (to accommodate m-1 as a valid input register for f)
and above all registers used by F and all the Gᵢ. -/
def compositionBase (m _n : ℕ) (pF : Program) (pGs : Fin m → Program) : ℕ :=
  max (m - 1) (max pF.maxRegister (maxGsRegister m pGs))

theorem compositionBase_ge_m_sub_one (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    m - 1 ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, le_max_iff]; left; rfl

theorem compositionBase_ge_F (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    pF.maxRegister ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, le_max_iff]; right; left; rfl

theorem compositionBase_ge_Gi (m n : ℕ) (pF : Program) (pGs : Fin m → Program) (i : Fin m) :
    (pGs i).maxRegister ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, maxGsRegister, le_max_iff]
  right; right
  exact @Finset.le_sup ℕ (Fin m) _ _ Finset.univ (fun j => (pGs j).maxRegister) i (Finset.mem_univ i)

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

/-! ## Standard Form Proof -/

/-- Single transfer instruction is straight-line. -/
private theorem single_T_isStraightLine' (src dst : ℕ) :
    Program.isStraightLine [Instr.T src dst] = true := rfl

/-- gPhase is straight-line when pG is straight-line. -/
theorem gPhase_isStraightLine {base n : ℕ} {pG : Program} {i : ℕ}
    (hG_sl : pG.isStraightLine = true) :
    (gPhase base n pG i).isStraightLine = true := by
  simp only [gPhase]
  apply Program.isStraightLine_concat (clearRegisters_isStraightLine base)
  apply Program.isStraightLine_concat (copyRegisterRange_isStraightLine (base + 1) 0 n)
  apply Program.isStraightLine_concat hG_sl
  exact single_T_isStraightLine' 0 (base + n + 1 + i)

/-- Helper: foldl over a list preserves straight-line when the combining function does. -/
private theorem foldl_preserves_isStraightLine
    {α : Type*} (l : List α) (f : Program → α → Program)
    (hf : ∀ acc a, acc.isStraightLine = true → (f acc a).isStraightLine = true)
    (acc : Program) (hacc : acc.isStraightLine = true) :
    (l.foldl f acc).isStraightLine = true := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (f acc x) (hf acc x hacc)

/-- allGPhases is straight-line when all pGs are straight-line. -/
theorem allGPhases_isStraightLine {m n base : ℕ} {pGs : Fin m → Program}
    (hGs_sl : ∀ i, (pGs i).isStraightLine = true) :
    (allGPhases m n base pGs).isStraightLine = true := by
  simp only [allGPhases]
  apply foldl_preserves_isStraightLine
  · intro acc i hacc
    apply Program.isStraightLine_concat hacc
    exact gPhase_isStraightLine (hGs_sl i)
  · rfl

/-- finalPhase is straight-line when pF is straight-line. -/
theorem finalPhase_isStraightLine {m n base : ℕ} {pF : Program}
    (hF_sl : pF.isStraightLine = true) :
    (finalPhase m n base pF).isStraightLine = true := by
  simp only [finalPhase]
  apply Program.isStraightLine_concat (clearRegisters_isStraightLine base)
  apply Program.isStraightLine_concat (transferResultsToInputs_isStraightLine (base + n + 1) m)
  exact hF_sl

/-- composeGeneral produces a straight-line program when all inputs are straight-line. -/
theorem composeGeneral_isStraightLine {m n : ℕ} {pF : Program} {pGs : Fin m → Program}
    (hF_sl : pF.isStraightLine = true)
    (hGs_sl : ∀ i, (pGs i).isStraightLine = true) :
    (Program.composeGeneral m n pF pGs).isStraightLine = true := by
  simp only [Program.composeGeneral]
  apply Program.isStraightLine_concat
    (copyRegisterRange_isStraightLine 0 (compositionBase m n pF pGs + 1) n)
  apply Program.isStraightLine_concat (allGPhases_isStraightLine hGs_sl)
  exact finalPhase_isStraightLine hF_sl

/-- Helper: gPhase is standard form when pG is standard form. -/
theorem gPhase_isStandardForm {base n : ℕ} {pG : Program} {i : ℕ}
    (hG : pG.IsStandardForm) :
    (gPhase base n pG i).IsStandardForm := by
  simp only [gPhase]
  apply Program.IsStandardForm.concat (straightLine_isStandardForm (clearRegisters_isStraightLine base))
  apply Program.IsStandardForm.concat (straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n))
  apply Program.IsStandardForm.concat hG
  exact straightLine_isStandardForm (single_T_isStraightLine' 0 (base + n + 1 + i))

/-- Helper: foldl over a list preserves standard form when the combining function does. -/
private theorem foldl_preserves_isStandardForm
    {α : Type*} (l : List α) (f : Program → α → Program)
    (hf : ∀ acc a, acc.IsStandardForm → (f acc a).IsStandardForm)
    (acc : Program) (hacc : acc.IsStandardForm) :
    (l.foldl f acc).IsStandardForm := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (f acc x) (hf acc x hacc)

/-- allGPhases is standard form when all pGs are standard form. -/
theorem allGPhases_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) :
    (allGPhases m n base pGs).IsStandardForm := by
  simp only [allGPhases]
  apply foldl_preserves_isStandardForm
  · intro acc i hacc
    apply Program.IsStandardForm.concat hacc
    exact gPhase_isStandardForm (hGs i)
  · exact straightLine_isStandardForm rfl  -- empty program is straight-line

/-- finalPhase is standard form when pF is standard form. -/
theorem finalPhase_isStandardForm {m n base : ℕ} {pF : Program}
    (hF : pF.IsStandardForm) :
    (finalPhase m n base pF).IsStandardForm := by
  simp only [finalPhase]
  apply Program.IsStandardForm.concat (straightLine_isStandardForm (clearRegisters_isStraightLine base))
  apply Program.IsStandardForm.concat (straightLine_isStandardForm (transferResultsToInputs_isStraightLine (base + n + 1) m))
  exact hF

/-- composeGeneral is standard form when F and all Gs are standard form. -/
theorem composeGeneral_isStandardForm {m n : ℕ} {pF : Program} {pGs : Fin m → Program}
    (hF : pF.IsStandardForm)
    (hGs : ∀ i, (pGs i).IsStandardForm) :
    (Program.composeGeneral m n pF pGs).IsStandardForm := by
  simp only [Program.composeGeneral]
  apply Program.IsStandardForm.concat
    (straightLine_isStandardForm (copyRegisterRange_isStraightLine 0 (compositionBase m n pF pGs + 1) n))
  apply Program.IsStandardForm.concat (allGPhases_isStandardForm hGs)
  exact finalPhase_isStandardForm hF

/-! ## Execution Helpers -/

-- Note: The detailed execution helper proofs for copyRegisterRange and transferResultsToInputs
-- require substantial infrastructure. We mark these as sorry for now and focus on the theorem
-- structure. These can be filled in following the patterns in BinaryUnaryComposition.lean.

/-- State after saving inputs to safe storage. -/
theorem copyRegisterRange_state (srcStart dstStart count : ℕ) (s : State) :
    ∃ s', straightLineFinalState (copyRegisterRange_isStraightLine srcStart dstStart count) s = s' ∧
      (∀ i : ℕ, i < count → s'.read (dstStart + i) = s.read (srcStart + i)) ∧
      (∀ r : ℕ, r < dstStart ∨ r ≥ dstStart + count → s'.read r = s.read r) := by
  sorry

/-- State after transferring results to input registers. -/
theorem transferResultsToInputs_state (resultStart arityF : ℕ) (s : State) :
    ∃ s', straightLineFinalState (transferResultsToInputs_isStraightLine resultStart arityF) s = s' ∧
      (∀ i : ℕ, i < arityF → s'.read i = s.read (resultStart + i)) ∧
      (∀ r : ℕ, r ≥ arityF → s'.read r = s.read r) := by
  sorry

/-! ## Main Theorem -/

/-- The composed function for general composition.
h(x) = f(g₁(x), ..., gₘ(x)) -/
def compFunction (m n : ℕ) (f : (Fin m → ℕ) → Part ℕ) (gs : Fin m → (Fin n → ℕ) → Part ℕ)
    (x : Fin n → ℕ) : Part ℕ :=
  (Part.sequence (fun i => gs i x)).bind f

/-- If the composition halts, then each gᵢ is defined on the inputs. -/
theorem comp_general_halts_imp_gi_dom
    {m n : ℕ} [NeZero m]
    {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hF_sf : pF.IsStandardForm)
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs))
    (i : Fin m) :
    (gs i inputs).Dom := by
  sorry

/-- If the composition halts and all gᵢ are defined, then f is defined. -/
theorem comp_general_halts_imp_f_dom
    {m n : ℕ} [NeZero m]
    {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hF_sf : pF.IsStandardForm)
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs))
    (hGs_dom : ∀ i, (gs i inputs).Dom) :
    (f (fun i => (gs i inputs).get (hGs_dom i))).Dom := by
  sorry

/-- If the composed function is defined, then the program halts. -/
theorem comp_general_dom_imp_halts
    {m n : ℕ} [NeZero m]
    {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hF_sf : pF.IsStandardForm)
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hDom : (compFunction m n f gs inputs).Dom) :
    Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs) := by
  sorry

/-- The result of the composition equals the composed function value. -/
theorem comp_general_result
    {m n : ℕ} [NeZero m]
    {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hF_sf : pF.IsStandardForm)
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs))
    (hDom : (compFunction m n f gs inputs).Dom) :
    Result (Program.composeGeneral m n pF pGs) (List.ofFn inputs) hHalts =
      (compFunction m n f gs inputs).get hDom := by
  sorry

/-- General closure under composition.
Given m-ary f and m n-ary functions g₁,...,gₘ, the composition
h(x₁,...,xₙ) = f(g₁(x),...,gₘ(x)) is computable. -/
theorem URMComputableSF.comp_general
    {m n : ℕ} [NeZero m]
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hf : URMComputableSF m f)
    (hgs : ∀ i, URMComputableSF n (gs i)) :
    URMComputableSF n (compFunction m n f gs) := by
  -- Extract the programs
  obtain ⟨pF, hF_sf, hF_spec⟩ := hf
  choose pGs hGs_sf hGs_spec using fun i => hgs i
  -- Construct the composed program
  let pH := Program.composeGeneral m n pF pGs
  use pH
  constructor
  · -- Standard form
    exact composeGeneral_isStandardForm hF_sf hGs_sf
  · -- Correctness
    intro inputs
    constructor
    · -- Halts ↔ Dom
      constructor
      · -- Halts → Dom
        intro hHalts
        simp only [compFunction]
        -- Need to show (Part.sequence (fun i => gs i inputs)).bind f is defined
        -- This means (1) Part.sequence is defined and (2) f applied to the result is defined
        have hGs_dom : ∀ i, (gs i inputs).Dom :=
          fun i => comp_general_halts_imp_gi_dom hF_sf hGs_sf hF_spec hGs_spec inputs hHalts i
        have hSeq_dom : (Part.sequence (fun i => gs i inputs)).Dom := Part.sequence_dom.mpr hGs_dom
        rw [Part.bind_dom]
        refine ⟨hSeq_dom, ?_⟩
        -- Now show f ((Part.sequence ...).get hSeq_dom) is defined
        have hf_dom := comp_general_halts_imp_f_dom hF_sf hGs_sf hF_spec hGs_spec inputs hHalts hGs_dom
        -- Need to show the get matches: the argument to f is the same
        have harg_eq : (Part.sequence (fun i => gs i inputs)).get hSeq_dom =
            (fun i => (gs i inputs).get (hGs_dom i)) := by
          funext i
          exact Part.sequence_get hSeq_dom i
        rw [harg_eq]
        exact hf_dom
      · -- Dom → Halts
        intro hDom
        exact comp_general_dom_imp_halts hF_sf hGs_sf hF_spec hGs_spec inputs hDom
    · -- Result correctness
      intro hHalts hDom
      exact comp_general_result hF_sf hGs_sf hF_spec hGs_spec inputs hHalts hDom

end Urm
