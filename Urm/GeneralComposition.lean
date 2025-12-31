/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.CompositionHelpers
import Urm.BinaryUnaryComposition
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.GetD

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
This is at least (n-1) (to ensure input saving doesn't overlap with working registers),
at least (m-1) (to accommodate m-1 as a valid input register for f),
and above all registers used by F and all the Gᵢ. -/
def compositionBase (m n : ℕ) (pF : Program) (pGs : Fin m → Program) : ℕ :=
  max (n - 1) (max (m - 1) (max pF.maxRegister (maxGsRegister m pGs)))

theorem compositionBase_ge_n_sub_one (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    n - 1 ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, le_max_iff]; left; rfl

theorem compositionBase_ge_m_sub_one (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    m - 1 ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, le_max_iff]; right; left; rfl

theorem compositionBase_ge_F (m n : ℕ) (pF : Program) (pGs : Fin m → Program) :
    pF.maxRegister ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, le_max_iff]; right; right; left; rfl

theorem compositionBase_ge_Gi (m n : ℕ) (pF : Program) (pGs : Fin m → Program) (i : Fin m) :
    (pGs i).maxRegister ≤ compositionBase m n pF pGs := by
  simp only [compositionBase, maxGsRegister, le_max_iff]
  right; right; right
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

/-- First i phases of allGPhases (phases 0 through i-1). -/
def allGPhases_prefix (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) : Program :=
  (List.finRange m).take i |>.foldl (fun acc j => acc.concat (gPhase base n (pGs j) j.val)) []

/-- Suffix of allGPhases starting from phase i. -/
def allGPhases_suffix (m n base : ℕ) (pGs : Fin m → Program) (i : ℕ) : Program :=
  (List.finRange m).drop i |>.foldl (fun acc j => acc.concat (gPhase base n (pGs j) j.val)) []

/-- Helper: foldl with concat distributes - starting from acc equals acc.concat starting from []. -/
private theorem foldl_concat_eq_acc_concat {α : Type*} (f : α → Program)
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

/-- Register preservation for copyRegisterRange: registers outside [dstStart, dstStart+count) unchanged. -/
theorem copyRegisterRange_preserves (srcStart dstStart count : ℕ) (s : State)
    (r : ℕ) (hr : r < dstStart ∨ r ≥ dstStart + count) :
    (straightLineFinalState (copyRegisterRange_isStraightLine srcStart dstStart count) s).read r = s.read r := by
  have hsl := copyRegisterRange_isStraightLine srcStart dstStart count
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  exact Steps.straightLine_preserves hsl hsteps (copyRegisterRange_preserves_outside srcStart dstStart count r hr)

/-- Register preservation for transferResultsToInputs: registers ≥ arityF unchanged. -/
theorem transferResultsToInputs_preserves (resultStart arityF : ℕ) (s : State)
    (r : ℕ) (hr : r ≥ arityF) :
    (straightLineFinalState (transferResultsToInputs_isStraightLine resultStart arityF) s).read r = s.read r := by
  have hsl := transferResultsToInputs_isStraightLine resultStart arityF
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  exact Steps.straightLine_preserves hsl hsteps (transferResultsToInputs_preserves_outside resultStart arityF r hr)

/-- State after saving inputs to safe storage (with non-overlapping ranges). -/
theorem copyRegisterRange_state (srcStart dstStart count : ℕ) (s : State)
    (hNoOverlap : srcStart + count ≤ dstStart ∨ dstStart + count ≤ srcStart) :
    ∃ s', straightLineFinalState (copyRegisterRange_isStraightLine srcStart dstStart count) s = s' ∧
      (∀ i : ℕ, i < count → s'.read (dstStart + i) = s.read (srcStart + i)) ∧
      (∀ r : ℕ, r < dstStart ∨ r ≥ dstStart + count → s'.read r = s.read r) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · -- Show copied values using straightLine_transfer_result
    intro i hi
    have hsl := copyRegisterRange_isStraightLine srcStart dstStart count
    let p := Program.copyRegisterRange srcStart dstStart count
    have hk : i < p.length := by simp only [p, copyRegisterRange_length]; exact hi
    have hwrite : p[i] = Instr.T (srcStart + i) (dstStart + i) := by
      simp only [p, Program.copyRegisterRange, List.getElem_map, List.getElem_range]
    have hnowrite : ∀ j (hj : j < p.length), i < j → (p[j]'hj).writesTo ≠ some (dstStart + i) := by
      intro j hj hij
      simp only [p, Program.copyRegisterRange, List.getElem_map, List.getElem_range, Instr.writesTo]
      simp only [ne_eq, Option.some.injEq]
      omega
    obtain ⟨s_before, ⟨c_i, hsteps_i, hpc_i, hs_before_eq⟩, hread_eq⟩ :=
      straightLine_transfer_result hsl s i (srcStart + i) (dstStart + i) hk hwrite hnowrite
    rw [hread_eq]
    -- Now show s_before.read (srcStart + i) = s.read (srcStart + i)
    -- Since srcStart + i is not in the dst range (by hNoOverlap), it's preserved
    have hsrc_preserved : s_before.read (srcStart + i) = s.read (srcStart + i) := by
      -- srcStart + i is outside [dstStart, dstStart + count) due to non-overlap
      have h_outside : srcStart + i < dstStart ∨ srcStart + i ≥ dstStart + count := by
        cases hNoOverlap with
        | inl h => left; omega
        | inr h => right; omega
      -- The execution from ⟨0, s⟩ to c_i preserves srcStart + i
      rw [← hs_before_eq]
      exact Steps.straightLine_preserves hsl hsteps_i
        (copyRegisterRange_preserves_outside srcStart dstStart count (srcStart + i) h_outside)
    exact hsrc_preserved
  · exact fun r hr => copyRegisterRange_preserves srcStart dstStart count s r hr

/-- State after transferring results to input registers (with non-overlapping ranges). -/
theorem transferResultsToInputs_state (resultStart arityF : ℕ) (s : State)
    (hNoOverlap : arityF ≤ resultStart) :
    ∃ s', straightLineFinalState (transferResultsToInputs_isStraightLine resultStart arityF) s = s' ∧
      (∀ i : ℕ, i < arityF → s'.read i = s.read (resultStart + i)) ∧
      (∀ r : ℕ, r ≥ arityF → s'.read r = s.read r) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · -- Show transferred values using straightLine_transfer_result
    intro i hi
    have hsl := transferResultsToInputs_isStraightLine resultStart arityF
    let p := Program.transferResultsToInputs resultStart arityF
    have hk : i < p.length := by simp only [p, transferResultsToInputs_length]; exact hi
    have hwrite : p[i] = Instr.T (resultStart + i) i := by
      simp only [p, Program.transferResultsToInputs, List.getElem_map, List.getElem_range]
    have hnowrite : ∀ j (hj : j < p.length), i < j → (p[j]'hj).writesTo ≠ some i := by
      intro j hj hij
      simp only [p, Program.transferResultsToInputs, List.getElem_map, List.getElem_range, Instr.writesTo]
      simp only [ne_eq, Option.some.injEq]
      omega
    obtain ⟨s_before, ⟨c_i, hsteps_i, hpc_i, hs_before_eq⟩, hread_eq⟩ :=
      straightLine_transfer_result hsl s i (resultStart + i) i hk hwrite hnowrite
    rw [hread_eq]
    -- Now show s_before.read (resultStart + i) = s.read (resultStart + i)
    -- Source (resultStart + i) is preserved since it's ≥ arityF (outside dst range)
    have hsrc_preserved : s_before.read (resultStart + i) = s.read (resultStart + i) := by
      have h_outside : resultStart + i ≥ arityF := by omega
      rw [← hs_before_eq]
      exact Steps.straightLine_preserves hsl hsteps_i
        (transferResultsToInputs_preserves_outside resultStart arityF (resultStart + i) h_outside)
    exact hsrc_preserved
  · exact fun r hr => transferResultsToInputs_preserves resultStart arityF s r hr

/-! ## Standard Form Helpers for Prefix/Suffix -/

/-- allGPhases_prefix is standard form when all pGs are standard form. -/
theorem allGPhases_prefix_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) (k : ℕ) :
    (allGPhases_prefix m n base pGs k).IsStandardForm := by
  simp only [allGPhases_prefix]
  apply foldl_preserves_isStandardForm
  · intro acc j hacc
    apply Program.IsStandardForm.concat hacc
    exact gPhase_isStandardForm (hGs j)
  · exact straightLine_isStandardForm rfl

/-- allGPhases_suffix is standard form when all pGs are standard form. -/
theorem allGPhases_suffix_isStandardForm {m n base : ℕ} {pGs : Fin m → Program}
    (hGs : ∀ i, (pGs i).IsStandardForm) (k : ℕ) :
    (allGPhases_suffix m n base pGs k).IsStandardForm := by
  simp only [allGPhases_suffix]
  apply foldl_preserves_isStandardForm
  · intro acc j hacc
    apply Program.IsStandardForm.concat hacc
    exact gPhase_isStandardForm (hGs j)
  · exact straightLine_isStandardForm rfl

/-- saveInputs is standard form. -/
theorem saveInputs_isStandardForm (base n : ℕ) :
    (copyRegisterRange 0 (base + 1) n).IsStandardForm :=
  straightLine_isStandardForm (copyRegisterRange_isStraightLine 0 (base + 1) n)

/-! ## Preservation Lemmas for Saved Inputs -/

/-- gPhase preserves registers in R[base+1..base+n].
These are the saved input registers that must be preserved through all G phases. -/
theorem gPhase_preserves_saved_inputs (base n : ℕ) (pG : Program) (j : ℕ)
    (hpG_sf : pG.IsStandardForm)
    (hpG_max : pG.maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (s s' : State) (c' : Config)
    (hsteps : Steps (gPhase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (gPhase base n pG j))
    (hstate_eq : c'.state = s') :
    ∀ r, base + 1 ≤ r → r ≤ base + n → s'.read r = s.read r := by
  intro r hr_lo hr_hi
  -- gPhase = clear ++ (copyRange ++ (pG ++ [T]))
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine base)
  have hCopyRange_sf := straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n)
  have hT_sf : Program.IsStandardForm [Instr.T 0 (base + n + 1 + j)] :=
    straightLine_isStandardForm rfl

  -- Extract clear execution and suffix
  obtain ⟨sClear, hClear_steps, ⟨cRest, hRest_steps, hRest_halted⟩⟩ :=
    suffix_of_concat_from_zero hsteps hhalted hClear_sf

  -- Extract copyRange execution and suffix
  obtain ⟨sCopy, hCopy_steps, ⟨cPGT, hPGT_steps, hPGT_halted⟩⟩ :=
    suffix_of_concat_from_zero hRest_steps hRest_halted hCopyRange_sf

  -- Extract pG execution and T
  obtain ⟨sPG, hPG_steps, ⟨cT, hT_steps, hT_halted⟩⟩ :=
    suffix_of_concat_from_zero hPGT_steps hPGT_halted hpG_sf

  -- 1. Clear preserves r > base
  have hClear_preserves : sClear.read r = s.read r := by
    have hClear_sl := clearRegisters_isStraightLine base
    have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted (clearRegisters base) := by
      simp [Config.isHalted]
    have hsClear_eq : sClear = straightLineFinalState hClear_sl s :=
      straightLineFinalState_eq_of_halted hClear_sl s ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'
    rw [hsClear_eq]
    exact clearRegisters_preserves_above' base s r (by omega : base < r)

  -- 2. CopyRange preserves r ≥ n (dst is [0, n), so r ≥ n is outside)
  have hCopy_preserves : sCopy.read r = sClear.read r := by
    have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
    have hCopy_halted' : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
        (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
    have hsCopy_eq : sCopy = straightLineFinalState hCopy_sl sClear :=
      straightLineFinalState_eq_of_halted hCopy_sl sClear ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩
        hCopy_steps hCopy_halted'
    rw [hsCopy_eq]
    exact copyRegisterRange_preserves (base + 1) 0 n sClear r (Or.inr (by omega : r ≥ 0 + n))

  -- 3. pG preserves r > maxRegister(pG)
  have hPG_preserves : sPG.read r = sCopy.read r := by
    have hr_gt_max : pG.maxRegister < r := Nat.lt_of_le_of_lt hpG_max (by omega : base < r)
    exact Steps.preserves_high_register hPG_steps r hr_gt_max

  -- 4. T 0 (base+n+1+j) preserves r ≠ base+n+1+j
  have hT_preserves : s'.read r = sPG.read r := by
    have hr_ne : r ≠ base + n + 1 + j := by omega
    -- [T 0 dst] is a single instruction that only writes to dst

    -- Use executeSingleTransfer to get the final state properties
    let tr := executeSingleTransfer 0 (base + n + 1 + j) sPG

    -- cT = tr.config by determinism
    have hcT_eq : cT = tr.config := Steps.halts_unique hT_steps hT_halted tr.steps tr.halted

    -- The final state of T from sPG preserves r
    have hT_state : cT.state.read r = sPG.read r := by
      simp only [hcT_eq, SingleTransferResult.config]
      exact tr.preserved r hr_ne

    -- Chain through determinism to show c'.state = cT.state
    -- Using Steps.chain_concat to build combined executions

    -- pG ++ T execution from sCopy halts at ⟨cT.pc + pG.length, cT.state⟩
    have hPG_halted : (⟨pG.length, sPG⟩ : Config).isHalted pG := by simp [Config.isHalted]
    have hPGT_combined := Steps.chain_concat hPG_steps hPG_halted rfl hT_steps hT_halted
    have hcPGT_state : cPGT.state = cT.state := by
      have heq := Steps.halts_unique hPGT_steps hPGT_halted hPGT_combined.1 hPGT_combined.2
      simp only [heq]

    -- copy ++ (pG ++ T) from sClear
    have hCopy_halted : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
        (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
    have hRest_combined := Steps.chain_concat hCopy_steps hCopy_halted rfl hPGT_steps hPGT_halted
    have hcRest_state : cRest.state = cPGT.state := by
      have heq := Steps.halts_unique hRest_steps hRest_halted hRest_combined.1 hRest_combined.2
      simp only [heq]

    -- clear ++ (copy ++ (pG ++ T)) = gPhase from s
    have hClear_halted : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
        (clearRegisters base) := by simp [Config.isHalted]
    have hGPhase_combined := Steps.chain_concat hClear_steps hClear_halted rfl hRest_steps hRest_halted
    have hc'_state : c'.state = cRest.state := by
      have heq := Steps.halts_unique hsteps hhalted hGPhase_combined.1 hGPhase_combined.2
      simp only [heq]

    -- Chain: s' = c'.state = cRest.state = cPGT.state = cT.state, and cT.state.read r = sPG.read r
    rw [← hstate_eq, hc'_state, hcRest_state, hcPGT_state, hT_state]

  -- Chain the preservation
  rw [hT_preserves, hPG_preserves, hCopy_preserves, hClear_preserves]

/-- allGPhases_prefix preserves registers in R[base+1..base+n]. -/
theorem allGPhases_prefix_preserves_saved_inputs (m n base : ℕ) (pGs : Fin m → Program)
    (hpGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hpGs_max : ∀ i, (pGs i).maxRegister ≤ base) (hn_le_base : n ≤ base + 1)
    (k : ℕ) (hk : k ≤ m)
    (s s' : State) (c' : Config)
    (hsteps : Steps (allGPhases_prefix m n base pGs k) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (allGPhases_prefix m n base pGs k))
    (hstate_eq : c'.state = s') :
    ∀ r, base + 1 ≤ r → r ≤ base + n → s'.read r = s.read r := by
  intro r hr_lo hr_hi
  -- Use strong induction on k
  induction k generalizing s s' c' with
  | zero =>
    -- prefix(0) = [], so s' = s
    simp only [allGPhases_prefix, List.take_zero, List.foldl_nil] at hsteps hhalted
    -- For empty program, hsteps is Relation.ReflTransGen.refl so c' = ⟨0, s⟩
    have hstate : c'.state = s := by
      -- No Step from empty program, so c' = ⟨0, s⟩
      have hc'_eq : c' = ⟨0, s⟩ := Steps.halts_unique hsteps hhalted (.refl _)
        (by simp [Config.isHalted])
      simp only [hc'_eq]
    -- Use transitivity: s' = c'.state = s
    calc s'.read r = (c'.state).read r := by rw [← hstate_eq]
      _ = s.read r := by rw [hstate]
  | succ k' ih =>
    -- prefix(k'+1) = prefix(k') ++ gPhase(k')
    have hk'_lt : k' < m := Nat.lt_of_succ_le hk
    let k'_fin : Fin m := ⟨k', hk'_lt⟩
    -- Establish that prefix(k'+1) = prefix(k').concat gPhase(k')
    have hPrefix_succ_eq : allGPhases_prefix m n base pGs (k' + 1) =
        (allGPhases_prefix m n base pGs k').concat (gPhase base n (pGs k'_fin) k') := by
      simp only [allGPhases_prefix]
      have htake_eq : (List.finRange m).take (k' + 1) = (List.finRange m).take k' ++ [k'_fin] := by
        rw [List.take_add_one]
        have hlen : k' < (List.finRange m).length := by simp only [List.length_finRange]; exact hk'_lt
        rw [getElem?_pos (List.finRange m) k' hlen, Option.toList_some]
        simp only [List.finRange, List.getElem_ofFn, k'_fin]
      rw [htake_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hPrefix_succ_eq] at hsteps hhalted
    -- Split execution: prefix(k') halts, then gPhase(k') halts
    have hPrefix_k'_sf : (allGPhases_prefix m n base pGs k').IsStandardForm :=
      allGPhases_prefix_isStandardForm hpGs_sf k'
    obtain ⟨sMid, hMid_steps, ⟨cGPhase, hGPhase_steps, hGPhase_halted⟩⟩ :=
      suffix_of_concat_from_zero hsteps hhalted hPrefix_k'_sf
    -- Apply IH to prefix(k')
    have hMid_halted : (⟨(allGPhases_prefix m n base pGs k').length, sMid⟩ : Config).isHalted
        (allGPhases_prefix m n base pGs k') := by simp [Config.isHalted]
    have hPrefix_preserves := ih (Nat.le_of_succ_le hk) s sMid ⟨(allGPhases_prefix m n base pGs k').length, sMid⟩
      hMid_steps hMid_halted rfl
    -- Apply gPhase preservation
    -- cGPhase.state = c'.state by determinism (both are final states of the same execution)
    have hGPhase_state_eq : cGPhase.state = s' := by
      rw [← hstate_eq]
      have hMid_halted' : (⟨(allGPhases_prefix m n base pGs k').length, sMid⟩ : Config).isHalted
          (allGPhases_prefix m n base pGs k') := by simp [Config.isHalted]
      have hMid_lifted := @Steps.concat_left_prefix _ (gPhase base n (pGs k'_fin) k') _ _ hMid_steps hMid_halted'
      have hSuffix_combined := Steps.deterministic_continuation hMid_lifted hsteps hhalted
      have hpc_ge : c'.pc ≥ (allGPhases_prefix m n base pGs k').length := by
        simp only [Config.isHalted, Program.concat_length] at hhalted
        omega
      obtain ⟨cGPhase', hGPhase'_steps, hGPhase'_halted, hGPhase'_state⟩ :=
        Steps.of_concat_right hSuffix_combined hhalted hpc_ge
      exact (Steps.halts_unique hGPhase_steps hGPhase_halted hGPhase'_steps hGPhase'_halted) ▸ hGPhase'_state
    have hGPhase_preserves := gPhase_preserves_saved_inputs base n (pGs k'_fin) k'
      (hpGs_sf k'_fin) (hpGs_max k'_fin) hn_le_base sMid s' cGPhase
      hGPhase_steps hGPhase_halted hGPhase_state_eq
    rw [hGPhase_preserves r hr_lo hr_hi, hPrefix_preserves]

/-- saveInputs writes inputs to R[base+1..base+n]. -/
theorem saveInputs_state (base n : ℕ) (hn_le_base : n ≤ base + 1) (inputs : Fin n → ℕ)
    (r : ℕ) (hr : r < n) :
    (straightLineFinalState (copyRegisterRange_isStraightLine 0 (base + 1) n)
      (State.fromInputs (List.ofFn inputs))).read (base + 1 + r) = inputs ⟨r, hr⟩ := by
  set s := State.fromInputs (List.ofFn inputs) with hs_def
  have hNoOverlap : 0 + n ≤ base + 1 ∨ (base + 1) + n ≤ 0 := Or.inl (by omega : 0 + n ≤ base + 1)
  obtain ⟨s', hs'_eq, hcopies, _⟩ := copyRegisterRange_state 0 (base + 1) n s hNoOverlap
  -- Show the goal's straightLineFinalState = s'
  have hsl := copyRegisterRange_isStraightLine 0 (base + 1) n
  have hfinal_eq : straightLineFinalState hsl s = s' := hs'_eq
  rw [hfinal_eq]
  have hcopy := hcopies r hr
  simp only [Nat.zero_add] at hcopy
  rw [hcopy]
  -- s.read r = inputs[r]
  simp only [hs_def, State.fromInputs, State.read]
  rw [List.getD_eq_getElem (List.ofFn inputs) 0 (by simp; exact hr), List.getElem_ofFn]

/-! ## Saved Results Tracking -/

/-- gPhase preserves result registers R[base+n+1+k] for k ≠ j.
This is because gPhase j only writes to R[base+n+1+j], and other writes are within R[0..base]. -/
theorem gPhase_preserves_other_results (base n : ℕ) (pG : Program) (j k : ℕ)
    (hpG_sf : pG.IsStandardForm)
    (hpG_max : pG.maxRegister ≤ base) (_hn_le_base : n ≤ base + 1)
    (hjk : j ≠ k)
    (s s' : State) (c' : Config)
    (hsteps : Steps (gPhase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (gPhase base n pG j))
    (hstate_eq : c'.state = s') :
    s'.read (base + n + 1 + k) = s.read (base + n + 1 + k) := by
  -- gPhase = clear ++ (copyRange ++ (pG ++ [T]))
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine base)
  have hCopyRange_sf := straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n)

  -- Extract clear execution and suffix
  obtain ⟨sClear, hClear_steps, ⟨cRest, hRest_steps, hRest_halted⟩⟩ :=
    suffix_of_concat_from_zero hsteps hhalted hClear_sf

  -- Extract copyRange execution and suffix
  obtain ⟨sCopy, hCopy_steps, ⟨cPGT, hPGT_steps, hPGT_halted⟩⟩ :=
    suffix_of_concat_from_zero hRest_steps hRest_halted hCopyRange_sf

  -- Extract pG execution and T
  obtain ⟨sPG, hPG_steps, ⟨cT, hT_steps, hT_halted⟩⟩ :=
    suffix_of_concat_from_zero hPGT_steps hPGT_halted hpG_sf

  -- The register base+n+1+k where k ≠ j
  let r := base + n + 1 + k

  -- 1. Clear preserves r (r > base)
  have hr_gt_base : base < r := by omega
  have hClear_preserves : sClear.read r = s.read r := by
    have hClear_sl := clearRegisters_isStraightLine base
    have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted (clearRegisters base) := by
      simp [Config.isHalted]
    have hsClear_eq : sClear = straightLineFinalState hClear_sl s :=
      straightLineFinalState_eq_of_halted hClear_sl s ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'
    rw [hsClear_eq]
    exact clearRegisters_preserves_above' base s r hr_gt_base

  -- 2. CopyRange preserves r (r ≥ n since r = base+n+1+k > n)
  have hCopy_preserves : sCopy.read r = sClear.read r := by
    have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
    have hCopy_halted' : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
        (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
    have hsCopy_eq : sCopy = straightLineFinalState hCopy_sl sClear :=
      straightLineFinalState_eq_of_halted hCopy_sl sClear
        ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ hCopy_steps hCopy_halted'
    rw [hsCopy_eq]
    exact copyRegisterRange_preserves (base + 1) 0 n sClear r (Or.inr (by omega : r ≥ 0 + n))

  -- 3. pG preserves r (r > maxRegister(pG))
  have hr_gt_max : pG.maxRegister < r := Nat.lt_of_le_of_lt hpG_max (by omega : base < r)
  have hPG_preserves : sPG.read r = sCopy.read r := Steps.preserves_high_register hPG_steps r hr_gt_max

  -- 4. T 0 (base+n+1+j) preserves r = base+n+1+k (since k ≠ j)
  have hr_ne : r ≠ base + n + 1 + j := by omega
  have hT_preserves : cT.state.read r = sPG.read r := by
    let tr := executeSingleTransfer 0 (base + n + 1 + j) sPG
    have hcT_eq : cT = tr.config := Steps.halts_unique hT_steps hT_halted tr.steps tr.halted
    simp only [hcT_eq, SingleTransferResult.config]
    exact tr.preserved r hr_ne

  -- Connect c'.state to cT.state through chain
  -- c' = final config of gPhase from ⟨0, s⟩
  -- cT = final config of [T] from ⟨0, sPG⟩
  -- They should have the same state (just different pc)

  -- Use that c'.state = cRest.state = cPGT.state = cT.state
  have hc'_state_eq : c'.state.read r = cT.state.read r := by
    -- cRest = final of copyRange ++ (pG ++ [T]) from ⟨0, sClear⟩
    -- cPGT = final of pG ++ [T] from ⟨0, sCopy⟩
    -- cT = final of [T] from ⟨0, sPG⟩
    -- All should have state from running through to cT

    -- c'.pc = gPhase.length, c'.state = ?
    -- The suffix_of_concat_from_zero preserves the state chain
    -- c' comes from hsteps : Steps gPhase ⟨0, s⟩ c'
    -- And gPhase = clear ++ rest, where rest ends at cRest
    -- cRest = ⟨rest.length, state_after_rest⟩
    -- And c' = ⟨gPhase.length, same_state⟩

    -- Actually, the state equality follows from determinism:
    -- The combined execution goes to a unique final state
    have hPG_halted : (⟨pG.length, sPG⟩ : Config).isHalted pG := by simp [Config.isHalted]
    have hPGT_combined := Steps.chain_concat hPG_steps hPG_halted rfl hT_steps hT_halted
    have hCopy_halted : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
        (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
    have hCopyPGT_combined := Steps.chain_concat hCopy_steps hCopy_halted rfl hPGT_steps hPGT_halted
    have hClear_halted : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
        (clearRegisters base) := by simp [Config.isHalted]
    have hClearRest_combined := Steps.chain_concat hClear_steps hClear_halted rfl hRest_steps hRest_halted

    -- c' = final of gPhase from ⟨0, s⟩
    -- hClearRest_combined.config = ⟨clear.len + rest.len, cRest.state⟩
    -- Both halted at gPhase, so c'.state = cRest.state
    have hc'_eq_cRest_state : c'.state = cRest.state := by
      have huniq := Steps.halts_unique hsteps hhalted hClearRest_combined.1 hClearRest_combined.2
      -- huniq : c' = ⟨cRest.pc + clear.length, cRest.state⟩
      rw [huniq]

    have hcRest_eq_cPGT_state : cRest.state = cPGT.state := by
      have huniq := Steps.halts_unique hRest_steps hRest_halted hCopyPGT_combined.1 hCopyPGT_combined.2
      -- huniq : cRest = ⟨..., cPGT.state⟩
      rw [huniq]

    have hcPGT_eq_cT_state : cPGT.state = cT.state := by
      have huniq := Steps.halts_unique hPGT_steps hPGT_halted hPGT_combined.1 hPGT_combined.2
      -- huniq : cPGT = ⟨..., cT.state⟩
      rw [huniq]

    rw [hc'_eq_cRest_state, hcRest_eq_cPGT_state, hcPGT_eq_cT_state]

  -- Chain all preservations
  rw [← hstate_eq, hc'_state_eq, hT_preserves, hPG_preserves, hCopy_preserves, hClear_preserves]

/-! ## Forward Direction Helpers: Dom → Halts -/

/-- A single gPhase halts from a state where R[base+1..base+n] contain the inputs.
This is the forward direction: given pGs i halts on inputs, gPhase halts from saved state. -/
theorem gPhase_halts_from_saved_inputs
    {base n : ℕ} {pG : Program} {i : ℕ}
    {inputs : Fin n → ℕ}
    (hpG_sf : pG.IsStandardForm)
    (hpG_max : pG.maxRegister ≤ base)
    (hn_le_base : n ≤ base + 1)
    (hpG_halts : Halts pG (List.ofFn inputs))
    (s : State)
    (hSaved : ∀ j : ℕ, (hj : j < n) → s.read (base + 1 + j) = inputs ⟨j, hj⟩) :
    ∃ c, Steps (gPhase base n pG i) ⟨0, s⟩ c ∧ c.isHalted (gPhase base n pG i) := by
  -- gPhase = clear ++ (copyRange ++ (pG ++ [T]))
  have hClear_sl := clearRegisters_isStraightLine base
  have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
  have hT_sl := single_T_isStraightLine' 0 (base + n + 1 + i)

  -- Clear halts
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves⟩ :=
    clearRegisters_exec base s

  -- After clear, saved inputs still there
  have hSaved_after_clear : ∀ j : ℕ, (hj : j < n) → cClear.state.read (base + 1 + j) = inputs ⟨j, hj⟩ :=
    fun j hj => by rw [hClear_preserves (base + 1 + j) (by omega)]; exact hSaved j hj

  -- Copy restored inputs: use straightLine_halts_from_state directly
  have hNoOverlap : base + 1 + n ≤ 0 ∨ 0 + n ≤ base + 1 := Or.inr (by omega)
  obtain ⟨sCopy, hsCopy_eq, hCopy_correct, hCopy_preserves⟩ :=
    copyRegisterRange_state (base + 1) 0 n cClear.state hNoOverlap

  -- Get halting from arbitrary state
  obtain ⟨cCopy, hCopy_steps', hCopy_halted', hCopy_pc⟩ :=
    straightLine_halts_from_state hCopy_sl cClear.state
  -- State equals straightLineFinalState
  have hCopy_state_eq : cCopy.state = straightLineFinalState hCopy_sl cClear.state :=
    straightLineFinalState_eq_of_halted hCopy_sl cClear.state cCopy hCopy_steps' hCopy_halted'
  -- So cCopy.state = sCopy
  have hCopy_state_sCopy : cCopy.state = sCopy := by rw [hCopy_state_eq, hsCopy_eq]

  -- Build steps/halted for target config
  have hCopy_steps : Steps (copyRegisterRange (base + 1) 0 n) ⟨0, cClear.state⟩
      ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ := by
    have : cCopy = ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ := by
      ext <;> simp only [hCopy_pc, hCopy_state_sCopy]
    rw [← this]; exact hCopy_steps'
  have hCopy_halted : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
      (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]

  -- After copy, R[0..n-1] = inputs
  have hInputs_restored : ∀ j : ℕ, (hj : j < n) → sCopy.read j = inputs ⟨j, hj⟩ := by
    intro j hj
    have h1 := hCopy_correct j hj
    simp only [Nat.zero_add] at h1
    rw [h1, hSaved_after_clear j hj]

  -- State agrees with inputs on R[0..pG.maxRegister]
  have hagree : sCopy.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG.maxRegister := by
    intro r _hr0 hr_max
    by_cases hr_n : r < n
    · rw [hInputs_restored r hr_n]
      simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hr_n, ↓reduceDIte, Option.getD_some]
    · -- r ≥ n, both should be 0
      have hr_le_base : r ≤ base := Nat.le_trans hr_max hpG_max
      have hsCopy_r : sCopy.read r = 0 := by
        have h1 : sCopy.read r = cClear.state.read r := hCopy_preserves r (by omega)
        have h2 : cClear.state.read r = 0 := hClear_zeros r (by omega)
        rw [h1, h2]
      have hfromInputs_r : (State.fromInputs (List.ofFn inputs)).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hr_n, ↓reduceDIte, Option.getD_none]
      rw [hsCopy_r, hfromInputs_r]

  -- pG halts from sCopy via agreeing execution
  let epG := Halts.executeFromAgreeingState hpG_halts hpG_sf hagree
  have hpG_steps' := epG.steps
  have hpG_halted' := epG.halted
  have hpG_pc' := epG.pc_eq

  -- T halts
  obtain ⟨cT, hT_steps, hT_halted, hT_pc, _hT_state⟩ :=
    single_transfer_halts 0 (base + n + 1 + i) epG.config.state

  -- Chain: pG ++ T
  have ⟨hPGT_steps, hPGT_halted⟩ := Steps.chain_concat hpG_steps' hpG_halted' hpG_pc' hT_steps hT_halted

  -- Chain: copy ++ (pG ++ T)
  have ⟨hCopyPGT_steps, hCopyPGT_halted⟩ := Steps.chain_concat hCopy_steps hCopy_halted rfl hPGT_steps hPGT_halted

  -- Chain: clear ++ (copy ++ (pG ++ T))
  have ⟨hGPhase_steps, hGPhase_halted⟩ := Steps.chain_concat hClear_steps hClear_halted hClear_pc hCopyPGT_steps hCopyPGT_halted

  exact ⟨_, hGPhase_steps, hGPhase_halted⟩

/-- A single gPhase writes the result of pG to R[base+n+1+j].
This tracks what value gPhase writes, not just that it halts. -/
theorem gPhase_writes_result
    {base n : ℕ} {pG : Program} {j : ℕ}
    {inputs : Fin n → ℕ}
    (hpG_sf : pG.IsStandardForm)
    (hpG_max : pG.maxRegister ≤ base)
    (hn_le_base : n ≤ base + 1)
    (hpG_halts : Halts pG (List.ofFn inputs))
    (s : State)
    (hSaved : ∀ k : ℕ, (hk : k < n) → s.read (base + 1 + k) = inputs ⟨k, hk⟩)
    (c' : Config)
    (hsteps : Steps (gPhase base n pG j) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (gPhase base n pG j)) :
    c'.state.read (base + n + 1 + j) = Result pG (List.ofFn inputs) hpG_halts := by
  -- gPhase = clear ++ (copyRange ++ (pG ++ [T]))
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine base)
  have hCopyRange_sf := straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n)

  -- Extract clear execution and suffix
  obtain ⟨sClear, hClear_steps, ⟨cRest, hRest_steps, hRest_halted⟩⟩ :=
    suffix_of_concat_from_zero hsteps hhalted hClear_sf

  -- Extract copyRange execution and suffix
  obtain ⟨sCopy, hCopy_steps, ⟨cPGT, hPGT_steps, hPGT_halted⟩⟩ :=
    suffix_of_concat_from_zero hRest_steps hRest_halted hCopyRange_sf

  -- Extract pG execution and T
  obtain ⟨sPG, hPG_steps, ⟨cT, hT_steps, hT_halted⟩⟩ :=
    suffix_of_concat_from_zero hPGT_steps hPGT_halted hpG_sf

  -- After clear, saved inputs still there
  have hSaved_after_clear : ∀ k : ℕ, (hk : k < n) → sClear.read (base + 1 + k) = inputs ⟨k, hk⟩ := by
    intro k hk
    have hClear_sl := clearRegisters_isStraightLine base
    have hsClear_eq : sClear = straightLineFinalState hClear_sl s := by
      have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted (clearRegisters base) := by
        simp [Config.isHalted]
      exact straightLineFinalState_eq_of_halted hClear_sl s ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'
    rw [hsClear_eq]
    have hpres := clearRegisters_preserves_above' base s (base + 1 + k) (by omega)
    rw [hpres, hSaved k hk]

  -- After copy, R[0..n-1] = inputs
  have hInputs_after_copy : ∀ k : ℕ, (hk : k < n) → sCopy.read k = inputs ⟨k, hk⟩ := by
    intro k hk
    have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
    have hsCopy_eq : sCopy = straightLineFinalState hCopy_sl sClear := by
      have hCopy_halted' : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
          (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
      exact straightLineFinalState_eq_of_halted hCopy_sl sClear
        ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ hCopy_steps hCopy_halted'
    rw [hsCopy_eq]
    have hNoOverlap : base + 1 + n ≤ 0 ∨ 0 + n ≤ base + 1 := Or.inr (by omega)
    obtain ⟨sCopy', hsCopy'_eq, hCopy_correct, _⟩ := copyRegisterRange_state (base + 1) 0 n sClear hNoOverlap
    rw [← hsCopy'_eq, hCopy_correct k hk]
    simp only [Nat.zero_add]
    exact hSaved_after_clear k hk

  -- State sCopy agrees with inputs on R[0..pG.maxRegister]
  have hagree : sCopy.agreeOn (State.fromInputs (List.ofFn inputs)) 0 pG.maxRegister := by
    intro r _hr0 hr_max
    by_cases hr_n : r < n
    · rw [hInputs_after_copy r hr_n]
      simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hr_n, ↓reduceDIte, Option.getD_some]
    · -- r ≥ n, both should be 0
      have hClear_sl := clearRegisters_isStraightLine base
      have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
      have hsClear_eq : sClear = straightLineFinalState hClear_sl s := by
        have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted (clearRegisters base) := by
          simp [Config.isHalted]
        exact straightLineFinalState_eq_of_halted hClear_sl s ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'
      have hsCopy_eq : sCopy = straightLineFinalState hCopy_sl sClear := by
        have hCopy_halted' : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
            (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
        exact straightLineFinalState_eq_of_halted hCopy_sl sClear
          ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ hCopy_steps hCopy_halted'
      have hr_le_base : r ≤ base := Nat.le_trans hr_max hpG_max
      have hsCopy_r : sCopy.read r = 0 := by
        rw [hsCopy_eq]
        have hNoOverlap : base + 1 + n ≤ 0 ∨ 0 + n ≤ base + 1 := Or.inr (by omega)
        obtain ⟨sCopy', hsCopy'_eq, _, hCopy_preserves⟩ := copyRegisterRange_state (base + 1) 0 n sClear hNoOverlap
        rw [← hsCopy'_eq, hCopy_preserves r (Or.inr (by omega : r ≥ 0 + n))]
        rw [hsClear_eq]
        exact clearRegisters_zeros' base s r (by omega)
      have hfromInputs_r : (State.fromInputs (List.ofFn inputs)).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hr_n, ↓reduceDIte, Option.getD_none]
      rw [hsCopy_r, hfromInputs_r]

  -- pG runs from sCopy via agreeing execution
  let epG := Halts.executeFromAgreeingState hpG_halts hpG_sf hagree

  -- sPG = epG.config.state (by determinism)
  have hsPG_eq : sPG = epG.config.state := by
    have huniq := Steps.halts_unique hPG_steps
      (by simp [Config.isHalted, hpG_sf.pc_eq_length_of_halted] at hPGT_halted ⊢; omega)
      epG.steps epG.halted
    simp only [huniq]

  -- After pG, R[0] = Result pG inputs
  have hR0_after_pG : sPG.read 0 = Result pG (List.ofFn inputs) hpG_halts := by
    rw [hsPG_eq]
    have hmax : 0 ≤ pG.maxRegister := Nat.zero_le _
    rw [AgreeingExecution.output_eq epG hmax]
    simp only [Result, State.output]

  -- T copies R[0] to R[base+n+1+j]
  have hT_result : cT.state.read (base + n + 1 + j) = sPG.read 0 := by
    let tr := executeSingleTransfer 0 (base + n + 1 + j) sPG
    have hcT_eq : cT = tr.config := Steps.halts_unique hT_steps hT_halted tr.steps tr.halted
    simp only [hcT_eq, SingleTransferResult.config, SingleTransferResult.state]
    simp only [State.write, State.read]
    simp only [ite_true]

  -- Chain state equalities
  -- c' has the same state as cT (modulo pc)
  have hc'_state_eq : c'.state = cT.state := by
    -- Use determinism: both c' and our chain reach the same final state
    have hPG_halted : (⟨pG.length, sPG⟩ : Config).isHalted pG := by simp [Config.isHalted]
    have hPGT_combined := Steps.chain_concat hPG_steps hPG_halted rfl hT_steps hT_halted
    have hCopy_halted : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
        (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
    have hCopyPGT_combined := Steps.chain_concat hCopy_steps hCopy_halted rfl hPGT_steps hPGT_halted
    have hClear_halted : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
        (clearRegisters base) := by simp [Config.isHalted]
    have hClearRest_combined := Steps.chain_concat hClear_steps hClear_halted rfl hRest_steps hRest_halted
    have huniq := Steps.halts_unique hsteps hhalted hClearRest_combined.1 hClearRest_combined.2
    rw [huniq]
    -- Now show cRest.state = cT.state through the chain
    have hcRest_eq : cRest.state = cPGT.state := by
      have huniq := Steps.halts_unique hRest_steps hRest_halted hCopyPGT_combined.1 hCopyPGT_combined.2
      rw [huniq]
    have hcPGT_eq : cPGT.state = cT.state := by
      have huniq := Steps.halts_unique hPGT_steps hPGT_halted hPGT_combined.1 hPGT_combined.2
      rw [huniq]
    rw [hcRest_eq, hcPGT_eq]

  rw [hc'_state_eq, hT_result, hR0_after_pG]

/-- All gPhases halt from a state where R[base+1..base+n] contain the inputs.
This is proved by induction on the number of phases. -/
theorem allGPhases_halts_from_saved_inputs
    {m n : ℕ} {base : ℕ} {pGs : Fin m → Program}
    {inputs : Fin n → ℕ}
    (hpGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hpGs_max : ∀ i, (pGs i).maxRegister ≤ base)
    (hn_le_base : n ≤ base + 1)
    (hpGs_halts : ∀ i, Halts (pGs i) (List.ofFn inputs))
    (s : State)
    (hSaved : ∀ j : ℕ, (hj : j < n) → s.read (base + 1 + j) = inputs ⟨j, hj⟩) :
    ∃ c, Steps (allGPhases m n base pGs) ⟨0, s⟩ c ∧ c.isHalted (allGPhases m n base pGs) := by
  -- Induction on m (number of phases)
  induction m with
  | zero =>
    -- Empty program halts immediately
    simp only [allGPhases, List.finRange_zero, List.foldl_nil]
    exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, by simp [Config.isHalted]⟩
  | succ m' ih =>
    -- allGPhases (m'+1) = allGPhases m' ++ gPhase (Fin.last m')
    simp only [allGPhases]
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map, List.foldl_cons, List.foldl_nil]

    -- Define pGs' = pGs restricted to Fin m' via castSucc
    let pGs' : Fin m' → Program := fun i => pGs i.castSucc

    -- The inner foldl equals allGPhases m' n base pGs'
    have hPrefix_eq : List.foldl (fun x y => x.concat (gPhase base n (pGs y.castSucc) ↑y.castSucc))
        [] (List.finRange m') = allGPhases m' n base pGs' := by
      unfold allGPhases
      congr 1
      funext acc i
      simp only [pGs', Fin.coe_castSucc]

    rw [hPrefix_eq]

    -- Apply IH to get prefix halts
    have hpGs'_sf : ∀ i, (pGs' i).IsStandardForm := fun i => hpGs_sf i.castSucc
    have hpGs'_max : ∀ i, (pGs' i).maxRegister ≤ base := fun i => hpGs_max i.castSucc
    have hpGs'_halts : ∀ i, Halts (pGs' i) (List.ofFn inputs) := fun i => hpGs_halts i.castSucc

    obtain ⟨cPrefix, hPrefix_steps, hPrefix_halted⟩ := ih hpGs'_sf hpGs'_max hpGs'_halts s hSaved

    -- Get prefix pc and standard form
    have hPrefix_sf : (allGPhases m' n base pGs').IsStandardForm := allGPhases_isStandardForm hpGs'_sf
    have hPrefix_pc : cPrefix.pc = (allGPhases m' n base pGs').length :=
      hPrefix_sf.pc_eq_length_of_halted hPrefix_halted

    -- Saved inputs preserved after prefix (use preservation lemma)
    have hSaved_after_prefix : ∀ j : ℕ, (hj : j < n) → cPrefix.state.read (base + 1 + j) = inputs ⟨j, hj⟩ := by
      intro j hj
      exact allGPhases_prefix_preserves_saved_inputs m' n base pGs' hpGs'_sf hpGs'_max hn_le_base
        m' (Nat.le_refl m') s cPrefix.state cPrefix hPrefix_steps hPrefix_halted rfl
        (base + 1 + j) (by omega) (by omega)
        ▸ hSaved j hj

    -- gPhase (Fin.last m') halts from cPrefix.state
    have hLast_halts := gPhase_halts_from_saved_inputs
      (hpGs_sf (Fin.last m'))
      (hpGs_max (Fin.last m'))
      hn_le_base
      (hpGs_halts (Fin.last m'))
      cPrefix.state
      hSaved_after_prefix
    obtain ⟨cLast, hLast_steps, hLast_halted⟩ := hLast_halts

    -- Chain prefix with last gPhase
    have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hPrefix_steps hPrefix_halted hPrefix_pc
      hLast_steps hLast_halted

    exact ⟨_, hTotal_steps, hTotal_halted⟩

/-- Final phase halts from a state where R[base+n+1..base+n+m] contain the results. -/
theorem finalPhase_halts_from_results
    {m n : ℕ} {base : ℕ} {pF : Program}
    {results : Fin m → ℕ}
    (hpF_sf : pF.IsStandardForm)
    (hpF_max : pF.maxRegister ≤ base)
    (hm_le_base : m ≤ base + 1)
    (hpF_halts : Halts pF (List.ofFn results))
    (s : State)
    (hResults : ∀ j : ℕ, (hj : j < m) → s.read (base + n + 1 + j) = results ⟨j, hj⟩) :
    ∃ c, Steps (finalPhase m n base pF) ⟨0, s⟩ c ∧ c.isHalted (finalPhase m n base pF) := by
  -- finalPhase = clear ++ (transfer ++ pF)
  have hClear_sl := clearRegisters_isStraightLine base
  have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m

  -- Clear halts
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves⟩ :=
    clearRegisters_exec base s

  -- After clear, results still there
  have hResults_after_clear : ∀ j : ℕ, (hj : j < m) → cClear.state.read (base + n + 1 + j) = results ⟨j, hj⟩ :=
    fun j hj => by rw [hClear_preserves (base + n + 1 + j) (by omega)]; exact hResults j hj

  -- Transfer halts and sets up inputs: use straightLine_halts_from_state directly
  have hNoOverlap : m ≤ base + n + 1 := by omega
  obtain ⟨sTransfer, hsTransfer_eq, hTransfer_correct, hTransfer_preserves⟩ :=
    transferResultsToInputs_state (base + n + 1) m cClear.state hNoOverlap

  -- Get halting from arbitrary state
  obtain ⟨cTransfer, hTransfer_steps', hTransfer_halted', hTransfer_pc⟩ :=
    straightLine_halts_from_state hTransfer_sl cClear.state
  -- State equals straightLineFinalState
  have hTransfer_state_eq : cTransfer.state = straightLineFinalState hTransfer_sl cClear.state :=
    straightLineFinalState_eq_of_halted hTransfer_sl cClear.state cTransfer hTransfer_steps' hTransfer_halted'
  -- So cTransfer.state = sTransfer
  have hTransfer_state_sTransfer : cTransfer.state = sTransfer := by rw [hTransfer_state_eq, hsTransfer_eq]

  -- Build steps/halted for target config
  have hTransfer_steps : Steps (transferResultsToInputs (base + n + 1) m) ⟨0, cClear.state⟩
      ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
    have : cTransfer = ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
      ext <;> simp only [hTransfer_pc, hTransfer_state_sTransfer]
    rw [← this]; exact hTransfer_steps'
  have hTransfer_halted : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).isHalted
      (transferResultsToInputs (base + n + 1) m) := by simp [Config.isHalted]

  -- After transfer, R[0..m-1] = results
  have hInputs_set : ∀ j : ℕ, (hj : j < m) → sTransfer.read j = results ⟨j, hj⟩ := by
    intro j hj
    rw [hTransfer_correct j hj, hResults_after_clear j hj]

  -- State agrees with results on R[0..pF.maxRegister]
  have hagree : sTransfer.agreeOn (State.fromInputs (List.ofFn results)) 0 pF.maxRegister := by
    intro r _hr0 hr_max
    by_cases hr_m : r < m
    · rw [hInputs_set r hr_m]
      simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hr_m, ↓reduceDIte, Option.getD_some]
    · -- r ≥ m, both should be 0
      have hr_le_base : r ≤ base := Nat.le_trans hr_max hpF_max
      have hsTransfer_r : sTransfer.read r = 0 := by
        rw [hTransfer_preserves r (by omega), hClear_zeros r (by omega)]
      have hfromResults_r : (State.fromInputs (List.ofFn results)).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hr_m, ↓reduceDIte, Option.getD_none]
      rw [hsTransfer_r, hfromResults_r]

  -- pF halts from sTransfer via agreeing execution
  let epF := Halts.executeFromAgreeingState hpF_halts hpF_sf hagree
  have hpF_steps' := epF.steps
  have hpF_halted' := epF.halted

  -- Chain: transfer ++ pF
  have hTransfer_pc : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).pc =
      (transferResultsToInputs (base + n + 1) m).length := rfl
  have ⟨hTransferF_steps, hTransferF_halted⟩ := Steps.chain_concat hTransfer_steps hTransfer_halted
    hTransfer_pc hpF_steps' hpF_halted'

  -- Chain: clear ++ (transfer ++ pF)
  have ⟨hFinal_steps, hFinal_halted⟩ := Steps.chain_concat hClear_steps hClear_halted hClear_pc
    hTransferF_steps hTransferF_halted

  exact ⟨_, hFinal_steps, hFinal_halted⟩

/-- Suffix of allGPhases preserves result registers R[base+n+1+k] for k < start index.
This is because each phase j in the suffix writes only to R[base+n+1+j] where j ≥ start. -/
theorem allGPhases_suffix_preserves_earlier_results
    {m n : ℕ} {base : ℕ} {pGs : Fin m → Program}
    (hpGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hpGs_max : ∀ i, (pGs i).maxRegister ≤ base)
    (hn_le_base : n ≤ base + 1)
    (start k : ℕ) (hk_lt_start : k < start)
    (s : State) (c' : Config)
    (hsteps : Steps (allGPhases_suffix m n base pGs start) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (allGPhases_suffix m n base pGs start)) :
    c'.state.read (base + n + 1 + k) = s.read (base + n + 1 + k) := by
  -- Induction on the number of phases in suffix
  induction m generalizing start s c' with
  | zero =>
    simp only [allGPhases_suffix, List.finRange_zero, List.drop_nil, List.foldl_nil] at hsteps hhalted
    have hc'_eq : c' = ⟨0, s⟩ := by
      have h : Steps [] ⟨0, s⟩ ⟨0, s⟩ := Relation.ReflTransGen.refl
      have hh : (⟨0, s⟩ : Config).isHalted [] := by simp [Config.isHalted]
      exact Steps.halts_unique hsteps hhalted h hh
    rw [hc'_eq]
  | succ m' ih =>
    by_cases hEmpty : start ≥ m' + 1
    · -- Suffix is empty
      simp only [allGPhases_suffix, List.drop_eq_nil_of_le (by simp; omega), List.foldl_nil] at hsteps hhalted
      have hc'_eq : c' = ⟨0, s⟩ := by
        have h : Steps [] ⟨0, s⟩ ⟨0, s⟩ := Relation.ReflTransGen.refl
        have hh : (⟨0, s⟩ : Config).isHalted [] := by simp [Config.isHalted]
        exact Steps.halts_unique hsteps hhalted h hh
      rw [hc'_eq]
    · push_neg at hEmpty
      -- Suffix = gPhase start ++ rest_suffix
      have hSuffix_decomp : allGPhases_suffix (m' + 1) n base pGs start =
          (gPhase base n (pGs ⟨start, hEmpty⟩) start).concat
          (allGPhases_suffix (m' + 1) n base pGs (start + 1)) := by
        simp only [allGPhases_suffix]
        have hDrop : (List.finRange (m' + 1)).drop start =
            (List.finRange (m' + 1))[start]'(by simp; exact hEmpty) ::
            (List.finRange (m' + 1)).drop (start + 1) := by
          rw [List.drop_eq_getElem_cons (by simp; exact hEmpty)]
        rw [hDrop, List.foldl_cons]
        rw [foldl_concat_eq_acc_concat]
        congr 1
        simp [List.getElem_finRange]

      rw [hSuffix_decomp] at hsteps hhalted
      have hGPhase_sf := gPhase_isStandardForm (hpGs_sf ⟨start, hEmpty⟩)
      obtain ⟨sFirst, hFirst_steps, ⟨cRest, hRest_steps, hRest_halted⟩⟩ :=
        suffix_of_concat_from_zero hsteps hhalted hGPhase_sf

      -- gPhase start preserves R[base+n+1+k] since start ≠ k (start > k)
      have hFirst_preserves : sFirst.read (base + n + 1 + k) = s.read (base + n + 1 + k) := by
        have hFirst_halted : (⟨(gPhase base n (pGs ⟨start, hEmpty⟩) start).length, sFirst⟩ : Config).isHalted
            (gPhase base n (pGs ⟨start, hEmpty⟩) start) := by
          simp [Config.isHalted]
        exact (gPhase_preserves_other_results base n (pGs ⟨start, hEmpty⟩) start k
          (hpGs_sf _) (hpGs_max _) hn_le_base (by omega)
          s sFirst ⟨_, sFirst⟩ hFirst_steps hFirst_halted rfl).symm

      -- IH: rest_suffix preserves R[base+n+1+k]
      have hRest_preserves : cRest.state.read (base + n + 1 + k) = sFirst.read (base + n + 1 + k) := by
        have hk_lt_start' : k < start + 1 := by omega
        -- For suffixes starting at start+1, we need to adjust
        -- The rest suffix is allGPhases_suffix (m'+1) n base pGs (start+1)
        -- This is the same as allGPhases_suffix but with a later start
        -- Apply IH recursively

        -- Since hRest_steps/halted are for suffix starting at start+1,
        -- and we have k < start+1, the recursion applies
        exact allGPhases_suffix_preserves_earlier_results hpGs_sf hpGs_max hn_le_base
          (start + 1) k hk_lt_start' sFirst cRest hRest_steps hRest_halted

      -- c'.state = cRest.state by determinism
      have hc'_eq_cRest : c'.state = cRest.state := by
        have hChain := Steps.chain_concat hFirst_steps
          (by simp [Config.isHalted])
          rfl hRest_steps hRest_halted
        have huniq := Steps.halts_unique hsteps hhalted hChain.1 hChain.2
        rw [huniq]

      rw [hc'_eq_cRest, hRest_preserves, hFirst_preserves]
termination_by (m' + 1) - start
decreasing_by simp_wf; omega

set_option maxHeartbeats 400000 in
/-- After saveInputs ++ allGPhases halts, R[base+n+1+i] contains the result of g_i.
This is the key lemma for tracking how gPhase saves each result. -/
theorem allGPhases_saves_result
    {m n : ℕ} [NeZero m]
    {pF : Program} {pGs : Fin m → Program}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hGs_dom : ∀ i, (gs i inputs).Dom)
    (i : Fin m)
    (sSaveGPhases : State)
    (hSaveGPhases_halted : ∃ c : Config,
      Steps ((copyRegisterRange 0 (compositionBase m n pF pGs + 1) n).concat
             (allGPhases m n (compositionBase m n pF pGs) pGs))
        ⟨0, State.fromInputs (List.ofFn inputs)⟩ c ∧
      c.isHalted ((copyRegisterRange 0 (compositionBase m n pF pGs + 1) n).concat
                  (allGPhases m n (compositionBase m n pF pGs) pGs)) ∧
      c.state = sSaveGPhases) :
    sSaveGPhases.read (compositionBase m n pF pGs + n + 1 + i.val) =
      (gs i inputs).get (hGs_dom i) := by
  -- Setup
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  obtain ⟨c, hsteps, hhalted, hstate_eq⟩ := hSaveGPhases_halted

  -- We use allGPhases_split to decompose: allGPhases m = prefix(i+1) ++ suffix(i+1)
  -- where prefix(i+1) contains phases 0..i (so gPhase i is the last phase in prefix)
  have hSplit : allGPhases m n base pGs =
      (allGPhases_prefix m n base pGs (i.val + 1)).concat
      (allGPhases_suffix m n base pGs (i.val + 1)) :=
    allGPhases_split m n base pGs (i.val + 1) (Nat.lt_iff_add_one_le.mp i.isLt)

  -- Standard form facts
  have hSave_sf := saveInputs_isStandardForm base n
  have hPrefix_sf := allGPhases_prefix_isStandardForm hGs_sf (i.val + 1)
  have hSuffix_sf := allGPhases_suffix_isStandardForm hGs_sf (i.val + 1)

  -- Rewrite the program
  have hProg_eq : saveInputs.concat (allGPhases m n base pGs) =
      (saveInputs.concat (allGPhases_prefix m n base pGs (i.val + 1))).concat
      (allGPhases_suffix m n base pGs (i.val + 1)) := by
    rw [hSplit, concat_assoc]

  -- Get execution up to prefix (including gPhase i)
  have hSavePrefix_sf := hSave_sf.concat hPrefix_sf
  have hSuffixStart : Steps (saveInputs.concat (allGPhases m n base pGs))
      ⟨0, State.fromInputs (List.ofFn inputs)⟩ c := hsteps
  rw [hProg_eq] at hSuffixStart hhalted

  obtain ⟨sSavePrefix, hSavePrefix_steps, ⟨cSuffix, hSuffix_steps, hSuffix_halted⟩⟩ :=
    suffix_of_concat_from_zero hSuffixStart hhalted hSavePrefix_sf

  -- Now show R[base+n+1+i] has correct value after prefix and is preserved by suffix

  -- Part 1: Extract execution of gPhase i from the end of prefix
  -- prefix(i+1) = prefix(i) ++ gPhase i
  have hPrefixDecomp : allGPhases_prefix m n base pGs (i.val + 1) =
      (allGPhases_prefix m n base pGs i.val).concat (gPhase base n (pGs i) i.val) := by
    simp only [allGPhases_prefix]
    have hTake : (List.finRange m).take (i.val + 1) =
        (List.finRange m).take i.val ++ [(List.finRange m)[i.val]'(by simp; exact i.isLt)] := by
      rw [List.take_succ]
      simp only [List.getElem?_eq_getElem (by simp; exact i.isLt)]
    rw [hTake, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [foldl_concat_eq_acc_concat]
    congr 1
    · rfl
    · simp [List.getElem_finRange]

  have hSavePrefixI_sf := hSave_sf.concat (allGPhases_prefix_isStandardForm hGs_sf i.val)
  have hGPhase_i_sf := gPhase_isStandardForm (hGs_sf i)

  -- Rewrite saveInputs ++ prefix(i+1) = (saveInputs ++ prefix(i)) ++ gPhase i
  have hSavePrefix_eq : saveInputs.concat (allGPhases_prefix m n base pGs (i.val + 1)) =
      (saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat
      (gPhase base n (pGs i) i.val) := by
    rw [hPrefixDecomp, concat_assoc]

  rw [hSavePrefix_eq] at hSavePrefix_steps

  -- Extract gPhase i execution from the end of saveInputs ++ prefix(i+1)
  have hSavePrefixI_halted : (⟨(saveInputs.concat (allGPhases_prefix m n base pGs i.val)).length, sSavePrefix⟩ : Config).isHalted
      (saveInputs.concat (allGPhases_prefix m n base pGs i.val)) := by
    simp [Config.isHalted]

  obtain ⟨sSavePrefixI, hSavePrefixI_steps, ⟨cGPhase_i, hGPhase_i_steps, hGPhase_i_halted⟩⟩ :=
    suffix_of_concat_from_zero hSavePrefix_steps hSavePrefixI_halted hSavePrefixI_sf

  -- Part 2: Show that sSavePrefix (after gPhase i) has R[base+n+1+i] = result of g_i
  -- First, show saved inputs are preserved up to the start of gPhase i
  have hpGs_max : ∀ j, (pGs j).maxRegister ≤ base := fun j => compositionBase_ge_pGs_max m n pF pGs j
  have hn_le_base : n ≤ base + 1 := compositionBase_ge_n m n pF pGs

  have hSaved_i : ∀ k : ℕ, (hk : k < n) → sSavePrefixI.read (base + 1 + k) = inputs ⟨k, hk⟩ := by
    intro k hk
    -- Show that saved inputs are preserved through saveInputs ++ prefix(i)
    -- First, saveInputs saves the inputs
    -- Then, prefix(i) preserves them
    have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
    have hNoOverlap : 0 + n ≤ base + 1 := by omega
    obtain ⟨sSave, hsSave_eq, hSave_copies, hSave_preserves⟩ :=
      copyRegisterRange_state 0 (base + 1) n (State.fromInputs (List.ofFn inputs)) (Or.inr hNoOverlap)

    -- After saveInputs: R[base+1+k] = inputs[k]
    have hAfterSave : sSave.read (base + 1 + k) = inputs ⟨k, hk⟩ := by
      rw [hSave_copies k hk]
      simp only [State.fromInputs, State.read, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hk, ↓reduceDIte, Option.getD_some]

    -- Get the state after saveInputs
    have hSave_halts := straightLine_halts hSave_sl (List.ofFn inputs)
    obtain ⟨cSave, hSave_steps', hSave_halted', hSave_pc'⟩ :=
      straightLine_halts_from_state hSave_sl (State.fromInputs (List.ofFn inputs))
    have hSave_state_eq : cSave.state = straightLineFinalState hSave_sl (State.fromInputs (List.ofFn inputs)) :=
      straightLineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps' hSave_halted'
    have hSave_state_sSave : cSave.state = sSave := by rw [hSave_state_eq, hsSave_eq]

    -- Then prefix(i) preserves saved inputs
    by_cases hi_zero : i.val = 0
    · -- prefix(0) is empty, so sSavePrefixI = cSave.state
      simp only [hi_zero, allGPhases_prefix, List.take_zero, List.foldl_nil, concat_nil_right] at hSavePrefixI_steps hSavePrefixI_halted
      have hSavePrefixI_eq : sSavePrefixI = sSave := by
        have hSave_halted'' : (⟨saveInputs.length, sSave⟩ : Config).isHalted saveInputs := by
          simp [Config.isHalted]
        have hSave_steps'' : Steps saveInputs ⟨0, State.fromInputs (List.ofFn inputs)⟩ ⟨saveInputs.length, sSave⟩ := by
          have : cSave = ⟨saveInputs.length, sSave⟩ := by
            ext <;> simp only [hSave_pc', hSave_state_sSave, copyRegisterRange_length]
          rw [← this]; exact hSave_steps'
        have huniq := Steps.halts_unique hSavePrefixI_steps hSavePrefixI_halted hSave_steps'' hSave_halted''
        simp only [huniq]
      rw [hSavePrefixI_eq, hAfterSave]
    · -- prefix(i) is non-empty, use allGPhases_prefix_preserves_saved_inputs
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi_zero
      let pGs' : Fin i.val → Program := fun j => pGs (j.castLE (Nat.le_of_lt i.isLt))
      have hpGs'_sf : ∀ j, (pGs' j).IsStandardForm := fun j => hGs_sf _
      have hpGs'_max : ∀ j, (pGs' j).maxRegister ≤ base := fun j => hpGs_max _

      -- Use existing preservation lemma
      have hprefix_i_eq : allGPhases_prefix m n base pGs i.val = allGPhases i.val n base pGs' := by
        simp only [allGPhases_prefix, allGPhases]
        congr 1
        · rw [List.finRange_take (by exact i.isLt)]
          simp only [List.map_inj_left]
          intro a _
          simp only [pGs', Fin.castLE, Fin.coe_castSucc]
        · funext acc j
          simp only [pGs', Fin.castLE, Fin.coe_castSucc]

      have hPrefix_i_preserves := allGPhases_prefix_preserves_saved_inputs i.val n base pGs'
        hpGs'_sf hpGs'_max hn_le_base i.val (Nat.le_refl i.val)

      -- Need to track through the execution to apply this
      -- For simplicity, use the combined preservation
      rw [hprefix_i_eq] at hSavePrefixI_sf hSavePrefixI_steps

      -- Get execution: saveInputs halts, then allGPhases i.val halts
      have hSaveGPrefixI := Steps.chain_concat
        (by have : cSave = ⟨saveInputs.length, sSave⟩ := by
              ext <;> simp only [hSave_pc', hSave_state_sSave, copyRegisterRange_length]
            rw [← this]; exact hSave_steps')
        (by simp [Config.isHalted])
        (by simp [copyRegisterRange_length])
        (by -- Steps for allGPhases i.val
            obtain ⟨cAG, hAG_steps, hAG_halted⟩ := allGPhases_halts_from_saved_inputs
              hpGs'_sf hpGs'_max hn_le_base
              (fun j => (hGs_spec (j.castLE (Nat.le_of_lt i.isLt)) inputs).1.mpr (hGs_dom _))
              sSave
              (fun j hj => hAfterSave j hj)
            exact hAG_steps)
        (by -- halted
            obtain ⟨cAG, hAG_steps, hAG_halted⟩ := allGPhases_halts_from_saved_inputs
              hpGs'_sf hpGs'_max hn_le_base
              (fun j => (hGs_spec (j.castLE (Nat.le_of_lt i.isLt)) inputs).1.mpr (hGs_dom _))
              sSave
              (fun j hj => hAfterSave j hj)
            exact hAG_halted)

      -- Extract the final state equality
      have hSavePrefixI_halted' : (⟨(saveInputs.concat (allGPhases i.val n base pGs')).length, sSavePrefixI⟩ : Config).isHalted
          (saveInputs.concat (allGPhases i.val n base pGs')) := by
        simp [Config.isHalted]

      -- Use preservation from allGPhases
      obtain ⟨cAG, hAG_steps, hAG_halted⟩ := allGPhases_halts_from_saved_inputs
        hpGs'_sf hpGs'_max hn_le_base
        (fun j => (hGs_spec (j.castLE (Nat.le_of_lt i.isLt)) inputs).1.mpr (hGs_dom _))
        sSave
        (fun j hj => hAfterSave j hj)

      have hAG_preserves := hPrefix_i_preserves sSave cAG.state cAG hAG_steps hAG_halted rfl (base + 1 + k) (by omega) (by omega)

      -- Connect sSavePrefixI to cAG.state
      have hfinal_eq : sSavePrefixI = cAG.state := by
        have hChain := hSaveGPrefixI
        have huniq := Steps.halts_unique hSavePrefixI_steps hSavePrefixI_halted' hChain.1 hChain.2
        simp only [huniq]

      rw [hfinal_eq, ← hAG_preserves, hAfterSave]

  -- Now apply gPhase_writes_result
  have hGPhase_halts_i := (hGs_spec i inputs).1.mpr (hGs_dom i)

  have hGPhase_i_result := gPhase_writes_result
    (hGs_sf i) (hpGs_max i) hn_le_base hGPhase_halts_i
    sSavePrefixI hSaved_i cGPhase_i hGPhase_i_steps hGPhase_i_halted

  -- Part 3: Show that suffix preserves R[base+n+1+i]
  -- The suffix contains phases i+1..m-1, each of which preserves R[base+n+1+i]
  have hSuffix_preserves : cSuffix.state.read (base + n + 1 + i.val) = sSavePrefix.read (base + n + 1 + i.val) := by
    -- Use the helper lemma: suffix starting at (i+1) preserves register i
    have hi_lt : i.val < i.val + 1 := by omega
    exact allGPhases_suffix_preserves_earlier_results hGs_sf hpGs_max hn_le_base
      (i.val + 1) i.val hi_lt sSavePrefix cSuffix hSuffix_steps hSuffix_halted

  -- Connect sSavePrefix to cGPhase_i final state
  have hSavePrefix_eq_cGPhase_i : sSavePrefix = cGPhase_i.state := by
    -- sSavePrefix is the final state of saveInputs ++ prefix(i+1)
    -- cGPhase_i is the final config of gPhase i starting from sSavePrefixI
    -- By the structure, sSavePrefix = cGPhase_i.state

    -- Use the fact that saveInputs ++ prefix(i+1) = (saveInputs ++ prefix(i)) ++ gPhase i
    -- and the execution was split exactly this way
    have hSavePrefixI_halted' : (⟨(saveInputs.concat (allGPhases_prefix m n base pGs i.val)).length, sSavePrefixI⟩ : Config).isHalted
        (saveInputs.concat (allGPhases_prefix m n base pGs i.val)) := by
      simp [Config.isHalted]
    have hGPhase_i_halted' : (⟨(gPhase base n (pGs i) i.val).length, cGPhase_i.state⟩ : Config).isHalted
        (gPhase base n (pGs i) i.val) := by
      have hpc := hGPhase_i_sf.pc_eq_length_of_halted hGPhase_i_halted
      simp [Config.isHalted, hpc]
    have hChain := Steps.chain_concat hSavePrefixI_steps hSavePrefixI_halted'
      (by simp) hGPhase_i_steps hGPhase_i_halted
    -- hChain shows Steps for saveInputs ++ prefix(i+1), final state is cGPhase_i.state
    -- hSavePrefix_steps also gives Steps for the same program, final state is sSavePrefix
    have hSavePrefix_halted' : (⟨(saveInputs.concat (allGPhases_prefix m n base pGs (i.val + 1))).length, sSavePrefix⟩ : Config).isHalted
        (saveInputs.concat (allGPhases_prefix m n base pGs (i.val + 1))) := by
      simp [Config.isHalted]
    rw [hSavePrefix_eq] at hSavePrefix_halted'
    have huniq := Steps.halts_unique hSavePrefix_steps hSavePrefix_halted' hChain.1 hChain.2
    simp only at huniq
    rw [huniq]

  -- Final chain
  rw [← hstate_eq, ← hSuffix_preserves, hSavePrefix_eq_cGPhase_i, hGPhase_i_result]

  -- Now show Result pG inputs hpG_halts = (gs i inputs).get (hGs_dom i)
  have hResult_eq := (hGs_spec i inputs).2 hGPhase_halts_i (hGs_dom i)
  rw [hResult_eq]

/-! ## Main Theorem -/

/-- The composed function for general composition.
h(x) = f(g₁(x), ..., gₘ(x)) -/
def compFunction (m n : ℕ) (f : (Fin m → ℕ) → Part ℕ) (gs : Fin m → (Fin n → ℕ) → Part ℕ)
    (x : Fin n → ℕ) : Part ℕ :=
  (Part.sequence (fun i => gs i x)).bind f

set_option maxHeartbeats 400000 in
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
  -- Set up base register
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF

  -- Standard form facts
  have hSaveInputs_sf := saveInputs_isStandardForm base n
  have hGPhases_sf : gPhases.IsStandardForm := allGPhases_isStandardForm hGs_sf
  have hGPhase_i_sf : (gPhase base n (pGs i) i.val).IsStandardForm :=
    gPhase_isStandardForm (hGs_sf i)

  -- The program structure: H = saveInputs ++ gPhases ++ final
  have hH_eq : Program.composeGeneral m n pF pGs = saveInputs.concat (gPhases.concat final) := rfl

  -- Split allGPhases at position i.val: allGPhases = prefix(i) ++ gPhase(i) ++ suffix(i+1)
  -- Actually: prefix(i) ++ suffix(i) where suffix(i) starts with gPhase(i)
  have hGPhases_split := allGPhases_split m n base pGs i.val (Nat.le_of_lt i.isLt)
  have hPrefix_i_sf : (allGPhases_prefix m n base pGs i.val).IsStandardForm :=
    allGPhases_prefix_isStandardForm hGs_sf i.val
  have hSuffix_i_sf : (allGPhases_suffix m n base pGs i.val).IsStandardForm :=
    allGPhases_suffix_isStandardForm hGs_sf i.val

  -- saveInputs ++ prefix(i) is standard form
  have hSavePrefix_sf := hSaveInputs_sf.concat hPrefix_i_sf

  -- Rewrite program as (saveInputs ++ gPhases) ++ final
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  rw [hH_eq, ← concat_assoc] at hHalts

  -- Extract: saveInputs ++ gPhases halts (as prefix of full program)
  have hSaveGPhases_halts := Halts.prefix_of_concat_sf hHalts hSaveGPhases_sf

  -- Unfold gPhases as prefix(i) ++ suffix(i)
  -- saveInputs ++ gPhases = saveInputs ++ (prefix ++ suffix) = (saveInputs ++ prefix) ++ suffix
  have hSaveGPhases_eq : saveInputs.concat gPhases =
      (saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat
        (allGPhases_suffix m n base pGs i.val) := by
    show saveInputs.concat (allGPhases m n base pGs) = _
    rw [hGPhases_split, concat_assoc]
  rw [hSaveGPhases_eq] at hSaveGPhases_halts

  -- Extract: saveInputs ++ prefix(i) halts
  have hSavePrefix_halts := Halts.prefix_of_concat_sf hSaveGPhases_halts hSavePrefix_sf

  -- Get suffix execution from (saveInputs ++ prefix)
  obtain ⟨sSavePrefix, _, hsSavePrefix_eq, cSuffix, hSuffix_steps, hSuffix_halted⟩ :=
    Halts.suffix_of_concat_sf hSaveGPhases_halts hSavePrefix_sf

  -- suffix(i) = gPhase(i) ++ rest
  -- gPhase(i) = clear ++ copyRange ++ pGs[i] ++ [T 0 (base+n+1+i)]
  have hGPhase_i : gPhase base n (pGs i) i.val =
      (clearRegisters base).concat ((copyRegisterRange (base + 1) 0 n).concat
        ((pGs i).concat [Instr.T 0 (base + n + 1 + i.val)])) := rfl

  -- Need to show that suffix(i) starts with gPhase(i)
  -- suffix(i) = foldl over (drop i (finRange m)) starting from []
  -- The first element after drop is i itself (when i < m)
  have hSuffix_i_eq : allGPhases_suffix m n base pGs i.val =
      (gPhase base n (pGs i) i.val).concat (allGPhases_suffix m n base pGs (i.val + 1)) := by
    simp only [allGPhases_suffix]
    have hdrop_eq : (List.finRange m).drop i.val = i :: (List.finRange m).drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons]
      · congr 1; simp only [List.finRange, List.getElem_ofFn]
      · simp only [List.length_finRange]; exact i.isLt
    rw [hdrop_eq, List.foldl_cons, concat_nil_left]
    exact foldl_concat_eq_acc_concat _ _ _

  rw [hSuffix_i_eq] at hSuffix_steps hSuffix_halted

  -- Extract gPhase(i) halting from suffix execution
  obtain ⟨_, hGPhase_i_steps, hGPhase_i_halted⟩ :=
    prefix_of_concat_from_zero hSuffix_steps hSuffix_halted hGPhase_i_sf

  -- Now extract pGs[i] from gPhase(i)
  -- gPhase = clear ++ (copyRange ++ (pGs_i ++ [T]))
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine base)
  have hCopyRange_sf := straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n)
  have hT_sl : Program.isStraightLine [Instr.T 0 (base + n + 1 + i.val)] = true := rfl
  have hT_sf : Program.IsStandardForm [Instr.T 0 (base + n + 1 + i.val)] :=
    straightLine_isStandardForm hT_sl

  -- Extract clear halting and state
  obtain ⟨sClear, hClear_steps, ⟨cCopyRest, hCopyRest_steps, hCopyRest_halted⟩⟩ :=
    suffix_of_concat_from_zero hGPhase_i_steps hGPhase_i_halted hClear_sf

  -- Extract copyRange halting and state
  obtain ⟨sCopy, hCopy_steps, ⟨cGiT, hGiT_steps, hGiT_halted⟩⟩ :=
    suffix_of_concat_from_zero hCopyRest_steps hCopyRest_halted hCopyRange_sf

  -- Extract pGs[i] halting from pGs[i] ++ [T]
  obtain ⟨cGi', hGi_steps, hGi_halted⟩ :=
    prefix_of_concat_from_zero hGiT_steps hGiT_halted (hGs_sf i)

  -- Now show state agreement: sCopy agrees with inputs on registers 0..maxRegister(pGs i)
  -- This follows from:
  -- 1. After saveInputs, inputs are in R[base+1..base+n]
  -- 2. After clear (applied to sSavePrefix), R[0..base] = 0
  -- 3. After copyRange, R[0..n-1] = inputs

  -- First, track what's in sSavePrefix (state after saveInputs ++ prefix(i))
  -- The saved inputs in R[base+1..base+n] are preserved through all previous phases

  -- Key insight: After copyRegisterRange in gPhase(i), R[j] for j < n equals saved input[j]
  -- And after clear, R[j] for j >= n and j <= base equals 0

  have hbase_ge : (pGs i).maxRegister ≤ base := compositionBase_ge_Gi m n pF pGs i
  have hbase_ge_n : n - 1 ≤ base := compositionBase_ge_n_sub_one m n pF pGs

  -- The state sCopy has:
  -- - R[j] = inputs[j] for j < n (from copyRange copying R[base+1+j] which has inputs[j])
  -- - R[j] = 0 for n ≤ j ≤ base (preserved from clear)

  -- For agreeing state, we need: for r ≤ maxRegister(pGs i), sCopy.read r = fromInputs(inputs).read r
  have hagreeGi : ∀ r, r ≤ (pGs i).maxRegister →
      sCopy.read r = (State.fromInputs (List.ofFn inputs)).read r := by
    intro r hr
    -- r ≤ maxRegister ≤ base
    have hr_le_base : r ≤ base := Nat.le_trans hr hbase_ge
    -- Two cases: r < n (input register) or r ≥ n (should be 0)
    rcases Nat.lt_or_ge r n with hr_lt_n | hr_ge_n
    · -- r < n: sCopy.read r = inputs[r]
      -- copyRange copied from base+1+r to r
      -- Need to trace: inputs saved to R[base+1+j], then copied back to R[j]

      -- Step 1: sCopy.read r = sClear.read (base+1+r)
      have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
      have hCopy_halted' : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
          (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
      have hsCopy_eq : sCopy = straightLineFinalState hCopy_sl sClear :=
        straightLineFinalState_eq_of_halted hCopy_sl sClear
          ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ hCopy_steps hCopy_halted'

      -- Use copyRegisterRange_state to get the copy property
      have hNoOverlap_copy : (base + 1) + n ≤ 0 ∨ 0 + n ≤ base + 1 := Or.inr (by omega)
      obtain ⟨_, hsCopy_final_eq, hsCopy_copies, _⟩ :=
        copyRegisterRange_state (base + 1) 0 n sClear hNoOverlap_copy
      -- hsCopy_copies : ∀ i, i < n → s'.read (0 + i) = sClear.read ((base + 1) + i)

      have hsCopy_r : sCopy.read r = sClear.read (base + 1 + r) := by
        have hr' := hsCopy_copies r hr_lt_n
        simp only [Nat.zero_add] at hr'
        rw [hsCopy_eq, hsCopy_final_eq]
        convert hr' using 2 <;> omega

      -- Step 2: sClear.read (base+1+r) = sSavePrefix.read (base+1+r)
      -- clearRegisters preserves registers above base
      have hClear_sl := clearRegisters_isStraightLine base
      have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
          (clearRegisters base) := by simp [Config.isHalted]
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sSavePrefix :=
        straightLineFinalState_eq_of_halted hClear_sl sSavePrefix
          ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'

      have hbase_1_r_gt : base < base + 1 + r := by omega
      have hsClear_preserves : sClear.read (base + 1 + r) = sSavePrefix.read (base + 1 + r) := by
        rw [hsClear_eq]
        exact clearRegisters_preserves_above' base sSavePrefix (base + 1 + r) hbase_1_r_gt

      -- Step 3: sSavePrefix.read (base+1+r) = inputs[r]
      -- This requires tracking that inputs are preserved through saveInputs and all prefix phases.
      -- Key insight: R[base+1..base+n] is only written by saveInputs, then preserved by all phases.
      -- - saveInputs writes inputs to R[base+1..base+n]
      -- - Each gPhase clears R[0..base], copies from R[base+1..] to R[0..n-1], runs G, saves to R[base+n+1+j]
      -- - None of these touch R[base+1..base+n]

      -- For now, we need to trace through the prefix execution.
      -- This is complex and requires induction over the prefix phases.
      -- The key lemma needed: for any sequence of gPhases, R[base+1..base+n] is preserved.

      -- Simplified approach: use that sSavePrefix is the result of saveInputs ++ prefix(i)
      -- and show the preservation property holds.

      -- The RHS value: (State.fromInputs l).read r = l.getD r 0
      -- For List.ofFn inputs with r < n: (List.ofFn inputs).getD r 0 = inputs ⟨r, _⟩
      have hRHS : (State.fromInputs (List.ofFn inputs)).read r = inputs ⟨r, hr_lt_n⟩ := by
        simp only [State.fromInputs, State.read]
        -- Use List.getD_eq_getElem from Mathlib to convert getD to getElem
        rw [List.getD_eq_getElem (List.ofFn inputs) 0 (by simp; exact hr_lt_n), List.getElem_ofFn]

      rw [hsCopy_r, hsClear_preserves, hRHS]

      -- Now need: sSavePrefix.read (base + 1 + r) = inputs ⟨r, hr_lt_n⟩

      -- sSavePrefix is the state after (saveInputs ++ prefix(i)) halts
      -- Split execution: saveInputs halts, then prefix(i) halts

      -- Get the Halts for saveInputs ++ prefix(i)
      -- hSavePrefix_halts : Halts (saveInputs ++ prefix(i)) inputs
      obtain ⟨sSave, hSave_steps, ⟨cPrefix, hPrefix_steps, hPrefix_halted⟩⟩ :=
        suffix_of_concat_from_zero hSavePrefix_halts.choose_spec.1
          hSavePrefix_halts.choose_spec.2 hSaveInputs_sf

      -- After saveInputs, R[base+1+r] = inputs[r]
      have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
      have hSave_halted' : (⟨(copyRegisterRange 0 (base + 1) n).length, sSave⟩ : Config).isHalted
          (copyRegisterRange 0 (base + 1) n) := by simp [Config.isHalted]
      have hsSave_eq : sSave = straightLineFinalState hSave_sl (State.fromInputs (List.ofFn inputs)) :=
        straightLineFinalState_eq_of_halted hSave_sl (State.fromInputs (List.ofFn inputs))
          ⟨(copyRegisterRange 0 (base + 1) n).length, sSave⟩ hSave_steps hSave_halted'

      -- prefix(i) preserves R[base+1+r]
      have hpGs_max : ∀ j, (pGs j).maxRegister ≤ base := fun j => compositionBase_ge_Gi m n pF pGs j
      have hn_le_base : n ≤ base + 1 := by
        have h := compositionBase_ge_n_sub_one m n pF pGs
        omega

      have hSave_value := saveInputs_state base n hn_le_base inputs r hr_lt_n
      -- Rewrite hSave_value to use sSave instead of straightLineFinalState
      have hsSave_value : sSave.read (base + 1 + r) = inputs ⟨r, hr_lt_n⟩ := by
        rw [hsSave_eq]; exact hSave_value

      -- Show sSavePrefix = cPrefix.state (state after prefix halts)
      have hPrefix_state_match : cPrefix.state = sSavePrefix := by
        -- cPrefix comes from suffix_of_concat_from_zero on hSavePrefix_halts
        -- sSavePrefix comes from Halts.suffix_of_concat_sf on hSaveGPhases_halts
        -- Both represent the final state after saveInputs ++ prefix(i) halts
        have h1 := Steps.chain_concat hSave_steps hSave_halted' rfl hPrefix_steps hPrefix_halted
        -- h1.1 : Steps (saveInputs ++ prefix) ⟨0, fromInputs⟩ ⟨cPrefix.pc + save.length, cPrefix.state⟩
        -- h1.2 : halted
        -- hSavePrefix_halts.choose_spec : Steps (saveInputs ++ prefix) ⟨0, fromInputs⟩ c ∧ c.isHalted
        have hunique := Steps.halts_unique h1.1 h1.2 hSavePrefix_halts.choose_spec.1 hSavePrefix_halts.choose_spec.2
        -- hunique : ⟨cPrefix.pc + save.length, cPrefix.state⟩ = Classical.choose hSavePrefix_halts
        -- We need to show cPrefix.state = sSavePrefix
        -- sSavePrefix = (Classical.choose hSavePrefix_halts).state by hsSavePrefix_eq
        have heq := hsSavePrefix_eq hSavePrefix_halts
        rw [heq]
        -- Goal: cPrefix.state = (Classical.choose hSavePrefix_halts).state
        -- Use hunique to extract state equality
        have hstate_eq : cPrefix.state = (Classical.choose hSavePrefix_halts).state := by
          have := congrArg Config.state hunique
          exact this
        exact hstate_eq

      have hPrefix_preserves := allGPhases_prefix_preserves_saved_inputs m n base pGs hGs_sf hpGs_max hn_le_base
        i.val (Nat.le_of_lt i.isLt)
        sSave sSavePrefix cPrefix hPrefix_steps hPrefix_halted hPrefix_state_match

      -- Chain: sSavePrefix.read (base+1+r) = sSave.read (base+1+r) = inputs[r]
      rw [hPrefix_preserves (base + 1 + r) (by omega) (by omega), hsSave_value]
    · -- r ≥ n: should be 0
      have hRHS_zero : (State.fromInputs (List.ofFn inputs)).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; exact hr_ge_n)]
        rfl
      rw [hRHS_zero]
      -- After clear, R[r] = 0 for r ≤ base
      -- copyRange only writes to R[0..n-1], so R[r] still 0 for r ≥ n

      -- Connect sClear to straightLineFinalState
      have hClear_sl := clearRegisters_isStraightLine base
      have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
          (clearRegisters base) := by simp [Config.isHalted]

      -- Get the starting state for clear - need to extract from the context
      -- sSavePrefix is the state after saveInputs ++ prefix(i)
      -- Actually, we need to know that hClear_steps starts from some state s_before_clear

      -- Use suffix_of_concat_from_zero structure: hGPhase_i_steps starts from sSavePrefix
      -- gPhase = clear ++ rest, so clear starts from sSavePrefix too
      -- We got sClear from suffix_of_concat_from_zero hGPhase_i_steps ...

      -- Connect sCopy.read r to sClear.read r using copyRange_preserves
      -- copyRange (base+1) 0 n writes to [0, n), so for r ≥ n, R[r] is preserved
      have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
      have hCopy_halted' : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
          (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
      have hsCopy_eq : sCopy = straightLineFinalState hCopy_sl sClear :=
        straightLineFinalState_eq_of_halted hCopy_sl sClear
          ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ hCopy_steps hCopy_halted'

      -- r ≥ n means r is outside the write range [0, n)
      have hr_outside : r < 0 ∨ r ≥ 0 + n := Or.inr (by omega : r ≥ 0 + n)
      rw [hsCopy_eq, copyRegisterRange_preserves (base + 1) 0 n sClear r hr_outside]

      -- Now show sClear.read r = 0
      -- hClear_steps has starting state sSavePrefix (from the gPhase execution)
      -- Use straightLineFinalState_eq_of_halted to connect sClear to straightLineFinalState

      -- The starting state for clear is sSavePrefix (traced through the obtain chain)
      -- hGPhase_i_steps : Steps gPhase ⟨0, sSavePrefix⟩ _ (from hSuffix_steps starting at sSavePrefix)
      -- suffix_of_concat_from_zero preserves the starting state: clear starts from sSavePrefix

      have hsClear_eq : sClear = straightLineFinalState hClear_sl sSavePrefix :=
        straightLineFinalState_eq_of_halted hClear_sl sSavePrefix
          ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'
      rw [hsClear_eq]
      exact clearRegisters_zeros' base sSavePrefix r hr_le_base

  -- Use Halts.of_agreeing_state to conclude Halts (pGs i) (List.ofFn inputs)
  have hGi_halts : Halts (pGs i) (List.ofFn inputs) :=
    Halts.of_agreeing_state hGi_steps hGi_halted hagreeGi

  -- By hGs_spec, Halts → Dom
  exact (hGs_spec i inputs).1.mp hGi_halts

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
  -- Setup
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF

  -- Standard form facts
  have hSaveInputs_sf := saveInputs_isStandardForm base n
  have hGPhases_sf : gPhases.IsStandardForm := allGPhases_isStandardForm hGs_sf
  have hFinal_sf : final.IsStandardForm := finalPhase_isStandardForm hF_sf

  -- Program structure: H = saveInputs ++ (gPhases ++ final)
  have hH_eq : Program.composeGeneral m n pF pGs = saveInputs.concat (gPhases.concat final) := rfl

  -- Rewrite as (saveInputs ++ gPhases) ++ final
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  rw [hH_eq, ← concat_assoc] at hHalts

  -- Extract: saveInputs ++ gPhases halts (as prefix)
  have hSaveGPhases_halts := Halts.prefix_of_concat_sf hHalts hSaveGPhases_sf

  -- Extract: suffix execution (final phase) from the combined program
  obtain ⟨sFinal_start, hSaveGPhases_halts', hsFinal_start_eq', cFinal, hFinal_steps, hFinal_halted⟩ :=
    Halts.suffix_of_concat_sf hHalts hSaveGPhases_sf

  -- final = clear ++ (transfer ++ F)
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine base)
  have hTransfer_sf := straightLine_isStandardForm (transferResultsToInputs_isStraightLine (base + n + 1) m)

  -- Split final: clear halts, then (transfer ++ F) halts
  obtain ⟨sClear, hClear_steps, ⟨cTF, hTF_steps, hTF_halted⟩⟩ :=
    suffix_of_concat_from_zero hFinal_steps hFinal_halted hClear_sf

  -- Split transfer ++ F: transfer halts, then F halts
  obtain ⟨sTransfer, hTransfer_steps, ⟨cF, hF_steps, hF_halted⟩⟩ :=
    suffix_of_concat_from_zero hTF_steps hTF_halted hTransfer_sf

  -- Now we need to show that sTransfer agrees with the g results
  -- For each i < m, sTransfer.read i = (gs i inputs).get (hGs_dom i)

  -- First, by hGs_spec, each gs i inputs has a value via the halting gi
  have hGi_halts : ∀ i, Halts (pGs i) (List.ofFn inputs) := by
    intro i
    have hdom := hGs_dom i
    exact (hGs_spec i inputs).1.mpr hdom

  have hGi_results : ∀ i, ∃ v, Result (pGs i) (List.ofFn inputs) (hGi_halts i) = v ∧
      v = (gs i inputs).get (hGs_dom i) := by
    intro i
    use (gs i inputs).get (hGs_dom i)
    constructor
    · exact (hGs_spec i inputs).2 (hGi_halts i) (hGs_dom i)
    · rfl

  -- The key is that after all gPhases, R[base+n+1+i] = result of gi
  -- And transferResultsToInputs copies these to R[i]
  -- So sTransfer.read i = result of gi for i < m

  -- For now, we show state agreement for F
  have hagreeF : ∀ r, r ≤ pF.maxRegister →
      sTransfer.read r = (State.fromInputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r := by
    intro r hr
    -- r ≤ pF.maxRegister ≤ base
    have hr_le_base : r ≤ base := Nat.le_trans hr (compositionBase_ge_F m n pF pGs)
    -- Two cases: r < m (input to F) or r ≥ m (should be 0)
    rcases Nat.lt_or_ge r m with hr_lt_m | hr_ge_m
    · -- r < m: sTransfer.read r = gs r result
      -- 1. transferResults copies R[base+n+1+r] to R[r]
      -- 2. clear preserves R[base+n+1+r] since base+n+1+r > base
      -- 3. After allGPhases, R[base+n+1+r] = result of g_r

      -- RHS value
      have hRHS : (State.fromInputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r =
          (gs ⟨r, hr_lt_m⟩ inputs).get (hGs_dom ⟨r, hr_lt_m⟩) := by
        simp only [State.fromInputs, State.read]
        rw [List.getD_eq_getElem (List.ofFn _) 0 (by simp; exact hr_lt_m), List.getElem_ofFn]

      -- Connect sClear and sTransfer to straightLineFinalState
      have hClear_sl := clearRegisters_isStraightLine base
      have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
          (clearRegisters base) := by simp [Config.isHalted]
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sFinal_start :=
        straightLineFinalState_eq_of_halted hClear_sl sFinal_start
          ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'

      have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m
      have hTransfer_halted' : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).isHalted
          (transferResultsToInputs (base + n + 1) m) := by simp [Config.isHalted]
      have hsTransfer_eq : sTransfer = straightLineFinalState hTransfer_sl sClear :=
        straightLineFinalState_eq_of_halted hTransfer_sl sClear
          ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ hTransfer_steps hTransfer_halted'

      -- Step 1: sTransfer.read r = sClear.read (base+n+1+r)
      -- Using transferResultsToInputs_state
      have hNoOverlap_transfer : m ≤ base + n + 1 := by
        have h := compositionBase_ge_m_sub_one m n pF pGs
        omega
      obtain ⟨sTransfer', hsTransfer'_eq, hTransfer_copies, _⟩ :=
        transferResultsToInputs_state (base + n + 1) m sClear hNoOverlap_transfer
      have hTransfer_r : sTransfer.read r = sClear.read (base + n + 1 + r) := by
        rw [hsTransfer_eq, hsTransfer'_eq]
        exact hTransfer_copies r hr_lt_m

      -- Step 2: sClear.read (base+n+1+r) = sFinal_start.read (base+n+1+r)
      -- clear preserves registers > base
      have hr_saved_gt_base : base < base + n + 1 + r := by omega
      have hClear_preserves : sClear.read (base + n + 1 + r) = sFinal_start.read (base + n + 1 + r) := by
        rw [hsClear_eq]
        exact clearRegisters_preserves_above' base sFinal_start (base + n + 1 + r) hr_saved_gt_base

      -- Step 3: sFinal_start.read (base+n+1+r) = result of g_r
      -- Use allGPhases_saves_result helper
      have hSavedResult : sFinal_start.read (base + n + 1 + r) =
          (gs ⟨r, hr_lt_m⟩ inputs).get (hGs_dom ⟨r, hr_lt_m⟩) := by
        -- sFinal_start is the state after saveInputs ++ gPhases halts
        -- hsFinal_start_eq' says sFinal_start = (Classical.choose hSaveGPhases_halts').state
        have h1 : sFinal_start = (Classical.choose hSaveGPhases_halts').state :=
          hsFinal_start_eq' hSaveGPhases_halts'
        -- Get the canonical witness
        have hspec := Classical.choose_spec hSaveGPhases_halts'
        let cSaveGPhases := Classical.choose hSaveGPhases_halts'
        have hSaveGPhases_steps := hspec.1
        have hSaveGPhases_halted'' := hspec.2
        -- sFinal_start = cSaveGPhases.state
        have hsFinal_start_eq : sFinal_start = cSaveGPhases.state := h1
        rw [hsFinal_start_eq]
        exact allGPhases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨r, hr_lt_m⟩
          (sSaveGPhases := cSaveGPhases.state)
          ⟨cSaveGPhases, hSaveGPhases_steps, hSaveGPhases_halted'', rfl⟩

      rw [hRHS, hTransfer_r, hClear_preserves, hSavedResult]
    · -- r ≥ m: should be 0
      have hRHS_zero : (State.fromInputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; exact hr_ge_m)]
        rfl
      rw [hRHS_zero]
      -- After clear and transfer, R[r] = 0 for r ≥ m
      -- clear sets R[0..base] to 0
      -- transfer only writes to R[0..m-1]
      -- So R[r] for m ≤ r ≤ base is 0 (from clear)

      -- Connect sClear to straightLineFinalState
      have hClear_sl := clearRegisters_isStraightLine base
      have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
          (clearRegisters base) := by simp [Config.isHalted]
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sFinal_start :=
        straightLineFinalState_eq_of_halted hClear_sl sFinal_start
          ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'

      -- After clear, R[r] = 0 for r ≤ base
      have hsClear_zero : sClear.read r = 0 := by
        rw [hsClear_eq]
        exact clearRegisters_zeros' base sFinal_start r hr_le_base

      -- transfer preserves R[r] for r ≥ m
      have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m
      have hTransfer_halted' : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).isHalted
          (transferResultsToInputs (base + n + 1) m) := by simp [Config.isHalted]
      have hsTransfer_eq : sTransfer = straightLineFinalState hTransfer_sl sClear :=
        straightLineFinalState_eq_of_halted hTransfer_sl sClear
          ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ hTransfer_steps hTransfer_halted'

      rw [hsTransfer_eq, transferResultsToInputs_preserves (base + n + 1) m sClear r hr_ge_m, hsClear_zero]

  -- Use Halts.of_agreeing_state to conclude Halts pF (result inputs)
  have hF_halts : Halts pF (List.ofFn (fun i => (gs i inputs).get (hGs_dom i))) :=
    Halts.of_agreeing_state hF_steps hF_halted hagreeF

  -- By hF_spec, Halts → Dom
  exact (hF_spec (fun i => (gs i inputs).get (hGs_dom i))).1.mp hF_halts

set_option maxHeartbeats 800000 in
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
  -- Extract domain information from compFunction
  simp only [compFunction, Part.bind_dom] at hDom
  obtain ⟨hSeq_dom, hf_dom⟩ := hDom
  have hGs_dom : ∀ i, (gs i inputs).Dom := Part.sequence_dom.mp hSeq_dom

  -- Each Gi halts
  have hGi_halts : ∀ i, Halts (pGs i) (List.ofFn inputs) :=
    fun i => (hGs_spec i inputs).1.mpr (hGs_dom i)

  -- Get results
  let results : Fin m → ℕ := fun i => (gs i inputs).get (hGs_dom i)

  -- F halts on results
  have hf_dom' : (f results).Dom := by
    have h : results = (Part.sequence (fun i => gs i inputs)).get hSeq_dom := by
      funext i
      simp only [results, Part.sequence_get]
    rw [h]
    exact hf_dom
  have hF_halts := (hF_spec results).1.mpr hf_dom'

  -- Setup
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF

  -- Standard form facts
  have hSaveInputs_sf := saveInputs_isStandardForm base n
  have hGPhases_sf : gPhases.IsStandardForm := allGPhases_isStandardForm hGs_sf
  have hFinal_sf : final.IsStandardForm := finalPhase_isStandardForm hF_sf
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf

  -- Program structure
  have hH_eq : Program.composeGeneral m n pF pGs = saveInputs.concat (gPhases.concat final) := rfl

  -- saveInputs halts (straight-line)
  have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
  have hSave_halts := straightLine_halts hSave_sl (List.ofFn inputs)
  have hSave_pc := straightLine_halts_at_length hSave_sl (List.ofFn inputs)

  -- Get state after saveInputs
  have hNoOverlap : 0 + n ≤ base + 1 := compositionBase_ge_n m n pF pGs
  obtain ⟨sSave, hsSave_eq, hSave_copies, hSave_preserves⟩ :=
    copyRegisterRange_state 0 (base + 1) n (State.fromInputs (List.ofFn inputs)) (Or.inr hNoOverlap)
  obtain ⟨cSave, hSave_steps, hSave_halted, hSave_pc'⟩ :=
    straightLine_halts_from_state hSave_sl (State.fromInputs (List.ofFn inputs))
  have hcSave_state : cSave.state = sSave := by
    rw [straightLineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps hSave_halted, hsSave_eq]

  -- Saved inputs after saveInputs
  have hSaved : ∀ j : ℕ, (hj : j < n) → sSave.read (base + 1 + j) = inputs ⟨j, hj⟩ := by
    intro j hj
    rw [hSave_copies j hj]
    simp only [State.fromInputs, State.read, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hj, ↓reduceDIte, Option.getD_some]

  -- allGPhases halts from sSave
  have hpGs_max : ∀ i, (pGs i).maxRegister ≤ base := fun i => compositionBase_ge_pGs_max m n pF pGs i
  have hn_le_base : n ≤ base + 1 := compositionBase_ge_n m n pF pGs
  obtain ⟨cGPhases, hGPhases_steps, hGPhases_halted⟩ :=
    allGPhases_halts_from_saved_inputs hGs_sf hpGs_max hn_le_base hGi_halts sSave hSaved

  -- Chain saveInputs with gPhases
  have hSave_halted' : (⟨saveInputs.length, sSave⟩ : Config).isHalted saveInputs := by
    simp [Config.isHalted]
  have hSave_steps' : Steps saveInputs ⟨0, State.fromInputs (List.ofFn inputs)⟩ ⟨saveInputs.length, sSave⟩ := by
    have : cSave = ⟨saveInputs.length, sSave⟩ := by
      ext <;> simp only [hSave_pc', hcSave_state, copyRegisterRange_length]
    rw [← this]; exact hSave_steps
  have ⟨hSaveGPhases_steps, hSaveGPhases_halted⟩ := Steps.chain_concat hSave_steps' hSave_halted'
    rfl hGPhases_steps hGPhases_halted

  -- Get state after all gPhases
  have hGPhases_pc : cGPhases.pc = gPhases.length :=
    hGPhases_sf.pc_eq_length_of_halted hGPhases_halted
  let sGPhases := cGPhases.state

  -- sGPhases has results at correct locations
  have hResults : ∀ j : ℕ, (hj : j < m) → sGPhases.read (base + n + 1 + j) = results ⟨j, hj⟩ := by
    intro j hj
    -- Use allGPhases_saves_result through proper extraction
    -- We have execution of saveInputs ++ gPhases that reaches cGPhases.state
    let sSaveGPhases := cGPhases.state
    have hSaveGPhases_halted' : ∃ c : Config,
        Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩ c ∧
        c.isHalted (saveInputs.concat gPhases) ∧ c.state = sSaveGPhases := by
      have hSaveGPhases_halted'' : (⟨(saveInputs.concat gPhases).length, sGPhases⟩ : Config).isHalted (saveInputs.concat gPhases) := by
        simp [Config.isHalted, Program.concat_length, copyRegisterRange_length]
      have hchain_state_eq : sSaveGPhases = sGPhases := rfl
      exact ⟨⟨(saveInputs.concat gPhases).length, sGPhases⟩,
             by have huniq := Steps.halts_unique hSaveGPhases_steps hSaveGPhases_halted
                  (by have hpc : cGPhases.pc = gPhases.length := hGPhases_pc
                      have : (⟨(saveInputs.concat gPhases).length, cGPhases.state⟩ : Config) =
                          ⟨saveInputs.length + gPhases.length, sGPhases⟩ := by
                        simp only [Program.concat_length, hpc]
                      exact hSaveGPhases_steps)
                  hSaveGPhases_halted''
                rw [huniq] at hSaveGPhases_steps
                exact hSaveGPhases_steps,
             hSaveGPhases_halted'', rfl⟩
    have hres := allGPhases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨j, hj⟩ sSaveGPhases hSaveGPhases_halted'
    simp only [results]
    exact hres

  -- Saved inputs preserved after gPhases
  have hSaved_after_gPhases : ∀ j : ℕ, (hj : j < n) → sGPhases.read (base + 1 + j) = inputs ⟨j, hj⟩ := by
    intro j hj
    -- Use allGPhases_prefix_preserves_saved_inputs with full m phases
    have hAG_preserves := allGPhases_prefix_preserves_saved_inputs m n base pGs hGs_sf hpGs_max hn_le_base
      m (Nat.le_refl m) sSave sGPhases cGPhases hGPhases_steps hGPhases_halted rfl (base + 1 + j) (by omega) (by omega)
    rw [hAG_preserves, hSaved j hj]

  -- finalPhase halts from sGPhases
  have hpF_max : pF.maxRegister ≤ base := compositionBase_ge_pF_max m n pF pGs
  have hm_le_base : m ≤ base + 1 := compositionBase_ge_m m n pF pGs
  obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ :=
    finalPhase_halts_from_results hF_sf hpF_max hm_le_base hF_halts sGPhases hResults

  -- Chain all together
  have hSaveGPhases_halted' : (⟨(saveInputs.concat gPhases).length, sGPhases⟩ : Config).isHalted (saveInputs.concat gPhases) := by
    simp [Config.isHalted]
  have hSaveGPhases_steps' : Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩
      ⟨(saveInputs.concat gPhases).length, sGPhases⟩ := by
    have : ⟨(saveInputs.concat gPhases).length, sGPhases⟩ = cGPhases := by
      ext
      · simp only [Program.concat_length, copyRegisterRange_length, hGPhases_pc, allGPhases_length]
        ring
      · rfl
    have huniq := Steps.halts_unique hSaveGPhases_steps hSaveGPhases_halted
      (by rw [this]; exact hSaveGPhases_steps) (by rw [this]; exact hSaveGPhases_halted)
    rw [← huniq]
    exact hSaveGPhases_steps
  have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hSaveGPhases_steps' hSaveGPhases_halted'
    rfl hFinal_steps hFinal_halted

  -- The total program is saveInputs ++ (gPhases ++ final)
  have hProg_eq : saveInputs.concat (gPhases.concat final) = (saveInputs.concat gPhases).concat final := by
    rw [concat_assoc]
  rw [hH_eq, hProg_eq]
  exact ⟨_, hTotal_steps, hTotal_halted⟩

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
  -- Setup
  let H := Program.composeGeneral m n pF pGs
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF

  -- Extract g_i domain from hDom
  simp only [compFunction] at hDom
  have hSeq_dom : (Part.sequence fun i => gs i inputs).Dom := Part.bind_dom.mp hDom |>.1
  have hGs_dom : ∀ i, (gs i inputs).Dom := Part.sequence_dom.mp hSeq_dom

  -- Define results
  let results : Fin m → ℕ := fun i => (gs i inputs).get (hGs_dom i)

  -- f is defined on results
  have hf_dom : (f results).Dom := by
    have h := Part.bind_dom.mp hDom |>.2
    have harg_eq : (Part.sequence fun i => gs i inputs).get hSeq_dom = results := by
      funext i; exact Part.sequence_get hSeq_dom i
    rw [harg_eq] at h; exact h

  -- pF halts on results
  have hF_halts : Halts pF (List.ofFn results) := (hF_spec results).1.mpr hf_dom

  -- Get the canonical halted config for H
  let cH := Classical.choose hHalts
  have hH_spec := Classical.choose_spec hHalts
  have hH_steps : Steps H (Config.init (List.ofFn inputs)) cH := hH_spec.1
  have hH_halted : cH.isHalted H := hH_spec.2

  -- Get canonical halted config for pF on results
  let cF := Classical.choose hF_halts
  have hF_steps : Steps pF (Config.init (List.ofFn results)) cF := (Classical.choose_spec hF_halts).1
  have hF_halted : cF.isHalted pF := (Classical.choose_spec hF_halts).2
  have hF_pc : cF.pc = pF.length := hF_sf.halts_at_length (List.ofFn results) cF hF_steps hF_halted

  -- Bounds
  have hpF_max : pF.maxRegister ≤ base := compositionBase_ge_pF_max m n pF pGs
  have hpGs_max : ∀ i, (pGs i).maxRegister ≤ base := fun i => compositionBase_ge_pGs_max m n pF pGs i
  have hn_le_base : n ≤ base + 1 := compositionBase_ge_n m n pF pGs
  have hm_le_base : m ≤ base + 1 := compositionBase_ge_m m n pF pGs

  -- g_i halts for each i
  have hGi_halts : ∀ i, Halts (pGs i) (List.ofFn inputs) :=
    fun i => (hGs_spec i inputs).1.mpr (hGs_dom i)

  -- Standard form facts
  have hH_sf := composeGeneral_isStandardForm hF_sf hGs_sf
  have hSave_sf := saveInputs_isStandardForm base n
  have hGPhases_sf := allGPhases_isStandardForm hGs_sf

  -- Execute saveInputs
  have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
  obtain ⟨cSave, hSave_steps, hSave_halted⟩ := straightLine_halts_from_state hSave_sl (State.fromInputs (List.ofFn inputs))
  have hSave_pc' : cSave.pc = saveInputs.length := straightLine_pc_eq_length hSave_sl _ cSave hSave_steps hSave_halted
  obtain ⟨sSave, hsSave_eq, hSave_copies, hSave_preserves⟩ := copyRegisterRange_state 0 (base + 1) n (State.fromInputs (List.ofFn inputs))
  have hcSave_state : cSave.state = sSave := by
    rw [straightLineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps hSave_halted, hsSave_eq]

  -- Saved inputs after saveInputs
  have hSaved : ∀ j : ℕ, (hj : j < n) → sSave.read (base + 1 + j) = inputs ⟨j, hj⟩ := by
    intro j hj
    rw [hSave_copies j hj]
    simp only [State.fromInputs, State.read, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hj, ↓reduceDIte, Option.getD_some]

  -- allGPhases halts from sSave
  obtain ⟨cGPhases, hGPhases_steps, hGPhases_halted⟩ :=
    allGPhases_halts_from_saved_inputs hGs_sf hpGs_max hn_le_base hGi_halts sSave hSaved

  -- Chain saveInputs with gPhases
  have hSave_halted' : (⟨saveInputs.length, sSave⟩ : Config).isHalted saveInputs := by simp [Config.isHalted]
  have hSave_steps' : Steps saveInputs ⟨0, State.fromInputs (List.ofFn inputs)⟩ ⟨saveInputs.length, sSave⟩ := by
    have : cSave = ⟨saveInputs.length, sSave⟩ := by ext <;> simp only [hSave_pc', hcSave_state, copyRegisterRange_length]
    rw [← this]; exact hSave_steps
  have ⟨hSaveGPhases_steps, hSaveGPhases_halted⟩ := Steps.chain_concat hSave_steps' hSave_halted' rfl hGPhases_steps hGPhases_halted

  -- Get state after all gPhases
  have hGPhases_pc : cGPhases.pc = gPhases.length := hGPhases_sf.pc_eq_length_of_halted hGPhases_halted
  let sGPhases := cGPhases.state

  -- sGPhases has results at correct locations (use allGPhases_saves_result)
  have hResults : ∀ j : ℕ, (hj : j < m) → sGPhases.read (base + n + 1 + j) = results ⟨j, hj⟩ := by
    intro j hj
    let sSaveGPhases := cGPhases.state
    have hSaveGPhases_halted' : ∃ c : Config,
        Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩ c ∧
        c.isHalted (saveInputs.concat gPhases) ∧ c.state = sSaveGPhases := by
      have hSaveGPhases_halted'' : (⟨(saveInputs.concat gPhases).length, sGPhases⟩ : Config).isHalted (saveInputs.concat gPhases) := by
        simp [Config.isHalted, Program.concat_length, copyRegisterRange_length]
      exact ⟨⟨(saveInputs.concat gPhases).length, sGPhases⟩,
             by have huniq := Steps.halts_unique hSaveGPhases_steps hSaveGPhases_halted
                  (by have hpc : cGPhases.pc = gPhases.length := hGPhases_pc
                      have : (⟨(saveInputs.concat gPhases).length, cGPhases.state⟩ : Config) =
                          ⟨saveInputs.length + gPhases.length, sGPhases⟩ := by simp only [Program.concat_length, hpc]
                      exact hSaveGPhases_steps)
                  hSaveGPhases_halted''
                rw [huniq] at hSaveGPhases_steps; exact hSaveGPhases_steps,
             hSaveGPhases_halted'', rfl⟩
    have hres := allGPhases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨j, hj⟩ sSaveGPhases hSaveGPhases_halted'
    simp only [results]; exact hres

  -- Execute finalPhase from sGPhases
  -- finalPhase = clear ++ (transfer ++ pF)
  -- After clear+transfer: R[0..m-1] = results, R[m..base] = 0, agreeing with fromInputs results

  -- State agreement for pF: after clear+transfer, agrees with List.ofFn results
  have hagree_pF : ∀ sSetup : State,
      (∀ j : ℕ, (hj : j < m) → sSetup.read j = results ⟨j, hj⟩) →
      (∀ r, m ≤ r → r ≤ base → sSetup.read r = 0) →
      sSetup.agreeOn (State.fromInputs (List.ofFn results)) 0 pF.maxRegister := by
    intro sSetup hInputs hZeros
    apply agrees_list_inputs_after_clear_transfer hpF_max
    · intro i hi
      simp only [List.length_ofFn] at hi
      rw [hInputs i hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
    · intro r hr_ge hr_le
      simp only [List.length_ofFn] at hr_ge
      exact hZeros r hr_ge hr_le

  -- Get final state after clear + transfer
  have hClear_sl := clearRegisters_isStraightLine base
  have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m

  -- Clear halts from sGPhases
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves⟩ :=
    clearRegisters_exec base sGPhases

  -- After clear, results still there
  have hResults_after_clear : ∀ j : ℕ, (hj : j < m) → cClear.state.read (base + n + 1 + j) = results ⟨j, hj⟩ :=
    fun j hj => by rw [hClear_preserves (base + n + 1 + j) (by omega)]; exact hResults j hj

  -- Transfer halts and sets up inputs
  have hNoOverlap : m ≤ base + n + 1 := by omega
  obtain ⟨sTransfer, hsTransfer_eq, hTransfer_correct, hTransfer_preserves⟩ :=
    transferResultsToInputs_state (base + n + 1) m cClear.state hNoOverlap

  obtain ⟨cTransfer, hTransfer_steps', hTransfer_halted', hTransfer_pc⟩ :=
    straightLine_halts_from_state hTransfer_sl cClear.state
  have hTransfer_state_eq : cTransfer.state = straightLineFinalState hTransfer_sl cClear.state :=
    straightLineFinalState_eq_of_halted hTransfer_sl cClear.state cTransfer hTransfer_steps' hTransfer_halted'
  have hTransfer_state_sTransfer : cTransfer.state = sTransfer := by rw [hTransfer_state_eq, hsTransfer_eq]

  -- After transfer, R[0..m-1] = results
  have hInputs_set : ∀ j : ℕ, (hj : j < m) → sTransfer.read j = results ⟨j, hj⟩ := by
    intro j hj; rw [hTransfer_correct j hj, hResults_after_clear j hj]

  -- R[m..base] = 0 after transfer
  have hZeros_set : ∀ r, m ≤ r → r ≤ base → sTransfer.read r = 0 := by
    intro r hr_ge hr_le
    rw [hTransfer_preserves r (by omega), hClear_zeros r (by omega)]

  -- State agrees for pF execution
  have hagree : sTransfer.agreeOn (State.fromInputs (List.ofFn results)) 0 pF.maxRegister :=
    hagree_pF sTransfer hInputs_set hZeros_set

  -- pF halts from sTransfer via agreeing execution
  let epF := Halts.executeFromAgreeingState hF_halts hF_sf hagree
  have hpF_steps' := epF.steps
  have hpF_halted' := epF.halted

  -- The output matches: epF.config.state.output = cF.state.output
  have hOutput_eq : epF.config.state.read 0 = cF.state.read 0 := by
    have h := AgreeingExecution.result_matches_original epF
    simp only [Result] at h
    have hcF_eq : Classical.choose hF_halts = cF := rfl
    rw [hcF_eq] at h
    exact h

  -- Build execution in H from start to epF final state
  -- H = saveInputs ++ (gPhases ++ final)
  -- final = clear ++ (transfer ++ pF)
  have hH_eq : H = saveInputs.concat (gPhases.concat final) := rfl

  -- Chain clear with (transfer ++ pF)
  have hTransfer_steps : Steps (transferResultsToInputs (base + n + 1) m) ⟨0, cClear.state⟩
      ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
    have : cTransfer = ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
      ext <;> simp only [hTransfer_pc, hTransfer_state_sTransfer]
    rw [← this]; exact hTransfer_steps'
  have hTransfer_halted : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).isHalted
      (transferResultsToInputs (base + n + 1) m) := by simp [Config.isHalted]

  have ⟨hTransferF_steps, hTransferF_halted⟩ := Steps.chain_concat hTransfer_steps hTransfer_halted
    rfl hpF_steps' hpF_halted'

  have ⟨hClearTransferF_steps, hClearTransferF_halted⟩ := Steps.chain_concat hClear_steps hClear_halted
    hClear_pc hTransferF_steps hTransferF_halted

  -- Chain saveInputs ++ gPhases with final
  have hSaveGPhases_halted' : (⟨(saveInputs.concat gPhases).length, sGPhases⟩ : Config).isHalted (saveInputs.concat gPhases) := by
    simp [Config.isHalted]
  have hSaveGPhases_steps' : Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩
      ⟨(saveInputs.concat gPhases).length, sGPhases⟩ := by
    have : ⟨(saveInputs.concat gPhases).length, sGPhases⟩ = cGPhases := by
      ext
      · simp only [Program.concat_length, copyRegisterRange_length, hGPhases_pc, allGPhases_length]; ring
      · rfl
    have huniq := Steps.halts_unique hSaveGPhases_steps hSaveGPhases_halted
      (by rw [this]; exact hSaveGPhases_steps) (by rw [this]; exact hSaveGPhases_halted)
    rw [← huniq]; exact hSaveGPhases_steps

  have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hSaveGPhases_steps' hSaveGPhases_halted'
    rfl hClearTransferF_steps hClearTransferF_halted

  -- The total program is saveInputs ++ (gPhases ++ final)
  have hProg_eq : saveInputs.concat (gPhases.concat final) = (saveInputs.concat gPhases).concat final := by
    rw [concat_assoc]
  rw [hH_eq, hProg_eq] at hH_steps hH_halted

  -- The final state of our built execution
  let cH_built : Config := ⟨(saveInputs.concat gPhases).length + final.length + epF.config.pc - pF.length,
                            epF.config.state⟩

  -- Show cH_built equals the unique halted config
  have hcH_built_halted : cH_built.isHalted ((saveInputs.concat gPhases).concat final) := by
    simp only [Config.isHalted, Program.concat_length, cH_built]
    have hepF_pc : epF.config.pc = pF.length := epF.pc_eq
    simp only [hepF_pc, Nat.add_sub_cancel]
    simp only [finalPhase, Program.concat_length, clearRegisters_length, transferResultsToInputs_length]
    omega

  have hH_steps_built : Steps ((saveInputs.concat gPhases).concat final)
      ⟨0, State.fromInputs (List.ofFn inputs)⟩ cH_built := by
    have hpc_match : (saveInputs.concat gPhases).length + final.length + epF.config.pc - pF.length =
        (saveInputs.concat gPhases).length + (final.length - pF.length + epF.config.pc) := by
      have hepF_pc : epF.config.pc = pF.length := epF.pc_eq
      simp only [hepF_pc, Nat.add_sub_cancel]
      simp only [finalPhase, Program.concat_length, clearRegisters_length, transferResultsToInputs_length]
      ring
    have : cH_built.state = epF.config.state := rfl
    -- Need to show hTotal_steps reaches cH_built
    -- The final config in hTotal_halted has pc = length and state = epF.config.state
    have hfinal_pc : epF.config.pc = pF.length := epF.pc_eq
    have hTotal_final : Steps ((saveInputs.concat gPhases).concat final) ⟨0, State.fromInputs (List.ofFn inputs)⟩
        ⟨((saveInputs.concat gPhases).concat final).length, epF.config.state⟩ := by
      have hfinal_len : final.length = (clearRegisters base).length + (transferResultsToInputs (base + n + 1) m).length + pF.length := by
        simp only [finalPhase, Program.concat_length]
      have hClearTransferF_pc : (⟨0, sGPhases⟩ : Config).pc + (clearRegisters base).length +
          (transferResultsToInputs (base + n + 1) m).length + epF.config.pc =
          final.length := by
        simp only [hfinal_len, hfinal_pc]; ring
      convert hTotal_steps using 2
      simp only [Program.concat_length, hfinal_pc]
      simp only [finalPhase, Program.concat_length, clearRegisters_length, transferResultsToInputs_length]
      ring
    convert hTotal_final using 2
    simp only [Program.concat_length, cH_built, hfinal_pc, Nat.add_sub_cancel]

  have hcH_eq := Steps.halts_unique hH_steps hH_halted hH_steps_built hcH_built_halted

  -- Final calculation
  have hResult_eq : cH.state.read 0 = cF.state.read 0 := by
    calc cH.state.read 0 = cH_built.state.read 0 := by rw [hcH_eq]
      _ = epF.config.state.read 0 := rfl
      _ = cF.state.read 0 := hOutput_eq

  -- Connect to compFunction
  calc Result H (List.ofFn inputs) hHalts
      = cH.state.output := rfl
    _ = cH.state.read 0 := rfl
    _ = cF.state.read 0 := hResult_eq
    _ = Result pF (List.ofFn results) hF_halts := rfl
    _ = (f results).get hf_dom := (hF_spec results).2 hF_halts hf_dom
    _ = (compFunction m n f gs inputs).get hDom := by
        simp only [compFunction]
        have hSeq_get : (Part.sequence fun i => gs i inputs).get hSeq_dom = results := by
          funext i; exact Part.sequence_get hSeq_dom i
        rw [Part.bind_get]
        simp only [hSeq_get]

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
