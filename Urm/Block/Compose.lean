/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Block.Basic
import Urm.Block.Compile
import Urm.Block.Glue
import Urm.StraightLine
import Urm.PartSequence
import Urm.Composition.Core
import Urm.Composition.Preservation
import Urm.Composition.Helpers
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-! # Composition Combinator for URMBlock

This file defines the composition combinator for URMBlock, implementing
h(x) = f(g₁(x), ..., gₘ(x)).

## Register Layout

Using a single "base" offset with fresh input copying before each block:

```
[0..n-1]              : original inputs x (preserved)
[base..base+maxReg]   : workspace for running each gᵢ and f
[base+n+1..base+n+m]  : saved results g₁(x)..gₘ(x)
```

## Program Structure

1. Save inputs: copy [0..n-1] to [base+1..base+n]
2. For each gᵢ (i = 0..m-1):
   a. Clear workspace at base
   b. Copy saved inputs [base+1..base+n] to [0..n-1] at base offset
   c. Run gᵢ.compile(base)
   d. Save result: copy base to results[i] = base+n+1+i
3. Clear workspace at base
4. Copy results [base+n+1..base+n+m] to [0..m-1] at base offset
5. Run f.compile(base)
6. Copy result from base to register 0

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

namespace URMBlock

open Program

/-! ## Base Computation -/

/-- Maximum maxReg among all gᵢ blocks. -/
def maxGsReg (m : ℕ) (gs : Fin m → URMBlock) : ℕ :=
  Finset.univ.sup fun i => (gs i).maxReg

/-- The base offset for composition.
Must be large enough to accommodate:
- n inputs
- m results
- max register of f
- max register of any gᵢ -/
def composeBase (n : ℕ) (f : URMBlock) (m : ℕ) (gs : Fin m → URMBlock) : ℕ :=
  max (n - 1) (max (m - 1) (max f.maxReg (maxGsReg m gs)))

theorem composeBase_ge_n_sub_one (n : ℕ) (f : URMBlock) (m : ℕ) (gs : Fin m → URMBlock) :
    n - 1 ≤ composeBase n f m gs := by
  simp only [composeBase, le_max_iff]; left; rfl

theorem composeBase_ge_m_sub_one (n : ℕ) (f : URMBlock) (m : ℕ) (gs : Fin m → URMBlock) :
    m - 1 ≤ composeBase n f m gs := by
  simp only [composeBase, le_max_iff]; right; left; rfl

theorem composeBase_ge_f (n : ℕ) (f : URMBlock) (m : ℕ) (gs : Fin m → URMBlock) :
    f.maxReg ≤ composeBase n f m gs := by
  simp only [composeBase, le_max_iff]; right; right; left; rfl

theorem composeBase_ge_gi (n : ℕ) (f : URMBlock) (m : ℕ) (gs : Fin m → URMBlock) (i : Fin m) :
    (gs i).maxReg ≤ composeBase n f m gs := by
  simp only [composeBase, maxGsReg, le_max_iff]; right; right; right
  exact @Finset.le_sup ℕ (Fin m) _ _ Finset.univ (fun j => (gs j).maxReg) i (Finset.mem_univ i)

theorem composeBase_ge_n (n : ℕ) (f : URMBlock) (m : ℕ) (gs : Fin m → URMBlock) :
    n ≤ composeBase n f m gs + 1 := by
  have h := composeBase_ge_n_sub_one n f m gs; omega

theorem composeBase_ge_m (n : ℕ) (f : URMBlock) (m : ℕ) (gs : Fin m → URMBlock) :
    m ≤ composeBase n f m gs + 1 := by
  have h := composeBase_ge_m_sub_one n f m gs; omega

/-! ## Program Construction -/

/-- Phase for running gᵢ: clear base, copy inputs, run gᵢ, save result. -/
def gPhase (base n : ℕ) (g : URMBlock) (i : ℕ) : Program :=
  -- Clear the workspace register at base
  (clearRegisters base).concat (
    -- Copy saved inputs from [base+1..base+n] to [base..base+n-1]
    (copyRegisterRange (base + 1) base n).concat (
      -- Run gᵢ at offset base
      (g.compile base).concat
        -- Save result from base to results[i] = base + n + 1 + i
        [Instr.T base (base + n + 1 + i)]))

/-- All g phases concatenated. -/
def allGPhases (m n base : ℕ) (gs : Fin m → URMBlock) : Program :=
  (List.finRange m).foldl (fun acc i => acc.concat (gPhase base n (gs i) i.val)) []

/-- Final phase: clear, copy results to f's inputs, run f, copy output to R0. -/
def finalPhase (m n base : ℕ) (f : URMBlock) : Program :=
  -- Clear workspace
  (clearRegisters base).concat (
    -- Copy results from [base+n+1..base+n+m] to [base..base+m-1]
    (transferResultsToInputs (base + n + 1) m).concat (
      -- Run f at offset base
      (f.compile base).concat
        -- Copy result from base to register 0
        [Instr.T base 0]))

/-- The composed program: save inputs, run all gs, run f. -/
def composeProgram (n : ℕ) (f : URMBlock) (m : ℕ) (gs : Fin m → URMBlock) : Program :=
  let base := composeBase n f m gs
  -- Save inputs from [0..n-1] to [base+1..base+n]
  (copyRegisterRange 0 (base + 1) n).concat (
    -- Run all g phases
    (allGPhases m n base gs).concat
      -- Run final phase with f
      (finalPhase m n base f))

/-! ## MaxRegister Bounds -/

/-- A single instruction [T a b] has maxRegister max a b. -/
private theorem single_transfer_maxRegister (a b : ℕ) :
    Program.maxRegister [Instr.T a b] = max a b := by
  rfl

/-- MaxRegister of gPhase is bounded by max(base + n + 1 + i, 2*base), assuming g.maxReg ≤ base. -/
theorem gPhase_maxRegister (base n : ℕ) (g : URMBlock) (i : ℕ) (hg_bounded : g.maxReg ≤ base) :
    (gPhase base n g i).maxRegister ≤ max (base + n + 1 + i) (2 * base) := by
  simp only [gPhase]
  rw [concat_maxRegister, concat_maxRegister, concat_maxRegister]
  simp only [clearRegisters_maxRegister, single_transfer_maxRegister]
  -- Components:
  -- clearRegisters base: maxRegister = base
  -- copyRegisterRange (base+1) base n: maxRegister ≤ base + n
  -- g.compile base: maxRegister ≤ g.maxReg + base ≤ 2*base
  -- [T base (base + n + 1 + i)]: maxRegister = max base (base + n + 1 + i)
  have h1 : base ≤ max (base + n + 1 + i) (2 * base) := by omega
  have h2 : (copyRegisterRange (base + 1) base n).maxRegister ≤ max (base + n + 1 + i) (2 * base) := by
    have hcopy := copyRegisterRange_maxRegister (base + 1) base n
    cases n with
    | zero => simp at hcopy ⊢; omega
    | succ k =>
      simp only [Nat.add_succ_sub_one] at hcopy
      calc (copyRegisterRange (base + 1) base (k + 1)).maxRegister
          ≤ max (base + 1 + k) (base + k) := hcopy
        _ ≤ max (base + (k + 1) + 1 + i) (2 * base) := by omega
  have h3 : (g.compile base).maxRegister ≤ max (base + n + 1 + i) (2 * base) := by
    by_cases hp : g.program = []
    · simp [URMBlock.compile, hp, Program.shiftRegisters, Program.maxRegister]
    · simp only [URMBlock.compile, Program.maxRegister_shiftRegisters base g.program hp]
      -- Note: g.maxReg = g.program.maxRegister by definition
      calc g.program.maxRegister + base = g.maxReg + base := rfl
        _ ≤ base + base := Nat.add_le_add_right hg_bounded base
        _ ≤ max (base + n + 1 + i) (2 * base) := by omega
  have h4 : max base (base + n + 1 + i) ≤ max (base + n + 1 + i) (2 * base) := by omega
  omega

/-- MaxRegister of allGPhases is bounded by max(base + n + m, 2*base). -/
theorem allGPhases_maxRegister (m n base : ℕ) (gs : Fin m → URMBlock)
    (hgs_bounded : ∀ i, (gs i).maxReg ≤ base) :
    (allGPhases m n base gs).maxRegister ≤ max (base + n + m) (2 * base) := by
  simp only [allGPhases]
  -- Prove by induction on the list
  have hfold : ∀ (xs : List (Fin m)) (init : Program),
      init.maxRegister ≤ max (base + n + m) (2 * base) →
      (xs.foldl (fun acc i => acc.concat (gPhase base n (gs i) i.val)) init).maxRegister
        ≤ max (base + n + m) (2 * base) := by
    intro xs init hinit
    induction xs generalizing init with
    | nil => exact hinit
    | cons hd tl ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [concat_maxRegister]
      have hgPhase := gPhase_maxRegister base n (gs hd) hd.val (hgs_bounded hd)
      have hi_lt : hd.val < m := hd.isLt
      -- gPhase bound: max (base + n + 1 + hd.val) (2 * base) ≤ max (base + n + m) (2 * base)
      have hgPhase' : (gPhase base n (gs hd) hd.val).maxRegister ≤ max (base + n + m) (2 * base) :=
        calc (gPhase base n (gs hd) hd.val).maxRegister
            ≤ max (base + n + 1 + hd.val) (2 * base) := hgPhase
          _ ≤ max (base + n + m) (2 * base) := by omega
      omega
  apply hfold
  simp [Program.maxRegister]

/-- MaxRegister of finalPhase is bounded by max(base + n + m, 2*base). -/
theorem finalPhase_maxRegister (m n base : ℕ) (f : URMBlock) (hf_bounded : f.maxReg ≤ base) :
    (finalPhase m n base f).maxRegister ≤ max (base + n + m) (2 * base) := by
  simp only [finalPhase]
  rw [concat_maxRegister, concat_maxRegister, concat_maxRegister]
  simp only [clearRegisters_maxRegister, single_transfer_maxRegister]
  -- Components:
  -- clearRegisters base: maxRegister = base
  -- transferResultsToInputs (base + n + 1) m: maxRegister ≤ base + n + m
  -- f.compile base: maxRegister ≤ f.maxReg + base ≤ 2*base
  -- [T base 0]: maxRegister = base
  have h1 : base ≤ max (base + n + m) (2 * base) := by omega
  have h2 : (transferResultsToInputs (base + n + 1) m).maxRegister ≤ max (base + n + m) (2 * base) := by
    have htrans := transferResultsToInputs_maxRegister (base + n + 1) m
    cases m with
    | zero => simp at htrans ⊢; omega
    | succ k =>
      simp only [Nat.add_succ_sub_one] at htrans
      calc (transferResultsToInputs (base + n + 1) (k + 1)).maxRegister
          ≤ max (base + n + 1 + k) k := htrans
        _ ≤ max (base + n + (k + 1)) (2 * base) := by omega
  have h3 : (f.compile base).maxRegister ≤ max (base + n + m) (2 * base) := by
    by_cases hp : f.program = []
    · simp [URMBlock.compile, hp, Program.shiftRegisters, Program.maxRegister]
    · simp only [URMBlock.compile, Program.maxRegister_shiftRegisters base f.program hp]
      -- Note: f.maxReg = f.program.maxRegister by definition
      calc f.program.maxRegister + base = f.maxReg + base := rfl
        _ ≤ base + base := Nat.add_le_add_right hf_bounded base
        _ ≤ max (base + n + m) (2 * base) := by omega
  have h4 : max base 0 ≤ max (base + n + m) (2 * base) := by omega
  omega

/-! ## Halting Helper Lemmas -/

/-- A single transfer instruction is straight-line. -/
private theorem single_transfer_isStraightLine (a b : ℕ) :
    Program.isStraightLine [Instr.T a b] = true := by
  rfl

/-- A single transfer instruction halts from any state. -/
private theorem single_transfer_halts_from_state (a b : ℕ) (s : State) :
    ∃ c, Steps [Instr.T a b] ⟨0, s⟩ c ∧ c.isHalted [Instr.T a b] := by
  obtain ⟨c, hsteps, hhalted, _⟩ := straightLine_halts_from_state (single_transfer_isStraightLine a b) s
  exact ⟨c, hsteps, hhalted⟩

/-- clearRegisters preserves registers strictly above base. -/
private theorem clearRegisters_preserves_above' (base : ℕ) (s : State) (r : ℕ) (hr : r > base) :
    (straightLineFinalState (clearRegisters_isStraightLine base) s).read r = s.read r :=
  clearRegisters_preserves_above base s r hr

/-- copyRegisterRange with "forward overlap" (src = dst + 1) still correctly copies values.
    Key insight: instruction k writes to (dstStart + k), so the source (dstStart + 1 + i)
    is never written by any instruction (would require k = 1 + i, but dstStart + 1 + i is
    in the source range, not the destination range).
    Note: This requires srcStart + count > dstStart + count - 1, i.e., srcStart > dstStart - 1,
    which is satisfied when srcStart = dstStart + 1. -/
private theorem copyRegisterRange_forward_overlap (srcStart dstStart count : ℕ)
    (hsrc : srcStart = dstStart + 1) (s : State) (i : ℕ) (hi : i < count) :
    (straightLineFinalState (copyRegisterRange_isStraightLine srcStart dstStart count) s).read (dstStart + i) =
    s.read (srcStart + i) := by
  have hsl := copyRegisterRange_isStraightLine srcStart dstStart count
  have hk : i < (Program.copyRegisterRange srcStart dstStart count).length := by simp [hi]
  have hwrite : (Program.copyRegisterRange srcStart dstStart count)[i] = Instr.T (srcStart + i) (dstStart + i) := by
    simp [Program.copyRegisterRange]
  have hnowrite : ∀ j (hj : j < (Program.copyRegisterRange srcStart dstStart count).length),
      i < j → ((Program.copyRegisterRange srcStart dstStart count)[j]'hj).writesTo ≠ some (dstStart + i) := by
    intro j hj hij
    simp only [Program.copyRegisterRange, List.getElem_map, List.getElem_range, Instr.writesTo,
               ne_eq, Option.some.injEq]; omega
  obtain ⟨s_before, ⟨c, hsteps, hpc, hs_eq⟩, hread_eq⟩ :=
    straightLine_transfer_result hsl s i (srcStart + i) (dstStart + i) hk hwrite hnowrite
  rw [hread_eq, ← hs_eq]
  -- Show: c.state.read (srcStart + i) = s.read (srcStart + i)
  -- The destination range is [dstStart, dstStart + count), source range is [srcStart, srcStart + count).
  -- Since srcStart = dstStart + 1, the source register (srcStart + i) = dstStart + 1 + i
  -- is never equal to any dstStart + k for k < count (would need k = 1 + i, but then
  -- dstStart + k = dstStart + 1 + i = srcStart + i, which means we'd be reading what we wrote,
  -- but the instruction writes to dstStart + k and reads from srcStart + k, not the same).
  -- Actually: no instruction writes to srcStart + i because all writes go to dstStart + k for k < count,
  -- and srcStart + i = dstStart + 1 + i > dstStart + count - 1 when i > count - 2, but also
  -- srcStart + i ≠ dstStart + k for k < count requires 1 + i ≠ k, which is true when k ≠ 1 + i.
  -- For k < count and k = 1 + i to hold, we need 1 + i < count, i.e., i < count - 1.
  -- So when i ≥ count - 1 (i.e., i = count - 1), no instruction writes to srcStart + i.
  -- When i < count - 1, instruction (1 + i) writes to dstStart + 1 + i = srcStart + i. BUT
  -- we only execute instructions 0..i-1 before reaching pc = i, and 1 + i > i, so instruction
  -- (1 + i) hasn't executed yet!
  -- Key insight: instructions 0..i-1 are executed to reach c with pc = i.
  -- Each instruction k writes to dstStart + k. The source register srcStart + i = dstStart + 1 + i.
  -- For k < i: dstStart + k ≠ dstStart + 1 + i since k < 1 + i.
  -- Use Steps.straightLine_preserves_partial with k = i and r = srcStart + i.
  have hnowrite_src : ∀ j (hj : j < i),
      ((Program.copyRegisterRange srcStart dstStart count)[j]'(Nat.lt_trans hj hk)).writesTo ≠ some (srcStart + i) := by
    intro j hj
    simp only [Program.copyRegisterRange, List.getElem_map, List.getElem_range, Instr.writesTo,
               ne_eq, Option.some.injEq, hsrc]
    omega
  exact Steps.straightLine_preserves_partial hsl (Nat.le_of_lt hk) hnowrite_src c hsteps hpc

/-- After clear + copy, the state agrees with the saved inputs.
    Precondition: inputs are saved at registers base+1..base+n in σ. -/
theorem gPhase_after_clear_copy (base n : ℕ) (inputs : Fin n → ℕ)
    (σ : State) (hSaved : ∀ j : ℕ, (hj : j < n) → σ.read (base + 1 + j) = inputs ⟨j, hj⟩)
    (_hn_le : n ≤ base + 1) :
    let σ_clear := straightLineFinalState (clearRegisters_isStraightLine base) σ
    let σ_copy := straightLineFinalState (copyRegisterRange_isStraightLine (base + 1) base n) σ_clear
    ∀ r : ℕ, (hr : r < n) → σ_copy.read (base + r) = inputs ⟨r, hr⟩ := by
  intro σ_clear σ_copy r hr
  -- Use the forward overlap lemma
  have hcopy := copyRegisterRange_forward_overlap (base + 1) base n rfl σ_clear r hr
  rw [hcopy]
  -- σ_clear preserves registers above base (and base+1+r > base)
  have hclear_preserves := clearRegisters_preserves_above' base σ (base + 1 + r) (by omega)
  rw [hclear_preserves, hSaved r hr]

/-! ## The Compose Combinator -/

/-- Compute the maximum register used by the composed program.
    The bound must account for:
    - base + n + m (last result slot at base + n + m)
    - 2 * base (workspace when compiling f or gi at offset base, since their maxReg ≤ base) -/
def composeMaxReg (n : ℕ) (f : URMBlock) (m : ℕ) (gs : Fin m → URMBlock) : ℕ :=
  let base := composeBase n f m gs
  max (base + n + m) (2 * base)

/-- The composition combinator: h(x) = f(g₁(x), ..., gₘ(x)).

Given:
- f : URMBlock with arity m (takes m inputs)
- gs : Fin m → URMBlock each with arity n (each takes n inputs)

Produces a block with arity n that computes the composition. -/
def compose (n : ℕ) (f : URMBlock) (m : ℕ) [NeZero m] (gs : Fin m → URMBlock)
    (hf_arity : f.arity = m) (hgs_arity : ∀ i, (gs i).arity = n) : URMBlock where
  program := composeProgram n f m gs
  arity := n
  h_sf := by
    -- TODO: Prove that composeProgram is in standard form
    -- This requires showing that all jumps in the composed program are bounded
    sorry

/-! ## Halting Helper Lemmas for Backward Direction -/

/-- gPhase halts when g is defined on the inputs that are saved at base+1..base+n.
    Returns: a configuration with the result saved at base+n+1+i. -/
theorem gPhase_halts_from_saved (base n : ℕ) (g : URMBlock) (i : ℕ)
    (gFunc : (Fin n → ℕ) → Part ℕ)
    (hg_computes : g.ComputesN n gFunc)
    (hg_bounded : g.maxReg ≤ base)
    (hn_le : n ≤ base + 1)
    (inputs : Fin n → ℕ)
    (hg_dom : (gFunc inputs).Dom)
    (σ : State)
    (hSaved : ∀ j : ℕ, (hj : j < n) → σ.read (base + 1 + j) = inputs ⟨j, hj⟩) :
    ∃ c, Steps (gPhase base n g i) ⟨0, σ⟩ c ∧ c.isHalted (gPhase base n g i) ∧
         c.state.read (base + n + 1 + i) = (gFunc inputs).get hg_dom := by
  -- gPhase = clear.concat(copy.concat(compile.concat [transfer]))
  -- We chain 4 phases: clear, copy, g.compile, transfer
  simp only [gPhase]
  -- Phase 1: clearRegisters halts (straight-line)
  let p_clear := clearRegisters base
  let p_copy := copyRegisterRange (base + 1) base n
  let p_compile := g.compile base
  let p_transfer := [Instr.T base (base + n + 1 + i)]
  have hclear_sl := clearRegisters_isStraightLine base
  have hspec1 := straightLineFinalState_spec hclear_sl σ
  let c1 := Classical.choose (straightLine_halts_from_state hclear_sl σ)
  have hsteps1 : Steps p_clear ⟨0, σ⟩ c1 := hspec1.1
  have hhalted1 : c1.isHalted p_clear := hspec1.2.1
  have hpc1 : c1.pc = p_clear.length := hspec1.2.2
  -- Phase 2: copyRegisterRange halts (straight-line)
  have hcopy_sl := copyRegisterRange_isStraightLine (base + 1) base n
  let σ1 := c1.state
  have hspec2 := straightLineFinalState_spec hcopy_sl σ1
  let c2 := Classical.choose (straightLine_halts_from_state hcopy_sl σ1)
  have hsteps2 : Steps p_copy ⟨0, σ1⟩ c2 := hspec2.1
  have hhalted2 : c2.isHalted p_copy := hspec2.2.1
  have hpc2 : c2.pc = p_copy.length := hspec2.2.2
  -- After clear + copy, inputs are at base..base+n-1
  have hInputsReady : ∀ r (hr : r < n), c2.state.read (base + r) = inputs ⟨r, hr⟩ := by
    intro r hr
    -- clearRegisters preserves base+1..base+n (where inputs are saved)
    have hclear_preserves : ∀ j (hj : j < n), c1.state.read (base + 1 + j) = σ.read (base + 1 + j) := by
      intro j hj
      have heq := straightLineFinalState_eq_of_halted hclear_sl σ c1 hsteps1 hhalted1
      rw [heq]
      exact clearRegisters_preserves_above base σ (base + 1 + j) (by omega)
    -- copyRegisterRange copies from base+1..base+n to base..base+n-1
    have hcopy_eq := straightLineFinalState_eq_of_halted hcopy_sl σ1 c2 hsteps2 hhalted2
    rw [hcopy_eq]
    have hcopy := copyRegisterRange_forward_overlap (base + 1) base n rfl σ1 r hr
    rw [hcopy, hclear_preserves r hr, hSaved r hr]
  -- Phase 3: g.compile halts using Halts.shift_from_state
  let σ2 := c2.state
  -- Create the init state agreement for the compiled block
  have hInitState : ∀ r, r ≤ g.program.maxRegister →
      σ2.read (r + base) = (List.ofFn inputs).getD r 0 := by
    intro r hr
    by_cases hrn : r < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hrn, ↓reduceDIte, Option.getD_some]
      show c2.state.read (r + base) = inputs ⟨r, hrn⟩
      rw [show r + base = base + r by omega, hInputsReady r hrn]
    · push_neg at hrn
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]
      -- Register r is outside input range, was cleared
      -- σ2 = c2.state, so we work with c2.state directly
      show c2.state.read (r + base) = 0
      rw [show r + base = base + r by omega]
      have heq := straightLineFinalState_eq_of_halted hcopy_sl σ1 c2 hsteps2 hhalted2
      rw [heq]
      have hcopy_preserves := copyRegisterRange_preserves (base + 1) base n σ1 (base + r)
        (by right; omega)
      rw [hcopy_preserves]
      have heq1 := straightLineFinalState_eq_of_halted hclear_sl σ c1 hsteps1 hhalted1
      simp only [σ1, heq1]
      -- Note: clearRegisters base zeros 0..base, but we need base+r (where r ≤ g.maxReg ≤ base)
      -- This requires proving that σ already has zeros in the range base..2*base
      -- or that the compile phase uses shifted registers so r+base should be within 0..base
      sorry -- TODO: fix the register range logic
  -- Get halting of g.program
  have hhalts_g : Halts g.program (List.ofFn inputs) := (hg_computes inputs).1.mpr hg_dom
  -- Use Halts.shift_from_state to run g.compile from σ2
  obtain ⟨c3, hsteps3, hhalted3, hresult3⟩ := Halts.shift_from_state base hhalts_g hInitState
  -- Phase 4: transfer instruction halts (single instruction)
  let σ3 := c3.state
  have htransfer_step : Step p_transfer ⟨0, σ3⟩ ⟨1, σ3.write (base + n + 1 + i) (σ3.read base)⟩ := by
    exact Step.trans (by simp [p_transfer, Program.getInstr])
  let c4 : Config := ⟨1, σ3.write (base + n + 1 + i) (σ3.read base)⟩
  have hsteps4 : Steps p_transfer ⟨0, σ3⟩ c4 := Relation.ReflTransGen.single htransfer_step
  have hhalted4 : c4.isHalted p_transfer := by simp [Config.isHalted, p_transfer, c4]
  -- Chain all phases through the concat structure
  -- The chaining is tedious but straightforward using:
  -- - Steps.concat_left_prefix_interior for first-part steps
  -- - Steps.concat_right for second-part steps
  -- - Relation.ReflTransGen.trans to chain them
  -- For now, we leave this as sorry and focus on higher-level structure
  let c_final_state := c4.state
  let c_final_pc := p_clear.length + p_copy.length + p_compile.length + 1
  have hresult : c_final_state.read (base + n + 1 + i) = (gFunc inputs).get hg_dom := by
    simp only [c_final_state, c4, State.write_read_same]
    sorry -- TODO: connect hresult3 to the goal
  sorry

/-- All g phases halt when all gs are defined. -/
theorem allGPhases_halts_from_saved (m n base : ℕ) (gs : Fin m → URMBlock)
    (gsFunc : Fin m → (Fin n → ℕ) → Part ℕ)
    (hgs_computes : ∀ i, (gs i).ComputesN n (gsFunc i))
    (hgs_bounded : ∀ i, (gs i).maxReg ≤ base)
    (hn_le : n ≤ base + 1)
    (inputs : Fin n → ℕ)
    (hgs_dom : ∀ i, (gsFunc i inputs).Dom)
    (σ : State)
    (hSaved : ∀ j : ℕ, (hj : j < n) → σ.read (base + 1 + j) = inputs ⟨j, hj⟩) :
    ∃ c, Steps (allGPhases m n base gs) ⟨0, σ⟩ c ∧ c.isHalted (allGPhases m n base gs) ∧
         (∀ i : Fin m, c.state.read (base + n + 1 + i.val) = (gsFunc i inputs).get (hgs_dom i)) := by
  -- Induction on m
  sorry

/-- Final phase halts when f is defined on the results. -/
theorem finalPhase_halts_from_results (m n base : ℕ) (f : URMBlock)
    (fFunc : (Fin m → ℕ) → Part ℕ)
    (hf_computes : f.ComputesN m fFunc)
    (hf_bounded : f.maxReg ≤ base)
    (hm_le : m ≤ base + 1)
    (results : Fin m → ℕ)
    (hf_dom : (fFunc results).Dom)
    (σ : State)
    (hResults : ∀ i : Fin m, σ.read (base + n + 1 + i.val) = results i) :
    ∃ c, Steps (finalPhase m n base f) ⟨0, σ⟩ c ∧ c.isHalted (finalPhase m n base f) ∧
         c.state.read 0 = (fFunc results).get hf_dom := by
  sorry

/-! ## Correctness -/

/-- The composed function. -/
def compFunction (n m : ℕ) (fFunc : (Fin m → ℕ) → Part ℕ)
    (gsFunc : Fin m → (Fin n → ℕ) → Part ℕ) : (Fin n → ℕ) → Part ℕ :=
  fun inputs => (Part.sequence (fun i => gsFunc i inputs)).bind fFunc

/-- Composition correctness theorem.

If f computes fFunc and each gᵢ computes gsFunc i, then
compose n f m gs computes compFunction n m fFunc gsFunc. -/
theorem compose_correct (n : ℕ) (f : URMBlock) (m : ℕ) [NeZero m]
    (gs : Fin m → URMBlock)
    (fFunc : (Fin m → ℕ) → Part ℕ)
    (gsFunc : Fin m → (Fin n → ℕ) → Part ℕ)
    (hf_arity : f.arity = m)
    (hgs_arity : ∀ i, (gs i).arity = n)
    (hf_computes : f.ComputesN m fFunc)
    (hgs_computes : ∀ i, (gs i).ComputesN n (gsFunc i)) :
    (compose n f m gs hf_arity hgs_arity).ComputesN n (compFunction n m fFunc gsFunc) := by
  intro inputs
  simp only [compFunction]
  constructor
  · -- Halting equivalence
    constructor
    · -- Forward: composed program halts → function defined
      intro hHalts
      -- Each gᵢ must halt, then f must halt on the results
      sorry
    · -- Backward: function defined → composed program halts
      intro hDom
      -- Use bind_dom to decompose
      rw [Part.bind_dom] at hDom
      obtain ⟨hSeq_dom, hf_dom⟩ := hDom
      -- Each gᵢ is defined
      have hgs_dom : ∀ i, (gsFunc i inputs).Dom := Part.sequence_dom.mp hSeq_dom
      -- Setup: get base and bounds
      let base := composeBase n f m gs
      have hgs_bounded : ∀ i, (gs i).maxReg ≤ base := fun i => composeBase_ge_gi n f m gs i
      have hf_bounded : f.maxReg ≤ base := composeBase_ge_f n f m gs
      have hn_le : n ≤ base + 1 := composeBase_ge_n n f m gs
      have hm_le : m ≤ base + 1 := composeBase_ge_m n f m gs
      -- Phase 1: Save inputs from [0..n-1] to [base+1..base+n] (straight-line, always halts)
      have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
      let σ_init := State.fromInputs (List.ofFn inputs)
      obtain ⟨cSave, hSave_steps, hSave_halted, _⟩ :=
        straightLine_halts_from_state hSave_sl σ_init
      -- After saving, inputs are at base+1..base+n
      have hSaved : ∀ j : ℕ, (hj : j < n) → cSave.state.read (base + 1 + j) = inputs ⟨j, hj⟩ := by
        intro j hj
        -- Connect cSave.state to straightLineFinalState
        have hstate_eq := straightLineFinalState_eq_of_halted hSave_sl σ_init cSave hSave_steps hSave_halted
        rw [hstate_eq]
        -- Use saveInputs_state from Preservation.lean
        exact saveInputs_state base n hn_le inputs j hj
      -- Phase 2: Run all g phases using allGPhases_halts_from_saved
      -- This produces results at base+n+1..base+n+m
      have hSeq_get : (Part.sequence fun i => gsFunc i inputs).get hSeq_dom = fun i =>
          (gsFunc i inputs).get (hgs_dom i) := by
        funext i; exact Part.sequence_get hSeq_dom i
      let results : Fin m → ℕ := fun i => (gsFunc i inputs).get (hgs_dom i)
      obtain ⟨cGPhases, hGPhases_steps, hGPhases_halted, hResults⟩ :=
        allGPhases_halts_from_saved m n base gs gsFunc hgs_computes hgs_bounded hn_le inputs
          hgs_dom cSave.state hSaved
      -- Phase 3: Run final phase using finalPhase_halts_from_results
      -- Need to show fFunc results is defined
      have hf_results_dom : (fFunc results).Dom := by
        -- results = fun i => (gsFunc i inputs).get (hgs_dom i)
        -- hf_dom says: (fFunc (Part.sequence ...).get hSeq_dom).Dom
        -- Since Part.sequence.get = results, this is the same
        convert hf_dom using 1
        congr 1
        exact hSeq_get.symm
      obtain ⟨cFinal, hFinal_steps, hFinal_halted, _⟩ :=
        finalPhase_halts_from_results m n base f fFunc hf_computes hf_bounded hm_le results
          hf_results_dom cGPhases.state hResults
      -- Chain all steps together
      -- composeProgram = saveInputs.concat(allGPhases.concat(finalPhase))
      sorry -- TODO: Use concat lemmas to chain Steps
  · -- Result correctness
    intro hHalts hDom
    sorry

end URMBlock

end Urm
