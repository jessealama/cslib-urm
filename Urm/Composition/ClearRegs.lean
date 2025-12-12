/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.JumpsBounded.SeqSecond

/-! # Register Clearing Operations

This file defines operations to clear (zero out) ranges of registers.

## Main definitions

- `Urm.clearRegsFrom1`: Zero out registers 1 through k
- `Urm.clearRegsRange`: Zero out registers base through base+count-1
- `Urm.State.clearFrom1`: State after clearing registers 1..k
-/

namespace Urm

/-- Zero out registers 1 through k (used to prepare clean state for composition). -/
def clearRegsFrom1 (k : ℕ) : Program :=
  (List.range k).map fun i => Instr.Z (i + 1)

@[simp]
theorem clearRegsFrom1_length (k : ℕ) : (clearRegsFrom1 k).length = k := by
  simp [clearRegsFrom1]

/-- The instruction at position i in clearRegsFrom1 k is Z (i+1). -/
theorem clearRegsFrom1_getInstr (k i : ℕ) (hi : i < k) :
    (clearRegsFrom1 k).getInstr i = some (Instr.Z (i + 1)) := by
  simp only [clearRegsFrom1, Program.getInstr, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp; exact hi)]
  simp [List.getElem_range]

/-- clearRegsFrom1 k has bounded jumps (it has no jumps at all). -/
theorem clearRegsFrom1_bounded (k : ℕ) : JumpsBounded (clearRegsFrom1 k) := by
  intro i hi m n q hinstr
  simp only [clearRegsFrom1, Program.getInstr, List.getElem?_map] at hinstr
  rw [clearRegsFrom1_length] at hi
  rw [List.getElem?_eq_getElem (by simp; exact hi)] at hinstr
  simp only [List.getElem_range, Option.map_some] at hinstr
  -- hinstr : some (Instr.Z (i + 1)) = some (Instr.J m n q) - contradiction
  cases hinstr

/-- The clearing program halts in exactly k steps. -/
theorem clearRegsFrom1_haltsIn (k : ℕ) (inputs : List ℕ) :
    HaltsIn (clearRegsFrom1 k) k inputs := by
  -- We construct the execution: starting at PC=0, each Z instruction advances PC by 1
  -- After k steps, PC=k which equals the program length, so we're halted
  -- Define the state after executing i instructions
  let stateAfter (σ : State) (i : ℕ) := (List.range i).foldl (fun s j => s.write (j + 1) 0) σ
  -- Prove by induction that after i steps, we reach PC=i with the appropriate state
  have hsteps : ∀ i ≤ k, ∀ σ : State,
      StepsN (clearRegsFrom1 k) i ⟨0, σ⟩ ⟨i, stateAfter σ i⟩ := by
    intro i
    induction i with
    | zero =>
      intro _ σ
      simp only [stateAfter, List.range_zero, List.foldl_nil]
      exact StepsN.zero _
    | succ j ihj =>
      intro hj σ
      have hj' : j ≤ k := Nat.le_of_succ_le hj
      have hjbound : j < k := Nat.lt_of_succ_le hj
      -- First take j steps to reach PC=j
      have steps_j := ihj hj' σ
      -- Then take one more step: execute Z (j+1)
      have hinstr : (clearRegsFrom1 k).getInstr j = some (Instr.Z (j + 1)) :=
        clearRegsFrom1_getInstr k j hjbound
      have hstep : Step (clearRegsFrom1 k) ⟨j, stateAfter σ j⟩ ⟨j + 1, (stateAfter σ j).write (j + 1) 0⟩ :=
        Step.zero hinstr
      -- Show that stateAfter σ (j+1) = (stateAfter σ j).write (j+1) 0
      have hstate_eq : stateAfter σ (j + 1) = (stateAfter σ j).write (j + 1) 0 := by
        simp only [stateAfter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      -- Combine using StepsN.add
      rw [hstate_eq]
      exact StepsN.add steps_j (StepsN.succ hstep (StepsN.zero _))
  -- Apply with i = k
  refine ⟨⟨k, stateAfter (State.fromInputs inputs) k⟩, hsteps k (Nat.le_refl k) _, ?_⟩
  -- Prove halted: PC = k = length
  simp [Config.isHalted]

/-- The clearing program halts on any state. -/
theorem clearRegsFrom1_halts (k : ℕ) (inputs : List ℕ) : Halts (clearRegsFrom1 k) inputs :=
  (clearRegsFrom1_haltsIn k inputs).toHalts

/-- State after clearing registers 1..k: R[0] unchanged, R[1..k] = 0. -/
def State.clearFrom1 (σ : State) (k : ℕ) : State :=
  fun n => if n = 0 then σ 0 else if n ≤ k then 0 else σ n

/-- Helper: the foldl-based state computation equals clearFrom1. -/
private theorem foldl_write_eq_clearFrom1 (σ : State) (k : ℕ) :
    (List.range k).foldl (fun s j => s.write (j + 1) 0) σ = σ.clearFrom1 k := by
  funext n
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, State.clearFrom1]
    split_ifs with h1 h2
    · subst h1; rfl
    · omega  -- n ≠ 0 but n ≤ 0
    · rfl
  | succ k ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    -- LHS: ((foldl ... σ (range k)).write (k+1) 0) n
    -- RHS: (σ.clearFrom1 (k+1)) n
    simp only [State.clearFrom1]
    by_cases h_eq : n = k + 1
    · -- n = k+1: LHS writes 0, RHS gives 0 since n ≤ k+1
      simp only [h_eq, if_true, Nat.le_refl, if_neg (Nat.succ_ne_zero k)]
      simp only [State.write, Function.update_self]
    · -- n ≠ k+1: LHS reads from foldl result
      have h_update : ((List.range k).foldl (fun s j => s.write (j + 1) 0) σ).write (k + 1) 0 n =
                      (List.range k).foldl (fun s j => s.write (j + 1) 0) σ n := by
        simp only [State.write, Function.update, h_eq, dite_false]
      rw [h_update, ih]
      simp only [State.clearFrom1]
      -- σ.clearFrom1 k n = if n = 0 then σ 0 else if n ≤ k+1 then 0 else σ n
      -- LHS: if n = 0 then σ 0 else if n ≤ k then 0 else σ n
      split_ifs with h0 hle_k1 hle_k
      · rfl  -- n = 0
      · rfl  -- n ≠ 0, n ≤ k+1, n ≤ k: both give 0
      · omega  -- n ≠ 0, n ≤ k+1, n > k: n = k+1, contradicts h_eq
      · omega  -- n ≠ 0, n > k+1, n ≤ k: impossible
      · rfl  -- n ≠ 0, n > k+1, n > k: both give σ n

/-- Running clearRegsFrom1 k from state σ reaches state σ.clearFrom1 k at PC = k. -/
theorem clearRegsFrom1_reaches_clearFrom1 (k : ℕ) (σ : State) :
    Steps (clearRegsFrom1 k) ⟨0, σ⟩ ⟨k, σ.clearFrom1 k⟩ := by
  -- Use the same construction as clearRegsFrom1_haltsIn
  let stateAfter (σ' : State) (i : ℕ) := (List.range i).foldl (fun s j => s.write (j + 1) 0) σ'
  -- Prove steps to stateAfter σ k
  have hsteps : ∀ i ≤ k, StepsN (clearRegsFrom1 k) i ⟨0, σ⟩ ⟨i, stateAfter σ i⟩ := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [stateAfter, List.range_zero, List.foldl_nil]
      exact StepsN.zero _
    | succ j ihj =>
      intro hj
      have hj' : j ≤ k := Nat.le_of_succ_le hj
      have hjbound : j < k := Nat.lt_of_succ_le hj
      have steps_j := ihj hj'
      have hinstr : (clearRegsFrom1 k).getInstr j = some (Instr.Z (j + 1)) :=
        clearRegsFrom1_getInstr k j hjbound
      have hstep : Step (clearRegsFrom1 k) ⟨j, stateAfter σ j⟩ ⟨j + 1, (stateAfter σ j).write (j + 1) 0⟩ :=
        Step.zero hinstr
      have hstate_eq : stateAfter σ (j + 1) = (stateAfter σ j).write (j + 1) 0 := by
        simp only [stateAfter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hstate_eq]
      exact StepsN.add steps_j (StepsN.succ hstep (StepsN.zero _))
  -- stateAfter σ k = σ.clearFrom1 k by foldl_write_eq_clearFrom1
  have hstate : stateAfter σ k = σ.clearFrom1 k := foldl_write_eq_clearFrom1 σ k
  rw [← hstate]
  exact (hsteps k (Nat.le_refl _)).toSteps

/-- A cleared state agrees with `State.fromInputs [v]` on registers 0..k when R[0] = v. -/
theorem State.clearFrom1_eq_fromInputs_on_range (σ : State) (k : ℕ) (n : ℕ) (hn : n ≤ k) :
    (σ.clearFrom1 k) n = (State.fromInputs [σ 0]) n := by
  simp only [clearFrom1, fromInputs, List.getD]
  cases n with
  | zero => simp
  | succ n' =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_le_iff] at hn ⊢
    simp [hn]

/-- The output of a cleared state equals the original output. -/
@[simp]
theorem State.clearFrom1_output (σ : State) (k : ℕ) : (σ.clearFrom1 k).output = σ.output := by
  simp [clearFrom1, output]

/-- Clearing from 1 to 0 is identity (nothing to clear). -/
@[simp]
theorem State.clearFrom1_zero (σ : State) : σ.clearFrom1 0 = σ := by
  funext r
  simp only [clearFrom1]
  split_ifs with h h'
  · subst h; rfl  -- r = 0
  · omega  -- r ≠ 0 but r ≤ 0, impossible for ℕ
  · rfl  -- r > 0

/-- Lift clearing steps to the first part of a sequential composition.
    This handles both k=0 (clearing is empty) and k>0 (use seq_steps_first). -/
theorem Steps.clearRegsFrom1_in_seq (k : ℕ) (p : Program) (σ : State) :
    Steps ((clearRegsFrom1 k).seq p) ⟨0, σ⟩ ⟨k, σ.clearFrom1 k⟩ := by
  by_cases hk : k = 0
  · simp only [hk, clearRegsFrom1, Program.seq, List.range_zero, List.map_nil, List.nil_append,
               List.length_nil, Program.shiftJumps_zero, State.clearFrom1_zero]
    exact Steps.refl _
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    have hclear_steps := clearRegsFrom1_reaches_clearFrom1 k σ
    apply Steps.seq_steps_first hclear_steps
    · simp only [clearRegsFrom1_length]; exact hk_pos
    · simp

/-! ## clearRegsRange: Clear an Arbitrary Range of Registers -/

/-- Zero out registers base, base+1, ..., base+count-1. -/
def clearRegsRange (base count : ℕ) : Program :=
  (List.range count).map fun i => Instr.Z (base + i)

@[simp]
theorem clearRegsRange_length (base count : ℕ) : (clearRegsRange base count).length = count := by
  simp [clearRegsRange]

/-- The instruction at position i in clearRegsRange base count is Z (base + i). -/
theorem clearRegsRange_getInstr (base count i : ℕ) (hi : i < count) :
    (clearRegsRange base count).getInstr i = some (Instr.Z (base + i)) := by
  simp only [clearRegsRange, Program.getInstr, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp; exact hi)]
  simp [List.getElem_range]

/-- clearRegsRange has bounded jumps (it has no jumps at all). -/
theorem clearRegsRange_bounded (base count : ℕ) : JumpsBounded (clearRegsRange base count) := by
  intro i hi m n q hinstr
  simp only [clearRegsRange, Program.getInstr, List.getElem?_map] at hinstr
  rw [clearRegsRange_length] at hi
  rw [List.getElem?_eq_getElem (by simp; exact hi)] at hinstr
  simp only [List.getElem_range, Option.map_some] at hinstr
  cases hinstr

/-- The clearing program halts in exactly count steps. -/
theorem clearRegsRange_haltsIn (base count : ℕ) (inputs : List ℕ) :
    HaltsIn (clearRegsRange base count) count inputs := by
  let stateAfter (σ : State) (i : ℕ) := (List.range i).foldl (fun s j => s.write (base + j) 0) σ
  have hsteps : ∀ i ≤ count, ∀ σ : State,
      StepsN (clearRegsRange base count) i ⟨0, σ⟩ ⟨i, stateAfter σ i⟩ := by
    intro i
    induction i with
    | zero =>
      intro _ σ
      simp only [stateAfter, List.range_zero, List.foldl_nil]
      exact StepsN.zero _
    | succ j ihj =>
      intro hj σ
      have hj' : j ≤ count := Nat.le_of_succ_le hj
      have hjbound : j < count := Nat.lt_of_succ_le hj
      have steps_j := ihj hj' σ
      have hinstr : (clearRegsRange base count).getInstr j = some (Instr.Z (base + j)) :=
        clearRegsRange_getInstr base count j hjbound
      have hstep : Step (clearRegsRange base count) ⟨j, stateAfter σ j⟩
                        ⟨j + 1, (stateAfter σ j).write (base + j) 0⟩ :=
        Step.zero hinstr
      have hstate_eq : stateAfter σ (j + 1) = (stateAfter σ j).write (base + j) 0 := by
        simp only [stateAfter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hstate_eq]
      exact StepsN.add steps_j (StepsN.succ hstep (StepsN.zero _))
  refine ⟨⟨count, stateAfter (State.fromInputs inputs) count⟩, hsteps count (Nat.le_refl count) _, ?_⟩
  simp [Config.isHalted]

/-- The clearing program halts on any state. -/
theorem clearRegsRange_halts (base count : ℕ) (inputs : List ℕ) :
    Halts (clearRegsRange base count) inputs :=
  (clearRegsRange_haltsIn base count inputs).toHalts

/-- State after clearing a range of registers: R[base..base+count-1] = 0. -/
def State.clearRange (σ : State) (base count : ℕ) : State :=
  fun n => if base ≤ n ∧ n < base + count then 0 else σ n

/-- Helper: state after i clear operations from base. -/
private def clearRegsRange_stateAfter (σ : State) (base : ℕ) (i : ℕ) : State :=
  (List.range i).foldl (fun s j => s.write (base + j) 0) σ

/-- The foldl-based state equals clearRange. -/
private theorem clearRegsRange_stateAfter_eq_clearRange (σ : State) (base count : ℕ) :
    clearRegsRange_stateAfter σ base count = σ.clearRange base count := by
  funext n
  simp only [clearRegsRange_stateAfter, State.write]
  induction count with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, State.clearRange]
    split_ifs with h
    · omega
    · rfl
  | succ k ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h_eq : n = base + k
    · subst h_eq
      simp only [Function.update_self, State.clearRange]
      split_ifs with h
      · rfl
      · omega
    · simp only [Function.update, h_eq, dite_false]
      rw [ih]
      simp only [State.clearRange]
      split_ifs with h1 h2
      · rfl
      · omega
      · omega
      · rfl

/-- Running clearRegsRange from state σ reaches the expected state. -/
theorem clearRegsRange_reaches (base count : ℕ) (σ : State) :
    Steps (clearRegsRange base count) ⟨0, σ⟩ ⟨count, σ.clearRange base count⟩ := by
  have hsteps : ∀ i ≤ count, StepsN (clearRegsRange base count) i ⟨0, σ⟩
      ⟨i, clearRegsRange_stateAfter σ base i⟩ := by
    intro i hi
    induction i with
    | zero =>
      simp only [clearRegsRange_stateAfter, List.range_zero, List.foldl_nil]
      exact StepsN.zero _
    | succ j ihj =>
      have hj' : j ≤ count := Nat.le_of_succ_le hi
      have hjbound : j < count := Nat.lt_of_succ_le hi
      have steps_j := ihj hj'
      have hinstr := clearRegsRange_getInstr base count j hjbound
      have hstep : Step (clearRegsRange base count)
          ⟨j, clearRegsRange_stateAfter σ base j⟩
          ⟨j + 1, (clearRegsRange_stateAfter σ base j).write (base + j) 0⟩ :=
        Step.zero hinstr
      have hstate_eq : clearRegsRange_stateAfter σ base (j + 1) =
          (clearRegsRange_stateAfter σ base j).write (base + j) 0 := by
        simp only [clearRegsRange_stateAfter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hstate_eq]
      exact StepsN.add steps_j (StepsN.succ hstep (StepsN.zero _))
  have hstepsN := hsteps count (Nat.le_refl count)
  rw [clearRegsRange_stateAfter_eq_clearRange] at hstepsN
  exact hstepsN.toSteps

/-- Lift clearRegsRange steps to the first part of a sequential composition. -/
theorem Steps.clearRegsRange_in_seq (base count : ℕ) (p : Program) (σ : State) :
    Steps ((clearRegsRange base count).seq p) ⟨0, σ⟩ ⟨count, σ.clearRange base count⟩ := by
  by_cases hcount : count = 0
  · subst hcount
    have hclear : σ.clearRange base 0 = σ := by
      funext r
      simp only [State.clearRange, Nat.add_zero]
      split_ifs with h
      · omega
      · rfl
    simp only [hclear]
    exact Steps.refl _
  · have hcount_pos : 0 < count := Nat.pos_of_ne_zero hcount
    have hclear_steps := clearRegsRange_reaches base count σ
    apply Steps.seq_steps_first hclear_steps
    · simp only [clearRegsRange_length]; exact hcount_pos
    · simp

end Urm
