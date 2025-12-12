/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.ClearRegs

/-! # copyRegs Execution Lemmas

This file proves execution properties for the copyRegs register copying operation.

## Main definitions

- `Urm.State.afterCopy`: Semantic state after copy operation
- `Urm.copyRegs_bounded`: copyRegs has no jumps
- `Urm.copyRegs_reaches`: Stepping behavior of copyRegs
- `Urm.copyRegs_halts`: copyRegs always halts
-/

namespace Urm

/-- copyRegs has bounded jumps (it has no jumps at all). -/
theorem copyRegs_bounded (cnt srcBase dstBase : ℕ) : JumpsBounded (copyRegs cnt srcBase dstBase) := by
  intro i hi m n q hinstr
  simp only [copyRegs, Program.getInstr, List.getElem?_map] at hinstr
  rw [copyRegs_length] at hi
  rw [List.getElem?_eq_getElem (by simp; exact hi)] at hinstr
  simp only [List.getElem_finRange, Option.map_some] at hinstr
  -- hinstr : some (Instr.T ...) = some (Instr.J m n q) - contradiction
  cases hinstr

/-- State after copying registers: destination registers contain copies of source registers.
    Note: This is a semantic definition - the actual copying behavior depends on
    whether source and destination ranges overlap. -/
def State.afterCopy (σ : State) (cnt srcBase dstBase : ℕ) : State :=
  fun r =>
    if dstBase ≤ r ∧ r < dstBase + cnt then
      σ (srcBase + (r - dstBase))
    else
      σ r

/-- After copyRegs, destination registers contain copies from source (semantic definition). -/
theorem State.afterCopy_read_dst (σ : State) (cnt srcBase dstBase : ℕ) (i : ℕ) (hi : i < cnt) :
    (σ.afterCopy cnt srcBase dstBase) (dstBase + i) = σ (srcBase + i) := by
  simp only [afterCopy]
  split_ifs with h
  · simp only [Nat.add_sub_cancel_left]
  · omega

/-- After copyRegs, registers outside the destination range are unchanged. -/
theorem State.afterCopy_read_other (σ : State) (cnt srcBase dstBase : ℕ) (r : ℕ)
    (h : r < dstBase ∨ dstBase + cnt ≤ r) :
    (σ.afterCopy cnt srcBase dstBase) r = σ r := by
  simp only [afterCopy]
  split_ifs with h'
  · omega
  · rfl

/-- Helper: state after i copy operations. -/
private def copyRegs_stateAfter (σ : State) (srcBase dstBase : ℕ) (i : ℕ) : State :=
  (List.range i).foldl (fun s j => s.write (dstBase + j) (σ (srcBase + j))) σ

/-- Reading source register from intermediate copyRegs state gives original value
    (when ranges don't overlap). -/
private theorem copyRegs_stateAfter_preserves_src (σ : State) (srcBase dstBase j : ℕ)
    (hdisjoint : ∀ k < j, srcBase + j ≠ dstBase + k) :
    (copyRegs_stateAfter σ srcBase dstBase j) (srcBase + j) = σ (srcBase + j) := by
  simp only [copyRegs_stateAfter]
  -- The foldl writes to dstBase + 0, ..., dstBase + (j-1)
  -- We're reading srcBase + j, which by hdisjoint is different from all of those
  induction j with
  | zero => simp [List.range_zero, List.foldl_nil]
  | succ k ihk =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [State.write, Function.update]
    have h_ne : srcBase + (k + 1) ≠ dstBase + k := hdisjoint k (Nat.lt_succ_self k)
    simp only [h_ne, dite_false]
    -- Now need to show the inner foldl (range k) at position srcBase + (k+1) = σ (srcBase + (k+1))
    -- The inner foldl writes to dstBase + 0, ..., dstBase + (k-1)
    -- Prove by a simpler approach: the foldl only writes to dstBase+i for i < k
    -- and srcBase + (k+1) ≠ dstBase + i for all i < k (by hdisjoint)
    -- We use a general helper lemma about foldl preserving other positions
    clear ihk
    suffices h : ∀ m ≤ k, (List.range m).foldl (fun s j => s.write (dstBase + j) (σ (srcBase + j))) σ
        (srcBase + (k + 1)) = σ (srcBase + (k + 1)) by
      exact h k (Nat.le_refl k)
    intro m hm
    induction m with
    | zero => simp [List.range_zero, List.foldl_nil]
    | succ n ihn =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [State.write, Function.update]
      have hn_lt_j : n < k + 1 := by omega
      have h_ne' : srcBase + (k + 1) ≠ dstBase + n := hdisjoint n hn_lt_j
      simp only [h_ne', dite_false]
      exact ihn (Nat.le_of_succ_le hm)

/-- The foldl-based state equals afterCopy for full range. -/
private theorem copyRegs_stateAfter_eq_afterCopy (σ : State) (cnt srcBase dstBase : ℕ) :
    copyRegs_stateAfter σ srcBase dstBase cnt = σ.afterCopy cnt srcBase dstBase := by
  funext r
  simp only [copyRegs_stateAfter, State.write]
  induction cnt with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, State.afterCopy]
    split_ifs with h
    · omega
    · rfl
  | succ k ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h_eq : r = dstBase + k
    · subst h_eq
      simp only [Function.update_self, State.afterCopy, Nat.add_sub_cancel_left]
      split_ifs with h
      · rfl
      · omega
    · simp only [Function.update, h_eq, dite_false]
      rw [ih]
      simp only [State.afterCopy]
      split_ifs with h1 h2
      · rfl
      · omega
      · omega
      · rfl

/-- Running copyRegs cnt from state σ reaches the expected state.
    Requires that source and destination ranges don't overlap in a problematic way:
    either they're disjoint, or dstBase + cnt ≤ srcBase (copy from higher to lower). -/
theorem copyRegs_reaches (cnt srcBase dstBase : ℕ) (σ : State)
    (hdisjoint : dstBase + cnt ≤ srcBase ∨ srcBase + cnt ≤ dstBase) :
    Steps (copyRegs cnt srcBase dstBase) ⟨0, σ⟩ ⟨cnt, σ.afterCopy cnt srcBase dstBase⟩ := by
  -- Prove by induction that after i steps we reach stateAfter i
  have hsteps : ∀ i ≤ cnt, StepsN (copyRegs cnt srcBase dstBase) i ⟨0, σ⟩
      ⟨i, copyRegs_stateAfter σ srcBase dstBase i⟩ := by
    intro i hi
    induction i with
    | zero =>
      simp only [copyRegs_stateAfter, List.range_zero, List.foldl_nil]
      exact StepsN.zero _
    | succ j ihj =>
      have hj' : j ≤ cnt := Nat.le_of_succ_le hi
      have hjbound : j < cnt := Nat.lt_of_succ_le hi
      have steps_j := ihj hj'
      have hinstr := copyRegs_getInstr cnt srcBase dstBase j hjbound
      -- Key: reading srcBase + j from intermediate state gives σ (srcBase + j)
      have hdisjoint_j : ∀ k < j, srcBase + j ≠ dstBase + k := by
        intro k hk
        cases hdisjoint with
        | inl h => omega
        | inr h => omega
      have hread : (copyRegs_stateAfter σ srcBase dstBase j).read (srcBase + j) = σ (srcBase + j) := by
        simp only [State.read]
        exact copyRegs_stateAfter_preserves_src σ srcBase dstBase j hdisjoint_j
      have hstep : Step (copyRegs cnt srcBase dstBase)
          ⟨j, copyRegs_stateAfter σ srcBase dstBase j⟩
          ⟨j + 1, (copyRegs_stateAfter σ srcBase dstBase j).write (dstBase + j)
                   ((copyRegs_stateAfter σ srcBase dstBase j).read (srcBase + j))⟩ :=
        Step.trans hinstr
      have hstate_eq : copyRegs_stateAfter σ srcBase dstBase (j + 1) =
          (copyRegs_stateAfter σ srcBase dstBase j).write (dstBase + j)
           ((copyRegs_stateAfter σ srcBase dstBase j).read (srcBase + j)) := by
        simp only [copyRegs_stateAfter, List.range_succ, List.foldl_append, List.foldl_cons,
                   List.foldl_nil, State.read]
        congr 1
        exact hread.symm
      rw [hstate_eq]
      exact StepsN.add steps_j (StepsN.succ hstep (StepsN.zero _))
  have hstepsN := hsteps cnt (Nat.le_refl cnt)
  rw [copyRegs_stateAfter_eq_afterCopy] at hstepsN
  exact hstepsN.toSteps

/-- The copying program halts in exactly cnt steps. -/
theorem copyRegs_haltsIn (cnt srcBase dstBase : ℕ) (inputs : List ℕ)
    (hdisjoint : dstBase + cnt ≤ srcBase ∨ srcBase + cnt ≤ dstBase) :
    HaltsIn (copyRegs cnt srcBase dstBase) cnt inputs := by
  refine ⟨⟨cnt, (State.fromInputs inputs).afterCopy cnt srcBase dstBase⟩, ?_, ?_⟩
  · -- Prove StepsN using the same approach as copyRegs_reaches
    have hsteps : ∀ i ≤ cnt, StepsN (copyRegs cnt srcBase dstBase) i
        ⟨0, State.fromInputs inputs⟩
        ⟨i, copyRegs_stateAfter (State.fromInputs inputs) srcBase dstBase i⟩ := by
      intro i hi
      induction i with
      | zero =>
        simp only [copyRegs_stateAfter, List.range_zero, List.foldl_nil]
        exact StepsN.zero _
      | succ j ihj =>
        have hj' : j ≤ cnt := Nat.le_of_succ_le hi
        have hjbound : j < cnt := Nat.lt_of_succ_le hi
        have steps_j := ihj hj'
        have hinstr := copyRegs_getInstr cnt srcBase dstBase j hjbound
        have hdisjoint_j : ∀ k < j, srcBase + j ≠ dstBase + k := by
          intro k hk
          cases hdisjoint with
          | inl h => omega
          | inr h => omega
        have hread : (copyRegs_stateAfter (State.fromInputs inputs) srcBase dstBase j).read (srcBase + j) =
            (State.fromInputs inputs) (srcBase + j) := by
          simp only [State.read]
          exact copyRegs_stateAfter_preserves_src (State.fromInputs inputs) srcBase dstBase j hdisjoint_j
        have hstep : Step (copyRegs cnt srcBase dstBase)
            ⟨j, copyRegs_stateAfter (State.fromInputs inputs) srcBase dstBase j⟩
            ⟨j + 1, (copyRegs_stateAfter (State.fromInputs inputs) srcBase dstBase j).write (dstBase + j)
                     ((copyRegs_stateAfter (State.fromInputs inputs) srcBase dstBase j).read (srcBase + j))⟩ :=
          Step.trans hinstr
        have hstate_eq : copyRegs_stateAfter (State.fromInputs inputs) srcBase dstBase (j + 1) =
            (copyRegs_stateAfter (State.fromInputs inputs) srcBase dstBase j).write (dstBase + j)
             ((copyRegs_stateAfter (State.fromInputs inputs) srcBase dstBase j).read (srcBase + j)) := by
          simp only [copyRegs_stateAfter, List.range_succ, List.foldl_append, List.foldl_cons,
                     List.foldl_nil, State.read]
          congr 1
          exact hread.symm
        rw [hstate_eq]
        exact StepsN.add steps_j (StepsN.succ hstep (StepsN.zero _))
    have hfinal := hsteps cnt (Nat.le_refl cnt)
    rw [copyRegs_stateAfter_eq_afterCopy] at hfinal
    exact hfinal
  · simp [Config.isHalted]

/-- The copying program halts on any input. -/
theorem copyRegs_halts (cnt srcBase dstBase : ℕ) (inputs : List ℕ)
    (hdisjoint : dstBase + cnt ≤ srcBase ∨ srcBase + cnt ≤ dstBase) :
    Halts (copyRegs cnt srcBase dstBase) inputs :=
  (copyRegs_haltsIn cnt srcBase dstBase inputs hdisjoint).toHalts

/-- Lift copyRegs steps to the first part of a sequential composition. -/
theorem Steps.copyRegs_in_seq (cnt srcBase dstBase : ℕ) (p : Program) (σ : State)
    (hdisjoint : dstBase + cnt ≤ srcBase ∨ srcBase + cnt ≤ dstBase) :
    Steps ((copyRegs cnt srcBase dstBase).seq p) ⟨0, σ⟩ ⟨cnt, σ.afterCopy cnt srcBase dstBase⟩ := by
  by_cases hcnt : cnt = 0
  · -- When cnt = 0, copyRegs is empty and afterCopy is identity
    subst hcnt
    have hafter : σ.afterCopy 0 srcBase dstBase = σ := by
      funext r
      simp only [State.afterCopy, Nat.add_zero]
      split_ifs with h
      · omega
      · rfl
    simp only [hafter]
    exact Steps.refl _
  · have hcnt_pos : 0 < cnt := Nat.pos_of_ne_zero hcnt
    have hcopy_steps := copyRegs_reaches cnt srcBase dstBase σ hdisjoint
    apply Steps.seq_steps_first hcopy_steps
    · simp only [copyRegs_length]; exact hcnt_pos
    · simp

end Urm
