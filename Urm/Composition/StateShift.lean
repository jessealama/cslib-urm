/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.StateAgreement

/-! # State Shifting Operations

This file defines state shifting/unshifting and proves that program execution
is preserved under register shifting. This is essential for running programs
at different register offsets during composition.

## Main definitions

- `Urm.State.shift`: Shift a state by offset (register n+offset maps to n)
- `Urm.State.unshift`: Unshift a state (register n maps to n+offset)
- `Urm.State.agreeFrom`: Two states agree on registers ≥ offset
- `Urm.Step.shiftRegisters_of_step`: Step preservation under register shifting
- `Urm.Steps.shiftRegisters_of_steps`: Multi-step preservation
-/

namespace Urm

/-- Shift a state by `offset`: register `n + offset` in the shifted state
    equals register `n` in the original state. -/
def State.shift (σ : State) (offset : ℕ) : State :=
  fun n => if n < offset then 0 else σ (n - offset)

/-- Unshift a state: register `n` in the unshifted state equals register `n + offset`
    in the original state. -/
def State.unshift (σ : State) (offset : ℕ) : State :=
  fun n => σ (n + offset)

/-! ### State Shifting Lemmas -/

namespace State

@[simp]
theorem shift_read (σ : State) (offset n : ℕ) :
    (σ.shift offset).read n = if n < offset then 0 else σ.read (n - offset) := rfl

@[simp]
theorem unshift_read (σ : State) (offset n : ℕ) :
    (σ.unshift offset).read n = σ.read (n + offset) := rfl

/-- unshift after shift recovers the original state. -/
theorem unshift_shift (σ : State) (offset : ℕ) :
    (σ.shift offset).unshift offset = σ := by
  funext n
  simp only [shift, unshift, Nat.add_sub_cancel]
  simp [Nat.not_lt_of_le (Nat.le_add_left offset n)]

/-- Writing to a register then unshifting is the same as unshifting then writing. -/
theorem unshift_write (σ : State) (offset n v : ℕ) :
    (σ.write (n + offset) v).unshift offset = (σ.unshift offset).write n v := by
  funext k
  simp only [unshift, State.write, Function.update]
  split_ifs with h1 h2
  · simp_all
  · exfalso; omega
  · exfalso; omega
  · rfl

/-- Writing to register n then shifting equals shifting then writing to n + offset. -/
theorem shift_write (σ : State) (offset n v : ℕ) :
    (σ.write n v).shift offset = (σ.shift offset).write (n + offset) v := by
  funext k
  simp only [shift, State.write, Function.update]
  by_cases hlt : k < offset
  · -- k < offset: both sides give 0
    simp only [hlt, ↓reduceIte]
    have hne : k ≠ n + offset := by omega
    simp [hne]
  · -- k >= offset
    push_neg at hlt
    have hlt' : ¬ k < offset := Nat.not_lt.mpr hlt
    simp only [hlt', ↓reduceIte]
    by_cases heq : k = n + offset
    · -- k = n + offset: both sides give v
      simp only [heq, ↓reduceIte]
      have : k - offset = n := by omega
      simp [this]
    · -- k ≠ n + offset: both sides give σ (k - offset)
      simp only [heq, ↓reduceIte]
      have : k - offset ≠ n := by omega
      simp [this]

/-- Reading from a shifted state at n + offset gives the original value at n. -/
@[simp]
theorem shift_read_add (σ : State) (offset n : ℕ) :
    (σ.shift offset).read (n + offset) = σ.read n := by
  simp only [shift_read, Nat.add_sub_cancel]
  simp [Nat.not_lt_of_le (Nat.le_add_left offset n)]

end State

/-! ### Register Shifting and Execution -/

/-- Length is preserved under register shifting. -/
@[simp]
theorem Program.shiftRegisters_length (p : Program) (offset : ℕ) :
    (p.shiftRegisters offset).length = p.length := by
  simp [Program.shiftRegisters]

-- Note: Detailed Step.shiftRegisters lemmas require careful handling of state
-- representation. For the composition proof, we may use a different approach.

/-- JumpsBounded is preserved under register shifting (jump targets unchanged). -/
theorem JumpsBounded.shiftRegisters {p : Program} (h : JumpsBounded p) (offset : ℕ) :
    JumpsBounded (p.shiftRegisters offset) := by
  intro i hi m n q hinstr
  simp only [Program.shiftRegisters_length] at hi
  have hi' : i < p.length := hi
  -- Get the instruction from shifted program
  simp only [Program.shiftRegisters, Program.getInstr, List.getElem?_map] at hinstr
  -- The shifted instruction must have come from a J instruction in the original
  cases hget : p[i]? with
  | none => simp [hget] at hinstr
  | some instr =>
    rw [hget] at hinstr
    simp only [Option.map] at hinstr
    cases instr with
    | J m' n' q' =>
      simp only [Instr.shiftRegisters, Option.some.injEq] at hinstr
      -- hinstr : Instr.J (m' + offset) (n' + offset) q' = Instr.J m n q
      cases hinstr
      -- After cases: q = q' (unified), need to show q ≤ length
      simp only [Program.shiftRegisters_length]
      exact h i hi' m' n' q (by simp [Program.getInstr, hget])
    | Z _ => simp [Instr.shiftRegisters] at hinstr
    | S _ => simp [Instr.shiftRegisters] at hinstr
    | T _ _ => simp [Instr.shiftRegisters] at hinstr

/-! ### Step Simulation for Shifted Programs -/

/-- Helper: get instruction from shifted program relates to original. -/
theorem Program.getInstr_shiftRegisters (p : Program) (offset pc : ℕ) :
    (p.shiftRegisters offset).getInstr pc = (p.getInstr pc).map (Instr.shiftRegisters offset) := by
  simp only [Program.shiftRegisters, Program.getInstr, List.getElem?_map]

/-- If program p takes a step, then p.shiftRegisters takes a corresponding step
    on the shifted state. -/
theorem Step.shiftRegisters_of_step {p : Program} {pc pc' : ℕ} {σ σ' : State} (offset : ℕ)
    (h : Step p ⟨pc, σ⟩ ⟨pc', σ'⟩) :
    Step (p.shiftRegisters offset) ⟨pc, σ.shift offset⟩ ⟨pc', σ'.shift offset⟩ := by
  cases h with
  | zero hinstr =>
    -- p has Z n at pc, σ' = σ.write n 0, pc' = pc + 1
    -- Need: p.shiftRegisters has Z (n + offset), result state is σ'.shift offset
    rename_i n
    have hinstr' : (p.shiftRegisters offset).getInstr pc = some (Instr.Z (n + offset)) := by
      simp only [Program.getInstr_shiftRegisters, hinstr, Option.map_some, Instr.shiftRegisters]
    rw [State.shift_write]
    exact Step.zero hinstr'
  | succ hinstr =>
    rename_i n
    have hinstr' : (p.shiftRegisters offset).getInstr pc = some (Instr.S (n + offset)) := by
      simp only [Program.getInstr_shiftRegisters, hinstr, Option.map_some, Instr.shiftRegisters]
    have hread_eq : σ.read n + 1 = (σ.shift offset).read (n + offset) + 1 := by
      simp [State.shift_read_add]
    conv_rhs => rw [hread_eq]
    rw [State.shift_write]
    exact Step.succ hinstr'
  | trans hinstr =>
    rename_i m n
    have hinstr' : (p.shiftRegisters offset).getInstr pc = some (Instr.T (m + offset) (n + offset)) := by
      simp only [Program.getInstr_shiftRegisters, hinstr, Option.map_some, Instr.shiftRegisters]
    have hread_eq : σ.read m = (σ.shift offset).read (m + offset) := by
      simp [State.shift_read_add]
    conv_rhs => rw [hread_eq]
    rw [State.shift_write]
    exact Step.trans hinstr'
  | jump_eq hinstr heq =>
    have hinstr' : (p.shiftRegisters offset).getInstr pc = (p.getInstr pc).map (Instr.shiftRegisters offset) :=
      Program.getInstr_shiftRegisters p offset pc
    rw [hinstr] at hinstr'
    simp only [Option.map_some, Instr.shiftRegisters] at hinstr'
    exact Step.jump_eq hinstr' (by simp only [State.shift_read_add]; exact heq)
  | jump_ne hinstr hne =>
    have hinstr' : (p.shiftRegisters offset).getInstr pc = (p.getInstr pc).map (Instr.shiftRegisters offset) :=
      Program.getInstr_shiftRegisters p offset pc
    rw [hinstr] at hinstr'
    simp only [Option.map_some, Instr.shiftRegisters] at hinstr'
    exact Step.jump_ne hinstr' (by simp only [State.shift_read_add]; exact hne)

/-- Converse: if p.shiftRegisters takes a step on a shifted state,
    then p takes a corresponding step on the original state. -/
theorem Step.of_shiftRegisters_step {p : Program} {pc pc' : ℕ} {σ σ' : State} (offset : ℕ)
    (h : Step (p.shiftRegisters offset) ⟨pc, σ.shift offset⟩ ⟨pc', σ'⟩) :
    ∃ σ'', Step p ⟨pc, σ⟩ ⟨pc', σ''⟩ ∧ σ' = σ''.shift offset := by
  cases h with
  | zero hinstr =>
    simp only [Program.getInstr_shiftRegisters] at hinstr
    cases hget : p.getInstr pc with
    | none => simp [hget] at hinstr
    | some instr =>
      simp [hget] at hinstr
      cases instr with
      | Z n =>
        simp only [Instr.shiftRegisters, Option.some.injEq, Instr.Z.injEq] at hinstr
        refine ⟨σ.write n 0, Step.zero ?_, ?_⟩
        · simp only [Program.getInstr] at hget; exact hget
        · rw [← hinstr, State.shift_write]
      | S _ => simp [Instr.shiftRegisters] at hinstr
      | T _ _ => simp [Instr.shiftRegisters] at hinstr
      | J _ _ _ => simp [Instr.shiftRegisters] at hinstr
  | succ hinstr =>
    simp only [Program.getInstr_shiftRegisters] at hinstr
    cases hget : p.getInstr pc with
    | none => simp [hget] at hinstr
    | some instr =>
      simp [hget] at hinstr
      cases instr with
      | S n =>
        simp only [Instr.shiftRegisters, Option.some.injEq, Instr.S.injEq] at hinstr
        refine ⟨σ.write n (σ.read n + 1), Step.succ ?_, ?_⟩
        · simp only [Program.getInstr] at hget; exact hget
        · rw [← hinstr, State.shift_write, State.shift_read_add]
      | Z _ => simp [Instr.shiftRegisters] at hinstr
      | T _ _ => simp [Instr.shiftRegisters] at hinstr
      | J _ _ _ => simp [Instr.shiftRegisters] at hinstr
  | trans hinstr =>
    simp only [Program.getInstr_shiftRegisters] at hinstr
    cases hget : p.getInstr pc with
    | none => simp [hget] at hinstr
    | some instr =>
      simp [hget] at hinstr
      cases instr with
      | T m n =>
        simp only [Instr.shiftRegisters, Option.some.injEq] at hinstr
        obtain ⟨rfl, rfl⟩ := hinstr
        refine ⟨σ.write n (σ.read m), Step.trans ?_, ?_⟩
        · simp only [Program.getInstr] at hget; exact hget
        · rw [State.shift_write, State.shift_read_add]
      | Z _ => simp [Instr.shiftRegisters] at hinstr
      | S _ => simp [Instr.shiftRegisters] at hinstr
      | J _ _ _ => simp [Instr.shiftRegisters] at hinstr
  | jump_eq hinstr heq =>
    simp only [Program.getInstr_shiftRegisters] at hinstr
    cases hget : p.getInstr pc with
    | none => simp [hget] at hinstr
    | some instr =>
      simp [hget] at hinstr
      cases instr with
      | J m n q =>
        simp only [Instr.shiftRegisters, Option.some.injEq, Instr.J.injEq] at hinstr
        obtain ⟨hm, hn, hq⟩ := hinstr
        subst hq  -- Now q = pc' is substituted, making hget have the right type
        simp only [State.shift_read_add] at heq
        have heq' : σ.read m = σ.read n := by
          convert heq using 1 <;> simp [← hm, ← hn]
        refine ⟨σ, Step.jump_eq ?_ heq', rfl⟩
        simp only [Program.getInstr] at hget; exact hget
      | Z _ => simp [Instr.shiftRegisters] at hinstr
      | S _ => simp [Instr.shiftRegisters] at hinstr
      | T _ _ => simp [Instr.shiftRegisters] at hinstr
  | jump_ne hinstr hne =>
    simp only [Program.getInstr_shiftRegisters] at hinstr
    cases hget : p.getInstr pc with
    | none => simp [hget] at hinstr
    | some instr =>
      simp [hget] at hinstr
      cases instr with
      | J m n q =>
        simp only [Instr.shiftRegisters, Option.some.injEq, Instr.J.injEq] at hinstr
        obtain ⟨hm, hn, hq⟩ := hinstr
        simp only [State.shift_read_add] at hne
        have hne' : σ.read m ≠ σ.read n := by
          convert hne using 1 <;> simp [← hm, ← hn]
        refine ⟨σ, Step.jump_ne (q := q) ?_ hne', rfl⟩
        simp only [Program.getInstr] at hget; exact hget
      | Z _ => simp [Instr.shiftRegisters] at hinstr
      | S _ => simp [Instr.shiftRegisters] at hinstr
      | T _ _ => simp [Instr.shiftRegisters] at hinstr

/-- Multi-step execution is preserved under register shifting. -/
theorem Steps.shiftRegisters_of_steps {p : Program} {c c' : Config} (offset : ℕ)
    (h : Steps p c c') :
    Steps (p.shiftRegisters offset) ⟨c.pc, c.state.shift offset⟩ ⟨c'.pc, c'.state.shift offset⟩ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hstep _ ih =>
    exact Relation.ReflTransGen.head (Step.shiftRegisters_of_step offset hstep) ih

/-- If p halts reaching pc=p.length, then p.shiftRegisters also halts. -/
theorem shiftRegisters_halts {p : Program} {σ σ' : State} (offset : ℕ)
    (h : Steps p ⟨0, σ⟩ ⟨p.length, σ'⟩) :
    Steps (p.shiftRegisters offset) ⟨0, σ.shift offset⟩ ⟨p.length, σ'.shift offset⟩ := by
  have := Steps.shiftRegisters_of_steps offset h
  simp only [Program.shiftRegisters_length] at this ⊢
  exact this

/-! ### State Agreement from Offset (for shifted programs) -/

/-- Two states agree on registers ≥ offset. -/
def State.agreeFrom (σ₁ σ₂ : State) (offset : ℕ) : Prop :=
  ∀ r, offset ≤ r → σ₁ r = σ₂ r

/-- Two states agree on registers in range [lo, hi]. -/
def State.agreeFromTo (σ₁ σ₂ : State) (lo hi : ℕ) : Prop :=
  ∀ r, lo ≤ r → r ≤ hi → σ₁ r = σ₂ r

/-- agreeFrom implies agreeFromTo for any upper bound. -/
theorem State.agreeFrom_implies_agreeFromTo {σ₁ σ₂ : State} {lo hi : ℕ}
    (h : σ₁.agreeFrom σ₂ lo) : σ₁.agreeFromTo σ₂ lo hi :=
  fun r hlo _ => h r hlo

/-- Symmetry for agreeFromTo. -/
theorem State.agreeFromTo_symm {σ₁ σ₂ : State} {lo hi : ℕ}
    (h : σ₁.agreeFromTo σ₂ lo hi) : σ₂.agreeFromTo σ₁ lo hi :=
  fun r hlo hhi => (h r hlo hhi).symm

/-- Writes to registers in [lo, hi] preserve agreement on [lo, hi]. -/
theorem State.agreeFromTo_write {σ₁ σ₂ : State} {lo hi n v : ℕ}
    (hagree : σ₁.agreeFromTo σ₂ lo hi) (_hlo : lo ≤ n) (_hhi : n ≤ hi) :
    (σ₁.write n v).agreeFromTo (σ₂.write n v) lo hi := by
  intro r hrlo hrhi
  simp only [write, Function.update]
  split_ifs with heq
  · rfl
  · exact hagree r hrlo hrhi

/-- Writes to registers ≥ offset preserve agreement on registers ≥ offset. -/
theorem State.agreeFrom_write {σ₁ σ₂ : State} {offset n v : ℕ}
    (hagree : σ₁.agreeFrom σ₂ offset) (_hn : offset ≤ n) :
    (σ₁.write n v).agreeFrom (σ₂.write n v) offset := by
  intro r hr
  simp only [write, Function.update]
  split_ifs with heq
  · rfl
  · exact hagree r hr

/-- If states agree from offset and p.shiftRegisters offset steps, execution is identical.
    Key insight: p.shiftRegisters offset only accesses registers ≥ offset. -/
theorem Step.shiftRegisters_agreeFrom {p : Program} {pc pc' : ℕ} {σ₁ σ₂ σ₁' : State}
    {offset : ℕ}
    (hagree : σ₁.agreeFrom σ₂ offset)
    (hstep : Step (p.shiftRegisters offset) ⟨pc, σ₁⟩ ⟨pc', σ₁'⟩) :
    ∃ σ₂', Step (p.shiftRegisters offset) ⟨pc, σ₂⟩ ⟨pc', σ₂'⟩ ∧
           σ₁'.agreeFrom σ₂' offset := by
  match hstep with
  | Step.zero (n := n) h =>
    -- Instruction is Z n where n = n' + offset for some n' (since program is shifted)
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | Z n' =>
        simp only [Instr.shiftRegisters, Option.some.injEq] at h
        cases h -- n = n' + offset
        refine ⟨σ₂.write (n' + offset) 0, Step.zero ?_, State.agreeFrom_write hagree (Nat.le_add_left _ _)⟩
        simp only [Program.getInstr_shiftRegisters, hget, Option.map_some, Instr.shiftRegisters]
      | S _ => simp [Instr.shiftRegisters] at h
      | T _ _ => simp [Instr.shiftRegisters] at h
      | J _ _ _ => simp [Instr.shiftRegisters] at h
  | Step.succ (n := n) h =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | S n' =>
        simp only [Instr.shiftRegisters, Option.some.injEq] at h
        cases h -- n = n' + offset
        have hread_eq : σ₁.read (n' + offset) = σ₂.read (n' + offset) :=
          hagree (n' + offset) (Nat.le_add_left _ _)
        have hinstr' : (p.shiftRegisters offset).getInstr pc = some (Instr.S (n' + offset)) := by
          simp only [Program.getInstr_shiftRegisters, hget, Option.map_some, Instr.shiftRegisters]
        refine ⟨σ₂.write (n' + offset) (σ₂.read (n' + offset) + 1), Step.succ hinstr',
               ?_⟩
        -- Need: (σ₁.write (n' + offset) (σ₁.read (n' + offset) + 1)).agreeFrom
        --       (σ₂.write (n' + offset) (σ₂.read (n' + offset) + 1)) offset
        intro r hr
        simp only [State.write, Function.update]
        split_ifs with heqr
        · -- r = n' + offset: both sides write read+1
          subst heqr
          simp only [State.read]
          exact congrArg (· + 1) hread_eq
        · exact hagree r hr
      | Z _ => simp [Instr.shiftRegisters] at h
      | T _ _ => simp [Instr.shiftRegisters] at h
      | J _ _ _ => simp [Instr.shiftRegisters] at h
  | Step.trans (m := m) (n := n) h =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | T m' n' =>
        simp only [Instr.shiftRegisters, Option.some.injEq, Instr.T.injEq] at h
        obtain ⟨hm, hn⟩ := h
        subst hm hn -- m = m' + offset, n = n' + offset
        have hread_eq : σ₁.read (m' + offset) = σ₂.read (m' + offset) :=
          hagree (m' + offset) (Nat.le_add_left _ _)
        have hinstr' : (p.shiftRegisters offset).getInstr pc = some (Instr.T (m' + offset) (n' + offset)) := by
          simp only [Program.getInstr_shiftRegisters, hget, Option.map_some, Instr.shiftRegisters]
        refine ⟨σ₂.write (n' + offset) (σ₂.read (m' + offset)), Step.trans hinstr', ?_⟩
        intro r hr
        simp only [State.write, Function.update]
        split_ifs with heqr
        · -- r = n' + offset: both sides wrote σ.read (m' + offset)
          subst heqr
          simp only [State.read]
          exact hread_eq
        · exact hagree r hr
      | Z _ => simp [Instr.shiftRegisters] at h
      | S _ => simp [Instr.shiftRegisters] at h
      | J _ _ _ => simp [Instr.shiftRegisters] at h
  | Step.jump_eq (m := m) (n := n) (q := q) h heq =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | J m' n' q' =>
        simp only [Instr.shiftRegisters, Option.some.injEq, Instr.J.injEq] at h
        obtain ⟨hm, hn, hq⟩ := h
        subst hm hn hq -- m = m' + offset, n = n' + offset, q = q'
        have hread_m : σ₁.read (m' + offset) = σ₂.read (m' + offset) :=
          hagree (m' + offset) (Nat.le_add_left _ _)
        have hread_n : σ₁.read (n' + offset) = σ₂.read (n' + offset) :=
          hagree (n' + offset) (Nat.le_add_left _ _)
        have heq' : σ₂.read (m' + offset) = σ₂.read (n' + offset) := by
          rw [← hread_m, ← hread_n]; exact heq
        refine ⟨σ₂, Step.jump_eq ?_ heq', hagree⟩
        simp only [Program.getInstr_shiftRegisters, hget, Option.map_some, Instr.shiftRegisters]
      | Z _ => simp [Instr.shiftRegisters] at h
      | S _ => simp [Instr.shiftRegisters] at h
      | T _ _ => simp [Instr.shiftRegisters] at h
  | Step.jump_ne (m := m) (n := n) (q := q) h hne =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | J m' n' q' =>
        simp only [Instr.shiftRegisters, Option.some.injEq, Instr.J.injEq] at h
        obtain ⟨hm, hn, hq⟩ := h
        subst hm hn hq
        have hread_m : σ₁.read (m' + offset) = σ₂.read (m' + offset) :=
          hagree (m' + offset) (Nat.le_add_left _ _)
        have hread_n : σ₁.read (n' + offset) = σ₂.read (n' + offset) :=
          hagree (n' + offset) (Nat.le_add_left _ _)
        have hne' : σ₂.read (m' + offset) ≠ σ₂.read (n' + offset) := by
          rw [← hread_m, ← hread_n]; exact hne
        have hinstr' : (p.shiftRegisters offset).getInstr pc = some (Instr.J (m' + offset) (n' + offset) q') := by
          simp only [Program.getInstr_shiftRegisters, hget, Option.map_some, Instr.shiftRegisters]
        refine ⟨σ₂, Step.jump_ne hinstr' hne', hagree⟩
      | Z _ => simp [Instr.shiftRegisters] at h
      | S _ => simp [Instr.shiftRegisters] at h
      | T _ _ => simp [Instr.shiftRegisters] at h

/-- Multi-step agreement: if states agree from offset and p.shiftRegisters offset steps,
    execution from the agreeing state produces the same PC. -/
theorem Steps.shiftRegisters_agreeFrom {p : Program} {c₁ c₁' : Config}
    {offset : ℕ}
    (hsteps : Steps (p.shiftRegisters offset) c₁ c₁')
    {σ₂ : State} (hagree : c₁.state.agreeFrom σ₂ offset) :
    ∃ c₂', Steps (p.shiftRegisters offset) ⟨c₁.pc, σ₂⟩ c₂' ∧
           c₁'.pc = c₂'.pc ∧ c₁'.state.agreeFrom c₂'.state offset := by
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing σ₂ with
  | refl =>
    exact ⟨⟨c₁'.pc, σ₂⟩, Relation.ReflTransGen.refl, rfl, hagree⟩
  | head hstep _ ih =>
    rename_i c_mid
    obtain ⟨σ_mid', hstep', hagree'⟩ := Step.shiftRegisters_agreeFrom hagree hstep
    obtain ⟨c₂', hsteps', hpc_eq', hagree''⟩ := ih hagree'
    refine ⟨c₂', Relation.ReflTransGen.head hstep' ?_, hpc_eq', hagree''⟩
    exact hsteps'

/-! ### Bounded Agreement for Shifted Programs -/

/-- A shifted program only accesses registers in [offset, offset + p.maxRegister].
    If states agree on this range, execution produces the same results. -/
theorem Step.shiftRegisters_agreeFromTo {p : Program} {pc pc' : ℕ} {σ₁ σ₂ σ₁' : State}
    {offset : ℕ}
    (hagree : σ₁.agreeFromTo σ₂ offset (offset + p.maxRegister))
    (hstep : Step (p.shiftRegisters offset) ⟨pc, σ₁⟩ ⟨pc', σ₁'⟩) :
    ∃ σ₂', Step (p.shiftRegisters offset) ⟨pc, σ₂⟩ ⟨pc', σ₂'⟩ ∧
           σ₁'.agreeFromTo σ₂' offset (offset + p.maxRegister) := by
  match hstep with
  | Step.zero (n := n) h =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | Z n' =>
        simp only [Instr.shiftRegisters, Option.some.injEq] at h
        cases h -- n = n' + offset
        have ⟨hpc_lt, heq⟩ := List.getElem?_eq_some_iff.mp hget
        have hinstr_mem : (Instr.Z n') ∈ p := heq ▸ List.getElem_mem hpc_lt
        have hn'_le : n' ≤ p.maxRegister := by
          have := Instr.maxRegister_le_of_mem hinstr_mem
          simp only [Instr.maxRegister] at this
          exact this
        have hlo : offset ≤ n' + offset := Nat.le_add_left _ _
        have hhi : n' + offset ≤ offset + p.maxRegister := by omega
        refine ⟨σ₂.write (n' + offset) 0, Step.zero ?_,
                State.agreeFromTo_write hagree hlo hhi⟩
        simp only [Program.getInstr_shiftRegisters, hget, Option.map_some, Instr.shiftRegisters]
      | S _ => simp [Instr.shiftRegisters] at h
      | T _ _ => simp [Instr.shiftRegisters] at h
      | J _ _ _ => simp [Instr.shiftRegisters] at h
  | Step.succ (n := n) h =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | S n' =>
        simp only [Instr.shiftRegisters, Option.some.injEq] at h
        cases h
        have ⟨hpc_lt, heq⟩ := List.getElem?_eq_some_iff.mp hget
        have hinstr_mem : (Instr.S n') ∈ p := heq ▸ List.getElem_mem hpc_lt
        have hn'_le : n' ≤ p.maxRegister := by
          have := Instr.maxRegister_le_of_mem hinstr_mem
          simp only [Instr.maxRegister] at this
          exact this
        have hlo : offset ≤ n' + offset := Nat.le_add_left _ _
        have hhi : n' + offset ≤ offset + p.maxRegister := by omega
        have hread_eq : σ₁.read (n' + offset) = σ₂.read (n' + offset) := hagree (n' + offset) hlo hhi
        have hinstr' : (p.shiftRegisters offset).getInstr pc = some (Instr.S (n' + offset)) := by
          simp only [Program.getInstr_shiftRegisters, hget, Option.map_some, Instr.shiftRegisters]
        refine ⟨σ₂.write (n' + offset) (σ₂.read (n' + offset) + 1), Step.succ hinstr', ?_⟩
        intro r hrlo hrhi
        simp only [State.write, Function.update]
        split_ifs with heqr
        · subst heqr
          simp only [State.read]
          exact congrArg (· + 1) hread_eq
        · exact hagree r hrlo hrhi
      | Z _ => simp [Instr.shiftRegisters] at h
      | T _ _ => simp [Instr.shiftRegisters] at h
      | J _ _ _ => simp [Instr.shiftRegisters] at h
  | Step.trans (m := m) (n := n) h =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | T m' n' =>
        simp only [Instr.shiftRegisters, Option.some.injEq, Instr.T.injEq] at h
        obtain ⟨hm, hn⟩ := h
        subst hm hn
        have ⟨hpc_lt, heq⟩ := List.getElem?_eq_some_iff.mp hget
        have hinstr_mem : (Instr.T m' n') ∈ p := heq ▸ List.getElem_mem hpc_lt
        have hmax := Instr.maxRegister_le_of_mem hinstr_mem
        simp only [Instr.maxRegister] at hmax
        have hm'_le : m' ≤ p.maxRegister := Nat.le_trans (Nat.le_max_left _ _) hmax
        have hn'_le : n' ≤ p.maxRegister := Nat.le_trans (Nat.le_max_right _ _) hmax
        have hm_lo : offset ≤ m' + offset := Nat.le_add_left _ _
        have hm_hi : m' + offset ≤ offset + p.maxRegister := by omega
        have hn_lo : offset ≤ n' + offset := Nat.le_add_left _ _
        have hn_hi : n' + offset ≤ offset + p.maxRegister := by omega
        have hread_eq : σ₁.read (m' + offset) = σ₂.read (m' + offset) := hagree (m' + offset) hm_lo hm_hi
        have hinstr' : (p.shiftRegisters offset).getInstr pc = some (Instr.T (m' + offset) (n' + offset)) := by
          simp only [Program.getInstr_shiftRegisters, hget, Option.map_some, Instr.shiftRegisters]
        refine ⟨σ₂.write (n' + offset) (σ₂.read (m' + offset)), Step.trans hinstr', ?_⟩
        intro r hrlo hrhi
        simp only [State.write, Function.update]
        split_ifs with heqr
        · subst heqr
          simp only [State.read]
          exact hread_eq
        · exact hagree r hrlo hrhi
      | Z _ => simp [Instr.shiftRegisters] at h
      | S _ => simp [Instr.shiftRegisters] at h
      | J _ _ _ => simp [Instr.shiftRegisters] at h
  | Step.jump_eq (m := m) (n := n) (q := q) h heq =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | J m' n' q' =>
        simp only [Instr.shiftRegisters, Option.some.injEq, Instr.J.injEq] at h
        obtain ⟨hm, hn, hq⟩ := h
        subst hm hn hq
        have ⟨hpc_lt, hinstreq⟩ := List.getElem?_eq_some_iff.mp hget
        have hinstr_mem : (Instr.J m' n' q') ∈ p := hinstreq ▸ List.getElem_mem hpc_lt
        have hmax := Instr.maxRegister_le_of_mem hinstr_mem
        simp only [Instr.maxRegister] at hmax
        have hm'_le : m' ≤ p.maxRegister := Nat.le_trans (Nat.le_max_left _ _) hmax
        have hn'_le : n' ≤ p.maxRegister := Nat.le_trans (Nat.le_max_right _ _) hmax
        have hm_lo : offset ≤ m' + offset := Nat.le_add_left _ _
        have hm_hi : m' + offset ≤ offset + p.maxRegister := by omega
        have hn_lo : offset ≤ n' + offset := Nat.le_add_left _ _
        have hn_hi : n' + offset ≤ offset + p.maxRegister := by omega
        have hread_m : σ₁.read (m' + offset) = σ₂.read (m' + offset) := hagree (m' + offset) hm_lo hm_hi
        have hread_n : σ₁.read (n' + offset) = σ₂.read (n' + offset) := hagree (n' + offset) hn_lo hn_hi
        have heq' : σ₂.read (m' + offset) = σ₂.read (n' + offset) := by
          rw [← hread_m, ← hread_n]; exact heq
        refine ⟨σ₂, Step.jump_eq ?_ heq', hagree⟩
        simp only [Program.getInstr_shiftRegisters, hget, Option.map_some, Instr.shiftRegisters]
      | Z _ => simp [Instr.shiftRegisters] at h
      | S _ => simp [Instr.shiftRegisters] at h
      | T _ _ => simp [Instr.shiftRegisters] at h
  | Step.jump_ne (m := m) (n := n) (q := q) h hne =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | J m' n' q' =>
        simp only [Instr.shiftRegisters, Option.some.injEq, Instr.J.injEq] at h
        obtain ⟨hm, hn, hq⟩ := h
        subst hm hn hq
        have ⟨hpc_lt, hinstreq⟩ := List.getElem?_eq_some_iff.mp hget
        have hinstr_mem : (Instr.J m' n' q') ∈ p := hinstreq ▸ List.getElem_mem hpc_lt
        have hmax := Instr.maxRegister_le_of_mem hinstr_mem
        simp only [Instr.maxRegister] at hmax
        have hm'_le : m' ≤ p.maxRegister := Nat.le_trans (Nat.le_max_left _ _) hmax
        have hn'_le : n' ≤ p.maxRegister := Nat.le_trans (Nat.le_max_right _ _) hmax
        have hm_lo : offset ≤ m' + offset := Nat.le_add_left _ _
        have hm_hi : m' + offset ≤ offset + p.maxRegister := by omega
        have hn_lo : offset ≤ n' + offset := Nat.le_add_left _ _
        have hn_hi : n' + offset ≤ offset + p.maxRegister := by omega
        have hread_m : σ₁.read (m' + offset) = σ₂.read (m' + offset) := hagree (m' + offset) hm_lo hm_hi
        have hread_n : σ₁.read (n' + offset) = σ₂.read (n' + offset) := hagree (n' + offset) hn_lo hn_hi
        have hne' : σ₂.read (m' + offset) ≠ σ₂.read (n' + offset) := by
          rw [← hread_m, ← hread_n]; exact hne
        have hinstr' : (p.shiftRegisters offset).getInstr pc = some (Instr.J (m' + offset) (n' + offset) q') := by
          simp only [Program.getInstr_shiftRegisters, hget, Option.map_some, Instr.shiftRegisters]
        refine ⟨σ₂, Step.jump_ne hinstr' hne', hagree⟩
      | Z _ => simp [Instr.shiftRegisters] at h
      | S _ => simp [Instr.shiftRegisters] at h
      | T _ _ => simp [Instr.shiftRegisters] at h

/-- Multi-step bounded agreement: if states agree on [offset, offset + p.maxRegister],
    execution of p.shiftRegisters offset produces the same PC. -/
theorem Steps.shiftRegisters_agreeFromTo {p : Program} {c₁ c₁' : Config}
    {offset : ℕ}
    (hsteps : Steps (p.shiftRegisters offset) c₁ c₁')
    {σ₂ : State} (hagree : c₁.state.agreeFromTo σ₂ offset (offset + p.maxRegister)) :
    ∃ c₂', Steps (p.shiftRegisters offset) ⟨c₁.pc, σ₂⟩ c₂' ∧
           c₁'.pc = c₂'.pc ∧ c₁'.state.agreeFromTo c₂'.state offset (offset + p.maxRegister) := by
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing σ₂ with
  | refl =>
    exact ⟨⟨c₁'.pc, σ₂⟩, Relation.ReflTransGen.refl, rfl, hagree⟩
  | head hstep _ ih =>
    rename_i c_mid
    obtain ⟨σ_mid', hstep', hagree'⟩ := Step.shiftRegisters_agreeFromTo hagree hstep
    obtain ⟨c₂', hsteps', hpc_eq', hagree''⟩ := ih hagree'
    refine ⟨c₂', Relation.ReflTransGen.head hstep' ?_, hpc_eq', hagree''⟩
    exact hsteps'

end Urm
