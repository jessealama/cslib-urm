/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Execution

/-! # Shifted Program Semantics

This file formalizes Cutland's notion of "shifted" programs, where all register
references are uniformly offset. This provides a clean foundation for proving
composition theorems, as each subprogram can operate on disjoint register ranges.

## Main definitions

- `State.shift`: Shift a state so register r maps to original register r - offset
- `Config.shift`: Shift a configuration (state shifted, PC unchanged)

## Main results

- `Step.shift`: If P steps c→c', then P.shiftRegisters steps shifted(c)→shifted(c')
- `Steps.shift`: Multi-step version of Step.shift
- `Halts.shift`: Shifted program halts iff original halts
- `Halts.shift_from_state`: Key lemma for composition - run shifted program from
  arbitrary state agreeing on relevant registers

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## State Shifting -/

namespace State

/-- Shift a state by offset: register r in the shifted view maps to register r - offset
in the original. For r < offset, the value is 0 (the "undefined" region below offset). -/
@[scoped grind =]
def shift (σ : State) (offset : ℕ) : State :=
  fun r => if offset ≤ r then σ (r - offset) else 0

/-- Unshift a state: register r maps to original register r + offset.
This is the inverse operation in the valid region. -/
@[scoped grind =]
def unshift (σ : State) (offset : ℕ) : State :=
  fun r => σ (r + offset)

/-! ### Basic shift/unshift properties -/

@[simp]
theorem shift_zero (σ : State) : σ.shift 0 = σ := by
  funext r; simp [shift]

@[simp]
theorem unshift_zero (σ : State) : σ.unshift 0 = σ := by
  funext r; simp [unshift]

theorem shift_unshift (σ : State) (offset : ℕ) :
    (σ.shift offset).unshift offset = σ := by
  funext r
  simp only [unshift, shift, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]

theorem unshift_shift (σ : State) (offset : ℕ) (r : ℕ) (hr : offset ≤ r) :
    (σ.unshift offset).shift offset r = σ r := by
  simp only [shift, unshift, hr, ↓reduceIte]
  congr 1
  omega

/-! ### Read interaction with shifting -/

@[simp]
theorem shift_read (σ : State) (offset r : ℕ) (hr : offset ≤ r) :
    (σ.shift offset).read r = σ.read (r - offset) := by
  simp only [shift, read, hr, ↓reduceIte]

theorem shift_read_below (σ : State) (offset r : ℕ) (hr : r < offset) :
    (σ.shift offset).read r = 0 := by
  simp only [shift, read, Nat.not_le.mpr hr, ↓reduceIte]

@[simp]
theorem unshift_read (σ : State) (offset r : ℕ) :
    (σ.unshift offset).read r = σ.read (r + offset) := by
  simp only [unshift, read]

/-! ### Write interaction with shifting -/

/-- The key commutation lemma: shifting then writing at n + offset equals
writing at n then shifting. -/
theorem shift_write (σ : State) (offset n v : ℕ) :
    (σ.shift offset).write (n + offset) v = (σ.write n v).shift offset := by
  funext r
  simp only [shift, write]
  by_cases h1 : r = n + offset
  · subst h1
    simp only [Function.update_self, Nat.le_add_left, ↓reduceIte]
    rw [Nat.add_sub_cancel, Function.update_self]
  · simp only [Function.update_of_ne h1]
    by_cases h2 : offset ≤ r
    · have hne : r - offset ≠ n := by omega
      simp only [h2, ↓reduceIte, Function.update_of_ne hne, shift]
    · simp only [h2, ↓reduceIte, shift]

end State

/-! ## Configuration Shifting -/

namespace Config

/-- Shift a configuration: the PC stays the same, only the state is shifted. -/
@[scoped grind =]
def shift (c : Config) (offset : ℕ) : Config :=
  ⟨c.pc, c.state.shift offset⟩

/-- Unshift a configuration. -/
@[scoped grind =]
def unshift (c : Config) (offset : ℕ) : Config :=
  ⟨c.pc, c.state.unshift offset⟩

@[simp]
theorem shift_zero (c : Config) : c.shift 0 = c := by
  simp only [shift, State.shift_zero]

@[simp]
theorem shift_pc (c : Config) (offset : ℕ) : (c.shift offset).pc = c.pc := rfl

@[simp]
theorem shift_state (c : Config) (offset : ℕ) :
    (c.shift offset).state = c.state.shift offset := rfl

/-- Halted status is preserved under shifting (since PC doesn't change
and program length is preserved). -/
theorem isHalted_shift (c : Config) (p : Program) (offset : ℕ) :
    (c.shift offset).isHalted (p.shiftRegisters offset) ↔ c.isHalted p := by
  simp only [isHalted, shift_pc, Program.shiftRegisters, List.length_map]

/-- Unshifting a shifted config recovers the original. -/
@[simp]
theorem shift_unshift (c : Config) (offset : ℕ) :
    (c.shift offset).unshift offset = c := by
  simp only [shift, unshift, State.shift_unshift]

/-- A config equals its shift iff offset is 0 or we use unshift to recover. -/
theorem eq_unshift_of_shift (c c' : Config) (offset : ℕ) (h : c' = c.shift offset) :
    c = c'.unshift offset := by
  simp [h]

end Config

/-! ## Program Shifting Properties -/

namespace Instr

@[simp]
theorem shiftRegisters_zero (instr : Instr) : instr.shiftRegisters 0 = instr := by
  cases instr <;> simp [shiftRegisters]

theorem shiftRegisters_add (k₁ k₂ : ℕ) (instr : Instr) :
    (instr.shiftRegisters k₁).shiftRegisters k₂ = instr.shiftRegisters (k₁ + k₂) := by
  cases instr <;> simp [shiftRegisters, Nat.add_assoc]

@[simp]
theorem maxRegister_shiftRegisters (offset : ℕ) (instr : Instr) :
    (instr.shiftRegisters offset).maxRegister = instr.maxRegister + offset := by
  cases instr <;> simp [shiftRegisters, maxRegister, Nat.add_max_add_right]

end Instr

namespace Program

@[simp]
theorem shiftRegisters_length (offset : ℕ) (p : Program) :
    (p.shiftRegisters offset).length = p.length := by
  simp [shiftRegisters]

@[simp]
theorem shiftRegisters_zero (p : Program) : p.shiftRegisters 0 = p := by
  simp only [shiftRegisters]
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, Instr.shiftRegisters_zero, ih]

theorem shiftRegisters_add (k₁ k₂ : ℕ) (p : Program) :
    (p.shiftRegisters k₁).shiftRegisters k₂ = p.shiftRegisters (k₁ + k₂) := by
  simp only [shiftRegisters, List.map_map, Function.comp_def, Instr.shiftRegisters_add]

theorem getInstr_shiftRegisters (offset : ℕ) (p : Program) (i : ℕ) :
    (p.shiftRegisters offset).getInstr i = (p.getInstr i).map (Instr.shiftRegisters offset) := by
  simp only [shiftRegisters, getInstr, List.getElem?_map]

@[simp]
theorem shiftRegisters_nil (offset : ℕ) : Program.shiftRegisters offset [] = [] := rfl

theorem shiftRegisters_cons (offset : ℕ) (instr : Instr) (p : Program) :
    Program.shiftRegisters offset (instr :: p) =
    instr.shiftRegisters offset :: p.shiftRegisters offset := rfl

/-- Helper: foldl max with offset on function values shifts the result. -/
private theorem foldl_max_add_aux (offset : ℕ) (init : ℕ) (p : Program) :
    p.foldl (fun acc instr => max acc (instr.maxRegister + offset)) (init + offset) =
    p.foldl (fun acc instr => max acc instr.maxRegister) init + offset := by
  induction p generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have : max (init + offset) (hd.maxRegister + offset) = max init hd.maxRegister + offset := by omega
    rw [this, ih]

/-- Specialization for init = 0. -/
private theorem foldl_max_add_zero (offset : ℕ) (p : Program) :
    p.foldl (fun acc instr => max acc (instr.maxRegister + offset)) offset =
    p.foldl (fun acc instr => max acc instr.maxRegister) 0 + offset := by
  have h := foldl_max_add_aux offset 0 p
  simp at h
  exact h

/-- The maxRegister of a shifted nonempty program equals the original maxRegister plus offset. -/
theorem maxRegister_shiftRegisters (offset : ℕ) (p : Program) (hp : p ≠ []) :
    (p.shiftRegisters offset).maxRegister = p.maxRegister + offset := by
  simp only [shiftRegisters, maxRegister]
  rw [List.foldl_map]
  simp only [Instr.maxRegister_shiftRegisters]
  cases p with
  | nil => contradiction
  | cons hd tl =>
    simp only [List.foldl_cons]
    have : max 0 (hd.maxRegister + offset) = max 0 hd.maxRegister + offset := by omega
    rw [this, foldl_max_add_aux]

/-- Weaker version: maxRegister of shifted is at most original + offset. Always holds. -/
theorem maxRegister_shiftRegisters_le (offset : ℕ) (p : Program) :
    (p.shiftRegisters offset).maxRegister ≤ p.maxRegister + offset := by
  cases hp : p with
  | nil => simp [shiftRegisters, maxRegister]
  | cons hd tl =>
    rw [maxRegister_shiftRegisters offset (hd :: tl) (List.cons_ne_nil hd tl)]

end Program

/-! ## Step Correspondence -/

/-- Core theorem: If program P steps from c to c', then P.shiftRegisters(offset)
steps from c.shift(offset) to c'.shift(offset).

The key insight is that:
- Register reads at n become reads at n + offset
- Register writes at n become writes at n + offset
- Jump targets stay the same (only register indices shift, not PCs) -/
theorem Step.shift {p : Program} {c c' : Config} (offset : ℕ)
    (hstep : Step p c c') :
    Step (p.shiftRegisters offset) (c.shift offset) (c'.shift offset) := by
  cases hstep with
  | zero hinstr =>
    rename_i n
    have h : (p.shiftRegisters offset).getInstr c.pc = some (Instr.Z (n + offset)) := by
      rw [Program.getInstr_shiftRegisters, hinstr]
      rfl
    -- c' = ⟨c.pc + 1, c.state.write n 0⟩
    -- c'.shift offset = ⟨c.pc + 1, (c.state.write n 0).shift offset⟩
    --                 = ⟨c.pc + 1, (c.state.shift offset).write (n + offset) 0⟩
    show Step (p.shiftRegisters offset) (c.shift offset)
              ⟨c.pc + 1, (c.state.write n 0).shift offset⟩
    rw [← State.shift_write]
    exact Step.zero h
  | succ hinstr =>
    rename_i n
    have h : (p.shiftRegisters offset).getInstr c.pc = some (Instr.S (n + offset)) := by
      rw [Program.getInstr_shiftRegisters, hinstr]
      rfl
    show Step (p.shiftRegisters offset) (c.shift offset)
              ⟨c.pc + 1, (c.state.write n (c.state.read n + 1)).shift offset⟩
    rw [← State.shift_write]
    have heq : c.state.read n = (c.state.shift offset).read (n + offset) := by
      simp only [State.shift_read (hr := Nat.le_add_left offset n), Nat.add_sub_cancel]
    rw [heq]
    exact Step.succ h
  | trans hinstr =>
    rename_i m n
    have h : (p.shiftRegisters offset).getInstr c.pc = some (Instr.T (m + offset) (n + offset)) := by
      rw [Program.getInstr_shiftRegisters, hinstr]
      rfl
    show Step (p.shiftRegisters offset) (c.shift offset)
              ⟨c.pc + 1, (c.state.write n (c.state.read m)).shift offset⟩
    rw [← State.shift_write]
    have heq : c.state.read m = (c.state.shift offset).read (m + offset) := by
      simp only [State.shift_read (hr := Nat.le_add_left offset m), Nat.add_sub_cancel]
    rw [heq]
    exact Step.trans h
  | jump_eq hinstr hcmp =>
    rename_i m n q
    have h : (p.shiftRegisters offset).getInstr c.pc =
             some (Instr.J (m + offset) (n + offset) q) := by
      rw [Program.getInstr_shiftRegisters, hinstr]
      rfl
    have hcmp' : (c.state.shift offset).read (m + offset) =
                 (c.state.shift offset).read (n + offset) := by
      simp only [State.shift_read (hr := Nat.le_add_left offset m),
                 State.shift_read (hr := Nat.le_add_left offset n), Nat.add_sub_cancel]
      exact hcmp
    exact Step.jump_eq h hcmp'
  | jump_ne hinstr hcmp =>
    rename_i m n q
    have h : (p.shiftRegisters offset).getInstr c.pc =
             some (Instr.J (m + offset) (n + offset) q) := by
      rw [Program.getInstr_shiftRegisters, hinstr]
      rfl
    have hcmp' : (c.state.shift offset).read (m + offset) ≠
                 (c.state.shift offset).read (n + offset) := by
      simp only [State.shift_read (hr := Nat.le_add_left offset m),
                 State.shift_read (hr := Nat.le_add_left offset n), Nat.add_sub_cancel]
      exact hcmp
    exact Step.jump_ne h hcmp'

/-- Multi-step version: if P goes from c to c' in multiple steps,
then P.shiftRegisters goes from shifted(c) to shifted(c'). -/
theorem Steps.shift {p : Program} {c c' : Config} (offset : ℕ)
    (hsteps : Steps p c c') :
    Steps (p.shiftRegisters offset) (c.shift offset) (c'.shift offset) := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hstep _ ih =>
    exact Relation.ReflTransGen.head (Step.shift offset hstep) ih

/-! ## Halting Equivalence -/

/-- If the original program halts, the shifted program halts. -/
theorem Halts.shift {p : Program} {inputs : List ℕ} (offset : ℕ)
    (h : Halts p inputs) :
    ∃ c, Steps (p.shiftRegisters offset)
              ((Config.init inputs).shift offset) c ∧
         c.isHalted (p.shiftRegisters offset) := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  use c.shift offset
  constructor
  · exact Steps.shift offset hsteps
  · rw [Config.isHalted_shift]
    exact hhalted

/-- Key invariant: A step in the shifted program from a shifted config produces a shifted config.
More precisely, the result is exactly the shift of what the original program would produce. -/
theorem Step.shift_inv {p : Program} {c : Config} {c' : Config} (offset : ℕ)
    (hstep : Step (p.shiftRegisters offset) (c.shift offset) c') :
    ∃ d, c' = d.shift offset ∧ Step p c d := by
  -- The shifted program's instruction at PC is a shifted instruction
  -- We case split on what instruction it is
  cases hinstr : p.getInstr c.pc with
  | none =>
    -- If no instruction, the program can't step - contradiction
    have h : (p.shiftRegisters offset).getInstr (c.shift offset).pc = none := by
      simp only [Config.shift_pc, Program.getInstr_shiftRegisters, hinstr]; rfl
    -- All Step cases require the instruction to be `some`, which contradicts `h`
    cases hstep <;> simp_all
  | some instr =>
    -- There's an instruction; it becomes instr.shiftRegisters offset in the shifted program
    have hshift_instr : (p.shiftRegisters offset).getInstr (c.shift offset).pc =
                        some (instr.shiftRegisters offset) := by
      simp only [Config.shift_pc, Program.getInstr_shiftRegisters, hinstr]; rfl
    -- Case on the instruction type
    cases instr with
    | Z n =>
      simp only [Instr.shiftRegisters] at hshift_instr
      -- The step must be zero with register n + offset
      cases hstep with
      | zero h' =>
        -- h' : ... = some (Instr.Z n'), hshift_instr : ... = some (Instr.Z (n + offset))
        -- By transitivity, n' = n + offset
        rw [hshift_instr] at h'; cases h'
        use ⟨c.pc + 1, c.state.write n 0⟩
        constructor
        · simp only [Config.shift]
          rw [← State.shift_write]
        · exact Step.zero hinstr
      | succ h' => rw [hshift_instr] at h'; cases h'
      | trans h' => rw [hshift_instr] at h'; cases h'
      | jump_eq h' _ => rw [hshift_instr] at h'; cases h'
      | jump_ne h' _ => rw [hshift_instr] at h'; cases h'
    | S n =>
      simp only [Instr.shiftRegisters] at hshift_instr
      cases hstep with
      | succ h' =>
        rw [hshift_instr] at h'; cases h'
        use ⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩
        constructor
        · simp only [Config.shift]
          rw [← State.shift_write]
          congr 1
          simp only [State.shift_read (hr := Nat.le_add_left offset n), Nat.add_sub_cancel]
        · exact Step.succ hinstr
      | zero h' => rw [hshift_instr] at h'; cases h'
      | trans h' => rw [hshift_instr] at h'; cases h'
      | jump_eq h' _ => rw [hshift_instr] at h'; cases h'
      | jump_ne h' _ => rw [hshift_instr] at h'; cases h'
    | T m n =>
      simp only [Instr.shiftRegisters] at hshift_instr
      cases hstep with
      | trans h' =>
        rw [hshift_instr] at h'; cases h'
        use ⟨c.pc + 1, c.state.write n (c.state.read m)⟩
        constructor
        · simp only [Config.shift]
          rw [← State.shift_write]
          congr 1
          simp only [State.shift_read (hr := Nat.le_add_left offset m), Nat.add_sub_cancel]
        · exact Step.trans hinstr
      | zero h' => rw [hshift_instr] at h'; cases h'
      | succ h' => rw [hshift_instr] at h'; cases h'
      | jump_eq h' _ => rw [hshift_instr] at h'; cases h'
      | jump_ne h' _ => rw [hshift_instr] at h'; cases h'
    | J m n q =>
      simp only [Instr.shiftRegisters] at hshift_instr
      cases hstep with
      | jump_eq h' hcmp =>
        -- Extract that the instruction matches
        rw [hshift_instr] at h'; cases h'
        -- The comparison in shifted uses shifted reads, convert to original
        have hcmp_orig : c.state.read m = c.state.read n := by
          simp only [Config.shift_state, State.shift_read (hr := Nat.le_add_left offset m),
                     State.shift_read (hr := Nat.le_add_left offset n),
                     Nat.add_sub_cancel] at hcmp
          exact hcmp
        use ⟨q, c.state⟩
        constructor
        · simp only [Config.shift]
        · exact Step.jump_eq hinstr hcmp_orig
      | jump_ne h' hne =>
        rw [hshift_instr] at h'; cases h'
        have hne_orig : c.state.read m ≠ c.state.read n := by
          simp only [Config.shift_state, State.shift_read (hr := Nat.le_add_left offset m),
                     State.shift_read (hr := Nat.le_add_left offset n),
                     Nat.add_sub_cancel] at hne
          exact hne
        use ⟨c.pc + 1, c.state⟩
        constructor
        · simp only [Config.shift]
        · exact Step.jump_ne hinstr hne_orig
      | zero h' => rw [hshift_instr] at h'; cases h'
      | succ h' => rw [hshift_instr] at h'; cases h'
      | trans h' => rw [hshift_instr] at h'; cases h'

/-- Invariant extended to multi-step: configs reachable from shifted initial are shifted. -/
theorem Steps.shift_inv {p : Program} {c₀ c : Config} (offset : ℕ)
    (hsteps : Steps (p.shiftRegisters offset) (c₀.shift offset) c) :
    ∃ d, c = d.shift offset ∧ Steps p c₀ d := by
  -- Use a generalized induction
  generalize hc₀' : c₀.shift offset = c₀' at hsteps
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing c₀ with
  | refl =>
    use c₀
    constructor
    · exact hc₀'.symm
    · exact Relation.ReflTransGen.refl
  | head hstep hrest ih =>
    -- hstep : Step (p.shiftRegisters offset) c₀' c_mid
    -- hrest : Steps (p.shiftRegisters offset) c_mid c
    -- hc₀' : c₀.shift offset = c₀'
    subst hc₀'
    -- Now hstep : Step (p.shiftRegisters offset) (c₀.shift offset) c_mid
    obtain ⟨d, hd_eq, hd_step⟩ := Step.shift_inv offset hstep
    -- d is the unshifted version of c_mid, c_mid = d.shift offset
    -- hd_step : Step p c₀ d
    -- Now apply ih with c₀ := d (implicit, inferred from hd_eq.symm)
    obtain ⟨e, he_eq, he_steps⟩ := ih hd_eq.symm
    use e
    constructor
    · exact he_eq
    · exact Relation.ReflTransGen.head hd_step he_steps

/-- If the shifted program halts from a shifted initial state, the original halts. -/
theorem Halts.of_shift {p : Program} {inputs : List ℕ} (offset : ℕ)
    (h : ∃ c, Steps (p.shiftRegisters offset)
                    ((Config.init inputs).shift offset) c ∧
              c.isHalted (p.shiftRegisters offset)) :
    Halts p inputs := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  obtain ⟨d, hd_eq, hd_steps⟩ := Steps.shift_inv offset hsteps
  use d
  constructor
  · exact hd_steps
  · rw [← Config.isHalted_shift, ← hd_eq]
    exact hhalted

/-! ## Register Independence

For composition, we need to show that program execution only depends on registers
actually used by the program. Two states that agree on registers `[0, maxRegister]`
produce the same execution. -/

/-- Two states agree on registers in `[lo, hi]`. -/
def State.agreeOn (σ₁ σ₂ : State) (lo hi : ℕ) : Prop :=
  ∀ r, lo ≤ r → r ≤ hi → σ₁.read r = σ₂.read r

theorem State.agreeOn_refl (σ : State) (lo hi : ℕ) : σ.agreeOn σ lo hi := by
  intro r _ _; rfl

theorem State.agreeOn_symm {σ₁ σ₂ : State} {lo hi : ℕ}
    (h : σ₁.agreeOn σ₂ lo hi) : σ₂.agreeOn σ₁ lo hi := by
  intro r hlo hhi; exact (h r hlo hhi).symm

/-- Writing the same value to the same register preserves agreement. -/
theorem State.agreeOn_write_same {σ₁ σ₂ : State} {lo hi n : ℕ} {v : ℕ}
    (h : σ₁.agreeOn σ₂ lo hi) :
    (σ₁.write n v).agreeOn (σ₂.write n v) lo hi := by
  intro r hlo hhi
  by_cases hr : r = n
  · simp [hr]
  · simp [write_read_diff _ _ _ _ hr, h r hlo hhi]

/-- If states agree on a range and we read from that range, we get the same value. -/
theorem State.agreeOn_read {σ₁ σ₂ : State} {lo hi r : ℕ}
    (h : σ₁.agreeOn σ₂ lo hi) (hlo : lo ≤ r) (hhi : r ≤ hi) :
    σ₁.read r = σ₂.read r := h r hlo hhi

/-- Helper for foldl max: value in accumulator is preserved. -/
private theorem foldl_max_ge_init (p : List Instr) (init : ℕ) :
    init ≤ p.foldl (fun acc i => max acc i.maxRegister) init := by
  induction p generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    calc init ≤ max init hd.maxRegister := Nat.le_max_left _ _
      _ ≤ _ := ih _

/-- Helper for foldl max: any element's maxRegister is ≤ the result. -/
private theorem foldl_max_ge_elem (p : List Instr) (init : ℕ) (instr : Instr) (h : instr ∈ p) :
    instr.maxRegister ≤ p.foldl (fun acc i => max acc i.maxRegister) init := by
  induction p generalizing init with
  | nil => cases h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases h with
    | head =>
      calc instr.maxRegister
          ≤ max init instr.maxRegister := Nat.le_max_right _ _
        _ ≤ _ := foldl_max_ge_init _ _
    | tail _ htl =>
      exact ih _ htl

/-- Helper: the instruction at a position has maxRegister ≤ program's maxRegister. -/
theorem Program.getInstr_maxRegister {p : Program} {i : ℕ} {instr : Instr}
    (h : p.getInstr i = some instr) : instr.maxRegister ≤ p.maxRegister := by
  simp only [getInstr] at h
  have hmem : instr ∈ p := List.mem_of_getElem? h
  simp only [maxRegister]
  exact foldl_max_ge_elem p 0 instr hmem

/-- Key lemma: if two configs agree on `[0, maxRegister]` and PC is the same,
    a step produces configs that still agree. -/
theorem Step.agreeOn {p : Program} {c₁ c₁' c₂ : Config}
    (hstep : Step p c₁ c₁')
    (hpc : c₁.pc = c₂.pc)
    (hagree : c₁.state.agreeOn c₂.state 0 p.maxRegister) :
    ∃ c₂', Step p c₂ c₂' ∧ c₁'.pc = c₂'.pc ∧
           c₁'.state.agreeOn c₂'.state 0 p.maxRegister := by
  cases hstep with
  | zero hinstr =>
    rename_i n
    -- The instruction is at c₁.pc = c₂.pc, so c₂ can take the same step
    rw [hpc] at hinstr
    use ⟨c₂.pc + 1, c₂.state.write n 0⟩
    refine ⟨Step.zero hinstr, ?_, ?_⟩
    · simp [hpc]
    · apply State.agreeOn_write_same hagree
  | succ hinstr =>
    rename_i n
    rw [hpc] at hinstr
    -- c₁ and c₂ read the same value from register n (since it's ≤ maxRegister)
    have hmax : n ≤ p.maxRegister := by
      have hinstr' : p.getInstr c₂.pc = some (Instr.S n) := hinstr
      have := Program.getInstr_maxRegister hinstr'
      simp [Instr.maxRegister] at this
      exact this
    have hread : c₁.state.read n = c₂.state.read n := hagree n (Nat.zero_le n) hmax
    use ⟨c₂.pc + 1, c₂.state.write n (c₂.state.read n + 1)⟩
    refine ⟨Step.succ hinstr, ?_, ?_⟩
    · simp [hpc]
    · rw [hread]
      apply State.agreeOn_write_same hagree
  | trans hinstr =>
    rename_i m n
    rw [hpc] at hinstr
    have hmax : m ≤ p.maxRegister ∧ n ≤ p.maxRegister := by
      have hinstr' : p.getInstr c₂.pc = some (Instr.T m n) := hinstr
      have := Program.getInstr_maxRegister hinstr'
      simp [Instr.maxRegister] at this
      constructor <;> omega
    have hread : c₁.state.read m = c₂.state.read m := hagree m (Nat.zero_le m) hmax.1
    use ⟨c₂.pc + 1, c₂.state.write n (c₂.state.read m)⟩
    refine ⟨Step.trans hinstr, ?_, ?_⟩
    · simp [hpc]
    · rw [hread]
      apply State.agreeOn_write_same hagree
  | jump_eq hinstr hcmp =>
    rename_i m n q
    rw [hpc] at hinstr
    have hmax : m ≤ p.maxRegister ∧ n ≤ p.maxRegister := by
      have hinstr' : p.getInstr c₂.pc = some (Instr.J m n q) := hinstr
      have := Program.getInstr_maxRegister hinstr'
      simp [Instr.maxRegister] at this
      constructor <;> omega
    have hreadm : c₁.state.read m = c₂.state.read m := hagree m (Nat.zero_le m) hmax.1
    have hreadn : c₁.state.read n = c₂.state.read n := hagree n (Nat.zero_le n) hmax.2
    have hcmp' : c₂.state.read m = c₂.state.read n := by rw [← hreadm, ← hreadn]; exact hcmp
    use ⟨q, c₂.state⟩
    refine ⟨Step.jump_eq hinstr hcmp', rfl, hagree⟩
  | jump_ne hinstr hcmp =>
    rename_i m n q
    rw [hpc] at hinstr
    have hmax : m ≤ p.maxRegister ∧ n ≤ p.maxRegister := by
      have hinstr' : p.getInstr c₂.pc = some (Instr.J m n q) := hinstr
      have := Program.getInstr_maxRegister hinstr'
      simp [Instr.maxRegister] at this
      constructor <;> omega
    have hreadm : c₁.state.read m = c₂.state.read m := hagree m (Nat.zero_le m) hmax.1
    have hreadn : c₁.state.read n = c₂.state.read n := hagree n (Nat.zero_le n) hmax.2
    have hcmp' : c₂.state.read m ≠ c₂.state.read n := by
      rw [← hreadm, ← hreadn]; exact hcmp
    use ⟨c₂.pc + 1, c₂.state⟩
    refine ⟨Step.jump_ne hinstr hcmp', ?_, hagree⟩
    simp [hpc]

/-- Multi-step agreement: if configs agree, multi-step produces agreeing configs. -/
theorem Steps.agreeOn {p : Program} {c₁ c₁' c₂ : Config}
    (hsteps : Steps p c₁ c₁')
    (hpc : c₁.pc = c₂.pc)
    (hagree : c₁.state.agreeOn c₂.state 0 p.maxRegister) :
    ∃ c₂', Steps p c₂ c₂' ∧ c₁'.pc = c₂'.pc ∧
           c₁'.state.agreeOn c₂'.state 0 p.maxRegister := by
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing c₂ with
  | refl =>
    exact ⟨c₂, Relation.ReflTransGen.refl, hpc, hagree⟩
  | head hstep _ ih =>
    obtain ⟨c₂_mid, hstep₂, hpc_mid, hagree_mid⟩ := Step.agreeOn hstep hpc hagree
    obtain ⟨c₂', hsteps₂, hpc', hagree'⟩ := ih hpc_mid hagree_mid
    exact ⟨c₂', Relation.ReflTransGen.head hstep₂ hsteps₂, hpc', hagree'⟩

/-- A shifted program only uses registers in [offset, offset + maxRegister]. -/
theorem Program.shiftRegisters_uses_range {p : Program} {offset i : ℕ} {instr : Instr}
    (h : (p.shiftRegisters offset).getInstr i = some instr) :
    ∀ r, (r ∈ instr.readsFrom ∨ instr.writesTo = some r) →
         offset ≤ r ∧ r ≤ offset + p.maxRegister := by
  intro r hr
  simp only [shiftRegisters, getInstr, List.getElem?_map] at h
  cases hp : p[i]? with
  | none => simp [hp] at h
  | some orig_instr =>
    simp [hp] at h
    have hmem : orig_instr ∈ p := List.mem_of_getElem? hp
    have horig_max : orig_instr.maxRegister ≤ p.maxRegister := foldl_max_ge_elem _ _ _ hmem
    cases orig_instr with
    | Z n =>
      simp [Instr.shiftRegisters] at h; subst h
      simp [Instr.readsFrom, Instr.writesTo] at hr
      subst hr
      simp [Instr.maxRegister] at horig_max
      omega
    | S n =>
      simp [Instr.shiftRegisters] at h; subst h
      simp [Instr.readsFrom, Instr.writesTo] at hr
      simp [Instr.maxRegister] at horig_max
      rcases hr with rfl | rfl <;> omega
    | T m n =>
      simp [Instr.shiftRegisters] at h; subst h
      simp [Instr.readsFrom, Instr.writesTo] at hr
      simp [Instr.maxRegister] at horig_max
      rcases hr with rfl | rfl | rfl <;> omega
    | J m n q =>
      simp [Instr.shiftRegisters] at h; subst h
      simp [Instr.readsFrom, Instr.writesTo] at hr
      simp [Instr.maxRegister] at horig_max
      rcases hr with rfl | rfl <;> omega

/-- For shifted programs, agreement on [offset, offset + original maxRegister] suffices. -/
theorem Step.agreeOn_shifted {p : Program} {offset : ℕ} {c₁ c₁' c₂ : Config}
    (hstep : Step (p.shiftRegisters offset) c₁ c₁')
    (hpc : c₁.pc = c₂.pc)
    (hagree : c₁.state.agreeOn c₂.state offset (offset + p.maxRegister)) :
    ∃ c₂', Step (p.shiftRegisters offset) c₂ c₂' ∧ c₁'.pc = c₂'.pc ∧
           c₁'.state.agreeOn c₂'.state offset (offset + p.maxRegister) := by
  cases hstep with
  | zero hinstr =>
    rename_i n
    rw [hpc] at hinstr
    have ⟨hlo, hhi⟩ := Program.shiftRegisters_uses_range hinstr n
                        (Or.inr rfl : n ∈ (Instr.Z n).readsFrom ∨ (Instr.Z n).writesTo = some n)
    use ⟨c₂.pc + 1, c₂.state.write n 0⟩
    refine ⟨Step.zero hinstr, ?_, ?_⟩
    · simp [hpc]
    · apply State.agreeOn_write_same hagree
  | succ hinstr =>
    rename_i n
    rw [hpc] at hinstr
    have ⟨hlo, hhi⟩ := Program.shiftRegisters_uses_range hinstr n
                        (Or.inl (List.mem_singleton.mpr rfl) : n ∈ (Instr.S n).readsFrom ∨ _)
    have hread : c₁.state.read n = c₂.state.read n := hagree n hlo hhi
    use ⟨c₂.pc + 1, c₂.state.write n (c₂.state.read n + 1)⟩
    refine ⟨Step.succ hinstr, ?_, ?_⟩
    · simp [hpc]
    · rw [hread]; apply State.agreeOn_write_same hagree
  | trans hinstr =>
    rename_i m n
    rw [hpc] at hinstr
    have ⟨hlo_m, hhi_m⟩ := Program.shiftRegisters_uses_range hinstr m
                            (Or.inl (List.Mem.head []) : m ∈ (Instr.T m n).readsFrom ∨ _)
    have hread : c₁.state.read m = c₂.state.read m := hagree m hlo_m hhi_m
    use ⟨c₂.pc + 1, c₂.state.write n (c₂.state.read m)⟩
    refine ⟨Step.trans hinstr, ?_, ?_⟩
    · simp [hpc]
    · rw [hread]; apply State.agreeOn_write_same hagree
  | jump_eq hinstr hcmp =>
    rename_i m n q
    rw [hpc] at hinstr
    have ⟨hlo_m, hhi_m⟩ := Program.shiftRegisters_uses_range hinstr m
                            (Or.inl (List.Mem.head [n]) : m ∈ (Instr.J m n q).readsFrom ∨ _)
    have ⟨hlo_n, hhi_n⟩ := Program.shiftRegisters_uses_range hinstr n
                            (Or.inl (List.mem_cons_of_mem m (List.mem_singleton.mpr rfl)) :
                             n ∈ (Instr.J m n q).readsFrom ∨ _)
    have hreadm : c₁.state.read m = c₂.state.read m := hagree m hlo_m hhi_m
    have hreadn : c₁.state.read n = c₂.state.read n := hagree n hlo_n hhi_n
    have hcmp' : c₂.state.read m = c₂.state.read n := by rw [← hreadm, ← hreadn]; exact hcmp
    use ⟨q, c₂.state⟩
    refine ⟨Step.jump_eq hinstr hcmp', rfl, hagree⟩
  | jump_ne hinstr hne =>
    rename_i m n q
    rw [hpc] at hinstr
    have ⟨hlo_m, hhi_m⟩ := Program.shiftRegisters_uses_range hinstr m
                            (Or.inl (List.Mem.head [n]) : m ∈ (Instr.J m n q).readsFrom ∨ _)
    have ⟨hlo_n, hhi_n⟩ := Program.shiftRegisters_uses_range hinstr n
                            (Or.inl (List.mem_cons_of_mem m (List.mem_singleton.mpr rfl)) :
                             n ∈ (Instr.J m n q).readsFrom ∨ _)
    have hreadm : c₁.state.read m = c₂.state.read m := hagree m hlo_m hhi_m
    have hreadn : c₁.state.read n = c₂.state.read n := hagree n hlo_n hhi_n
    have hne' : c₂.state.read m ≠ c₂.state.read n := by rw [← hreadm, ← hreadn]; exact hne
    use ⟨c₂.pc + 1, c₂.state⟩
    refine ⟨Step.jump_ne hinstr hne', ?_, hagree⟩
    simp [hpc]

/-- Multi-step version for shifted programs. -/
theorem Steps.agreeOn_shifted {p : Program} {offset : ℕ} {c₁ c₁' c₂ : Config}
    (hsteps : Steps (p.shiftRegisters offset) c₁ c₁')
    (hpc : c₁.pc = c₂.pc)
    (hagree : c₁.state.agreeOn c₂.state offset (offset + p.maxRegister)) :
    ∃ c₂', Steps (p.shiftRegisters offset) c₂ c₂' ∧ c₁'.pc = c₂'.pc ∧
           c₁'.state.agreeOn c₂'.state offset (offset + p.maxRegister) := by
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing c₂ with
  | refl => exact ⟨c₂, Relation.ReflTransGen.refl, hpc, hagree⟩
  | head hstep _ ih =>
    obtain ⟨c₂_mid, hstep₂, hpc_mid, hagree_mid⟩ := Step.agreeOn_shifted hstep hpc hagree
    obtain ⟨c₂', hsteps₂, hpc', hagree'⟩ := ih hpc_mid hagree_mid
    exact ⟨c₂', Relation.ReflTransGen.head hstep₂ hsteps₂, hpc', hagree'⟩

/-- Key lemma for composition: run a shifted program from an arbitrary state
that agrees with the shifted initial state on the program's registers.

This allows us to run multiple shifted programs on disjoint register ranges
starting from a shared state. -/
theorem Halts.shift_from_state {p : Program} {inputs : List ℕ} {σ : State}
    (offset : ℕ)
    (h : Halts p inputs)
    (hagree : ∀ r, r ≤ p.maxRegister → σ.read (r + offset) = inputs.getD r 0) :
    ∃ c, Steps (p.shiftRegisters offset) ⟨0, σ⟩ c ∧
         c.isHalted (p.shiftRegisters offset) ∧
         c.state.read offset = Result p inputs h := by
  -- Get the halting config from the shifted initial state
  obtain ⟨c_shift, hsteps_shift, hhalted_shift⟩ := Halts.shift offset h
  -- Show σ agrees with the shifted initial state on [offset, offset + maxRegister]
  have hagree' : σ.agreeOn ((State.fromInputs inputs).shift offset) offset
                           (offset + p.maxRegister) := by
    intro r hlo hhi
    have hr_off : r - offset ≤ p.maxRegister := by omega
    have hread_eq := hagree (r - offset) hr_off
    have heq : r - offset + offset = r := by omega
    simp only [State.read] at hread_eq
    rw [heq] at hread_eq
    simp only [State.read, State.shift, hlo, ↓reduceIte, State.fromInputs, List.getD]
    exact hread_eq
  -- Use Steps.agreeOn_shifted to get execution from σ
  -- Note: (Config.init inputs).shift offset = ⟨0, (State.fromInputs inputs).shift offset⟩
  have hpc : ((Config.init inputs).shift offset).pc = (⟨0, σ⟩ : Config).pc := rfl
  obtain ⟨c, hsteps, hpc', hagree''⟩ :=
    Steps.agreeOn_shifted hsteps_shift hpc (State.agreeOn_symm hagree')
  use c
  refine ⟨hsteps, ?_, ?_⟩
  · -- Halted status: c.isHalted (p.shiftRegisters offset)
    -- We know c_shift.isHalted (p.shiftRegisters offset) and c_shift.pc = c.pc
    simp only [Config.isHalted, Program.shiftRegisters_length] at hhalted_shift ⊢
    omega
  · -- Result at offset
    -- c.state agrees with c_shift.state on [offset, offset + maxRegister]
    -- Result is at register offset, which is in this range
    have hread_agree := hagree'' offset (Nat.le_refl offset) (Nat.le_add_right offset p.maxRegister)
    rw [← hread_agree]
    -- Goal: c_shift.state.read offset = Result p inputs h
    -- Use Steps.shift_inv to get the original halting config
    obtain ⟨d, hd_eq, hd_steps⟩ := Steps.shift_inv offset hsteps_shift
    -- d is the original halting config, c_shift = d.shift offset
    -- c_shift.state.read offset = d.state.read 0
    have hread_shift : c_shift.state.read offset = d.state.read 0 := by
      simp only [hd_eq, Config.shift_state, State.shift_read (hr := Nat.le_refl offset)]
      simp
    rw [hread_shift]
    -- d is halted and reachable from Config.init inputs
    have hd_halted : d.isHalted p := by
      rw [← Config.isHalted_shift d p offset, ← hd_eq]
      exact hhalted_shift
    -- Now we need: d.state.read 0 = Result p inputs h
    -- Both d and (Classical.choose h) are halting configs reachable from same start
    -- By determinism, they must be equal
    have hd_halts : Halts p inputs := ⟨d, hd_steps, hd_halted⟩
    -- The result is defined as (Classical.choose h).state.output
    -- We show d = Classical.choose h using determinism
    have hd_eq_choose : d = Classical.choose h := by
      have hch := Classical.choose_spec h
      have hch_steps := hch.1
      have hch_halted := hch.2
      -- d is reachable from init, choose is halted and reachable from init
      -- By deterministic_continuation, (Classical.choose h) is reachable from d
      have h1 := Steps.deterministic_continuation hd_steps hch_steps hch_halted
      -- But d is halted, so no steps are possible from d
      -- Thus Steps p d (Classical.choose h) must be refl, so d = Classical.choose h
      cases h1 using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hstep _ => exact absurd hstep (Step.halted_no_step hd_halted)
    rw [hd_eq_choose]
    rfl

end Urm
