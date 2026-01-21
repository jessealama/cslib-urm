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

- `Step.shift`: If P steps c→c', then P.shift_registers steps shifted(c)→shifted(c')
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

theorem shift_unshift (σ : State) (offset : ℕ) :
    (σ.shift offset).unshift offset = σ := by
  funext r
  simp only [unshift, shift, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]

/-! ### Read interaction with shifting -/

@[simp]
theorem shift_read (σ : State) (offset r : ℕ) (hr : offset ≤ r) :
    (σ.shift offset).read r = σ.read (r - offset) := by
  simp only [shift, read, hr, ↓reduceIte]

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
theorem is_halted_shift (c : Config) (p : Program) (offset : ℕ) :
    (c.shift offset).is_halted (p.shift_registers offset) ↔ c.is_halted p := by
  simp only [is_halted, shift_pc, Program.shift_registers, List.length_map]

/-- Unshifting a shifted config recovers the original. -/
@[simp]
theorem shift_unshift (c : Config) (offset : ℕ) :
    (c.shift offset).unshift offset = c := by
  simp only [shift, unshift, State.shift_unshift]

end Config

/-! ## Program Shifting Properties -/

namespace Instr

@[simp]
theorem shift_registers_zero (instr : Instr) : instr.shift_registers 0 = instr := by
  cases instr <;> simp [shift_registers]

theorem shift_registers_add (k₁ k₂ : ℕ) (instr : Instr) :
    (instr.shift_registers k₁).shift_registers k₂ = instr.shift_registers (k₁ + k₂) := by
  cases instr <;> simp [shift_registers, Nat.add_assoc]

@[simp]
theorem max_register_shift_registers (offset : ℕ) (instr : Instr) :
    (instr.shift_registers offset).max_register = instr.max_register + offset := by
  cases instr <;> simp [shift_registers, max_register, Nat.add_max_add_right]

end Instr

namespace Program

@[simp]
theorem shift_registers_length (offset : ℕ) (p : Program) :
    (p.shift_registers offset).length = p.length := by
  simp [shift_registers]

@[simp]
theorem shift_registers_zero (p : Program) : p.shift_registers 0 = p := by
  simp only [shift_registers]
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, Instr.shift_registers_zero, ih]

theorem shift_registers_add (k₁ k₂ : ℕ) (p : Program) :
    (p.shift_registers k₁).shift_registers k₂ = p.shift_registers (k₁ + k₂) := by
  simp [shift_registers, List.map_map, Function.comp_def, Instr.shift_registers_add]

@[simp]
theorem getElem?_shift_registers (offset : ℕ) (p : Program) (i : ℕ) :
    (p.shift_registers offset)[i]? = p[i]?.map (Instr.shift_registers offset) := by
  simp only [shift_registers, List.getElem?_map]

/-- Helper: foldl max with offset on function values shifts the result. -/
private theorem foldl_max_add_aux (offset : ℕ) (init : ℕ) (p : Program) :
    p.foldl (fun acc instr => max acc (instr.max_register + offset)) (init + offset) =
    p.foldl (fun acc instr => max acc instr.max_register) init + offset := by
  induction p generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have : max (init + offset) (hd.max_register + offset) = max init hd.max_register + offset := by omega
    rw [this, ih]

/-- The max_register of a shifted nonempty program equals the original max_register plus offset. -/
theorem max_register_shift_registers (offset : ℕ) (p : Program) (hp : p ≠ []) :
    (p.shift_registers offset).max_register = p.max_register + offset := by
  simp only [shift_registers, max_register]
  rw [List.foldl_map]
  simp only [Instr.max_register_shift_registers]
  cases p with
  | nil => contradiction
  | cons hd tl =>
    simp only [List.foldl_cons]
    have : max 0 (hd.max_register + offset) = max 0 hd.max_register + offset := by omega
    rw [this, foldl_max_add_aux]

end Program

/-! ## Step Correspondence -/

/-- If P steps c→c', then P.shift_registers steps shifted(c)→shifted(c'). -/
theorem Step.shift {p : Program} {c c' : Config} (offset : ℕ)
    (hstep : Step p c c') :
    Step (p.shift_registers offset) (c.shift offset) (c'.shift offset) := by
  cases hstep with
  | zero hinstr =>
    rename_i n
    have h : (p.shift_registers offset)[c.pc]? = some (Instr.Z (n + offset)) := by
      simp only [Program.getElem?_shift_registers, hinstr, Option.map_some, Instr.shift_registers]
    show Step _ _ ⟨c.pc + 1, (c.state.write n 0).shift offset⟩
    rw [← State.shift_write]; exact Step.zero h
  | succ hinstr =>
    rename_i n
    have h : (p.shift_registers offset)[c.pc]? = some (Instr.S (n + offset)) := by
      simp only [Program.getElem?_shift_registers, hinstr, Option.map_some, Instr.shift_registers]
    show Step _ _ ⟨c.pc + 1, (c.state.write n (c.state.read n + 1)).shift offset⟩
    rw [← State.shift_write, show c.state.read n = (c.state.shift offset).read (n + offset) by
      simp only [State.shift_read (hr := Nat.le_add_left offset n), Nat.add_sub_cancel]]
    exact Step.succ h
  | trans hinstr =>
    rename_i m n
    have h : (p.shift_registers offset)[c.pc]? = some (Instr.T (m + offset) (n + offset)) := by
      simp only [Program.getElem?_shift_registers, hinstr, Option.map_some, Instr.shift_registers]
    show Step _ _ ⟨c.pc + 1, (c.state.write n (c.state.read m)).shift offset⟩
    rw [← State.shift_write, show c.state.read m = (c.state.shift offset).read (m + offset) by
      simp only [State.shift_read (hr := Nat.le_add_left offset m), Nat.add_sub_cancel]]
    exact Step.trans h
  | jump_eq hinstr hcmp =>
    rename_i m n q
    have h : (p.shift_registers offset)[c.pc]? = some (Instr.J (m + offset) (n + offset) q) := by
      simp only [Program.getElem?_shift_registers, hinstr, Option.map_some, Instr.shift_registers]
    exact Step.jump_eq h (by simp only [Config.shift_state, State.shift_read (hr := Nat.le_add_left offset m),
      State.shift_read (hr := Nat.le_add_left offset n), Nat.add_sub_cancel]; exact hcmp)
  | jump_ne hinstr hcmp =>
    rename_i m n q
    have h : (p.shift_registers offset)[c.pc]? = some (Instr.J (m + offset) (n + offset) q) := by
      simp only [Program.getElem?_shift_registers, hinstr, Option.map_some, Instr.shift_registers]
    exact Step.jump_ne h (by simp only [Config.shift_state, State.shift_read (hr := Nat.le_add_left offset m),
      State.shift_read (hr := Nat.le_add_left offset n), Nat.add_sub_cancel]; exact hcmp)

/-- Multi-step version: if P goes from c to c' in multiple steps,
then P.shift_registers goes from shifted(c) to shifted(c'). -/
theorem Steps.shift {p : Program} {c c' : Config} (offset : ℕ)
    (hsteps : Steps p c c') :
    Steps (p.shift_registers offset) (c.shift offset) (c'.shift offset) := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hstep _ ih =>
    exact Relation.ReflTransGen.head (Step.shift offset hstep) ih

/-! ## Halting Equivalence -/

/-- If the original program halts, the shifted program halts. -/
theorem Halts.shift {p : Program} {inputs : List ℕ} (offset : ℕ) (h : Halts p inputs) :
    ∃ c, Steps (p.shift_registers offset) ((Config.init inputs).shift offset) c ∧
         c.is_halted (p.shift_registers offset) := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  exact ⟨c.shift offset, Steps.shift offset hsteps, (Config.is_halted_shift ..).mpr hhalted⟩

/-- Key invariant: A step in the shifted program from a shifted config produces a shifted config. -/
theorem Step.shift_inv {p : Program} {c : Config} {c' : Config} (offset : ℕ)
    (hstep : Step (p.shift_registers offset) (c.shift offset) c') :
    ∃ d, c' = d.shift offset ∧ Step p c d := by
  cases hinstr : p[c.pc]? with
  | none =>
    have h : (p.shift_registers offset)[(c.shift offset).pc]? = none := by
      simp only [Config.shift_pc, Program.getElem?_shift_registers, hinstr]; rfl
    cases hstep <;> simp_all
  | some instr =>
    have hshift_instr : (p.shift_registers offset)[(c.shift offset).pc]? =
                        some (instr.shift_registers offset) := by
      simp only [Config.shift_pc, Program.getElem?_shift_registers, hinstr]; rfl
    cases instr with
    | Z n =>
      simp only [Instr.shift_registers] at hshift_instr
      cases hstep with
      | zero h' =>
        rw [hshift_instr] at h'; cases h'
        exact ⟨⟨c.pc + 1, c.state.write n 0⟩, by simp [Config.shift, ← State.shift_write], Step.zero hinstr⟩
      | succ h' | trans h' | jump_eq h' _ | jump_ne h' _ => rw [hshift_instr] at h'; cases h'
    | S n =>
      simp only [Instr.shift_registers] at hshift_instr
      cases hstep with
      | succ h' =>
        rw [hshift_instr] at h'; cases h'
        refine ⟨⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩, ?_, Step.succ hinstr⟩
        simp only [Config.shift, ← State.shift_write, State.shift_read (hr := Nat.le_add_left offset n), Nat.add_sub_cancel]
      | zero h' | trans h' | jump_eq h' _ | jump_ne h' _ => rw [hshift_instr] at h'; cases h'
    | T m n =>
      simp only [Instr.shift_registers] at hshift_instr
      cases hstep with
      | trans h' =>
        rw [hshift_instr] at h'; cases h'
        refine ⟨⟨c.pc + 1, c.state.write n (c.state.read m)⟩, ?_, Step.trans hinstr⟩
        simp only [Config.shift, ← State.shift_write, State.shift_read (hr := Nat.le_add_left offset m), Nat.add_sub_cancel]
      | zero h' | succ h' | jump_eq h' _ | jump_ne h' _ => rw [hshift_instr] at h'; cases h'
    | J m n q =>
      simp only [Instr.shift_registers] at hshift_instr
      cases hstep with
      | jump_eq h' hcmp =>
        rw [hshift_instr] at h'; cases h'
        have hcmp_orig : c.state.read m = c.state.read n := by
          simp only [Config.shift_state, State.shift_read (hr := Nat.le_add_left offset m),
                     State.shift_read (hr := Nat.le_add_left offset n), Nat.add_sub_cancel] at hcmp; exact hcmp
        exact ⟨⟨q, c.state⟩, by simp [Config.shift], Step.jump_eq hinstr hcmp_orig⟩
      | jump_ne h' hne =>
        rw [hshift_instr] at h'; cases h'
        have hne_orig : c.state.read m ≠ c.state.read n := by
          simp only [Config.shift_state, State.shift_read (hr := Nat.le_add_left offset m),
                     State.shift_read (hr := Nat.le_add_left offset n), Nat.add_sub_cancel] at hne; exact hne
        exact ⟨⟨c.pc + 1, c.state⟩, by simp [Config.shift], Step.jump_ne hinstr hne_orig⟩
      | zero h' | succ h' | trans h' => rw [hshift_instr] at h'; cases h'

/-- Invariant extended to multi-step: configs reachable from shifted initial are shifted. -/
theorem Steps.shift_inv {p : Program} {c₀ c : Config} (offset : ℕ)
    (hsteps : Steps (p.shift_registers offset) (c₀.shift offset) c) :
    ∃ d, c = d.shift offset ∧ Steps p c₀ d := by
  generalize hc₀' : c₀.shift offset = c₀' at hsteps
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing c₀ with
  | refl => exact ⟨c₀, hc₀'.symm, Relation.ReflTransGen.refl⟩
  | head hstep _ ih =>
    subst hc₀'
    obtain ⟨d, hd_eq, hd_step⟩ := Step.shift_inv offset hstep
    obtain ⟨e, he_eq, he_steps⟩ := ih hd_eq.symm
    exact ⟨e, he_eq, Relation.ReflTransGen.head hd_step he_steps⟩

/-! ## Register Independence

For composition, we need to show that program execution only depends on registers
actually used by the program. Two states that agree on registers `[0, max_register]`
produce the same execution. -/

/-- Two states agree on registers in `[lo, hi]`. -/
def State.agree_on (σ₁ σ₂ : State) (lo hi : ℕ) : Prop :=
  ∀ r, lo ≤ r → r ≤ hi → σ₁.read r = σ₂.read r

theorem State.agree_on_symm {σ₁ σ₂ : State} {lo hi : ℕ}
    (h : σ₁.agree_on σ₂ lo hi) : σ₂.agree_on σ₁ lo hi := by
  intro r hlo hhi; exact (h r hlo hhi).symm

/-- Writing the same value to the same register preserves agreement. -/
theorem State.agree_on_write_same {σ₁ σ₂ : State} {lo hi n : ℕ} {v : ℕ}
    (h : σ₁.agree_on σ₂ lo hi) :
    (σ₁.write n v).agree_on (σ₂.write n v) lo hi := fun r hlo hhi => by
  by_cases hr : r = n <;> simp [hr, write_read_of_ne, h r hlo hhi]

/-- Helper for foldl max: value in accumulator is preserved.
    Re-exported from Program namespace for local use. -/
private theorem foldl_max_ge_init (p : List Instr) (init : ℕ) :
    init ≤ p.foldl (fun acc i => max acc i.max_register) init :=
  Program.max_register_foldl_ge_init init p

/-- Helper for foldl max: any element's max_register is ≤ the result.
    Re-exported from Program namespace for local use. -/
private theorem foldl_max_ge_elem (p : List Instr) (init : ℕ) (instr : Instr) (h : instr ∈ p) :
    instr.max_register ≤ p.foldl (fun acc i => max acc i.max_register) init :=
  Program.max_register_foldl_ge_elem p init instr h

/-- Key lemma: if two configs agree on `[0, max_register]` and PC is the same,
    a step produces configs that still agree. -/
theorem Step.agree_on {p : Program} {c₁ c₁' c₂ : Config}
    (hstep : Step p c₁ c₁')
    (hpc : c₁.pc = c₂.pc)
    (hagree : c₁.state.agree_on c₂.state 0 p.max_register) :
    ∃ c₂', Step p c₂ c₂' ∧ c₁'.pc = c₂'.pc ∧
           c₁'.state.agree_on c₂'.state 0 p.max_register := by
  cases hstep with
  | zero hinstr =>
    rw [hpc] at hinstr
    exact ⟨⟨c₂.pc + 1, c₂.state.write _ 0⟩, Step.zero hinstr, by simp [hpc], State.agree_on_write_same hagree⟩
  | succ hinstr =>
    rename_i n; rw [hpc] at hinstr
    have hmax : n ≤ p.max_register := by simpa [Instr.max_register] using Program.getElem?_max_register p hinstr
    have hread := hagree n (Nat.zero_le n) hmax
    exact ⟨⟨c₂.pc + 1, c₂.state.write n (c₂.state.read n + 1)⟩, Step.succ hinstr, by simp [hpc],
           by rw [hread]; exact State.agree_on_write_same hagree⟩
  | trans hinstr =>
    rename_i m n; rw [hpc] at hinstr
    have hmax := by simpa [Instr.max_register] using Program.getElem?_max_register p hinstr
    have hread := hagree m (Nat.zero_le m) (by omega : m ≤ p.max_register)
    exact ⟨⟨c₂.pc + 1, c₂.state.write n (c₂.state.read m)⟩, Step.trans hinstr, by simp [hpc],
           by rw [hread]; exact State.agree_on_write_same hagree⟩
  | jump_eq hinstr hcmp =>
    rename_i m n q; rw [hpc] at hinstr
    have hmax := by simpa [Instr.max_register] using Program.getElem?_max_register p hinstr
    have hreadm := hagree m (Nat.zero_le m) (by omega); have hreadn := hagree n (Nat.zero_le n) (by omega)
    exact ⟨⟨q, c₂.state⟩, Step.jump_eq hinstr (by rw [← hreadm, ← hreadn]; exact hcmp), rfl, hagree⟩
  | jump_ne hinstr hcmp =>
    rename_i m n q; rw [hpc] at hinstr
    have hmax := by simpa [Instr.max_register] using Program.getElem?_max_register p hinstr
    have hreadm := hagree m (Nat.zero_le m) (by omega); have hreadn := hagree n (Nat.zero_le n) (by omega)
    exact ⟨⟨c₂.pc + 1, c₂.state⟩, Step.jump_ne hinstr (by rw [← hreadm, ← hreadn]; exact hcmp), by simp [hpc], hagree⟩

/-- Multi-step agreement: if configs agree, multi-step produces agreeing configs. -/
theorem Steps.agree_on {p : Program} {c₁ c₁' c₂ : Config}
    (hsteps : Steps p c₁ c₁')
    (hpc : c₁.pc = c₂.pc)
    (hagree : c₁.state.agree_on c₂.state 0 p.max_register) :
    ∃ c₂', Steps p c₂ c₂' ∧ c₁'.pc = c₂'.pc ∧
           c₁'.state.agree_on c₂'.state 0 p.max_register := by
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing c₂ with
  | refl =>
    exact ⟨c₂, Relation.ReflTransGen.refl, hpc, hagree⟩
  | head hstep _ ih =>
    obtain ⟨c₂_mid, hstep₂, hpc_mid, hagree_mid⟩ := Step.agree_on hstep hpc hagree
    obtain ⟨c₂', hsteps₂, hpc', hagree'⟩ := ih hpc_mid hagree_mid
    exact ⟨c₂', Relation.ReflTransGen.head hstep₂ hsteps₂, hpc', hagree'⟩

/-- A shifted program only uses registers in [offset, offset + max_register]. -/
theorem Program.shift_registers_uses_range {p : Program} {offset i : ℕ} {instr : Instr}
    (h : (p.shift_registers offset)[i]? = some instr) :
    ∀ r, (r ∈ instr.reads_from ∨ instr.writes_to = some r) → offset ≤ r ∧ r ≤ offset + p.max_register := by
  intro r hr
  simp only [shift_registers, List.getElem?_map] at h
  cases hp : p[i]? with
  | none => simp [hp] at h
  | some orig_instr =>
    simp [hp] at h
    have horig_max : orig_instr.max_register ≤ p.max_register := foldl_max_ge_elem _ _ _ (List.mem_of_getElem? hp)
    cases orig_instr with
    | Z n => simp [Instr.shift_registers] at h; subst h; simp [Instr.reads_from, Instr.writes_to] at hr; subst hr
             simp [Instr.max_register] at horig_max; omega
    | S n => simp [Instr.shift_registers] at h; subst h; simp [Instr.reads_from, Instr.writes_to] at hr
             simp [Instr.max_register] at horig_max; rcases hr with rfl | rfl <;> omega
    | T m n => simp [Instr.shift_registers] at h; subst h; simp [Instr.reads_from, Instr.writes_to] at hr
               simp [Instr.max_register] at horig_max; rcases hr with rfl | rfl | rfl <;> omega
    | J m n q => simp [Instr.shift_registers] at h; subst h; simp [Instr.reads_from, Instr.writes_to] at hr
                 simp [Instr.max_register] at horig_max; rcases hr with rfl | rfl <;> omega

/-- For shifted programs, agreement on [offset, offset + original max_register] suffices. -/
theorem Step.agree_on_shifted {p : Program} {offset : ℕ} {c₁ c₁' c₂ : Config}
    (hstep : Step (p.shift_registers offset) c₁ c₁')
    (hpc : c₁.pc = c₂.pc)
    (hagree : c₁.state.agree_on c₂.state offset (offset + p.max_register)) :
    ∃ c₂', Step (p.shift_registers offset) c₂ c₂' ∧ c₁'.pc = c₂'.pc ∧
           c₁'.state.agree_on c₂'.state offset (offset + p.max_register) := by
  cases hstep with
  | zero hinstr =>
    rename_i n; rw [hpc] at hinstr
    have ⟨_, _⟩ := Program.shift_registers_uses_range hinstr n (Or.inr rfl)
    exact ⟨⟨c₂.pc + 1, c₂.state.write n 0⟩, Step.zero hinstr, by simp [hpc], State.agree_on_write_same hagree⟩
  | succ hinstr =>
    rename_i n; rw [hpc] at hinstr
    have ⟨hlo, hhi⟩ := Program.shift_registers_uses_range hinstr n (Or.inl (Finset.mem_singleton_self n))
    have hread := hagree n hlo hhi
    exact ⟨⟨c₂.pc + 1, c₂.state.write n (c₂.state.read n + 1)⟩, Step.succ hinstr, by simp [hpc],
           by rw [hread]; exact State.agree_on_write_same hagree⟩
  | trans hinstr =>
    rename_i m n; rw [hpc] at hinstr
    have ⟨hlo, hhi⟩ := Program.shift_registers_uses_range hinstr m (Or.inl (Finset.mem_singleton_self m))
    have hread := hagree m hlo hhi
    exact ⟨⟨c₂.pc + 1, c₂.state.write n (c₂.state.read m)⟩, Step.trans hinstr, by simp [hpc],
           by rw [hread]; exact State.agree_on_write_same hagree⟩
  | jump_eq hinstr hcmp =>
    rename_i m n q; rw [hpc] at hinstr
    have ⟨hlo_m, hhi_m⟩ := Program.shift_registers_uses_range hinstr m (Or.inl (Finset.mem_insert_self m {n}))
    have ⟨hlo_n, hhi_n⟩ := Program.shift_registers_uses_range hinstr n
                            (Or.inl (Finset.mem_insert_of_mem (Finset.mem_singleton_self n)))
    have hreadm := hagree m hlo_m hhi_m; have hreadn := hagree n hlo_n hhi_n
    exact ⟨⟨q, c₂.state⟩, Step.jump_eq hinstr (by rw [← hreadm, ← hreadn]; exact hcmp), rfl, hagree⟩
  | jump_ne hinstr hne =>
    rename_i m n q; rw [hpc] at hinstr
    have ⟨hlo_m, hhi_m⟩ := Program.shift_registers_uses_range hinstr m (Or.inl (Finset.mem_insert_self m {n}))
    have ⟨hlo_n, hhi_n⟩ := Program.shift_registers_uses_range hinstr n
                            (Or.inl (Finset.mem_insert_of_mem (Finset.mem_singleton_self n)))
    have hreadm := hagree m hlo_m hhi_m; have hreadn := hagree n hlo_n hhi_n
    exact ⟨⟨c₂.pc + 1, c₂.state⟩, Step.jump_ne hinstr (by rw [← hreadm, ← hreadn]; exact hne), by simp [hpc], hagree⟩

/-- Multi-step version for shifted programs. -/
theorem Steps.agree_on_shifted {p : Program} {offset : ℕ} {c₁ c₁' c₂ : Config}
    (hsteps : Steps (p.shift_registers offset) c₁ c₁')
    (hpc : c₁.pc = c₂.pc)
    (hagree : c₁.state.agree_on c₂.state offset (offset + p.max_register)) :
    ∃ c₂', Steps (p.shift_registers offset) c₂ c₂' ∧ c₁'.pc = c₂'.pc ∧
           c₁'.state.agree_on c₂'.state offset (offset + p.max_register) := by
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing c₂ with
  | refl => exact ⟨c₂, Relation.ReflTransGen.refl, hpc, hagree⟩
  | head hstep _ ih =>
    obtain ⟨c₂_mid, hstep₂, hpc_mid, hagree_mid⟩ := Step.agree_on_shifted hstep hpc hagree
    obtain ⟨c₂', hsteps₂, hpc', hagree'⟩ := ih hpc_mid hagree_mid
    exact ⟨c₂', Relation.ReflTransGen.head hstep₂ hsteps₂, hpc', hagree'⟩

/-- Key lemma for composition: run a shifted program from an arbitrary state
that agrees with the shifted initial state on the program's registers. -/
theorem Halts.shift_from_state {p : Program} {inputs : List ℕ} {σ : State}
    (offset : ℕ)
    (h : Halts p inputs)
    (hagree : ∀ r, r ≤ p.max_register → σ.read (r + offset) = inputs.getD r 0) :
    ∃ c, Steps (p.shift_registers offset) ⟨0, σ⟩ c ∧
         c.is_halted (p.shift_registers offset) ∧
         c.state.read offset = Result p inputs h := by
  obtain ⟨c_shift, hsteps_shift, hhalted_shift⟩ := Halts.shift offset h
  have hagree' : σ.agree_on ((State.of_inputs inputs).shift offset) offset (offset + p.max_register) := by
    intro r hlo hhi
    simp only [State.read, State.shift, hlo, ↓reduceIte, State.of_inputs, List.getD]
    simpa [State.read, show r - offset + offset = r from by omega] using hagree (r - offset) (by omega)
  have hpc : ((Config.init inputs).shift offset).pc = (⟨0, σ⟩ : Config).pc := rfl
  obtain ⟨c, hsteps, hpc', hagree''⟩ := Steps.agree_on_shifted hsteps_shift hpc (State.agree_on_symm hagree')
  refine ⟨c, hsteps, by simp only [Config.is_halted, Program.shift_registers_length] at hhalted_shift ⊢; omega, ?_⟩
  have hread_agree := hagree'' offset (Nat.le_refl offset) (Nat.le_add_right offset p.max_register)
  rw [← hread_agree]
  obtain ⟨d, hd_eq, hd_steps⟩ := Steps.shift_inv offset hsteps_shift
  have hread_shift : c_shift.state.read offset = d.state.read 0 := by
    simp only [hd_eq, Config.shift_state, State.shift_read (hr := Nat.le_refl offset)]; simp
  rw [hread_shift]
  have hd_halted : d.is_halted p := by rw [← Config.is_halted_shift d p offset, ← hd_eq]; exact hhalted_shift
  have hch := Classical.choose_spec h
  have hd_eq_choose : d = Classical.choose h := by
    cases Steps.deterministic_continuation hd_steps hch.1 hch.2 using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hstep _ => exact absurd hstep (Step.no_step_of_halted hd_halted)
  rw [hd_eq_choose]; rfl

/-- If a program halts from a state agreeing with inputs on all relevant registers,
    then it halts on those inputs. -/
theorem Halts.of_agreeing_state {p : Program} {inputs : List ℕ} {s : State} {c : Config}
    (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.is_halted p)
    (hagree : ∀ r, r ≤ p.max_register → s.read r = (State.of_inputs inputs).read r) :
    Halts p inputs := by
  have hagree' : s.agree_on (State.of_inputs inputs) 0 p.max_register := fun r _ hhi => hagree r hhi
  have hpc_eq : (⟨0, s⟩ : Config).pc = (Config.init inputs).pc := rfl
  obtain ⟨c', hsteps', hpc', _⟩ := Steps.agree_on hsteps hpc_eq hagree'
  exact ⟨c', hsteps', by simp only [Config.is_halted] at hhalted ⊢; omega⟩

end Urm
