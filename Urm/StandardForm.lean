/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.StraightLine
import Urm.Computable

/-! # Standard Form Programs

This file defines standard-form programs (those with bounded jump targets).
A program is in standard form if all jump instructions target positions at most
equal to the program length. This allows jumps to any instruction (0..length-1)
or to the "virtual halt" position (length).

This property is essential for sequential composition: when we concatenate
programs, jump targets in the second program are shifted, and the bounded
property ensures they remain valid.

## Main definitions

- `Instr.has_bounded_jump`: checks if an instruction has a bounded jump target
- `Program.isStandardForm`: decidable check for standard form (Bool)
- `Program.IsStandardForm`: Prop version of standard form
- `URMComputableSF`: computability by a standard-form program

## Main results

- `straight_line_isStandardForm`: straight-line programs are standard form

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Standard Form

A program is in "standard form" if all jump targets are bounded by the program length.
This is a syntactic property: jumps can target any instruction index (0..length-1) or
the "virtual halt" position (length), but nothing beyond.

This property is essential for sequential composition: when concatenating programs,
jump targets in the second program are shifted by the first program's length, and
the bounded property ensures the shifted targets remain valid. -/

/-- Check if an instruction has a bounded jump target relative to a given length.
Non-jump instructions trivially satisfy this. -/
def Instr.has_bounded_jump (len : ℕ) : Instr → Bool
  | Instr.Z _ => true
  | Instr.S _ => true
  | Instr.T _ _ => true
  | Instr.J _ _ q => q ≤ len

/-- A program is in standard form if all jump targets are bounded by the program length.
Jumps can target any instruction (0..length-1) or the "virtual halt" position (length). -/
def Program.isStandardForm (p : Program) : Bool :=
  p.all (Instr.has_bounded_jump p.length)

/-- Prop version: a program is in standard form. -/
def Program.IsStandardForm (p : Program) : Prop :=
  p.isStandardForm = true

/-- A partial function is URM-computable by a standard form program. -/
def URMComputableSF (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∃ p : Program, p.IsStandardForm ∧
    ∀ inputs : Fin n → ℕ,
      let inputList := List.ofFn inputs
      (Halts p inputList ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts p inputList) (hDom : (f inputs).Dom),
        Result p inputList hHalts = (f inputs).get hDom

/-- Non-jumping instructions have bounded jumps for any length. -/
theorem Instr.has_bounded_jump_of_is_non_jumping {instr : Instr} (h : instr.is_non_jumping = true)
    (len : ℕ) : instr.has_bounded_jump len = true := by
  cases instr <;> simp_all [is_non_jumping, has_bounded_jump]

/-- has_bounded_jump is monotonic: if bounded for len1, then bounded for any len2 ≥ len1. -/
theorem Instr.has_bounded_jump_mono {instr : Instr} {len1 len2 : ℕ}
    (h : instr.has_bounded_jump len1 = true) (hle : len1 ≤ len2) :
    instr.has_bounded_jump len2 = true := by
  cases instr with
  | Z _ | S _ | T _ _ => simp [has_bounded_jump]
  | J _ _ q => simp only [has_bounded_jump, decide_eq_true_eq] at h ⊢; omega

/-- shift_jumps preserves bounded jumps with adjusted bound. -/
theorem Instr.has_bounded_jump_shift_jumps {instr : Instr} {len offset : ℕ}
    (h : instr.has_bounded_jump len = true) :
    (instr.shift_jumps offset).has_bounded_jump (offset + len) = true := by
  cases instr with
  | Z _ | S _ | T _ _ => simp [shift_jumps, has_bounded_jump]
  | J _ _ q => simp only [shift_jumps, has_bounded_jump, decide_eq_true_eq] at h ⊢; omega

/-- If p is standard form, then p.shift_jumps offset has bounded jumps for any bound ≥ offset + p.length.
This is the generic theorem for proving shifted subprograms have bounded jumps. -/
theorem Program.IsStandardForm.shift_jumps_has_bounded_jumps {p : Program} (hsf : p.IsStandardForm)
    (offset bound : ℕ) (hbound : offset + p.length ≤ bound) :
    ∀ instr ∈ p.shift_jumps offset, instr.has_bounded_jump bound = true := by
  intro instr hinstr
  simp only [Program.shift_jumps, List.mem_map] at hinstr
  obtain ⟨instr', hinstr'_mem, hinstr'_eq⟩ := hinstr
  subst hinstr'_eq
  have hbounded : instr'.has_bounded_jump p.length = true := by
    unfold IsStandardForm isStandardForm at hsf
    exact List.all_eq_true.mp hsf instr' hinstr'_mem
  have hshifted := Instr.has_bounded_jump_shift_jumps (len := p.length) (offset := offset) hbounded
  exact Instr.has_bounded_jump_mono hshifted hbound

/-- Straight-line programs are in standard form. -/
theorem straight_line_isStandardForm {p : Program} (hsl : p.is_straight_line = true) :
    p.IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm; rw [List.all_eq_true]
  intro instr hinstr
  exact Instr.has_bounded_jump_of_is_non_jumping (List.all_eq_true.mp hsl instr hinstr) p.length

/-! ## Semantic Consequence

The syntactic standard form property implies that whenever a program halts,
it halts exactly at the program length (not beyond). This is because:
1. Non-jump instructions increment pc by 1
2. Jump instructions set pc to at most p.length (by the bounded jump property)
3. Therefore pc can never exceed p.length
4. The only way to halt (pc ≥ p.length) is to have pc = p.length -/

/-- Extract the bounded jump property for a specific instruction from IsStandardForm. -/
theorem Program.IsStandardForm.getElem?_has_bounded_jump {p : Program} (hsf : p.IsStandardForm)
    {i : ℕ} {instr : Instr} (h : p[i]? = some instr) :
    instr.has_bounded_jump p.length = true := by
  unfold IsStandardForm isStandardForm at hsf
  rw [List.all_eq_true] at hsf
  have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
  have hmem : instr ∈ p := heq ▸ List.getElem_mem hlt
  exact hsf instr hmem

/-- A single step from pc < p.length results in pc' ≤ p.length for standard form programs. -/
theorem Step.pc_le_length_of_step {p : Program} (hsf : p.IsStandardForm)
    {c c' : Config} (hstep : Step p c c') : c'.pc ≤ p.length := by
  cases hstep with
  | zero hinstr | succ hinstr | trans hinstr | jump_ne hinstr _ =>
    exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hinstr).1
  | jump_eq hinstr _ =>
    simpa [Instr.has_bounded_jump] using hsf.getElem?_has_bounded_jump hinstr

/-- The pc stays ≤ p.length throughout execution of a standard form program. -/
theorem Program.IsStandardForm.pc_le_length {p : Program} (hsf : p.IsStandardForm)
    {c c' : Config} (hsteps : Steps p c c') (hpc : c.pc ≤ p.length) : c'.pc ≤ p.length := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact hpc
  | head hstep _ ih =>
    exact ih (Step.pc_le_length_of_step hsf hstep)

/-- Standard form programs halt exactly at their length.

This is the key semantic consequence of the syntactic bounded-jump property. -/
theorem Program.IsStandardForm.halts_at_length {p : Program} (hsf : p.IsStandardForm)
    (inputs : List ℕ) (c : Config) (hsteps : Steps p (Config.init inputs) c)
    (hhalted : c.is_halted p) : c.pc = p.length :=
  Nat.le_antisymm (hsf.pc_le_length hsteps (Nat.zero_le _)) hhalted

/-- When a standard form program halts from any starting point with pc ≤ length, pc = length. -/
theorem Program.IsStandardForm.pc_eq_length_of_halted {p : Program} (hsf : p.IsStandardForm)
    {c c' : Config} (hsteps : Steps p c c') (hpc : c.pc ≤ p.length)
    (hhalted : c'.is_halted p) : c'.pc = p.length :=
  Nat.le_antisymm (hsf.pc_le_length hsteps hpc) hhalted

/-! ## Standard Form Normalization

Every program can be converted to an equivalent standard form program by capping
jump targets at the program length. A jump to position > length causes immediate
halt, as does a jump to exactly length, so they're behaviorally equivalent. -/

/-- Cap a jump target to be at most `len`. Non-jump instructions are unchanged. -/
def Instr.cap_jump (len : ℕ) : Instr → Instr
  | Instr.Z n => Instr.Z n
  | Instr.S n => Instr.S n
  | Instr.T m n => Instr.T m n
  | Instr.J m n q => Instr.J m n (min q len)

/-- Convert a program to standard form by capping all jump targets at the program length. -/
def Program.to_standard_form (p : Program) : Program :=
  p.map (Instr.cap_jump p.length)

/-! ### Basic Properties of cap_jump and to_standard_form -/

@[simp]
theorem Instr.cap_jump_Z (len n : ℕ) : (Instr.Z n).cap_jump len = Instr.Z n := rfl

@[simp]
theorem Instr.cap_jump_S (len n : ℕ) : (Instr.S n).cap_jump len = Instr.S n := rfl

@[simp]
theorem Instr.cap_jump_T (len m n : ℕ) : (Instr.T m n).cap_jump len = Instr.T m n := rfl

@[simp]
theorem Instr.cap_jump_J (len m n q : ℕ) :
    (Instr.J m n q).cap_jump len = Instr.J m n (min q len) := rfl

/-- to_standard_form preserves program length. -/
@[simp]
theorem Program.to_standard_form_length (p : Program) :
    p.to_standard_form.length = p.length := by
  simp [to_standard_form]

/-- cap_jump always produces an instruction with bounded jump. -/
theorem Instr.has_bounded_jump_cap_jump (len : ℕ) (instr : Instr) :
    (instr.cap_jump len).has_bounded_jump len = true := by
  cases instr <;> simp [cap_jump, has_bounded_jump]

/-- to_standard_form produces a standard form program. -/
theorem Program.to_standard_form_isStandardForm (p : Program) :
    p.to_standard_form.IsStandardForm := by
  unfold IsStandardForm isStandardForm to_standard_form
  rw [List.all_eq_true, List.length_map]
  intro instr hinstr
  obtain ⟨orig, _, rfl⟩ := List.mem_map.mp hinstr
  exact Instr.has_bounded_jump_cap_jump p.length orig

/-! ### Instruction Access in to_standard_form -/

/-- Accessing an instruction in to_standard_form gives the cap_jump'd instruction. -/
theorem Program.getElem?_to_standard_form (p : Program) (i : ℕ) :
    p.to_standard_form[i]? = (p[i]?).map (Instr.cap_jump p.length) := by
  simp only [to_standard_form, List.getElem?_map]

/-! ### Behavioral Equivalence

Two programs are behaviorally equivalent if they halt on the same inputs
and produce the same results. We prove that p and p.to_standard_form are
behaviorally equivalent. -/

/-! #### Step Correspondence

For each instruction type, we show correspondence between steps in p and p.to_standard_form. -/

/-- If original program has instruction at pc, the transformed program has the capped version. -/
theorem Program.to_standard_form_getElem?_some {p : Program} {i : ℕ} {instr : Instr}
    (h : p[i]? = some instr) :
    p.to_standard_form[i]? = some (instr.cap_jump p.length) := by
  simp [getElem?_to_standard_form, h]

/-- Z instruction: identical step in both programs. -/
theorem Step.to_standard_form_zero {p : Program} {c : Config} {n : ℕ}
    (h : p[c.pc]? = some (Instr.Z n)) :
    Step p.to_standard_form c ⟨c.pc + 1, c.state.write n 0⟩ := by
  have hcap : p.to_standard_form[c.pc]? = some (Instr.Z n) := by
    simp [Program.getElem?_to_standard_form, h]
  exact Step.zero hcap

/-- S instruction: identical step in both programs. -/
theorem Step.to_standard_form_succ {p : Program} {c : Config} {n : ℕ}
    (h : p[c.pc]? = some (Instr.S n)) :
    Step p.to_standard_form c ⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩ := by
  have hcap : p.to_standard_form[c.pc]? = some (Instr.S n) := by
    simp [Program.getElem?_to_standard_form, h]
  exact Step.succ hcap

/-- T instruction: identical step in both programs. -/
theorem Step.to_standard_form_trans {p : Program} {c : Config} {m n : ℕ}
    (h : p[c.pc]? = some (Instr.T m n)) :
    Step p.to_standard_form c ⟨c.pc + 1, c.state.write n (c.state.read m)⟩ := by
  have hcap : p.to_standard_form[c.pc]? = some (Instr.T m n) := by
    simp [Program.getElem?_to_standard_form, h]
  exact Step.trans hcap

/-- J instruction with bounded target (q ≤ p.length): identical step in both programs
    when condition is true. -/
theorem Step.to_standard_form_jump_eq_bounded {p : Program} {c : Config} {m n q : ℕ}
    (h : p[c.pc]? = some (Instr.J m n q))
    (hbounded : q ≤ p.length)
    (heq : c.state.read m = c.state.read n) :
    Step p.to_standard_form c ⟨q, c.state⟩ := by
  have hcap : p.to_standard_form[c.pc]? = some (Instr.J m n (min q p.length)) := by
    simp [Program.getElem?_to_standard_form, h]
  have hmin : min q p.length = q := Nat.min_eq_left hbounded
  rw [hmin] at hcap
  exact Step.jump_eq hcap heq

/-- J instruction: identical step in both programs when condition is false. -/
theorem Step.to_standard_form_jump_ne {p : Program} {c : Config} {m n q : ℕ}
    (h : p[c.pc]? = some (Instr.J m n q))
    (hne : c.state.read m ≠ c.state.read n) :
    Step p.to_standard_form c ⟨c.pc + 1, c.state⟩ := by
  have hcap : p.to_standard_form[c.pc]? = some (Instr.J m n (min q p.length)) := by
    simp [Program.getElem?_to_standard_form, h]
  exact Step.jump_ne hcap hne

/-! #### Halting Equivalence

The key insight: when a jump target q > p.length, both the original and
the capped program cause immediate halt (original jumps to q ≥ p.length,
capped jumps to p.length). Both halt with the same state. -/

/-- Configuration relation for simulation: configs are related if they have the same
    pc and state, OR if both are in halted states with the same state. -/
def ConfigRelated (p : Program) (c₁ c₂ : Config) : Prop :=
  (c₁.pc = c₂.pc ∧ c₁.state = c₂.state) ∨
  (c₁.is_halted p ∧ c₂.is_halted p.to_standard_form ∧ c₁.state = c₂.state)

/-- Forward simulation: if original can step, standard form can step to a related config. -/
theorem Step.simulate_to_standard_form {p : Program} {c₁ c₁' : Config}
    (hstep : Step p c₁ c₁') :
    ∃ c₂', Steps p.to_standard_form c₁ c₂' ∧ ConfigRelated p c₁' c₂' := by
  cases hstep with
  | zero hinstr => exact ⟨_, Steps.single (Step.to_standard_form_zero hinstr), Or.inl ⟨rfl, rfl⟩⟩
  | succ hinstr => exact ⟨_, Steps.single (Step.to_standard_form_succ hinstr), Or.inl ⟨rfl, rfl⟩⟩
  | trans hinstr => exact ⟨_, Steps.single (Step.to_standard_form_trans hinstr), Or.inl ⟨rfl, rfl⟩⟩
  | jump_ne hinstr hne =>
    exact ⟨_, Steps.single (Step.to_standard_form_jump_ne hinstr hne), Or.inl ⟨rfl, rfl⟩⟩
  | jump_eq hinstr heq =>
    rename_i m n q
    by_cases hbounded : q ≤ p.length
    · exact ⟨_, Steps.single (Step.to_standard_form_jump_eq_bounded hinstr hbounded heq), Or.inl ⟨rfl, rfl⟩⟩
    · have hcap := Program.to_standard_form_getElem?_some hinstr
      simp only [Instr.cap_jump, Nat.min_eq_right (Nat.le_of_not_ge hbounded)] at hcap
      exact ⟨_, Steps.single (Step.jump_eq hcap heq),
             Or.inr ⟨by simp; omega, by simp [Program.to_standard_form_length], rfl⟩⟩

/-- Multi-step simulation: if original reaches halted config, standard form can too. -/
theorem Steps.simulate_to_standard_form_halts {p : Program} {c c' : Config}
    (hsteps : Steps p c c') (hhalted : c'.is_halted p) :
    ∃ c₂', Steps p.to_standard_form c c₂' ∧ c₂'.is_halted p.to_standard_form ∧ c'.state = c₂'.state := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨c', Steps.refl _, by simp [Program.to_standard_form_length] at hhalted ⊢; exact hhalted, rfl⟩
  | head hstep hrest ih =>
    obtain ⟨c₂_mid, hsteps₂_mid, hrel_mid⟩ := Step.simulate_to_standard_form hstep
    rcases hrel_mid with ⟨hpc_mid, hstate_mid⟩ | ⟨h_c_mid_halted, hhalted_mid, hstate_mid⟩
    · rename_i c_mid
      have hcfg_eq : c_mid = c₂_mid := by ext <;> [exact hpc_mid; simp only [hstate_mid]]
      subst hcfg_eq
      obtain ⟨c₂', hsteps₂', hhalted₂', hstate_eq⟩ := ih
      exact ⟨c₂', Steps.trans hsteps₂_mid hsteps₂', hhalted₂', hstate_eq⟩
    · have hc_mid_eq_c' : _ = c' := Steps.eq_of_halts (Steps.refl _) h_c_mid_halted hrest hhalted
      exact ⟨c₂_mid, hsteps₂_mid, hhalted_mid, by rw [← hc_mid_eq_c']; exact hstate_mid⟩

/-- Forward halting: if original halts, standard form halts with same state. -/
theorem Halts.to_standard_form {p : Program} {inputs : List ℕ}
    (h : Halts p inputs) : Halts p.to_standard_form inputs := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  obtain ⟨c₂, hsteps₂, hhalted₂, _⟩ := Steps.simulate_to_standard_form_halts hsteps hhalted
  exact ⟨c₂, hsteps₂, hhalted₂⟩

/-! #### Reverse Direction -/

/-- Reverse simulation: if standard form can step, original can step to a related config. -/
theorem Step.simulate_from_to_standard_form {p : Program} {c₁ c₁' : Config}
    (hstep : Step p.to_standard_form c₁ c₁') :
    ∃ c₂', Steps p c₁ c₂' ∧ ConfigRelated p c₂' c₁' := by
  cases hstep with
  | zero hinstr =>
    rw [Program.getElem?_to_standard_form] at hinstr; simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr_orig, hinstr_orig, hcap⟩ := hinstr
    cases instr_orig with
    | Z n' => simp at hcap; subst hcap; exact ⟨_, Steps.single (Step.zero hinstr_orig), Or.inl ⟨rfl, rfl⟩⟩
    | S _ | T _ _ | J _ _ _ => simp at hcap
  | succ hinstr =>
    rw [Program.getElem?_to_standard_form] at hinstr; simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr_orig, hinstr_orig, hcap⟩ := hinstr
    cases instr_orig with
    | S n' => simp at hcap; subst hcap; exact ⟨_, Steps.single (Step.succ hinstr_orig), Or.inl ⟨rfl, rfl⟩⟩
    | Z _ | T _ _ | J _ _ _ => simp at hcap
  | trans hinstr =>
    rw [Program.getElem?_to_standard_form] at hinstr; simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr_orig, hinstr_orig, hcap⟩ := hinstr
    cases instr_orig with
    | T m' n' => simp at hcap; obtain ⟨rfl, rfl⟩ := hcap
                 exact ⟨_, Steps.single (Step.trans hinstr_orig), Or.inl ⟨rfl, rfl⟩⟩
    | Z _ | S _ | J _ _ _ => simp at hcap
  | jump_eq hinstr heq_reg =>
    rw [Program.getElem?_to_standard_form] at hinstr; simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr_orig, hinstr_orig, hcap⟩ := hinstr
    cases instr_orig with
    | J m' n' q' =>
      simp only [Instr.cap_jump_J, Instr.J.injEq] at hcap; obtain ⟨rfl, rfl, htarget⟩ := hcap
      by_cases hbounded : q' ≤ p.length
      · rw [Nat.min_eq_left hbounded] at htarget; subst htarget
        exact ⟨_, Steps.single (Step.jump_eq hinstr_orig heq_reg), Or.inl ⟨rfl, rfl⟩⟩
      · have hgt : q' > p.length := Nat.not_le.mp hbounded
        rw [Nat.min_eq_right (Nat.le_of_lt hgt)] at htarget; subst htarget
        exact ⟨⟨q', c₁.state⟩, Steps.single (Step.jump_eq hinstr_orig heq_reg),
               Or.inr ⟨by simp; omega, by simp [Program.to_standard_form_length], rfl⟩⟩
    | Z _ | S _ | T _ _ => simp at hcap
  | jump_ne hinstr hne_reg =>
    rw [Program.getElem?_to_standard_form] at hinstr; simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr_orig, hinstr_orig, hcap⟩ := hinstr
    cases instr_orig with
    | J m' n' q' => simp at hcap; obtain ⟨rfl, rfl, _⟩ := hcap
                    exact ⟨_, Steps.single (Step.jump_ne hinstr_orig hne_reg), Or.inl ⟨rfl, rfl⟩⟩
    | Z _ | S _ | T _ _ => simp at hcap

/-- Multi-step reverse simulation: if standard form reaches halted config, original can too. -/
theorem Steps.simulate_from_to_standard_form_halts {p : Program} {c c' : Config}
    (hsteps : Steps p.to_standard_form c c') (hhalted : c'.is_halted p.to_standard_form) :
    ∃ c₂', Steps p c c₂' ∧ c₂'.is_halted p ∧ c'.state = c₂'.state := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨c', Steps.refl _, by simp [Program.to_standard_form_length] at hhalted ⊢; exact hhalted, rfl⟩
  | head hstep hrest ih =>
    obtain ⟨c₂_mid, hsteps₂_mid, hrel_mid⟩ := Step.simulate_from_to_standard_form hstep
    rcases hrel_mid with ⟨hpc_mid, hstate_mid⟩ | ⟨h_c_mid_halted, hhalted_mid, hstate_mid⟩
    · rename_i c_mid
      have hcfg_eq : c₂_mid = c_mid := by ext <;> [exact hpc_mid; simp only [hstate_mid]]
      subst hcfg_eq
      obtain ⟨c₂', hsteps₂', hhalted₂', hstate_eq⟩ := ih
      exact ⟨c₂', Steps.trans hsteps₂_mid hsteps₂', hhalted₂', hstate_eq⟩
    · rename_i c_mid
      have hc_mid_eq_c' : c_mid = c' := Steps.eq_of_halts (Steps.refl _) hhalted_mid hrest hhalted
      exact ⟨c₂_mid, hsteps₂_mid, h_c_mid_halted, by rw [← hc_mid_eq_c']; exact hstate_mid.symm⟩

/-- Reverse halting: if standard form halts, original halts with same state. -/
theorem Halts.of_to_standard_form {p : Program} {inputs : List ℕ}
    (h : Halts p.to_standard_form inputs) : Halts p inputs := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  obtain ⟨c₂, hsteps₂, hhalted₂, _⟩ := Steps.simulate_from_to_standard_form_halts hsteps hhalted
  exact ⟨c₂, hsteps₂, hhalted₂⟩

/-- Halting equivalence: original halts iff standard form halts. -/
theorem Halts.to_standard_form_iff {p : Program} {inputs : List ℕ} :
    Halts p inputs ↔ Halts p.to_standard_form inputs :=
  ⟨Halts.to_standard_form, Halts.of_to_standard_form⟩

/-! #### Result Preservation -/

/-- State preservation: both reach configs with the same state. -/
theorem Result.to_standard_form_state {p : Program} {inputs : List ℕ}
    (hp : Halts p inputs) (hq : Halts p.to_standard_form inputs) :
    (Classical.choose hp).state = (Classical.choose hq).state := by
  have ⟨hsteps, hhalted⟩ := Classical.choose_spec hp
  have ⟨hsteps', hhalted'⟩ := Classical.choose_spec hq
  obtain ⟨c₂, hsteps₂, hhalted₂, hstate_eq⟩ := Steps.simulate_to_standard_form_halts hsteps hhalted
  rw [Steps.eq_of_halts hsteps' hhalted' hsteps₂ hhalted₂, hstate_eq]

/-- Result equality: both programs produce the same output. -/
theorem Result.to_standard_form {p : Program} {inputs : List ℕ}
    (hp : Halts p inputs) (hq : Halts p.to_standard_form inputs) :
    Result p inputs hp = Result p.to_standard_form inputs hq := by
  simp only [Result, State.output, Result.to_standard_form_state hp hq]

/-- Standard form computability implies general computability (trivial direction). -/
theorem URMComputableSF.toComputable {n : ℕ} {f : (Fin n → ℕ) → Part ℕ}
    (h : URMComputableSF n f) : URMComputable n f := by
  obtain ⟨p, _, hspec⟩ := h
  exact ⟨p, hspec⟩

/-- General computability implies standard form computability.
Any computable function can be witnessed by a standard form program. -/
theorem URMComputable.toSF {n : ℕ} {f : (Fin n → ℕ) → Part ℕ}
    (h : URMComputable n f) : URMComputableSF n f := by
  obtain ⟨p, hspec⟩ := h
  refine ⟨p.to_standard_form, Program.to_standard_form_isStandardForm p, fun inputs => ?_⟩
  constructor
  · rw [← Halts.to_standard_form_iff]
    exact (hspec inputs).1
  · intro hHalts hDom
    have hp : Halts p (List.ofFn inputs) := Halts.to_standard_form_iff.mpr hHalts
    rw [← Result.to_standard_form hp hHalts]
    exact (hspec inputs).2 hp hDom

end Urm
