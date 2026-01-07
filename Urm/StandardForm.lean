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

- `Instr.hasBoundedJump`: checks if an instruction has a bounded jump target
- `Program.isStandardForm`: decidable check for standard form (Bool)
- `Program.IsStandardForm`: Prop version of standard form
- `URMComputableSF`: computability by a standard-form program
- `Program.Equiv`: behavioral equivalence (same partial function)

## Notation

- `p ~ q`: program equivalence (both compute the same partial function)

## Main results

- `straightLine_isStandardForm`: straight-line programs are standard form
- `Program.equiv_toStandardForm`: every program is equivalent to its standard form

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
def Instr.hasBoundedJump (len : ℕ) : Instr → Bool
  | Instr.Z _ => true
  | Instr.S _ => true
  | Instr.T _ _ => true
  | Instr.J _ _ q => q ≤ len

/-- A program is in standard form if all jump targets are bounded by the program length.
Jumps can target any instruction (0..length-1) or the "virtual halt" position (length). -/
def Program.isStandardForm (p : Program) : Bool :=
  p.all (Instr.hasBoundedJump p.length)

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
theorem Instr.hasBoundedJump_of_isNonJumping {instr : Instr} (h : instr.isNonJumping = true)
    (len : ℕ) : instr.hasBoundedJump len = true := by
  cases instr <;> simp_all [isNonJumping, hasBoundedJump]

/-- hasBoundedJump is monotonic: if bounded for len1, then bounded for any len2 ≥ len1. -/
theorem Instr.hasBoundedJump_mono {instr : Instr} {len1 len2 : ℕ}
    (h : instr.hasBoundedJump len1 = true) (hle : len1 ≤ len2) :
    instr.hasBoundedJump len2 = true := by
  cases instr with
  | Z _ | S _ | T _ _ => simp [hasBoundedJump]
  | J _ _ q => simp only [hasBoundedJump, decide_eq_true_eq] at h ⊢; exact Nat.le_trans h hle

/-- shiftJumps preserves bounded jumps with adjusted bound. -/
theorem Instr.hasBoundedJump_shiftJumps {instr : Instr} {len offset : ℕ}
    (h : instr.hasBoundedJump len = true) :
    (instr.shiftJumps offset).hasBoundedJump (offset + len) = true := by
  cases instr with
  | Z _ | S _ | T _ _ => simp [shiftJumps, hasBoundedJump]
  | J _ _ q => simp only [shiftJumps, hasBoundedJump, decide_eq_true_eq] at h ⊢; omega

/-- Straight-line programs are in standard form. -/
theorem straightLine_isStandardForm {p : Program} (hsl : p.isStraightLine = true) :
    p.IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm; rw [List.all_eq_true]
  intro instr hinstr
  exact Instr.hasBoundedJump_of_isNonJumping (List.all_eq_true.mp hsl instr hinstr) p.length

/-! ## Semantic Consequence

The syntactic standard form property implies that whenever a program halts,
it halts exactly at the program length (not beyond). This is because:
1. Non-jump instructions increment pc by 1
2. Jump instructions set pc to at most p.length (by the bounded jump property)
3. Therefore pc can never exceed p.length
4. The only way to halt (pc ≥ p.length) is to have pc = p.length -/

/-- Extract the bounded jump property for a specific instruction from IsStandardForm. -/
theorem Program.IsStandardForm.getInstr_hasBoundedJump {p : Program} (hsf : p.IsStandardForm)
    {i : ℕ} {instr : Instr} (h : p.getInstr i = some instr) :
    instr.hasBoundedJump p.length = true := by
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
    show c.pc + 1 ≤ p.length; have := List.getElem?_eq_some_iff.mp hinstr |>.1; omega
  | jump_eq hinstr _ =>
    have hbounded := hsf.getInstr_hasBoundedJump hinstr
    simp only [Instr.hasBoundedJump, decide_eq_true_eq] at hbounded; exact hbounded

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
    (hhalted : c.isHalted p) : c.pc = p.length := by
  -- From invariant: c.pc ≤ p.length
  have hle : c.pc ≤ p.length := hsf.pc_le_length hsteps (Nat.zero_le _)
  -- From halted: c.pc ≥ p.length
  -- Combine: c.pc = p.length
  exact Nat.le_antisymm hle hhalted

/-- When a standard form program halts from any starting point with pc ≤ length, pc = length. -/
theorem Program.IsStandardForm.pc_eq_length_of_halted {p : Program} (hsf : p.IsStandardForm)
    {c c' : Config} (hsteps : Steps p c c') (hpc : c.pc ≤ p.length)
    (hhalted : c'.isHalted p) : c'.pc = p.length :=
  Nat.le_antisymm (hsf.pc_le_length hsteps hpc) hhalted

/-! ## Standard Form Normalization

Every program can be converted to an equivalent standard form program by capping
jump targets at the program length. A jump to position > length causes immediate
halt, as does a jump to exactly length, so they're behaviorally equivalent. -/

/-- Cap a jump target to be at most `len`. Non-jump instructions are unchanged. -/
def Instr.capJump (len : ℕ) : Instr → Instr
  | Instr.Z n => Instr.Z n
  | Instr.S n => Instr.S n
  | Instr.T m n => Instr.T m n
  | Instr.J m n q => Instr.J m n (min q len)

/-- Convert a program to standard form by capping all jump targets at the program length. -/
def Program.toStandardForm (p : Program) : Program :=
  p.map (Instr.capJump p.length)

/-! ### Basic Properties of capJump and toStandardForm -/

@[simp]
theorem Instr.capJump_Z (len n : ℕ) : (Instr.Z n).capJump len = Instr.Z n := rfl

@[simp]
theorem Instr.capJump_S (len n : ℕ) : (Instr.S n).capJump len = Instr.S n := rfl

@[simp]
theorem Instr.capJump_T (len m n : ℕ) : (Instr.T m n).capJump len = Instr.T m n := rfl

@[simp]
theorem Instr.capJump_J (len m n q : ℕ) :
    (Instr.J m n q).capJump len = Instr.J m n (min q len) := rfl

/-- toStandardForm preserves program length. -/
@[simp]
theorem Program.toStandardForm_length (p : Program) :
    p.toStandardForm.length = p.length := by
  simp [toStandardForm]

/-- capJump always produces an instruction with bounded jump. -/
theorem Instr.hasBoundedJump_capJump (len : ℕ) (instr : Instr) :
    (instr.capJump len).hasBoundedJump len = true := by
  cases instr <;> simp [capJump, hasBoundedJump]

/-- toStandardForm produces a standard form program. -/
theorem Program.toStandardForm_isStandardForm (p : Program) :
    p.toStandardForm.IsStandardForm := by
  unfold IsStandardForm isStandardForm toStandardForm
  rw [List.all_eq_true, List.length_map]
  intro instr hinstr
  obtain ⟨orig, _, rfl⟩ := List.mem_map.mp hinstr
  exact Instr.hasBoundedJump_capJump p.length orig

/-- capJump is identity when the instruction already has bounded jump. -/
theorem Instr.capJump_of_hasBoundedJump {instr : Instr} {len : ℕ}
    (h : instr.hasBoundedJump len = true) : instr.capJump len = instr := by
  cases instr with
  | Z _ | S _ | T _ _ => rfl
  | J m n q => simp only [hasBoundedJump, decide_eq_true_eq] at h; simp only [capJump, Nat.min_eq_left h]

/-! ### Instruction Access in toStandardForm -/

/-- Accessing an instruction in toStandardForm gives the capJump'd instruction. -/
theorem Program.getInstr_toStandardForm (p : Program) (i : ℕ) :
    p.toStandardForm.getInstr i = (p.getInstr i).map (Instr.capJump p.length) := by
  simp only [getInstr, toStandardForm, List.getElem?_map]

/-! ### Behavioral Equivalence

Two programs are behaviorally equivalent if they halt on the same inputs
and produce the same results. We prove that p and p.toStandardForm are
behaviorally equivalent. -/

/-! #### Step Correspondence

For each instruction type, we show correspondence between steps in p and p.toStandardForm. -/

/-- If original program has instruction at pc, the transformed program has the capped version. -/
theorem Program.toStandardForm_getInstr_some {p : Program} {i : ℕ} {instr : Instr}
    (h : p.getInstr i = some instr) :
    p.toStandardForm.getInstr i = some (instr.capJump p.length) := by
  simp [getInstr_toStandardForm, h]

/-- Z instruction: identical step in both programs. -/
theorem Step.toStandardForm_zero {p : Program} {c : Config} {n : ℕ}
    (h : p.getInstr c.pc = some (Instr.Z n)) :
    Step p.toStandardForm c ⟨c.pc + 1, c.state.write n 0⟩ := by
  have hcap : p.toStandardForm.getInstr c.pc = some (Instr.Z n) := by
    simp [Program.getInstr_toStandardForm, h]
  exact Step.zero hcap

/-- S instruction: identical step in both programs. -/
theorem Step.toStandardForm_succ {p : Program} {c : Config} {n : ℕ}
    (h : p.getInstr c.pc = some (Instr.S n)) :
    Step p.toStandardForm c ⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩ := by
  have hcap : p.toStandardForm.getInstr c.pc = some (Instr.S n) := by
    simp [Program.getInstr_toStandardForm, h]
  exact Step.succ hcap

/-- T instruction: identical step in both programs. -/
theorem Step.toStandardForm_trans {p : Program} {c : Config} {m n : ℕ}
    (h : p.getInstr c.pc = some (Instr.T m n)) :
    Step p.toStandardForm c ⟨c.pc + 1, c.state.write n (c.state.read m)⟩ := by
  have hcap : p.toStandardForm.getInstr c.pc = some (Instr.T m n) := by
    simp [Program.getInstr_toStandardForm, h]
  exact Step.trans hcap

/-- J instruction with bounded target (q ≤ p.length): identical step in both programs
    when condition is true. -/
theorem Step.toStandardForm_jump_eq_bounded {p : Program} {c : Config} {m n q : ℕ}
    (h : p.getInstr c.pc = some (Instr.J m n q))
    (hbounded : q ≤ p.length)
    (heq : c.state.read m = c.state.read n) :
    Step p.toStandardForm c ⟨q, c.state⟩ := by
  have hcap : p.toStandardForm.getInstr c.pc = some (Instr.J m n (min q p.length)) := by
    simp [Program.getInstr_toStandardForm, h]
  have hmin : min q p.length = q := Nat.min_eq_left hbounded
  rw [hmin] at hcap
  exact Step.jump_eq hcap heq

/-- J instruction: identical step in both programs when condition is false. -/
theorem Step.toStandardForm_jump_ne {p : Program} {c : Config} {m n q : ℕ}
    (h : p.getInstr c.pc = some (Instr.J m n q))
    (hne : c.state.read m ≠ c.state.read n) :
    Step p.toStandardForm c ⟨c.pc + 1, c.state⟩ := by
  have hcap : p.toStandardForm.getInstr c.pc = some (Instr.J m n (min q p.length)) := by
    simp [Program.getInstr_toStandardForm, h]
  exact Step.jump_ne hcap hne

/-! #### Halting Equivalence

The key insight: when a jump target q > p.length, both the original and
the capped program cause immediate halt (original jumps to q ≥ p.length,
capped jumps to p.length). Both halt with the same state. -/

/-- Configuration relation for simulation: configs are related if they have the same
    pc and state, OR if both are in halted states with the same state. -/
def ConfigRelated (p : Program) (c₁ c₂ : Config) : Prop :=
  (c₁.pc = c₂.pc ∧ c₁.state = c₂.state) ∨
  (c₁.isHalted p ∧ c₂.isHalted p.toStandardForm ∧ c₁.state = c₂.state)

/-- Initial configs are related. -/
theorem ConfigRelated.init (p : Program) (inputs : List ℕ) :
    ConfigRelated p (Config.init inputs) (Config.init inputs) := Or.inl ⟨rfl, rfl⟩

/-- If both configs are halted with the same state, they are related. -/
theorem ConfigRelated.halted {p : Program} {c₁ c₂ : Config}
    (h1 : c₁.isHalted p) (h2 : c₂.isHalted p.toStandardForm) (heq : c₁.state = c₂.state) :
    ConfigRelated p c₁ c₂ := Or.inr ⟨h1, h2, heq⟩

/-- Forward simulation: if original can step, standard form can step to a related config. -/
theorem Step.simulate_toStandardForm {p : Program} {c₁ c₁' : Config}
    (hstep : Step p c₁ c₁') :
    ∃ c₂', Steps p.toStandardForm c₁ c₂' ∧ ConfigRelated p c₁' c₂' := by
  cases hstep with
  | zero hinstr => exact ⟨_, Steps.single (Step.toStandardForm_zero hinstr), Or.inl ⟨rfl, rfl⟩⟩
  | succ hinstr => exact ⟨_, Steps.single (Step.toStandardForm_succ hinstr), Or.inl ⟨rfl, rfl⟩⟩
  | trans hinstr => exact ⟨_, Steps.single (Step.toStandardForm_trans hinstr), Or.inl ⟨rfl, rfl⟩⟩
  | jump_ne hinstr hne_reg =>
    exact ⟨_, Steps.single (Step.toStandardForm_jump_ne hinstr hne_reg), Or.inl ⟨rfl, rfl⟩⟩
  | jump_eq hinstr heq_reg =>
    rename_i m n q
    by_cases hbounded : q ≤ p.length
    · exact ⟨⟨q, c₁.state⟩, Steps.single (Step.toStandardForm_jump_eq_bounded hinstr hbounded heq_reg),
             Or.inl ⟨rfl, rfl⟩⟩
    · have hgt : q > p.length := Nat.not_le.mp hbounded
      have hcap := Program.toStandardForm_getInstr_some hinstr
      simp only [Instr.capJump, Nat.min_eq_right (Nat.le_of_lt hgt)] at hcap
      exact ⟨⟨p.length, c₁.state⟩, Steps.single (Step.jump_eq hcap heq_reg),
             Or.inr ⟨by simp; omega, by simp [Program.toStandardForm_length], rfl⟩⟩

/-- Multi-step simulation: if original reaches halted config, standard form can too. -/
theorem Steps.simulate_toStandardForm_halts {p : Program} {c c' : Config}
    (hsteps : Steps p c c') (hhalted : c'.isHalted p) :
    ∃ c₂', Steps p.toStandardForm c c₂' ∧ c₂'.isHalted p.toStandardForm ∧ c'.state = c₂'.state := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨c', Steps.refl _, by simp [Program.toStandardForm_length] at hhalted ⊢; exact hhalted, rfl⟩
  | head hstep hrest ih =>
    obtain ⟨c₂_mid, hsteps₂_mid, hrel_mid⟩ := Step.simulate_toStandardForm hstep
    rcases hrel_mid with ⟨hpc_mid, hstate_mid⟩ | ⟨h_c_mid_halted, hhalted_mid, hstate_mid⟩
    · rename_i c_mid
      have hcfg_eq : c_mid = c₂_mid := by ext <;> [exact hpc_mid; simp only [hstate_mid]]
      subst hcfg_eq
      obtain ⟨c₂', hsteps₂', hhalted₂', hstate_eq⟩ := ih
      exact ⟨c₂', Steps.trans hsteps₂_mid hsteps₂', hhalted₂', hstate_eq⟩
    · have hc_mid_eq_c' : _ = c' := Steps.halts_unique (Steps.refl _) h_c_mid_halted hrest hhalted
      exact ⟨c₂_mid, hsteps₂_mid, hhalted_mid, by rw [← hc_mid_eq_c']; exact hstate_mid⟩

/-- Forward halting: if original halts, standard form halts with same state. -/
theorem Halts.toStandardForm {p : Program} {inputs : List ℕ}
    (h : Halts p inputs) : Halts p.toStandardForm inputs := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  obtain ⟨c₂, hsteps₂, hhalted₂, _⟩ := Steps.simulate_toStandardForm_halts hsteps hhalted
  exact ⟨c₂, hsteps₂, hhalted₂⟩

/-! #### Reverse Direction -/

/-- Reverse simulation: if standard form can step, original can step to a related config. -/
theorem Step.simulate_from_toStandardForm {p : Program} {c₁ c₁' : Config}
    (hstep : Step p.toStandardForm c₁ c₁') :
    ∃ c₂', Steps p c₁ c₂' ∧ ConfigRelated p c₂' c₁' := by
  cases hstep with
  | zero hinstr =>
    rw [Program.getInstr_toStandardForm] at hinstr; simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr_orig, hinstr_orig, hcap⟩ := hinstr
    cases instr_orig with
    | Z n' => simp at hcap; subst hcap; exact ⟨_, Steps.single (Step.zero hinstr_orig), Or.inl ⟨rfl, rfl⟩⟩
    | S _ | T _ _ | J _ _ _ => simp at hcap
  | succ hinstr =>
    rw [Program.getInstr_toStandardForm] at hinstr; simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr_orig, hinstr_orig, hcap⟩ := hinstr
    cases instr_orig with
    | S n' => simp at hcap; subst hcap; exact ⟨_, Steps.single (Step.succ hinstr_orig), Or.inl ⟨rfl, rfl⟩⟩
    | Z _ | T _ _ | J _ _ _ => simp at hcap
  | trans hinstr =>
    rw [Program.getInstr_toStandardForm] at hinstr; simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr_orig, hinstr_orig, hcap⟩ := hinstr
    cases instr_orig with
    | T m' n' => simp at hcap; obtain ⟨rfl, rfl⟩ := hcap
                 exact ⟨_, Steps.single (Step.trans hinstr_orig), Or.inl ⟨rfl, rfl⟩⟩
    | Z _ | S _ | J _ _ _ => simp at hcap
  | jump_eq hinstr heq_reg =>
    rw [Program.getInstr_toStandardForm] at hinstr; simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr_orig, hinstr_orig, hcap⟩ := hinstr
    cases instr_orig with
    | J m' n' q' =>
      simp only [Instr.capJump_J, Instr.J.injEq] at hcap; obtain ⟨rfl, rfl, htarget⟩ := hcap
      by_cases hbounded : q' ≤ p.length
      · rw [Nat.min_eq_left hbounded] at htarget; subst htarget
        exact ⟨_, Steps.single (Step.jump_eq hinstr_orig heq_reg), Or.inl ⟨rfl, rfl⟩⟩
      · have hgt : q' > p.length := Nat.not_le.mp hbounded
        rw [Nat.min_eq_right (Nat.le_of_lt hgt)] at htarget; subst htarget
        exact ⟨⟨q', c₁.state⟩, Steps.single (Step.jump_eq hinstr_orig heq_reg),
               Or.inr ⟨by simp; omega, by simp [Program.toStandardForm_length], rfl⟩⟩
    | Z _ | S _ | T _ _ => simp at hcap
  | jump_ne hinstr hne_reg =>
    rw [Program.getInstr_toStandardForm] at hinstr; simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr_orig, hinstr_orig, hcap⟩ := hinstr
    cases instr_orig with
    | J m' n' q' => simp at hcap; obtain ⟨rfl, rfl, _⟩ := hcap
                    exact ⟨_, Steps.single (Step.jump_ne hinstr_orig hne_reg), Or.inl ⟨rfl, rfl⟩⟩
    | Z _ | S _ | T _ _ => simp at hcap

/-- Multi-step reverse simulation: if standard form reaches halted config, original can too. -/
theorem Steps.simulate_from_toStandardForm_halts {p : Program} {c c' : Config}
    (hsteps : Steps p.toStandardForm c c') (hhalted : c'.isHalted p.toStandardForm) :
    ∃ c₂', Steps p c c₂' ∧ c₂'.isHalted p ∧ c'.state = c₂'.state := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨c', Steps.refl _, by simp [Program.toStandardForm_length] at hhalted ⊢; exact hhalted, rfl⟩
  | head hstep hrest ih =>
    obtain ⟨c₂_mid, hsteps₂_mid, hrel_mid⟩ := Step.simulate_from_toStandardForm hstep
    rcases hrel_mid with ⟨hpc_mid, hstate_mid⟩ | ⟨h_c_mid_halted, hhalted_mid, hstate_mid⟩
    · rename_i c_mid
      have hcfg_eq : c₂_mid = c_mid := by ext <;> [exact hpc_mid; simp only [hstate_mid]]
      subst hcfg_eq
      obtain ⟨c₂', hsteps₂', hhalted₂', hstate_eq⟩ := ih
      exact ⟨c₂', Steps.trans hsteps₂_mid hsteps₂', hhalted₂', hstate_eq⟩
    · rename_i c_mid
      have hc_mid_eq_c' : c_mid = c' := Steps.halts_unique (Steps.refl _) hhalted_mid hrest hhalted
      exact ⟨c₂_mid, hsteps₂_mid, h_c_mid_halted, by rw [← hc_mid_eq_c']; exact hstate_mid.symm⟩

/-- Reverse halting: if standard form halts, original halts with same state. -/
theorem Halts.of_toStandardForm {p : Program} {inputs : List ℕ}
    (h : Halts p.toStandardForm inputs) : Halts p inputs := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  obtain ⟨c₂, hsteps₂, hhalted₂, _⟩ := Steps.simulate_from_toStandardForm_halts hsteps hhalted
  exact ⟨c₂, hsteps₂, hhalted₂⟩

/-- Halting equivalence: original halts iff standard form halts. -/
theorem Halts.toStandardForm_iff {p : Program} {inputs : List ℕ} :
    Halts p inputs ↔ Halts p.toStandardForm inputs :=
  ⟨Halts.toStandardForm, Halts.of_toStandardForm⟩

/-! #### Result Preservation -/

/-- State preservation: both reach configs with the same state. -/
theorem Result.toStandardForm_state {p : Program} {inputs : List ℕ}
    (hp : Halts p inputs) (hq : Halts p.toStandardForm inputs) :
    (Classical.choose hp).state = (Classical.choose hq).state := by
  have ⟨hsteps, hhalted⟩ := Classical.choose_spec hp
  have ⟨hsteps', hhalted'⟩ := Classical.choose_spec hq
  obtain ⟨c₂, hsteps₂, hhalted₂, hstate_eq⟩ := Steps.simulate_toStandardForm_halts hsteps hhalted
  rw [Steps.halts_unique hsteps' hhalted' hsteps₂ hhalted₂, hstate_eq]

/-- Result equality: both programs produce the same output. -/
theorem Result.toStandardForm {p : Program} {inputs : List ℕ}
    (hp : Halts p inputs) (hq : Halts p.toStandardForm inputs) :
    Result p inputs hp = Result p.toStandardForm inputs hq := by
  simp only [Result, State.output, Result.toStandardForm_state hp hq]

/-! ## Program Equivalence

Two programs are equivalent if they compute the same partial function:
they halt on exactly the same inputs and produce the same results. -/

/-- Two programs are equivalent if they compute the same partial function. -/
def Program.Equiv (p q : Program) : Prop :=
  ∀ inputs, (Halts p inputs ↔ Halts q inputs) ∧
    ∀ hp hq, Result p inputs hp = Result q inputs hq

/-- Notation for program equivalence. -/
scoped infix:50 " ~ " => Program.Equiv

/-- Program equivalence is reflexive. -/
@[refl]
theorem Program.Equiv.refl (p : Program) : p ~ p :=
  fun _ => ⟨Iff.rfl, fun _ _ => rfl⟩

/-- Program equivalence is symmetric. -/
@[symm]
theorem Program.Equiv.symm {p q : Program} (h : p ~ q) : q ~ p :=
  fun inputs => ⟨(h inputs).1.symm, fun hq hp => ((h inputs).2 hp hq).symm⟩

/-- Program equivalence is transitive. -/
@[trans]
theorem Program.Equiv.trans {p q r : Program} (hpq : p ~ q) (hqr : q ~ r) : p ~ r :=
  fun inputs =>
    ⟨(hpq inputs).1.trans (hqr inputs).1,
     fun hp hr =>
       let hq := (hpq inputs).1.mp hp
       ((hpq inputs).2 hp hq).trans ((hqr inputs).2 hq hr)⟩

/-- A program is equivalent to its standard form. -/
theorem Program.equiv_toStandardForm (p : Program) : p ~ p.toStandardForm :=
  fun _ => ⟨Halts.toStandardForm_iff, fun hp hq => Result.toStandardForm hp hq⟩

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
  refine ⟨p.toStandardForm, Program.toStandardForm_isStandardForm p, fun inputs => ?_⟩
  constructor
  · rw [← Halts.toStandardForm_iff]
    exact (hspec inputs).1
  · intro hHalts hDom
    have hp : Halts p (List.ofFn inputs) := Halts.toStandardForm_iff.mpr hHalts
    rw [← Result.toStandardForm hp hHalts]
    exact (hspec inputs).2 hp hDom

end Urm
