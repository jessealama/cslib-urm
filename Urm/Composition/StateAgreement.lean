/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.CopyRegsExec

/-! # State Agreement Lemmas

This file defines and proves properties about state agreement up to a certain register bound.
When two states agree on registers up to p.maxRegister, program execution produces identical results.

## Main definitions

- `Urm.State.agreeUpTo`: Two states agree on registers 0..k
- `Urm.Step.agree_step`: Single step agreement preservation
- `Urm.Steps.agree_steps`: Multi-step agreement preservation
- `Urm.Halts.agree_halts`: If states agree and one halts, the other halts with same output
-/

namespace Urm

/-- Two states agree on registers 0..k. -/
def State.agreeUpTo (σ₁ σ₂ : State) (k : ℕ) : Prop :=
  ∀ n, n ≤ k → σ₁ n = σ₂ n

/-- A cleared state agrees with `fromInputs [σ 0]` on registers 0..k. -/
theorem State.clearFrom1_agreeUpTo_fromInputs (σ : State) (k : ℕ) :
    (σ.clearFrom1 k).agreeUpTo (State.fromInputs [σ 0]) k := fun r hr =>
  State.clearFrom1_eq_fromInputs_on_range σ k r hr

/-- Helper: foldl max is monotonic in the accumulator. -/
private theorem foldl_max_mono {l : List Instr} {a b : ℕ} (hab : a ≤ b) :
    l.foldl (fun acc instr => max acc instr.maxRegister) a ≤
    l.foldl (fun acc instr => max acc instr.maxRegister) b := by
  induction l generalizing a b with
  | nil => exact hab
  | cons head tail ih =>
    simp only [List.foldl_cons]
    apply ih
    omega

/-- Helper: foldl max is at least the accumulator. -/
private theorem foldl_max_ge_acc {l : List Instr} {a : ℕ} :
    a ≤ l.foldl (fun acc instr => max acc instr.maxRegister) a := by
  induction l generalizing a with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) ih

/-- An instruction's maxRegister is at most the program's maxRegister if the instruction is in the program. -/
theorem Instr.maxRegister_le_of_mem {p : Program} {instr : Instr} (hmem : instr ∈ p) :
    instr.maxRegister ≤ p.maxRegister := by
  induction p with
  | nil => simp at hmem
  | cons head tail ih =>
    simp only [Program.maxRegister, List.foldl_cons] at *
    cases hmem with
    | head =>
      calc instr.maxRegister
          ≤ max 0 instr.maxRegister := Nat.le_max_right _ _
        _ ≤ tail.foldl (fun acc i => max acc i.maxRegister) (max 0 instr.maxRegister) := foldl_max_ge_acc
    | tail _ htail =>
      have h := ih htail
      calc instr.maxRegister
          ≤ tail.foldl (fun acc i => max acc i.maxRegister) 0 := h
        _ ≤ tail.foldl (fun acc i => max acc i.maxRegister) (max 0 head.maxRegister) :=
            foldl_max_mono (Nat.zero_le _)

/-- Writes to registers ≤ p.maxRegister preserve agreement for registers ≤ p.maxRegister. -/
theorem State.agreeUpTo_write {σ₁ σ₂ : State} {k n v : ℕ}
    (hagree : σ₁.agreeUpTo σ₂ k) (_hn : n ≤ k) :
    (σ₁.write n v).agreeUpTo (σ₂.write n v) k := by
  intro m hm
  simp only [write, Function.update]
  split_ifs with heq
  · rfl
  · exact hagree m hm

/-- If states agree up to p.maxRegister, they produce identical step results. -/
theorem Step.agree_step {p : Program} {σ₁ σ₂ : State} {pc : ℕ}
    (hagree : σ₁.agreeUpTo σ₂ p.maxRegister)
    {c' : Config} (hstep : Step p ⟨pc, σ₁⟩ c') :
    ∃ c'', Step p ⟨pc, σ₂⟩ c'' ∧ c'.pc = c''.pc ∧ c'.state.agreeUpTo c''.state p.maxRegister := by
  match hstep with
  | Step.zero (n := n) h =>
    -- h : p.getInstr pc = some (Instr.Z n) means p[pc]? = some (Instr.Z n)
    have ⟨hpc, heq⟩ := List.getElem?_eq_some_iff.mp h
    have hinstr : (Instr.Z n) ∈ p := heq ▸ List.getElem_mem hpc
    have hmax := Instr.maxRegister_le_of_mem hinstr
    simp only [Instr.maxRegister] at hmax
    refine ⟨⟨pc + 1, σ₂.write n 0⟩, Step.zero h, rfl, ?_⟩
    exact State.agreeUpTo_write hagree hmax
  | Step.succ (n := n) h =>
    have ⟨hpc, heq⟩ := List.getElem?_eq_some_iff.mp h
    have hinstr : (Instr.S n) ∈ p := heq ▸ List.getElem_mem hpc
    have hmax := Instr.maxRegister_le_of_mem hinstr
    simp only [Instr.maxRegister] at hmax
    have hread : σ₁.read n = σ₂.read n := hagree n hmax
    refine ⟨⟨pc + 1, σ₂.write n (σ₂.read n + 1)⟩, Step.succ h, rfl, ?_⟩
    -- Goal: (σ₁.write n (σ₁.read n + 1)).agreeUpTo (σ₂.write n (σ₂.read n + 1)) p.maxRegister
    intro r hr
    simp only [State.write, Function.update, State.read]
    split_ifs with heqr
    · -- r = n: both sides write the same value
      simp only [State.read] at hread
      simp [hread]
    · -- r ≠ n: use original agreement
      exact hagree r hr
  | Step.trans (m := m) (n := n) h =>
    have ⟨hpc, heq⟩ := List.getElem?_eq_some_iff.mp h
    have hinstr : (Instr.T m n) ∈ p := heq ▸ List.getElem_mem hpc
    have hmax := Instr.maxRegister_le_of_mem hinstr
    simp only [Instr.maxRegister] at hmax
    have hreadM : σ₁.read m = σ₂.read m := hagree m (Nat.le_trans (Nat.le_max_left _ _) hmax)
    refine ⟨⟨pc + 1, σ₂.write n (σ₂.read m)⟩, Step.trans h, rfl, ?_⟩
    -- Goal: (σ₁.write n (σ₁.read m)).agreeUpTo (σ₂.write n (σ₂.read m)) p.maxRegister
    intro r hr
    simp only [State.write, Function.update, State.read]
    split_ifs with heqr
    · -- r = n: both sides write σ₁.read m = σ₂.read m
      simp only [State.read] at hreadM
      simp [hreadM]
    · -- r ≠ n: use original agreement
      exact hagree r hr
  | Step.jump_eq (m := m) (n := n) (q := q) h heq =>
    have ⟨hpc, hinstreq⟩ := List.getElem?_eq_some_iff.mp h
    have hinstr : (Instr.J m n q) ∈ p := hinstreq ▸ List.getElem_mem hpc
    have hmax := Instr.maxRegister_le_of_mem hinstr
    simp only [Instr.maxRegister] at hmax
    have hreadM : σ₁.read m = σ₂.read m := hagree m (Nat.le_trans (Nat.le_max_left _ _) hmax)
    have hreadN : σ₁.read n = σ₂.read n := hagree n (Nat.le_trans (Nat.le_max_right _ _) hmax)
    -- heq : σ₁.read m = σ₁.read n, need to show σ₂.read m = σ₂.read n
    have heq' : σ₂.read m = σ₂.read n := by
      simp only [State.read] at hreadM hreadN heq ⊢
      omega
    refine ⟨⟨q, σ₂⟩, Step.jump_eq h heq', rfl, hagree⟩
  | Step.jump_ne (m := m) (n := n) (q := q) h hne =>
    have ⟨hpc, hinstreq⟩ := List.getElem?_eq_some_iff.mp h
    have hinstr : (Instr.J m n q) ∈ p := hinstreq ▸ List.getElem_mem hpc
    have hmax := Instr.maxRegister_le_of_mem hinstr
    simp only [Instr.maxRegister] at hmax
    have hreadM : σ₁.read m = σ₂.read m := hagree m (Nat.le_trans (Nat.le_max_left _ _) hmax)
    have hreadN : σ₁.read n = σ₂.read n := hagree n (Nat.le_trans (Nat.le_max_right _ _) hmax)
    -- hne : σ₁.read m ≠ σ₁.read n, need to show σ₂.read m ≠ σ₂.read n
    have hne' : σ₂.read m ≠ σ₂.read n := by
      simp only [State.read] at hreadM hreadN hne ⊢
      omega
    refine ⟨⟨pc + 1, σ₂⟩, Step.jump_ne h hne', rfl, hagree⟩

/-- Multi-step agreement: if initial states agree and we can step from σ₁, we can also step from σ₂
    with agreeing states throughout. -/
theorem Steps.agree_steps {p : Program} {c₁ c₁' : Config}
    (hsteps : Steps p c₁ c₁')
    {σ₂ : State} (hagree : c₁.state.agreeUpTo σ₂ p.maxRegister) :
    ∃ c₂', Steps p ⟨c₁.pc, σ₂⟩ c₂' ∧ c₁'.pc = c₂'.pc ∧
           c₁'.state.agreeUpTo c₂'.state p.maxRegister := by
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing σ₂ with
  | refl =>
    -- In refl case, c₁ = c₁' (the induction uses same variable name)
    exact ⟨⟨c₁'.pc, σ₂⟩, Relation.ReflTransGen.refl, rfl, hagree⟩
  | head hstep hrest ih =>
    -- hstep : Step p c_start c_mid
    -- hrest : Steps p c_mid c₁'
    rename_i c_mid
    obtain ⟨c_mid', hstep', hpc_eq, hagree'⟩ := Step.agree_step hagree hstep
    obtain ⟨c₂', hsteps', hpc_eq', hagree''⟩ := ih hagree'
    refine ⟨c₂', Relation.ReflTransGen.head hstep' ?_, hpc_eq', hagree''⟩
    -- Need: Steps p c_mid' c₂'
    -- We have: hsteps' : Steps p ⟨c_mid.pc, c_mid'.state⟩ c₂'
    -- And: hpc_eq : c_mid.pc = c_mid'.pc
    have : c_mid' = ⟨c_mid'.pc, c_mid'.state⟩ := rfl
    rw [this, ← hpc_eq]
    exact hsteps'

/-- If states agree up to p.maxRegister and p halts from σ₁, then p halts from σ₂ with same output. -/
theorem Halts.agree_halts {p : Program} {inputs₁ inputs₂ : List ℕ}
    (hagree : (State.fromInputs inputs₁).agreeUpTo (State.fromInputs inputs₂) p.maxRegister)
    (h : Halts p inputs₁) :
    Halts p inputs₂ ∧ ∀ h₁ h₂, Result p inputs₁ h₁ = Result p inputs₂ h₂ := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  -- Use Steps.agree_steps to get parallel execution from inputs₂
  -- Config.init inputs₁ = ⟨0, State.fromInputs inputs₁⟩
  have hinit_eq : Config.init inputs₁ = ⟨0, State.fromInputs inputs₁⟩ := rfl
  have hinit_eq' : Config.init inputs₂ = ⟨0, State.fromInputs inputs₂⟩ := rfl
  obtain ⟨c', hsteps', hpc_eq, hagree'⟩ := Steps.agree_steps hsteps hagree
  -- c' is halted because it has the same PC as c
  have hhalted' : c'.isHalted p := by
    simp only [Config.isHalted] at hhalted ⊢
    omega
  -- hsteps' : Steps p ⟨(Config.init inputs₁).pc, State.fromInputs inputs₂⟩ c'
  -- = Steps p ⟨0, State.fromInputs inputs₂⟩ c'
  -- = Steps p (Config.init inputs₂) c'
  have hsteps'' : Steps p (Config.init inputs₂) c' := by
    simp only [Config.init] at hsteps' ⊢
    exact hsteps'
  constructor
  · exact ⟨c', hsteps'', hhalted'⟩
  · intro h₁ h₂
    -- Both results are output from R[0]
    simp only [Result, State.output]
    -- By uniqueness, the chosen configs equal c and c'
    have hc_eq := Steps.halts_unique
      (Classical.choose_spec h₁).1 (Classical.choose_spec h₁).2 hsteps hhalted
    have hc'_eq := Steps.halts_unique
      (Classical.choose_spec h₂).1 (Classical.choose_spec h₂).2 hsteps'' hhalted'
    rw [hc_eq, hc'_eq]
    -- Now need c.state 0 = c'.state 0
    exact hagree' 0 (Nat.zero_le _)

end Urm
