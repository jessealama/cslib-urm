/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable
import Urm.Shift
import Urm.Concat
import Urm.StandardForm
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-! # Composition Infrastructure -/

namespace Urm

namespace Program

def clearRegisters (maxReg : ℕ) : Program := (List.range (maxReg + 1)).map Instr.Z

def copyRegisterRange (srcStart dstStart count : ℕ) : Program :=
  (List.range count).map fun i => Instr.T (srcStart + i) (dstStart + i)

def transferResultsToInputs (resultStart arityF : ℕ) : Program :=
  (List.range arityF).map fun i => Instr.T (resultStart + i) i

end Program

@[simp]
theorem clearRegisters_length (maxReg : ℕ) :
    (Program.clearRegisters maxReg).length = maxReg + 1 := by simp [Program.clearRegisters]

@[simp]
theorem copyRegisterRange_length (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).length = count := by simp [Program.copyRegisterRange]

theorem copyRegisterRange_isStraightLine (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).isStraightLine = true := by
  simp only [Program.copyRegisterRange, Program.isStraightLine, List.all_map, List.all_eq_true]
  intro i _; simp [Instr.isNonJumping]

theorem copyRegisterRange_isStandardForm (srcStart dstStart count : ℕ) :
    (Program.copyRegisterRange srcStart dstStart count).IsStandardForm :=
  straightLine_isStandardForm (copyRegisterRange_isStraightLine srcStart dstStart count)

@[simp]
theorem transferResultsToInputs_length (resultStart arityF : ℕ) :
    (Program.transferResultsToInputs resultStart arityF).length = arityF := by
  simp [Program.transferResultsToInputs]

theorem transferResultsToInputs_isStraightLine (resultStart arityF : ℕ) :
    (Program.transferResultsToInputs resultStart arityF).isStraightLine = true := by
  simp only [Program.transferResultsToInputs, Program.isStraightLine, List.all_map, List.all_eq_true]
  intro i _; simp [Instr.isNonJumping]

theorem transferResultsToInputs_isStandardForm (resultStart arityF : ℕ) :
    (Program.transferResultsToInputs resultStart arityF).IsStandardForm :=
  straightLine_isStandardForm (transferResultsToInputs_isStraightLine resultStart arityF)

section RegisterIsolation

variable {p : Program}

theorem Program.instr_maxRegister_le {i : ℕ} {instr : Instr}
    (h : p.getInstr i = some instr) : instr.maxRegister ≤ p.maxRegister := by
  simp only [Program.getInstr] at h
  have hi : i < p.length := by by_contra hc; simp only [not_lt] at hc; simp [List.getElem?_eq_none hc] at h
  have foldl_ge_init : ∀ (init : ℕ) (l : List Instr), init ≤ l.foldl (fun acc i => max acc i.maxRegister) init := by
    intro init l; induction l generalizing init with
    | nil => exact Nat.le_refl _
    | cons h t iht => exact Nat.le_trans (Nat.le_max_left _ _) (iht _)
  have foldl_mono : ∀ (a b : ℕ) (l : List Instr), a ≤ b →
      l.foldl (fun acc i => max acc i.maxRegister) a ≤ l.foldl (fun acc i => max acc i.maxRegister) b := by
    intro a b l hab; induction l generalizing a b with
    | nil => exact hab
    | cons h t iht => simp only [List.foldl_cons]; apply iht; exact max_le_max hab (Nat.le_refl _)
  induction p generalizing i instr with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [Program.maxRegister, List.foldl_cons]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      exact Nat.le_trans (Nat.le_max_right 0 _) (foldl_ge_init _ _)
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hj : j < tl.length := by simp at hi; omega
      have ih' := ih h hj; simp only [Program.maxRegister] at ih'
      exact Nat.le_trans ih' (foldl_mono 0 _ tl (Nat.zero_le _))

theorem Step.preserves_high_register {c c' : Config} (hstep : Step p c c') (r : ℕ)
    (hr : p.maxRegister < r) : c'.state.read r = c.state.read r := by
  cases hstep with
  | zero h | succ h | trans h =>
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    simp only [State.read, State.write]; exact Function.update_of_ne (by omega) _ _
  | jump_eq _ _ | jump_ne _ _ => rfl

theorem Steps.preserves_high_register {c c' : Config} (hsteps : Steps p c c') (r : ℕ)
    (hr : p.maxRegister < r) : c'.state.read r = c.state.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih => rw [ih]; exact Step.preserves_high_register hstep r hr

end RegisterIsolation

theorem Halts.of_agreeing_state {p : Program} {inputs : List ℕ} {s : State} {c : Config}
    (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.isHalted p)
    (hagree : ∀ r, r ≤ p.maxRegister → s.read r = (State.fromInputs inputs).read r) :
    Halts p inputs := by
  have hagree' : s.agreeOn (State.fromInputs inputs) 0 p.maxRegister := fun r _ hhi => hagree r hhi
  have hpc_eq : (⟨0, s⟩ : Config).pc = (Config.init inputs).pc := rfl
  obtain ⟨c', hsteps', hpc', _⟩ := Steps.agreeOn hsteps hpc_eq hagree'
  exact ⟨c', hsteps', by simp only [Config.isHalted] at hhalted ⊢; omega⟩

def Part.sequence {α : Type*} : {n : ℕ} → (Fin n → Part α) → Part (Fin n → α)
  | 0, _ => Part.some Fin.elim0
  | _ + 1, f => (f 0).bind fun a0 => (Part.sequence (fun i => f i.succ)).map fun rest => Fin.cons a0 rest

theorem Part.sequence_succ {α : Type*} {n : ℕ} (f : Fin (n + 1) → Part α) :
    Part.sequence f = (f 0).bind fun a0 => (Part.sequence (fun i => f i.succ)).map fun rest => Fin.cons a0 rest := rfl

theorem Part.sequence_dom {α : Type*} {n : ℕ} {f : Fin n → Part α} :
    (Part.sequence f).Dom ↔ ∀ i, (f i).Dom := by
  induction n with
  | zero => simp only [Part.sequence, Part.some_dom]; exact ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | succ n ih =>
    simp only [Part.sequence, Part.bind_dom, Part.map_Dom]; constructor
    · intro ⟨hdom0, hrest⟩ i; match i with
      | ⟨0, _⟩ => exact hdom0
      | ⟨j + 1, hlt⟩ => exact ih.mp hrest ⟨j, Nat.lt_of_succ_lt_succ hlt⟩
    · intro hall; exact ⟨hall 0, ih.mpr (fun i => hall i.succ)⟩

theorem Part.sequence_get {α : Type*} {n : ℕ} {f : Fin n → Part α}
    (hdom : (Part.sequence f).Dom) (i : Fin n) :
    (Part.sequence f).get hdom i = (f i).get (Part.sequence_dom.mp hdom i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => match i with
    | ⟨0, _⟩ => simp only [Part.sequence_succ, Part.bind, Part.map] at hdom ⊢; rfl
    | ⟨j + 1, hlt⟩ => simp only [Part.sequence_succ, Part.bind, Part.map] at hdom ⊢; exact ih _ ⟨j, Nat.lt_of_succ_lt_succ hlt⟩

theorem Program.isStraightLine_concat {p1 p2 : Program}
    (h1 : p1.isStraightLine = true) (h2 : p2.isStraightLine = true) :
    (p1.concat p2).isStraightLine = true := by
  simp only [Program.concat, Program.isStraightLine, List.all_append, Program.shiftJumps, List.all_map] at h1 h2 ⊢
  rw [Bool.and_eq_true]
  exact ⟨h1, by convert h2 using 2; funext instr; cases instr <;> simp [Instr.shiftJumps, Instr.isNonJumping]⟩

theorem Program.IsStandardForm.concat {p1 p2 : Program}
    (h1 : p1.IsStandardForm) (h2 : p2.IsStandardForm) : (p1.concat p2).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm at *; rw [List.all_eq_true] at h1 h2 ⊢
  intro instr hinstr; simp only [Program.concat, Program.shiftJumps] at hinstr; rw [List.mem_append] at hinstr
  cases hinstr with
  | inl hp1 => simp only [Program.concat_length]; exact Instr.hasBoundedJump_mono (h1 instr hp1) (Nat.le_add_right _ _)
  | inr hp2 =>
    rw [List.mem_map] at hp2; obtain ⟨instr', hinstr', rfl⟩ := hp2
    simp only [Program.concat_length]; exact Instr.hasBoundedJump_shiftJumps (len := p2.length) (offset := p1.length) (h2 instr' hinstr')

theorem prefix_of_concat_from_zero {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.isHalted (p1.concat p2)) (h1 : p1.IsStandardForm) :
    ∃ c', Steps p1 ⟨0, s⟩ c' ∧ c'.isHalted p1 := by
  by_cases hp1 : p1.length = 0
  · exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, by simp [hp1]⟩
  suffices h : ∀ c0 c', Steps (p1.concat p2) c0 c' → c'.isHalted (p1.concat p2) → c0.pc ≤ p1.length →
      (∃ c'', Steps p1 c0 c'' ∧ c''.isHalted p1) by exact h ⟨0, s⟩ c hsteps hhalted (by simp)
  intro c0 c' hsteps'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl => intro hhalted' _; simp only [Config.isHalted, Program.concat_length] at hhalted'
            exact ⟨c', Relation.ReflTransGen.refl, by simp; omega⟩
  | @head a d hstep hrest ih =>
    intro hhalted' hpc_le
    by_cases hhalted_p1 : a.isHalted p1
    · exact ⟨a, Relation.ReflTransGen.refl, hhalted_p1⟩
    have hpc_lt : a.pc < p1.length := by simp only [Config.isHalted, not_le] at hhalted_p1; exact hhalted_p1
    have hstep_p1 := Step.of_concat_left hpc_lt hstep
    obtain ⟨c'', hsteps_dc'', hhalted_c''⟩ := ih hhalted' (Step.pc_le_length_of_step h1 hstep_p1)
    exact ⟨c'', Relation.ReflTransGen.head hstep_p1 hsteps_dc'', hhalted_c''⟩

theorem Halts.prefix_of_concat_sf {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs) (h1 : p1.IsStandardForm) : Halts p1 inputs := by
  obtain ⟨cH, hsteps, hhalted⟩ := hH; exact prefix_of_concat_from_zero hsteps hhalted h1

theorem clearRegisters_isStraightLine (maxReg : ℕ) :
    (Program.clearRegisters maxReg).isStraightLine = true := by
  simp only [Program.clearRegisters, Program.isStraightLine, List.all_map]
  induction maxReg + 1 with
  | zero => simp only [List.range_zero, List.all_nil]
  | succ k ih => simp only [List.range_succ, List.all_append, ih, List.all_cons, List.all_nil,
      Function.comp_apply, Instr.isNonJumping, Bool.and_self]

theorem clearRegisters_isStandardForm (maxReg : ℕ) :
    (Program.clearRegisters maxReg).IsStandardForm :=
  straightLine_isStandardForm (clearRegisters_isStraightLine maxReg)

theorem copyRegisterRange_writesTo (srcStart dstStart count : ℕ)
    (instr : Instr) (hinstr : instr ∈ Program.copyRegisterRange srcStart dstStart count) :
    ∃ i < count, instr.writesTo = some (dstStart + i) := by
  simp only [Program.copyRegisterRange, List.mem_map, List.mem_range] at hinstr
  obtain ⟨i, hi, hinstr_eq⟩ := hinstr; exact ⟨i, hi, by simp [← hinstr_eq, Instr.writesTo]⟩

theorem copyRegisterRange_preserves_outside (srcStart dstStart count : ℕ)
    (r : ℕ) (hr : r < dstStart ∨ r ≥ dstStart + count) :
    ∀ instr, instr ∈ Program.copyRegisterRange srcStart dstStart count → instr.writesTo ≠ some r := by
  intro instr hinstr; obtain ⟨i, hi, hwrites⟩ := copyRegisterRange_writesTo srcStart dstStart count instr hinstr
  rw [hwrites]; simp only [ne_eq, Option.some.injEq]; omega

theorem transferResultsToInputs_writesTo (resultStart arityF : ℕ)
    (instr : Instr) (hinstr : instr ∈ Program.transferResultsToInputs resultStart arityF) :
    ∃ i < arityF, instr.writesTo = some i := by
  simp only [Program.transferResultsToInputs, List.mem_map, List.mem_range] at hinstr
  obtain ⟨i, hi, hinstr_eq⟩ := hinstr; exact ⟨i, hi, by simp [← hinstr_eq, Instr.writesTo]⟩

theorem transferResultsToInputs_preserves_outside (resultStart arityF : ℕ) (r : ℕ) (hr : r ≥ arityF) :
    ∀ instr, instr ∈ Program.transferResultsToInputs resultStart arityF → instr.writesTo ≠ some r := by
  intro instr hinstr; obtain ⟨i, hi, hwrites⟩ := transferResultsToInputs_writesTo resultStart arityF instr hinstr
  rw [hwrites]; simp only [ne_eq, Option.some.injEq]; omega

theorem straightLine_transfer_after_exec {p : Program} (_hsl : p.isStraightLine = true)
    (s : State) (k src dst : ℕ) (hk : k < p.length) (hwrite : p[k] = Instr.T src dst)
    (c_k : Config) (hsteps_k : Steps p ⟨0, s⟩ c_k) (hpc_k : c_k.pc = k) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k + 1 ∧ c.state.read dst = c_k.state.read src := by
  have hinstr : p.getInstr k = some (Instr.T src dst) := by simp only [Program.getInstr, List.getElem?_eq_getElem hk, hwrite]
  have hinstr' : p.getInstr c_k.pc = some (Instr.T src dst) := hpc_k ▸ hinstr
  let c_next : Config := ⟨c_k.pc + 1, c_k.state.write dst (c_k.state.read src)⟩
  refine ⟨c_next, Relation.ReflTransGen.tail hsteps_k (Step.trans hinstr'), by simp [c_next, hpc_k], by simp [c_next]⟩

theorem straightLine_transfer_result {p : Program} (hsl : p.isStraightLine = true)
    (s : State) (k src dst : ℕ) (hk : k < p.length) (hwrite : p[k] = Instr.T src dst)
    (hnowrite : ∀ j (hj : j < p.length), k < j → (p[j]'hj).writesTo ≠ some dst) :
    ∃ s_before : State,
      (∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = k ∧ c.state = s_before) ∧
      (straightLineFinalState hsl s).read dst = s_before.read src := by
  obtain ⟨c_k, hsteps_k, hpc_k⟩ := straightLine_state_at_pc hsl s k (Nat.le_of_lt hk)
  refine ⟨c_k.state, ⟨c_k, hsteps_k, hpc_k, rfl⟩, ?_⟩
  have ⟨hsteps_final, hhalted, _⟩ := straightLineFinalState_spec hsl s
  obtain ⟨c_after_k, hsteps_to_after_k, _, hval⟩ :=
    straightLine_transfer_after_exec hsl s k src dst hk hwrite c_k hsteps_k hpc_k
  let final := Classical.choose (straightLine_halts_from_state hsl s)
  have hsteps_suffix := Steps.deterministic_continuation hsteps_to_after_k hsteps_final hhalted
  show (Classical.choose (straightLine_halts_from_state hsl s)).state.read dst = c_k.state.read src
  suffices h : ∀ a b, a.pc > k → Steps p a b → b.isHalted p → b.state.read dst = a.state.read dst by
    rw [h c_after_k final (by omega) hsteps_suffix hhalted, hval]
  intro a b hpc_gt hsteps hhalted_b
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head a' c' hstep hrest ih =>
    have ha'_pc_lt := Step.pc_lt_length hstep
    have hc'_pc_gt : c'.pc > k := by
      cases hstep with
      | zero h | succ h | trans h | jump_ne h _ => simp only []; omega
      | jump_eq h heq' =>
        simp only [Program.isStraightLine, List.all_eq_true] at hsl
        exact absurd (hsl _ ((List.getElem?_eq_some_iff.mp h).2 ▸ List.getElem_mem ha'_pc_lt)) (by simp [Instr.isNonJumping])
    rw [ih hc'_pc_gt]; apply Step.straightLine_preserves hsl hstep; intro instr hinstr
    rw [← (List.getElem?_eq_some_iff.mp hinstr).2]; exact hnowrite a'.pc ha'_pc_lt hpc_gt

section Continuation

variable {p1 p2 : Program}

theorem Step.of_concat_right {c c' : Config} (hpc_lo : p1.length ≤ c.pc) (hpc_hi : c.pc < p1.length + p2.length)
    (hstep : Step (p1.concat p2) c c') : Step p2 ⟨c.pc - p1.length, c.state⟩ ⟨c'.pc - p1.length, c'.state⟩ := by
  have hp2_pc : c.pc - p1.length < p2.length := by omega
  obtain ⟨instr, hinstr⟩ : ∃ instr, p2.getInstr (c.pc - p1.length) = some instr :=
    ⟨p2[c.pc - p1.length], by simp only [Program.getInstr]; exact List.getElem?_eq_getElem hp2_pc⟩
  have hconcat_instr : (p1.concat p2).getInstr c.pc = some (instr.shiftJumps p1.length) := by
    rw [Program.getInstr_concat_right c.pc hpc_lo hpc_hi, Program.getInstr_shiftJumps, hinstr]; rfl
  set pc2 := c.pc - p1.length with hpc2_def
  cases instr with
  | Z n => have hc' : c' = ⟨c.pc + 1, c.state.write n 0⟩ := by cases hstep <;> simp_all [Instr.shiftJumps]
           subst hc'; rw [show c.pc + 1 - p1.length = pc2 + 1 by omega]; exact Step.zero hinstr
  | S n => have hc' : c' = ⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩ := by cases hstep <;> simp_all [Instr.shiftJumps]
           subst hc'; rw [show c.pc + 1 - p1.length = pc2 + 1 by omega]; exact Step.succ hinstr
  | T m n => have hc' : c' = ⟨c.pc + 1, c.state.write n (c.state.read m)⟩ := by cases hstep <;> simp_all [Instr.shiftJumps]
             subst hc'; rw [show c.pc + 1 - p1.length = pc2 + 1 by omega]; exact Step.trans hinstr
  | J m n q =>
    cases hstep with
    | jump_eq h heq =>
      simp only [Instr.shiftJumps] at hconcat_instr; simp only [hconcat_instr, Option.some.injEq, Instr.J.injEq] at h
      obtain ⟨rfl, rfl, hq⟩ := h; simp only [← hq, Nat.add_sub_cancel]; exact Step.jump_eq hinstr heq
    | jump_ne h hne =>
      simp only [Instr.shiftJumps] at hconcat_instr; simp only [hconcat_instr, Option.some.injEq, Instr.J.injEq] at h
      obtain ⟨rfl, rfl, _⟩ := h; rw [show c.pc + 1 - p1.length = pc2 + 1 by omega]; exact Step.jump_ne hinstr hne
    | _ => simp_all [Instr.shiftJumps]

theorem Steps.of_concat_right {s : State} {c' : Config}
    (hsteps : Steps (p1.concat p2) ⟨p1.length, s⟩ c') (hhalted : c'.isHalted (p1.concat p2)) (_hpc' : c'.pc ≥ p1.length) :
    ∃ c, Steps p2 ⟨0, s⟩ c ∧ c.isHalted p2 ∧ c.state = c'.state := by
  suffices h : ∀ start c', start.pc ≥ p1.length → Steps (p1.concat p2) start c' → c'.isHalted (p1.concat p2) →
      ∃ c, Steps p2 ⟨start.pc - p1.length, start.state⟩ c ∧ c.isHalted p2 ∧ c.state = c'.state by
    have := h ⟨p1.length, s⟩ c' (Nat.le_refl _) hsteps hhalted; simp only [Nat.sub_self] at this; exact this
  intro start c'' hstart hsteps' hhalted'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨⟨c''.pc - p1.length, c''.state⟩, Relation.ReflTransGen.refl, ?_, rfl⟩
    simp only [Config.isHalted] at hhalted' ⊢
    simp only [Program.concat, List.length_append, Program.shiftJumps, List.length_map] at hhalted'; omega
  | @head a b hstep hrest ih =>
    have ha_in_range : a.pc < p1.length + p2.length := by
      by_contra hc; simp only [not_lt] at hc
      exact Step.halted_no_step (by simp only [Config.isHalted, Program.concat, List.length_append, Program.shiftJumps, List.length_map]; omega) hstep
    have hstep_p2 := Step.of_concat_right hstart ha_in_range hstep
    have hb_pc_ge : b.pc ≥ p1.length := by
      cases hstep with
      | zero _ | succ _ | trans _ | jump_ne _ _ => simp only []; omega
      | jump_eq h _ =>
        have hconcat := Program.getInstr_concat_right a.pc hstart ha_in_range
        rw [hconcat, Program.getInstr_shiftJumps] at h
        cases hp2 : p2.getInstr (a.pc - p1.length) with
        | none => simp only [hp2, Option.map_none] at h; nomatch h
        | some instr => simp only [hp2, Option.map_some] at h; cases instr with
          | J _ _ q' => simp only [Instr.shiftJumps, Option.some.injEq, Instr.J.injEq] at h; obtain ⟨_, _, hq_eq⟩ := h; simp only [← hq_eq]; omega
          | _ => simp only [Instr.shiftJumps, Option.some.injEq] at h; nomatch h
    obtain ⟨c, hrest_p2, hhalted_c, hstate_eq⟩ := ih hb_pc_ge
    exact ⟨c, Relation.ReflTransGen.head hstep_p2 hrest_p2, hhalted_c, hstate_eq⟩

theorem suffix_of_concat_from_zero {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.isHalted (p1.concat p2)) (h1 : p1.IsStandardForm) :
    ∃ s', Steps p1 ⟨0, s⟩ ⟨p1.length, s'⟩ ∧ (∃ c', Steps p2 ⟨0, s'⟩ c' ∧ c'.isHalted p2) := by
  obtain ⟨c1, hsteps_p1, hhalted_p1⟩ := prefix_of_concat_from_zero hsteps hhalted h1
  have hc1_pc : c1.pc = p1.length := by
    simp only [Config.isHalted] at hhalted_p1
    have hc1_le := h1.pc_le_length hsteps_p1 (by simp : (⟨0, s⟩ : Config).pc ≤ p1.length); omega
  refine ⟨c1.state, ?_, ?_⟩
  · convert hsteps_p1 using 1; ext <;> simp [hc1_pc]
  · have hsteps_p1_lifted : Steps (p1.concat p2) ⟨0, s⟩ ⟨p1.length, c1.state⟩ := by
      convert @Steps.concat_left_prefix p1 p2 ⟨0, s⟩ c1 hsteps_p1 hhalted_p1 using 1; ext <;> simp [hc1_pc]
    have h_suffix := Steps.deterministic_continuation hsteps_p1_lifted hsteps hhalted
    have hc_pc : c.pc ≥ p1.length := by simp only [Config.isHalted, Program.concat_length] at hhalted; omega
    obtain ⟨c', hsteps_p2, hhalted_p2, _⟩ := Steps.of_concat_right h_suffix hhalted hc_pc
    exact ⟨c', hsteps_p2, hhalted_p2⟩

/-- Extract just the intermediate state from a concatenated program execution.
    This is the state after p1 halts, before p2 begins. -/
noncomputable def suffix_of_concat_state {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.isHalted (p1.concat p2))
    (h1 : p1.IsStandardForm) : State :=
  (suffix_of_concat_from_zero hsteps hhalted h1).choose

/-- Steps in p1 reaching the intermediate state. -/
theorem suffix_of_concat_steps_left {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.isHalted (p1.concat p2))
    (h1 : p1.IsStandardForm) :
    Steps p1 ⟨0, s⟩ ⟨p1.length, suffix_of_concat_state hsteps hhalted h1⟩ :=
  (suffix_of_concat_from_zero hsteps hhalted h1).choose_spec.1

/-- p2 halts when starting from the intermediate state. -/
theorem suffix_of_concat_halts_right {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.isHalted (p1.concat p2))
    (h1 : p1.IsStandardForm) :
    ∃ c', Steps p2 ⟨0, suffix_of_concat_state hsteps hhalted h1⟩ c' ∧ c'.isHalted p2 :=
  (suffix_of_concat_from_zero hsteps hhalted h1).choose_spec.2

theorem Halts.suffix_of_concat_sf {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs) (h1 : p1.IsStandardForm) :
    ∃ s : State, Halts p1 inputs ∧ (∀ hP1 : Halts p1 inputs, s = (Classical.choose hP1).state) ∧
                 (∃ c, Steps p2 ⟨0, s⟩ c ∧ c.isHalted p2) := by
  have hP1 := Halts.prefix_of_concat_sf hH h1
  have hc1_spec := Classical.choose_spec hP1
  have hc1_pc := h1.halts_at_length inputs (Classical.choose hP1) hc1_spec.1 hc1_spec.2
  refine ⟨(Classical.choose hP1).state, hP1, ?_, ?_⟩
  · intro hP1'; rw [Steps.halts_unique hc1_spec.1 hc1_spec.2 (Classical.choose_spec hP1').1 (Classical.choose_spec hP1').2]
  · obtain ⟨cH, hH_steps, hH_halted⟩ := hH
    have h_to_c1 : Steps (p1.concat p2) (Config.init inputs) (Classical.choose hP1) :=
      Steps.concat_left_prefix hc1_spec.1 hc1_spec.2
    have h_suffix := Steps.deterministic_continuation h_to_c1 hH_steps hH_halted
    have h_suffix_start : Classical.choose hP1 = ⟨p1.length, (Classical.choose hP1).state⟩ := by ext; exact hc1_pc; rfl
    rw [h_suffix_start] at h_suffix
    have hcH_pc : cH.pc ≥ p1.length := by simp only [Config.isHalted, Program.concat_length] at hH_halted; omega
    obtain ⟨c, hsteps_p2, hhalted_p2, _⟩ := Steps.of_concat_right h_suffix hH_halted hcH_pc
    exact ⟨c, hsteps_p2, hhalted_p2⟩

end Continuation

end Urm
