/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable
import Urm.Shift
import Urm.Concat
import Urm.StandardForm
import Urm.PartSequence
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic



/-! # Composition Infrastructure -/

namespace Urm

namespace Program

/-- Transfer computed results to input registers 0, 1, ..., arityF - 1.
    Copies from resultStart + i to register i for i < arityF. -/
def transfer_results_to_inputs (resultStart arityF : ℕ) : Program :=
  (List.range arityF).map fun i => Instr.T (resultStart + i) i

end Program

theorem copy_register_range_isStandardForm (srcStart dstStart count : ℕ) :
    (Program.copy_register_range srcStart dstStart count).IsStandardForm :=
  straight_line_isStandardForm (copy_register_range_is_straight_line srcStart dstStart count)

@[simp]
theorem transfer_results_to_inputs_length (resultStart arityF : ℕ) :
    (Program.transfer_results_to_inputs resultStart arityF).length = arityF := by
  simp [Program.transfer_results_to_inputs]

theorem transfer_results_to_inputs_is_straight_line (resultStart arityF : ℕ) :
    (Program.transfer_results_to_inputs resultStart arityF).is_straight_line = true := by
  simp only [Program.transfer_results_to_inputs, Program.is_straight_line, List.all_map, List.all_eq_true]
  intro i _; simp [Instr.is_non_jumping]

theorem transfer_results_to_inputs_isStandardForm (resultStart arityF : ℕ) :
    (Program.transfer_results_to_inputs resultStart arityF).IsStandardForm :=
  straight_line_isStandardForm (transfer_results_to_inputs_is_straight_line resultStart arityF)

theorem Program.IsStandardForm.concat {p1 p2 : Program}
    (h1 : p1.IsStandardForm) (h2 : p2.IsStandardForm) : (p1.concat p2).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm at *; rw [List.all_eq_true] at h1 h2 ⊢
  intro instr hinstr; simp only [Program.concat, Program.shift_jumps] at hinstr; rw [List.mem_append] at hinstr
  cases hinstr with
  | inl hp1 => simp only [Program.concat_length]; exact Instr.has_bounded_jump_mono (h1 instr hp1) (Nat.le_add_right _ _)
  | inr hp2 =>
    rw [List.mem_map] at hp2; obtain ⟨instr', hinstr', rfl⟩ := hp2
    simp only [Program.concat_length]; exact Instr.has_bounded_jump_shift_jumps (len := p2.length) (offset := p1.length) (h2 instr' hinstr')

theorem prefix_of_concat_from_zero {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.is_halted (p1.concat p2)) (h1 : p1.IsStandardForm) :
    ∃ c', Steps p1 ⟨0, s⟩ c' ∧ c'.is_halted p1 := by
  by_cases hp1 : p1.length = 0
  · exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, by simp [hp1]⟩
  suffices h : ∀ c0 c', Steps (p1.concat p2) c0 c' → c'.is_halted (p1.concat p2) → c0.pc ≤ p1.length →
      (∃ c'', Steps p1 c0 c'' ∧ c''.is_halted p1) by exact h ⟨0, s⟩ c hsteps hhalted (by simp)
  intro c0 c' hsteps'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl => intro hhalted' _; simp only [Config.is_halted, Program.concat_length] at hhalted'
            exact ⟨c', Relation.ReflTransGen.refl, by simp; omega⟩
  | @head a d hstep hrest ih =>
    intro hhalted' hpc_le
    by_cases hhalted_p1 : a.is_halted p1
    · exact ⟨a, Relation.ReflTransGen.refl, hhalted_p1⟩
    have hpc_lt : a.pc < p1.length := by simp only [Config.is_halted, not_le] at hhalted_p1; exact hhalted_p1
    have hstep_p1 := Step.of_concat_left hpc_lt hstep
    obtain ⟨c'', hsteps_dc'', hhalted_c''⟩ := ih hhalted' (Step.pc_le_length_of_step h1 hstep_p1)
    exact ⟨c'', Relation.ReflTransGen.head hstep_p1 hsteps_dc'', hhalted_c''⟩

theorem Halts.prefix_of_concat_sf {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs) (h1 : p1.IsStandardForm) : Halts p1 inputs := by
  obtain ⟨cH, hsteps, hhalted⟩ := hH; exact prefix_of_concat_from_zero hsteps hhalted h1

theorem clear_registers_isStandardForm (maxReg : ℕ) :
    (Program.clear_registers maxReg).IsStandardForm :=
  straight_line_isStandardForm (clear_registers_is_straight_line maxReg)

theorem transfer_results_to_inputs_writes_to (resultStart arityF : ℕ)
    (instr : Instr) (hinstr : instr ∈ Program.transfer_results_to_inputs resultStart arityF) :
    ∃ i < arityF, instr.writes_to = some i := by
  simp only [Program.transfer_results_to_inputs, List.mem_map, List.mem_range] at hinstr
  obtain ⟨i, hi, hinstr_eq⟩ := hinstr; exact ⟨i, hi, by simp [← hinstr_eq, Instr.writes_to]⟩

theorem transfer_results_to_inputs_preserves_outside (resultStart arityF : ℕ) (r : ℕ) (hr : r ≥ arityF) :
    ∀ instr, instr ∈ Program.transfer_results_to_inputs resultStart arityF → instr.writes_to ≠ some r := by
  intro instr hinstr; obtain ⟨i, hi, hwrites⟩ := transfer_results_to_inputs_writes_to resultStart arityF instr hinstr
  rw [hwrites]; simp only [ne_eq, Option.some.injEq]; omega

section Continuation

variable {p1 p2 : Program}

theorem Step.of_concat_right {c c' : Config} (hpc_lo : p1.length ≤ c.pc) (hpc_hi : c.pc < p1.length + p2.length)
    (hstep : Step (p1.concat p2) c c') : Step p2 ⟨c.pc - p1.length, c.state⟩ ⟨c'.pc - p1.length, c'.state⟩ := by
  have hp2_pc : c.pc - p1.length < p2.length := by omega
  obtain ⟨instr, hinstr⟩ : ∃ instr, p2[c.pc - p1.length]? = some instr :=
    ⟨p2[c.pc - p1.length], List.getElem?_eq_getElem hp2_pc⟩
  have hconcat_instr : (p1.concat p2)[c.pc]? = some (instr.shift_jumps p1.length) := by
    rw [Program.getElem?_concat_of_ge c.pc hpc_lo, Program.getElem?_shift_jumps, hinstr]; rfl
  set pc2 := c.pc - p1.length with hpc2_def
  cases instr with
  | Z n => have hc' : c' = ⟨c.pc + 1, c.state.write n 0⟩ := by cases hstep <;> grind [Instr.shift_jumps]
           subst hc'; rw [show c.pc + 1 - p1.length = pc2 + 1 by omega]; exact Step.zero hinstr
  | S n => have hc' : c' = ⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩ := by cases hstep <;> grind [Instr.shift_jumps]
           subst hc'; rw [show c.pc + 1 - p1.length = pc2 + 1 by omega]; exact Step.succ hinstr
  | T m n => have hc' : c' = ⟨c.pc + 1, c.state.write n (c.state.read m)⟩ := by cases hstep <;> grind [Instr.shift_jumps]
             subst hc'; rw [show c.pc + 1 - p1.length = pc2 + 1 by omega]; exact Step.trans hinstr
  | J m n q =>
    cases hstep with
    | jump_eq h heq =>
      simp only [Instr.shift_jumps] at hconcat_instr; simp only [hconcat_instr, Option.some.injEq, Instr.J.injEq] at h
      obtain ⟨rfl, rfl, hq⟩ := h; simp only [← hq, Nat.add_sub_cancel]; exact Step.jump_eq hinstr heq
    | jump_ne h hne =>
      simp only [Instr.shift_jumps] at hconcat_instr; simp only [hconcat_instr, Option.some.injEq, Instr.J.injEq] at h
      obtain ⟨rfl, rfl, _⟩ := h; rw [show c.pc + 1 - p1.length = pc2 + 1 by omega]; exact Step.jump_ne hinstr hne
    | _ => grind [Instr.shift_jumps]

theorem Steps.of_concat_right {s : State} {c' : Config}
    (hsteps : Steps (p1.concat p2) ⟨p1.length, s⟩ c') (hhalted : c'.is_halted (p1.concat p2)) :
    ∃ c, Steps p2 ⟨0, s⟩ c ∧ c.is_halted p2 ∧ c.state = c'.state := by
  suffices h : ∀ start c', start.pc ≥ p1.length → Steps (p1.concat p2) start c' → c'.is_halted (p1.concat p2) →
      ∃ c, Steps p2 ⟨start.pc - p1.length, start.state⟩ c ∧ c.is_halted p2 ∧ c.state = c'.state by
    have := h ⟨p1.length, s⟩ c' (Nat.le_refl _) hsteps hhalted; simp only [Nat.sub_self] at this; exact this
  intro start c'' hstart hsteps' hhalted'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨⟨c''.pc - p1.length, c''.state⟩, Relation.ReflTransGen.refl, ?_, rfl⟩
    simp only [Config.is_halted] at hhalted' ⊢
    simp only [Program.concat, List.length_append, Program.shift_jumps, List.length_map] at hhalted'; omega
  | @head a b hstep hrest ih =>
    have ha_in_range : a.pc < p1.length + p2.length := by
      by_contra hc; simp only [not_lt] at hc
      exact Step.no_step_of_halted (by simp only [Config.is_halted, Program.concat, List.length_append, Program.shift_jumps, List.length_map]; omega) hstep
    have hstep_p2 := Step.of_concat_right hstart ha_in_range hstep
    have hb_pc_ge : b.pc ≥ p1.length := by
      cases hstep with
      | zero _ | succ _ | trans _ | jump_ne _ _ => simp only []; omega
      | jump_eq h _ =>
        rw [Program.getElem?_concat_of_ge a.pc hstart, Program.getElem?_shift_jumps] at h
        cases hp2 : p2[a.pc - p1.length]? with
        | none => simp only [hp2, Option.map_none] at h; nomatch h
        | some instr => simp only [hp2, Option.map_some] at h; cases instr with
          | J _ _ q' => simp only [Instr.shift_jumps, Option.some.injEq, Instr.J.injEq] at h; obtain ⟨_, _, hq_eq⟩ := h; simp only [← hq_eq]; omega
          | _ => simp only [Instr.shift_jumps, Option.some.injEq] at h; nomatch h
    obtain ⟨c, hrest_p2, hhalted_c, hstate_eq⟩ := ih hb_pc_ge
    exact ⟨c, Relation.ReflTransGen.head hstep_p2 hrest_p2, hhalted_c, hstate_eq⟩

theorem suffix_of_concat_from_zero {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.is_halted (p1.concat p2)) (h1 : p1.IsStandardForm) :
    ∃ s', Steps p1 ⟨0, s⟩ ⟨p1.length, s'⟩ ∧ (∃ c', Steps p2 ⟨0, s'⟩ c' ∧ c'.is_halted p2) := by
  obtain ⟨c1, hsteps_p1, hhalted_p1⟩ := prefix_of_concat_from_zero hsteps hhalted h1
  have hc1_le := h1.pc_le_length hsteps_p1 (by simp : (⟨0, s⟩ : Config).pc ≤ p1.length)
  have hc1_pc : c1.pc = p1.length := by simp only [Config.is_halted] at hhalted_p1; omega
  refine ⟨c1.state, ?_, ?_⟩
  · convert hsteps_p1 using 1; ext <;> simp [hc1_pc]
  · have hsteps_p1_lifted : Steps (p1.concat p2) ⟨0, s⟩ ⟨p1.length, c1.state⟩ := by
      convert @Steps.concat_left_prefix p1 p2 ⟨0, s⟩ c1 hsteps_p1 using 1; ext <;> simp [hc1_pc]
    have h_suffix := Steps.deterministic_continuation hsteps_p1_lifted hsteps hhalted
    obtain ⟨c', hsteps_p2, hhalted_p2, _⟩ := Steps.of_concat_right h_suffix hhalted
    exact ⟨c', hsteps_p2, hhalted_p2⟩

/-- Extract just the intermediate state from a concatenated program execution.
    This is the state after p1 halts, before p2 begins. -/
noncomputable def suffix_of_concat_state {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.is_halted (p1.concat p2))
    (h1 : p1.IsStandardForm) : State :=
  (suffix_of_concat_from_zero hsteps hhalted h1).choose

/-- Steps in p1 reaching the intermediate state. -/
theorem suffix_of_concat_steps_left {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.is_halted (p1.concat p2))
    (h1 : p1.IsStandardForm) :
    Steps p1 ⟨0, s⟩ ⟨p1.length, suffix_of_concat_state hsteps hhalted h1⟩ :=
  (suffix_of_concat_from_zero hsteps hhalted h1).choose_spec.1

/-- p2 halts when starting from the intermediate state. -/
theorem suffix_of_concat_halts_right {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.is_halted (p1.concat p2))
    (h1 : p1.IsStandardForm) :
    ∃ c', Steps p2 ⟨0, suffix_of_concat_state hsteps hhalted h1⟩ c' ∧ c'.is_halted p2 :=
  (suffix_of_concat_from_zero hsteps hhalted h1).choose_spec.2

/-- Bundle for decomposing execution of concatenated programs p1 ++ p2.
    Combines suffix_of_concat_state, suffix_of_concat_steps_left, and suffix_of_concat_halts_right
    into a single structure to reduce boilerplate. -/
structure ConcatDecomposition (p1 p2 : Program) (s : State) where
  /-- The intermediate state after p1 halts, before p2 begins. -/
  state : State
  /-- Steps in p1 reaching the intermediate state. -/
  steps_left : Steps p1 ⟨0, s⟩ ⟨p1.length, state⟩
  /-- Proof that p2 halts when starting from the intermediate state. -/
  halts_right : ∃ c', Steps p2 ⟨0, state⟩ c' ∧ c'.is_halted p2

/-- Decompose execution of p1 ++ p2 into intermediate state and proofs.
    This bundles the three separate calls (suffix_of_concat_state, suffix_of_concat_steps_left,
    suffix_of_concat_halts_right) into a single structure. -/
noncomputable def decompose_concat {p1 p2 : Program} {s : State} {c : Config}
    (hsteps : Steps (p1.concat p2) ⟨0, s⟩ c) (hhalted : c.is_halted (p1.concat p2))
    (h1 : p1.IsStandardForm) : ConcatDecomposition p1 p2 s :=
  ⟨suffix_of_concat_state hsteps hhalted h1,
   suffix_of_concat_steps_left hsteps hhalted h1,
   suffix_of_concat_halts_right hsteps hhalted h1⟩

theorem Halts.suffix_of_concat_sf {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs) (h1 : p1.IsStandardForm) :
    ∃ s : State, Halts p1 inputs ∧ (∀ hP1 : Halts p1 inputs, s = (Classical.choose hP1).state) ∧
                 (∃ c, Steps p2 ⟨0, s⟩ c ∧ c.is_halted p2) := by
  have hP1 := Halts.prefix_of_concat_sf hH h1
  have hc1_spec := Classical.choose_spec hP1
  have hc1_pc := h1.halts_at_length inputs (Classical.choose hP1) hc1_spec.1 hc1_spec.2
  refine ⟨(Classical.choose hP1).state, hP1, ?_, ?_⟩
  · intro hP1'; rw [Steps.eq_of_halts hc1_spec.1 hc1_spec.2 (Classical.choose_spec hP1').1 (Classical.choose_spec hP1').2]
  · obtain ⟨cH, hH_steps, hH_halted⟩ := hH
    have h_to_c1 : Steps (p1.concat p2) (Config.init inputs) (Classical.choose hP1) :=
      Steps.concat_left_prefix hc1_spec.1
    have h_suffix := Steps.deterministic_continuation h_to_c1 hH_steps hH_halted
    have h_suffix_start : Classical.choose hP1 = ⟨p1.length, (Classical.choose hP1).state⟩ := by ext; exact hc1_pc; rfl
    rw [h_suffix_start] at h_suffix
    obtain ⟨c, hsteps_p2, hhalted_p2, _⟩ := Steps.of_concat_right h_suffix hH_halted
    exact ⟨c, hsteps_p2, hhalted_p2⟩

end Continuation

end Urm
