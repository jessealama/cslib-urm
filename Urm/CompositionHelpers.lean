/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition

/-! # Composition Helpers

This file provides reusable infrastructure for composition proofs, factored out
from `UnaryComposition.lean` for use across different composition scenarios
(unary-unary, binary-unary, and eventually general n-ary composition).

## Main definitions

- `Program.boundedJumps`: Property that all jump targets are within bounds
- `State.agreesLow`: Two states agree on registers 0 through some maximum
- `Config.agreesLow`: Two configurations agree on pc and low registers
- `Program.clearAbove`: Clear registers from a starting point upward

## Main results

- `Step.mirror_agreesLow`: Low-register agreement is preserved through steps
- `Halts.of_agreesLow`: Halting behavior depends only on low registers
- `steps_concat_continuation_bounded`: Chain halting programs with bounded jumps
- `steps_extract_second_bounded`: Extract second program halting from concatenation

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Bounded Jumps

A program has bounded jumps if all jump targets are within the program's bounds.
This is a natural property of well-formed programs and ensures that concatenation
behaves predictably. -/

/-- A program has bounded jumps if all J instruction targets are ≤ program length.
A target equal to the length means "jump to halt" (fall through). -/
def Program.boundedJumps (p : Program) : Prop :=
  ∀ i : ℕ, ∀ m n q : ℕ, p.getInstr i = some (Instr.J m n q) → q ≤ p.length

/-- The empty program trivially has bounded jumps. -/
theorem Program.boundedJumps_nil : Program.boundedJumps [] := by
  intro i m n q h
  simp [Program.getInstr] at h

/-- A single Z instruction has bounded jumps (no jumps at all). -/
theorem Program.boundedJumps_single_Z (r : ℕ) : Program.boundedJumps [Instr.Z r] := by
  intro i m n q h
  simp only [Program.getInstr, List.length_singleton] at h ⊢
  cases i <;> simp_all

/-- A single S instruction has bounded jumps (no jumps at all). -/
theorem Program.boundedJumps_single_S (r : ℕ) : Program.boundedJumps [Instr.S r] := by
  intro i m n q h
  simp only [Program.getInstr, List.length_singleton] at h ⊢
  cases i <;> simp_all

/-- A single T instruction has bounded jumps (no jumps at all). -/
theorem Program.boundedJumps_single_T (m n : ℕ) : Program.boundedJumps [Instr.T m n] := by
  intro i m' n' q h
  simp only [Program.getInstr, List.length_singleton] at h ⊢
  cases i <;> simp_all

/-- A straight-line program has bounded jumps (no jumps at all). -/
theorem Program.boundedJumps_of_straightLine {p : Program} (hsl : p.isStraightLine = true) :
    p.boundedJumps := by
  intro i m n q hinstr
  simp only [Program.isStraightLine, List.all_eq_true] at hsl
  simp only [Program.getInstr] at hinstr
  have hi : i < p.length := by
    by_contra hc
    simp only [not_lt] at hc
    simp [List.getElem?_eq_none hc] at hinstr
  have hmem : Instr.J m n q ∈ p := by
    exact List.getElem?_eq_some_iff.mp hinstr |>.2 ▸ List.getElem_mem hi
  have := hsl (Instr.J m n q) hmem
  simp [Instr.isNonJumping] at this

/-! ## Bounded Jump Execution Properties -/

/-- A single step in a bounded-jump program keeps pc ≤ length or sets pc to the jump target. -/
theorem Step.pc_bounded_step {p : Program} {c c' : Config}
    (hbounded : p.boundedJumps) (hstep : Step p c c') :
    c'.pc ≤ p.length := by
  cases hstep with
  | zero h =>
    simp only [Program.getInstr] at h
    have hpc : c.pc < p.length := List.getElem?_eq_some_iff.mp h |>.1
    simp only
    omega
  | succ h =>
    simp only [Program.getInstr] at h
    have hpc : c.pc < p.length := List.getElem?_eq_some_iff.mp h |>.1
    simp only
    omega
  | trans h =>
    simp only [Program.getInstr] at h
    have hpc : c.pc < p.length := List.getElem?_eq_some_iff.mp h |>.1
    simp only
    omega
  | jump_eq h _ =>
    exact hbounded c.pc _ _ _ h
  | jump_ne h _ =>
    simp only [Program.getInstr] at h
    have hpc : c.pc < p.length := List.getElem?_eq_some_iff.mp h |>.1
    simp only
    omega

/-- Multi-step execution in a bounded-jump program keeps pc ≤ length. -/
theorem Steps.pc_bounded {p : Program} {c c' : Config}
    (hbounded : p.boundedJumps) (hsteps : Steps p c c')
    (hstart : c.pc ≤ p.length) :
    c'.pc ≤ p.length := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact hstart
  | head hstep _ ih =>
    exact ih (Step.pc_bounded_step hbounded hstep)

/-- In a bounded-jump program, a halting execution ends at exactly pc = length.
    pc ≤ length by bounded execution, pc ≥ length by halting definition. -/
theorem Halts.pc_eq_length {p : Program} {inputs : List ℕ}
    (hbounded : p.boundedJumps) (hhalts : Halts p inputs) :
    (Classical.choose hhalts).pc = p.length := by
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec hhalts
  have hpc_le := Steps.pc_bounded hbounded hsteps (by simp [Config.init])
  simp only [Config.isHalted] at hhalted
  omega

/-! ## Low-Register Agreement

For composition, we need to show that a program's behavior depends only on registers
0 through `p.maxRegister`. Two states that agree on these registers will produce
the same execution trace and output. -/

/-- Two states agree on registers 0 through maxReg. -/
def State.agreesLow (σ₁ σ₂ : State) (maxReg : ℕ) : Prop :=
  ∀ r, r ≤ maxReg → σ₁.read r = σ₂.read r

namespace State.agreesLow

variable {σ₁ σ₂ : State} {maxReg : ℕ}

theorem refl (σ : State) (maxReg : ℕ) : σ.agreesLow σ maxReg :=
  fun _ _ => rfl

theorem symm (h : σ₁.agreesLow σ₂ maxReg) : σ₂.agreesLow σ₁ maxReg :=
  fun r hr => (h r hr).symm

theorem read_eq (h : σ₁.agreesLow σ₂ maxReg) (r : ℕ) (hr : r ≤ maxReg) :
    σ₁.read r = σ₂.read r :=
  h r hr

/-- Writing to a register ≤ maxReg preserves agreement if we write the same value. -/
theorem write_same (h : σ₁.agreesLow σ₂ maxReg) (n : ℕ) (v : ℕ) :
    (σ₁.write n v).agreesLow (σ₂.write n v) maxReg := by
  intro r hr
  simp only [State.write, State.read, Function.update]
  split_ifs with heq
  · rfl
  · exact h r hr

/-- Writing to a register > maxReg preserves agreement. -/
theorem write_high (h : σ₁.agreesLow σ₂ maxReg) (n : ℕ) (hn : maxReg < n) (v₁ v₂ : ℕ) :
    (σ₁.write n v₁).agreesLow (σ₂.write n v₂) maxReg := by
  intro r hr
  simp only [State.write, State.read, Function.update]
  split_ifs with heq
  · omega
  · exact h r hr

end State.agreesLow

/-! ## Step Mirroring

If two states agree on low registers, executing the same instruction produces
states that still agree on low registers. -/

/-- If states agree on low registers and one can step, the other can take the same
    step with the same pc transition and preserved agreement. -/
theorem Step.mirror_agreesLow {p : Program} {σ₁ σ₂ : State} {pc : ℕ} {c₁' : Config}
    (hagree : σ₁.agreesLow σ₂ p.maxRegister)
    (hstep : Step p ⟨pc, σ₁⟩ c₁') :
    ∃ c₂', Step p ⟨pc, σ₂⟩ c₂' ∧ c₁'.pc = c₂'.pc ∧
           c₁'.state.agreesLow c₂'.state p.maxRegister := by
  cases hstep with
  | zero h =>
    -- Z n: writes 0 to register n
    rename_i n
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    refine ⟨⟨pc + 1, σ₂.write n 0⟩, Step.zero h, rfl, ?_⟩
    exact hagree.write_same n 0
  | succ h =>
    -- S n: reads and writes register n
    rename_i n
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    -- Both states read the same value from register n
    have hread : σ₁.read n = σ₂.read n := hagree.read_eq n hinstr
    refine ⟨⟨pc + 1, σ₂.write n (σ₂.read n + 1)⟩, Step.succ h, rfl, ?_⟩
    -- After writing, states still agree
    intro r hr
    by_cases heq : r = n
    · -- r = n: both wrote the same value (since reads were equal)
      subst heq
      simp only [State.write_read_same, hread]
    · -- r ≠ n: unchanged, so still agree
      simp only [State.write_read_diff _ _ _ _ heq]
      exact hagree.read_eq r hr
  | trans h =>
    -- T m n: reads m, writes to n
    rename_i m n
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    -- Both states read the same value from register m
    have hread : σ₁.read m = σ₂.read m := hagree.read_eq m (Nat.le_trans (Nat.le_max_left _ _) hinstr)
    refine ⟨⟨pc + 1, σ₂.write n (σ₂.read m)⟩, Step.trans h, rfl, ?_⟩
    intro r hr
    by_cases heq : r = n
    · -- r = n: both wrote the same value (since reads from m were equal)
      subst heq
      simp only [State.write_read_same]
      simp only [State.read] at hread
      exact hread
    · -- r ≠ n: unchanged, so still agree
      simp only [State.write_read_diff _ _ _ _ heq]
      exact hagree.read_eq r hr
  | jump_eq h heq =>
    -- J m n q with equal: reads m and n
    rename_i m n q
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    have hread_m : σ₁.read m = σ₂.read m :=
      hagree.read_eq m (Nat.le_trans (Nat.le_max_left _ _) hinstr)
    have hread_n : σ₁.read n = σ₂.read n :=
      hagree.read_eq n (Nat.le_trans (Nat.le_max_right _ _) hinstr)
    -- Since σ₁ has equal reads, so does σ₂
    have heq' : σ₂.read m = σ₂.read n := by rw [← hread_m, ← hread_n, heq]
    refine ⟨⟨q, σ₂⟩, Step.jump_eq h heq', rfl, ?_⟩
    exact hagree
  | jump_ne h hne =>
    -- J m n q with unequal: reads m and n
    rename_i m n q
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    have hread_m : σ₁.read m = σ₂.read m :=
      hagree.read_eq m (Nat.le_trans (Nat.le_max_left _ _) hinstr)
    have hread_n : σ₁.read n = σ₂.read n :=
      hagree.read_eq n (Nat.le_trans (Nat.le_max_right _ _) hinstr)
    -- Since σ₁ has unequal reads, so does σ₂
    have hne' : σ₂.read m ≠ σ₂.read n := by rw [← hread_m, ← hread_n]; exact hne
    refine ⟨⟨pc + 1, σ₂⟩, Step.jump_ne h hne', rfl, ?_⟩
    exact hagree

/-! ## Halting Independence

The main register independence theorem: if two states agree on low registers
and the program halts from one, it halts from the other with the same output. -/

/-- Auxiliary: configs that agree on pc and low registers. -/
def Config.agreesLow (c₁ c₂ : Config) (p : Program) : Prop :=
  c₁.pc = c₂.pc ∧ c₁.state.agreesLow c₂.state p.maxRegister

/-- Single step preserves config agreement. -/
theorem Step.preserves_agreesLow {p : Program} {c₁ c₁' c₂ : Config}
    (hagree : c₁.agreesLow c₂ p)
    (hstep : Step p c₁ c₁') :
    ∃ c₂', Step p c₂ c₂' ∧ c₁'.agreesLow c₂' p := by
  obtain ⟨hpc, hstate⟩ := hagree
  -- c₁ and c₂ have the same pc, and their states agree on low registers
  -- Use mirror_agreesLow to get the mirrored step
  obtain ⟨c₂', hstep₂, hpc_eq, hstate_eq⟩ := Step.mirror_agreesLow hstate hstep
  -- hstep₂ : Step p ⟨c₁.pc, c₂.state⟩ c₂'
  -- Since c₂.pc = c₁.pc (by hpc), we have Step p c₂ c₂'
  have hc₂_eq : c₂ = ⟨c₁.pc, c₂.state⟩ := Config.ext hpc.symm rfl
  rw [hc₂_eq]
  exact ⟨c₂', hstep₂, hpc_eq, hstate_eq⟩

/-- Multi-step execution preserves config agreement. -/
theorem Steps.preserves_agreesLow {p : Program} {c₁ c₁' c₂ : Config}
    (hagree : c₁.agreesLow c₂ p)
    (hsteps : Steps p c₁ c₁') :
    ∃ c₂', Steps p c₂ c₂' ∧ c₁'.agreesLow c₂' p := by
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing c₂ with
  | refl =>
    exact ⟨c₂, Relation.ReflTransGen.refl, hagree⟩
  | @head c_mid c_rest hstep hrest ih =>
    obtain ⟨c₂_mid, hstep₂, hagree_mid⟩ := Step.preserves_agreesLow hagree hstep
    obtain ⟨c₂', hsteps₂, hagree'⟩ := ih hagree_mid
    exact ⟨c₂', Relation.ReflTransGen.head hstep₂ hsteps₂, hagree'⟩

/-- If σ agrees with the fresh state on low registers, and the program halts
    from fresh state, then it also halts from σ with the same output. -/
theorem Halts.of_agreesLow {p : Program} {y : ℕ} {σ : State}
    (hagree : σ.agreesLow (State.fromInputs [y]) p.maxRegister)
    (hfresh : Halts p [y]) :
    ∃ c', Steps p ⟨0, σ⟩ c' ∧ c'.isHalted p ∧
          c'.state.read 0 = Result p [y] hfresh := by
  -- Get the fresh execution trace without destructing hfresh (we need it for the goal)
  let c_fresh := Classical.choose hfresh
  have hsteps_fresh : Steps p (Config.init [y]) c_fresh := (Classical.choose_spec hfresh).1
  have hhalted_fresh : c_fresh.isHalted p := (Classical.choose_spec hfresh).2
  -- Build config agreement: Config.init [y] agrees with ⟨0, σ⟩
  -- We need c₁ = Config.init [y] (the one with hsteps) and c₂ = ⟨0, σ⟩
  have hconfig_agree : (Config.init [y]).agreesLow ⟨0, σ⟩ p := by
    constructor
    · simp [Config.init]
    · exact hagree.symm
  -- Mirror the entire execution: from Config.init [y] to c_fresh, mirrors to ⟨0, σ⟩ to c'
  obtain ⟨c', hsteps', hagree'⟩ := Steps.preserves_agreesLow hconfig_agree hsteps_fresh
  refine ⟨c', hsteps', ?_, ?_⟩
  · -- c' is halted: same pc as c_fresh
    simp only [Config.isHalted] at hhalted_fresh ⊢
    rw [← hagree'.1]
    exact hhalted_fresh
  · -- R0 values match
    have h0 : 0 ≤ p.maxRegister := Nat.zero_le _
    -- hagree' : c_fresh.agreesLow c' p, so c_fresh.state agrees with c'.state on low regs
    have hR0 := hagree'.2.read_eq 0 h0
    -- hR0 : c_fresh.state.read 0 = c'.state.read 0
    -- Result p [y] hfresh is the R0 of the chosen config = c_fresh
    simp only [Result, State.output]
    -- Goal: c'.state.read 0 = c_fresh.state.read 0, so reverse direction
    exact hR0.symm

/-- Converse of of_agreesLow: if σ agrees with fresh on low registers and p halts from σ,
    then p also halts from fresh state with the same output. -/
theorem Halts.to_agreesLow {p : Program} {y : ℕ} {σ : State}
    (hagree : σ.agreesLow (State.fromInputs [y]) p.maxRegister)
    (hσ : ∃ c, Steps p ⟨0, σ⟩ c ∧ c.isHalted p) :
    Halts p [y] := by
  -- σ agrees with fresh, and p halts from σ
  -- By mirroring, p also halts from fresh
  obtain ⟨c_σ, hsteps_σ, hhalted_σ⟩ := hσ
  have hconfig_agree : (⟨0, σ⟩ : Config).agreesLow (Config.init [y]) p := by
    constructor
    · simp [Config.init]
    · exact hagree
  obtain ⟨c_fresh, hsteps_fresh, hagree'⟩ := Steps.preserves_agreesLow hconfig_agree hsteps_σ
  refine ⟨c_fresh, hsteps_fresh, ?_⟩
  simp only [Config.isHalted] at hhalted_σ ⊢
  rw [← hagree'.1]
  exact hhalted_σ

/-! ## Concatenation with Bounded Jumps

Lemmas for extracting halting information from concatenated programs when
the first program has bounded jumps. -/

/-- Concatenating programs preserves bounded jumps in the first program's part. -/
theorem Program.concat_boundedJumps {p1 p2 : Program}
    (hbounded1 : p1.boundedJumps)
    (hbounded2 : p2.boundedJumps) :
    (p1.concat p2).boundedJumps := by
  intro i m n q hinstr
  simp only [Program.concat, Program.getInstr, List.length_append,
             Program.shiftJumps_length] at hinstr ⊢
  by_cases hi : i < p1.length
  · -- Instruction from p1
    rw [List.getElem?_append_left hi] at hinstr
    have hq := hbounded1 i m n q hinstr
    omega
  · -- Instruction from p2 (shifted)
    push_neg at hi
    rw [List.getElem?_append_right hi] at hinstr
    simp only [Program.shiftJumps, List.getElem?_map] at hinstr
    cases hopt : p2[i - p1.length]? with
    | none =>
      simp only [hopt] at hinstr
      cases hinstr
    | some instr =>
      simp only [hopt, Option.map_some, Option.some.injEq] at hinstr
      cases instr with
      | Z _ => cases hinstr
      | S _ => cases hinstr
      | T _ _ => cases hinstr
      | J m' n' q' =>
        simp only [Instr.shiftJumps, Instr.J.injEq] at hinstr
        obtain ⟨_, _, hq_eq⟩ := hinstr
        have hq' := hbounded2 (i - p1.length) m' n' q' (by simp [Program.getInstr, hopt])
        omega

/-- If execution in p1.concat p2 is in the first part (pc < p1.length),
    and takes a step, the new pc is still ≤ p1.length when p1 has bounded jumps. -/
theorem Step.concat_left_pc_bounded {p1 p2 : Program} {c c' : Config}
    (hbounded : p1.boundedJumps)
    (hpc : c.pc < p1.length)
    (hstep : Step (p1.concat p2) c c') :
    c'.pc ≤ p1.length := by
  -- First, get the step in p1
  have hstep1 : Step p1 c c' := Step.of_concat_left hpc hstep
  -- Apply the bounded step lemma
  exact Step.pc_bounded_step hbounded hstep1

/-- Helper: If p1.concat p2 reaches a halted config from c where c.pc ≤ p1.length,
    execution must pass through the boundary at pc = p1.length. -/
private theorem Steps.reaches_boundary_aux {p1 p2 : Program} {c c' : Config}
    (hbounded1 : p1.boundedJumps)
    (hsteps : Steps (p1.concat p2) c c')
    (hstart : c.pc ≤ p1.length)
    (hhalted : c'.isHalted (p1.concat p2)) :
    ∃ cmid, Steps p1 c cmid ∧ cmid.pc = p1.length ∧
            Steps (p1.concat p2) cmid c' := by
  -- If c.pc = p1.length already, we're done (zero steps in p1)
  by_cases hc_at_boundary : c.pc = p1.length
  · exact ⟨c, Relation.ReflTransGen.refl, hc_at_boundary, hsteps⟩
  -- Otherwise c.pc < p1.length, use induction on the step sequence
  have hpc_lt : c.pc < p1.length := Nat.lt_of_le_of_ne hstart hc_at_boundary
  -- Revert hypotheses for the induction
  revert hstart hc_at_boundary hpc_lt
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hstart _ hpc_lt
    -- c = c' and c is halted, but c.pc < p1.length < (p1.concat p2).length
    simp only [Config.isHalted, Program.concat_length] at hhalted
    omega
  | @head a b hstep hrest ih =>
    intro hstart hc_at hpc_lt
    -- a.pc < p1.length (from hpc_lt), step to b
    have hb_pc : b.pc ≤ p1.length := Step.concat_left_pc_bounded hbounded1 hpc_lt hstep
    -- Convert this step to p1 (since a.pc < p1.length)
    have hstep1 : Step p1 a b := Step.of_concat_left hpc_lt hstep
    by_cases hb_at : b.pc = p1.length
    · -- b is at the boundary - done! One step in p1.
      exact ⟨b, Relation.ReflTransGen.single hstep1, hb_at, hrest⟩
    · -- b.pc < p1.length, continue with IH
      have hb_lt : b.pc < p1.length := Nat.lt_of_le_of_ne hb_pc hb_at
      -- Apply IH to get path from b to cmid in p1
      have ⟨cmid, hsteps_b_mid, hmid_pc, hsteps_mid_c'⟩ := ih hb_pc hb_at hb_lt
      -- Prepend the step from a to b
      exact ⟨cmid, Relation.ReflTransGen.head hstep1 hsteps_b_mid, hmid_pc, hsteps_mid_c'⟩

/-- If p1.concat p2 reaches a halted config from ⟨k, σ⟩ where k ≤ p1.length,
    execution must pass through the boundary at pc = p1.length. -/
theorem Steps.reaches_boundary {p1 p2 : Program} {k : ℕ} {σ : State} {c' : Config}
    (hbounded1 : p1.boundedJumps)
    (hsteps : Steps (p1.concat p2) ⟨k, σ⟩ c')
    (hk : k ≤ p1.length)
    (hhalted : c'.isHalted (p1.concat p2)) :
    ∃ cmid, Steps p1 ⟨k, σ⟩ cmid ∧ cmid.pc = p1.length ∧
            Steps (p1.concat p2) cmid c' :=
  Steps.reaches_boundary_aux hbounded1 hsteps hk hhalted

/-- If p1.concat p2 halts and p1 has bounded jumps, then p1 halts. -/
theorem Halts.of_concat_left_bounded {p1 p2 : Program} {inputs : List ℕ}
    (hbounded1 : p1.boundedJumps)
    (hconcat : Halts (p1.concat p2) inputs) :
    Halts p1 inputs := by
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec hconcat
  obtain ⟨cmid, hsteps_p1, hpc_eq, _⟩ :=
    Steps.reaches_boundary hbounded1 hsteps (by simp) hhalted
  exact ⟨cmid, hsteps_p1, by simp [Config.isHalted, hpc_eq]⟩

/-! ## Straight-Line Execution Utilities

Utilities for programs without jump instructions. -/

/-- A straight-line program halts when started from any state (not just Config.init).
    This is a generalization of straightLine_halts for use in continuation proofs. -/
theorem straightLine_halts_from_state {p : Program} (hsl : p.isStraightLine = true) (σ : State) :
    ∃ c, Steps p ⟨0, σ⟩ c ∧ c.isHalted p := by
  -- Reuse the proof structure from straightLine_halts
  suffices h : ∀ (c : Config), c.pc ≤ p.length →
      ∃ c', Steps p c c' ∧ c'.pc ≥ p.length by
    obtain ⟨c', hsteps, hpc⟩ := h ⟨0, σ⟩ (by simp)
    exact ⟨c', hsteps, hpc⟩
  intro c hpc_le
  generalize hrem : p.length - c.pc = remaining
  induction remaining generalizing c with
  | zero =>
    have hpc : c.pc = p.length := by omega
    exact ⟨c, Relation.ReflTransGen.refl, by omega⟩
  | succ k ih =>
    by_cases hhalted : c.pc ≥ p.length
    · exact ⟨c, Relation.ReflTransGen.refl, hhalted⟩
    · have hpc_lt : c.pc < p.length := by omega
      have hinstr : ∃ instr, p.getInstr c.pc = some instr := by
        simp only [Program.getInstr]
        exact ⟨p[c.pc], List.getElem?_eq_getElem hpc_lt⟩
      obtain ⟨instr, hinstr⟩ := hinstr
      have hnonjump : instr.isNonJumping = true := by
        simp only [Program.isStraightLine, List.all_eq_true] at hsl
        have hmem : instr ∈ p := by
          simp only [Program.getInstr] at hinstr
          exact List.getElem?_eq_some_iff.mp hinstr |>.2 ▸ List.getElem_mem hpc_lt
        exact hsl instr hmem
      -- Construct the step by case analysis on instruction type
      have hstep : ∃ c', Step p c c' ∧ c'.pc = c.pc + 1 := by
        cases instr with
        | Z n =>
          exact ⟨⟨c.pc + 1, c.state.write n 0⟩, Step.zero hinstr, rfl⟩
        | S n =>
          exact ⟨⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩, Step.succ hinstr, rfl⟩
        | T m n =>
          exact ⟨⟨c.pc + 1, c.state.write n (c.state.read m)⟩, Step.trans hinstr, rfl⟩
        | J m n q =>
          simp [Instr.isNonJumping] at hnonjump
      obtain ⟨c', hstep', hpc'_eq⟩ := hstep
      have hpc'_le : c'.pc ≤ p.length := by omega
      obtain ⟨c'', hsteps'', hpc''⟩ := ih c' hpc'_le (by omega)
      exact ⟨c'', Relation.ReflTransGen.head hstep' hsteps'', hpc''⟩

/-- For straight-line programs started from state σ, the halted pc equals the program length. -/
theorem straightLine_halts_from_state_at_length {p : Program}
    (hsl : p.isStraightLine = true) (σ : State) :
    let h := straightLine_halts_from_state hsl σ
    (Classical.choose h).pc = p.length := by
  have h := straightLine_halts_from_state hsl σ
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec h
  simp only [Config.isHalted] at hhalted
  suffices hsuff : ∀ c c' : Config, Steps p c c' → c'.pc ≤ max c.pc p.length by
    have := hsuff ⟨0, σ⟩ (Classical.choose h) hsteps
    simp only at this
    omega
  intro c c' hsteps'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl => simp only [le_max_iff, le_refl, true_or]
  | @head a b hstep _ ih =>
    -- For each step type in a straight-line program, pc increases by 1 or we get a contradiction
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    cases hstep with
    | zero hinstr =>
      simp only [Program.getInstr] at hinstr
      have hlt := List.getElem?_eq_some_iff.mp hinstr |>.1
      simp only at ih ⊢
      omega
    | succ hinstr =>
      simp only [Program.getInstr] at hinstr
      have hlt := List.getElem?_eq_some_iff.mp hinstr |>.1
      simp only at ih ⊢
      omega
    | trans hinstr =>
      simp only [Program.getInstr] at hinstr
      have hlt := List.getElem?_eq_some_iff.mp hinstr |>.1
      simp only at ih ⊢
      omega
    | jump_eq hinstr _ =>
      simp only [Program.getInstr] at hinstr
      have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
      have hmem : (Instr.J _ _ _) ∈ p := heq ▸ List.getElem_mem hlt
      exact absurd (hsl _ hmem) (by simp [Instr.isNonJumping])
    | jump_ne hinstr _ =>
      simp only [Program.getInstr] at hinstr
      have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
      have hmem : (Instr.J _ _ _) ∈ p := heq ▸ List.getElem_mem hlt
      exact absurd (hsl _ hmem) (by simp [Instr.isNonJumping])

/-- For straight-line programs, the final state from `straightLine_halts_from_state`
    equals `executeStraightLine`. This technical lemma connects step-based and
    fold-based semantics. -/
theorem straightLine_final_state_eq {p : Program} (hsl : p.isStraightLine = true) (σ : State) :
    let h := straightLine_halts_from_state hsl σ
    (Classical.choose h).state = executeStraightLine p σ := by
  -- This proof requires showing that step-based execution matches fold-based execution.
  -- The key insight is that for straight-line programs, each step corresponds to
  -- one iteration of the fold.
  sorry

/-! ## Continuation Lemmas -/

/-- Continuation for straight-line first program. -/
theorem steps_concat_continuation_straightLine {p1 p2 : Program} {σ : State}
    (hsl1 : p1.isStraightLine = true)
    (h1 : ∃ c, Steps p1 ⟨0, σ⟩ c ∧ c.isHalted p1)
    (h2 : ∃ c, Steps p2 ⟨0, (Classical.choose h1).state⟩ c ∧ c.isHalted p2) :
    ∃ c, Steps (p1.concat p2) ⟨0, σ⟩ c ∧ c.isHalted (p1.concat p2) := by
  obtain ⟨hsteps1, hhalted1⟩ := Classical.choose_spec h1
  obtain ⟨c2, hsteps2, hhalted2⟩ := h2
  -- Lift p1's steps to the concatenation
  have hsteps1' := Steps.concat_left_prefix (p2 := p2) hsteps1 hhalted1
  -- Lift p2's steps to the concatenation
  have hsteps2' := Steps.concat_right (p1 := p1) hsteps2 hhalted2
  -- For straight-line programs, halted pc = length
  have hc1_pc : (Classical.choose h1).pc = p1.length := by
    simp only [Config.isHalted] at hhalted1
    suffices hsuff : (Classical.choose h1).pc ≤ p1.length by omega
    have hsteps_from := straightLine_halts_from_state hsl1 σ
    have hpc_eq := straightLine_halts_from_state_at_length hsl1 σ
    have hunique := Steps.halts_unique hsteps1 hhalted1
        (Classical.choose_spec hsteps_from).1 (Classical.choose_spec hsteps_from).2
    rw [hunique, hpc_eq]
  -- Connect the two step sequences
  have hstart_eq : (⟨0 + p1.length, (Classical.choose h1).state⟩ : Config) =
                   ⟨(Classical.choose h1).pc, (Classical.choose h1).state⟩ := by
    simp only [Nat.zero_add, hc1_pc]
  rw [hstart_eq] at hsteps2'
  have hsteps_total := Relation.ReflTransGen.trans hsteps1' hsteps2'
  refine ⟨⟨c2.pc + p1.length, c2.state⟩, hsteps_total, ?_⟩
  simp only [Config.isHalted, Program.concat_length] at hhalted2 ⊢
  omega

/-- Reverse of Step.concat_right: stepping in concat from p2 range gives step in p2. -/
theorem Step.of_concat_right_bounded {p1 p2 : Program} {pc : ℕ} {σ : State} {c' : Config}
    (_hbounded : p2.boundedJumps)
    (hpc_ge : p1.length ≤ pc)
    (hpc_lt : pc < p1.length + p2.length)
    (hstep : Step (p1.concat p2) ⟨pc, σ⟩ c') :
    ∃ c2 : Config, Step p2 ⟨pc - p1.length, σ⟩ c2 ∧
      c'.pc = c2.pc + p1.length ∧ c'.state = c2.state := by
  have hinstr_eq : (p1.concat p2).getInstr pc = (p2.shiftJumps p1.length).getInstr (pc - p1.length) :=
    Program.getInstr_concat_right pc hpc_ge hpc_lt
  have hinstr_shift : (p2.shiftJumps p1.length).getInstr (pc - p1.length) =
      (p2.getInstr (pc - p1.length)).map (Instr.shiftJumps p1.length) :=
    Program.getInstr_shiftJumps p1.length p2 (pc - p1.length)
  cases hstep with
  | zero h =>
    rename_i n
    rw [hinstr_eq, hinstr_shift] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr, heq⟩ := h
    cases instr with
    | Z n' =>
      simp only [Instr.shiftJumps] at heq
      cases heq
      refine ⟨⟨(pc - p1.length) + 1, σ.write n 0⟩, Step.zero hinstr, ?_, rfl⟩
      simp only; omega
    | S _ => simp only [Instr.shiftJumps] at heq; cases heq
    | T _ _ => simp only [Instr.shiftJumps] at heq; cases heq
    | J _ _ _ => simp only [Instr.shiftJumps] at heq; cases heq
  | succ h =>
    rename_i n
    rw [hinstr_eq, hinstr_shift] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr, heq⟩ := h
    cases instr with
    | S n' =>
      simp only [Instr.shiftJumps] at heq
      cases heq
      refine ⟨⟨(pc - p1.length) + 1, σ.write n (σ.read n + 1)⟩, Step.succ hinstr, ?_, rfl⟩
      simp only; omega
    | Z _ => simp only [Instr.shiftJumps] at heq; cases heq
    | T _ _ => simp only [Instr.shiftJumps] at heq; cases heq
    | J _ _ _ => simp only [Instr.shiftJumps] at heq; cases heq
  | trans h =>
    rw [hinstr_eq, hinstr_shift] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr, heq⟩ := h
    cases instr with
    | T m' n' =>
      simp only [Instr.shiftJumps, Instr.T.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine ⟨⟨(pc - p1.length) + 1, σ.write n' (σ.read m')⟩, Step.trans hinstr, ?_, rfl⟩
      simp only; omega
    | Z _ => simp only [Instr.shiftJumps] at heq; cases heq
    | S _ => simp only [Instr.shiftJumps] at heq; cases heq
    | J _ _ _ => simp only [Instr.shiftJumps] at heq; cases heq
  | jump_eq h heq =>
    rename_i m n q
    rw [hinstr_eq, hinstr_shift] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr, heq'⟩ := h
    cases instr with
    | J m' n' q' =>
      simp only [Instr.shiftJumps, Instr.J.injEq] at heq'
      obtain ⟨rfl, rfl, hq_eq⟩ := heq'
      refine ⟨⟨q', σ⟩, Step.jump_eq hinstr heq, ?_, rfl⟩
      simp only; omega
    | Z _ => simp only [Instr.shiftJumps] at heq'; cases heq'
    | S _ => simp only [Instr.shiftJumps] at heq'; cases heq'
    | T _ _ => simp only [Instr.shiftJumps] at heq'; cases heq'
  | jump_ne h hne =>
    rename_i m n q
    rw [hinstr_eq, hinstr_shift] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr, heq'⟩ := h
    cases instr with
    | J m' n' q' =>
      simp only [Instr.shiftJumps, Instr.J.injEq] at heq'
      obtain ⟨rfl, rfl, _⟩ := heq'
      refine ⟨⟨(pc - p1.length) + 1, σ⟩, Step.jump_ne hinstr hne, ?_, rfl⟩
      simp only; omega
    | Z _ => simp only [Instr.shiftJumps] at heq'; cases heq'
    | S _ => simp only [Instr.shiftJumps] at heq'; cases heq'
    | T _ _ => simp only [Instr.shiftJumps] at heq'; cases heq'

/-- Helper: translate execution from the p2 region to p2. -/
private theorem halts_at_boundary_aux {p1 p2 : Program} {c c' : Config}
    (hbounded2 : p2.boundedJumps)
    (hpc_ge : p1.length ≤ c.pc)
    (hsteps : Steps (p1.concat p2) c c')
    (hhalted : c'.isHalted (p1.concat p2)) :
    ∃ c_p2, Steps p2 ⟨c.pc - p1.length, c.state⟩ c_p2 ∧ c_p2.isHalted p2 := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    simp only [Config.isHalted, Program.concat_length] at hhalted
    refine ⟨⟨c'.pc - p1.length, c'.state⟩, Relation.ReflTransGen.refl, ?_⟩
    simp only [Config.isHalted]
    omega
  | @head c_mid c_rest hstep hrest ih =>
    by_cases hhalted_c : c_mid.pc ≥ p1.length + p2.length
    · refine ⟨⟨c_mid.pc - p1.length, c_mid.state⟩, Relation.ReflTransGen.refl, ?_⟩
      simp only [Config.isHalted]
      omega
    · have hpc_lt : c_mid.pc < p1.length + p2.length := by omega
      obtain ⟨c_p2_mid, hstep_p2, hpc_eq, hstate_eq⟩ :=
        Step.of_concat_right_bounded hbounded2 hpc_ge hpc_lt hstep
      have hpc_ge_rest : p1.length ≤ c_rest.pc := by omega
      obtain ⟨c_p2_final, hsteps_rest, hhalted_final⟩ := ih hpc_ge_rest
      have hrest_pc : c_rest.pc - p1.length = c_p2_mid.pc := by omega
      have hrest_state : c_rest.state = c_p2_mid.state := hstate_eq
      rw [hrest_pc, hrest_state] at hsteps_rest
      have hconfig_eq : (⟨c_p2_mid.pc, c_p2_mid.state⟩ : Config) = c_p2_mid := rfl
      rw [hconfig_eq] at hsteps_rest
      exact ⟨c_p2_final, Relation.ReflTransGen.head hstep_p2 hsteps_rest, hhalted_final⟩

theorem halts_at_boundary_implies_p2_halts {p1 p2 : Program} {σ : State}
    (hbounded2 : p2.boundedJumps)
    (hsteps : ∃ c', Steps (p1.concat p2) ⟨p1.length, σ⟩ c' ∧ c'.isHalted (p1.concat p2)) :
    ∃ c, Steps p2 ⟨0, σ⟩ c ∧ c.isHalted p2 := by
  obtain ⟨c', hsteps', hhalted'⟩ := hsteps
  have hpc_ge : p1.length ≤ (⟨p1.length, σ⟩ : Config).pc := le_refl _
  obtain ⟨c_p2, hsteps_p2, hhalted_p2⟩ := halts_at_boundary_aux hbounded2 hpc_ge hsteps' hhalted'
  simp only [Nat.sub_self] at hsteps_p2
  exact ⟨c_p2, hsteps_p2, hhalted_p2⟩

/-- Extract p2 halting from p1.concat p2 halting. -/
theorem steps_extract_second_bounded {p1 p2 : Program} {σ : State}
    (hbounded1 : p1.boundedJumps)
    (hbounded2 : p2.boundedJumps)
    (h_concat : ∃ c, Steps (p1.concat p2) ⟨0, σ⟩ c ∧ c.isHalted (p1.concat p2))
    (h1 : ∃ c, Steps p1 ⟨0, σ⟩ c ∧ c.isHalted p1) :
    ∃ c, Steps p2 ⟨0, (Classical.choose h1).state⟩ c ∧ c.isHalted p2 := by
  obtain ⟨c_final, hsteps_concat, hhalted_concat⟩ := h_concat
  obtain ⟨hsteps1, hhalted1⟩ := Classical.choose_spec h1
  have hstart_le : (0 : ℕ) ≤ p1.length := Nat.zero_le _
  obtain ⟨c_mid, hsteps_to_mid, hmid_pc, hsteps_from_mid⟩ :=
    Steps.reaches_boundary hbounded1 hsteps_concat hstart_le hhalted_concat
  have hc_mid_state : c_mid.state = (Classical.choose h1).state := by
    have hunique := Steps.halts_unique hsteps_to_mid (by simp [Config.isHalted]; omega)
                      hsteps1 hhalted1
    simp only [hunique]
  have hc_mid_eq : c_mid = ⟨p1.length, (Classical.choose h1).state⟩ := by
    ext <;> simp only [hmid_pc, hc_mid_state]
  rw [hc_mid_eq] at hsteps_from_mid
  exact halts_at_boundary_implies_p2_halts hbounded2 ⟨c_final, hsteps_from_mid, hhalted_concat⟩

/-- Continuation for bounded-jump first program. -/
theorem steps_concat_continuation_bounded {p1 p2 : Program} {σ : State}
    (hbounded : p1.boundedJumps)
    (h1 : ∃ c, Steps p1 ⟨0, σ⟩ c ∧ c.isHalted p1)
    (h2 : ∃ c, Steps p2 ⟨0, (Classical.choose h1).state⟩ c ∧ c.isHalted p2) :
    ∃ c, Steps (p1.concat p2) ⟨0, σ⟩ c ∧ c.isHalted (p1.concat p2) := by
  obtain ⟨hsteps1, hhalted1⟩ := Classical.choose_spec h1
  obtain ⟨c2, hsteps2, hhalted2⟩ := h2
  have hsteps1' := Steps.concat_left_prefix (p2 := p2) hsteps1 hhalted1
  have hsteps2' := Steps.concat_right (p1 := p1) hsteps2 hhalted2
  have hc1_pc : (Classical.choose h1).pc = p1.length := by
    simp only [Config.isHalted] at hhalted1
    have hpc_le := Steps.pc_bounded hbounded hsteps1 (by simp)
    omega
  have hstart_eq : (⟨0 + p1.length, (Classical.choose h1).state⟩ : Config) =
                   ⟨(Classical.choose h1).pc, (Classical.choose h1).state⟩ := by
    simp only [Nat.zero_add, hc1_pc]
  rw [hstart_eq] at hsteps2'
  have hsteps_total := Relation.ReflTransGen.trans hsteps1' hsteps2'
  refine ⟨⟨c2.pc + p1.length, c2.state⟩, hsteps_total, ?_⟩
  simp only [Config.isHalted, Program.concat_length] at hhalted2 ⊢
  omega

/-! ## clearAbove: Generalized Register Clearing

`clearAbove start maxReg` clears registers from `start` up to `maxReg`,
preserving registers 0 through `start-1`. -/

/-- Clear registers R_start through R_maxReg (preserving R_0 through R_{start-1}).
    Returns empty program if start > maxReg. -/
def Program.clearAbove (start maxReg : ℕ) : Program :=
  if start > maxReg then []
  else (List.range (maxReg - start + 1)).map fun i => Instr.Z (start + i)

@[simp]
theorem Program.clearAbove_empty (start maxReg : ℕ) (h : start > maxReg) :
    Program.clearAbove start maxReg = [] := by
  simp [clearAbove, h]

@[simp]
theorem Program.clearAbove_length (start maxReg : ℕ) :
    (Program.clearAbove start maxReg).length = if start > maxReg then 0 else maxReg - start + 1 := by
  simp only [clearAbove]
  split_ifs <;> simp

/-- clearAbove produces a straight-line program. -/
theorem Program.clearAbove_isStraightLine (start maxReg : ℕ) :
    (Program.clearAbove start maxReg).isStraightLine = true := by
  simp only [clearAbove]
  split_ifs with h
  · simp [Program.isStraightLine]
  · simp only [Program.isStraightLine, List.all_map, Function.comp_apply,
      Instr.isNonJumping, List.all_eq_true, List.mem_range]
    intro _ _
    trivial

/-- clearAbove has bounded jumps (trivially, since it has no jumps). -/
theorem Program.clearAbove_boundedJumps (start maxReg : ℕ) :
    (Program.clearAbove start maxReg).boundedJumps :=
  Program.boundedJumps_of_straightLine (clearAbove_isStraightLine start maxReg)

/-- clearAbove halts on any state. -/
theorem Program.clearAbove_halts (start maxReg : ℕ) (σ : State) :
    ∃ c, Steps (Program.clearAbove start maxReg) ⟨0, σ⟩ c ∧ c.isHalted (Program.clearAbove start maxReg) :=
  straightLine_halts_from_state (clearAbove_isStraightLine start maxReg) σ

/-- Helper: executing a list of Z instructions starting at `start` preserves registers below `start`. -/
private theorem clearAbove_aux_preserves_below (n start : ℕ) (σ : State) (r : ℕ)
    (hr : r < start) :
    (executeStraightLine ((List.range n).map fun i => Instr.Z (start + i)) σ).read r = σ.read r := by
  induction n generalizing σ with
  | zero => simp [executeStraightLine]
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      executeStraightLine_append]
    simp only [executeStraightLine, List.foldl, State.read, State.write]
    have hne : r ≠ start + k := by omega
    rw [Function.update_of_ne hne]
    exact ih σ

/-- clearAbove preserves registers below start. -/
theorem Program.clearAbove_preserves_below (start maxReg : ℕ) (σ : State) (r : ℕ)
    (hr : r < start) :
    (executeStraightLine (Program.clearAbove start maxReg) σ).read r = σ.read r := by
  -- clearAbove only writes to registers >= start, so r < start is preserved
  simp only [clearAbove]
  split_ifs with h
  · simp [executeStraightLine]
  · -- The program zeroes registers start, start+1, ..., maxReg
    -- Since r < start, none of these Z instructions affect r
    exact clearAbove_aux_preserves_below (maxReg - start + 1) start σ r hr

/-- Helper: executing a list of Z instructions zeros the target registers. -/
private theorem clearAbove_aux_zeros (n start : ℕ) (σ : State) (r : ℕ)
    (hr_ge : start ≤ r) (hr_lt : r < start + n) :
    (executeStraightLine ((List.range n).map fun i => Instr.Z (start + i)) σ).read r = 0 := by
  induction n generalizing σ r with
  | zero => omega
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      executeStraightLine_append]
    simp only [executeStraightLine, List.foldl, State.read, State.write]
    by_cases heq : r = start + k
    · -- r is the register being zeroed in this step
      subst heq
      exact Function.update_self _ _ _
    · -- r was zeroed earlier
      have hr_lt_k : r < start + k := by omega
      rw [Function.update_of_ne heq]
      exact ih σ r hr_ge hr_lt_k

/-- clearAbove zeros registers in range [start, maxReg]. -/
theorem Program.clearAbove_zeros (start maxReg : ℕ) (σ : State) (r : ℕ)
    (hr_ge : start ≤ r) (hr_le : r ≤ maxReg) :
    (executeStraightLine (Program.clearAbove start maxReg) σ).read r = 0 := by
  -- clearAbove zeros registers start through maxReg
  simp only [clearAbove]
  split_ifs with h
  · omega
  · -- r is in the range [start, maxReg], so it gets zeroed
    -- The range is [start, start + (maxReg - start + 1) - 1] = [start, maxReg]
    have hr_lt : r < start + (maxReg - start + 1) := by omega
    exact clearAbove_aux_zeros (maxReg - start + 1) start σ r hr_ge hr_lt

/-- Zero registers R1 through maxReg (preserving R0). Empty if maxReg = 0. -/
def Program.clearScratch (maxReg : ℕ) : Program :=
  if maxReg = 0 then []
  else (List.range maxReg).map fun i => Instr.Z (i + 1)

/-- clearScratch is just clearAbove 1 (with matching structures). -/
theorem Program.clearScratch_eq_clearAbove (maxReg : ℕ) (h : maxReg ≥ 1) :
    Program.clearScratch maxReg = Program.clearAbove 1 maxReg := by
  -- Both produce Z instructions for registers 1 through maxReg
  -- clearScratch: Z (0+1), Z (1+1), ..., Z ((maxReg-1)+1)
  -- clearAbove 1: Z (1+0), Z (1+1), ..., Z (1+(maxReg-1))
  sorry

end Urm
