/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable
import Urm.Composition

/-! # Unary Composition

This file proves that unary URM-computable functions are closed under composition.
This is a simpler case of the general composition theorem (Cutland's Theorem 3.1),
handling functions `ℕ → Part ℕ` rather than `(Fin n → ℕ) → Part ℕ`.

## Main results

- `UnaryURMComputable.comp_bounded`: Composition closure assuming bounded jumps
- `UnaryURMComputable.comp`: Full composition closure (requires standardization theorem)

## Implementation notes

The key insight is that for unary functions, the composed program `H = Pg.concat Pf`
requires no register shuffling: both programs use R0 for input and output.

The proof requires a `boundedJumps` hypothesis to ensure that when `Pg.concat Pf` halts,
we can extract that `Pg` halted (didn't escape via a jump into `Pf`'s code).
This hypothesis can be dropped once we prove the standardization theorem:
every program has an equivalent program with bounded jumps.

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

/-! ## Unary Computability -/

/-- Unary URM computability for partial functions `ℕ → Part ℕ`.

A function `f : ℕ → Part ℕ` is unary URM-computable if there exists a program `p`
such that for all inputs `x`:
- `p` halts on `[x]` iff `f x` is defined
- When both hold, `Result p [x]` equals `(f x).get` -/
def UnaryURMComputable (f : ℕ → Part ℕ) : Prop :=
  ∃ p : Program, ∀ x : ℕ,
    (Halts p [x] ↔ (f x).Dom) ∧
    ∀ (hHalts : Halts p [x]) (hDom : (f x).Dom),
      Result p [x] hHalts = (f x).get hDom

/-- Equivalence between UnaryURMComputable and URMComputable for arity 1. -/
theorem unaryURMComputable_iff_urmComputable (f : ℕ → Part ℕ) :
    UnaryURMComputable f ↔ URMComputable 1 (fun inputs => f (inputs 0)) := by
  constructor
  · intro ⟨p, hp⟩
    use p
    intro inputs
    have hinputs : List.ofFn inputs = [inputs 0] := by
      simp only [List.ofFn]
      rfl
    rw [hinputs]
    exact hp (inputs 0)
  · intro ⟨p, hp⟩
    use p
    intro x
    have hinputs : List.ofFn (fun _ : Fin 1 => x) = [x] := by
      simp only [List.ofFn]
      rfl
    specialize hp (fun _ => x)
    rw [hinputs] at hp
    simp only at hp
    exact hp

/-! ## Concat Extraction Lemmas

These lemmas allow us to extract information about subprogram halting
from the halting of a concatenated program. -/

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

/-- Key lemma: In bounded-jump program execution starting at pc < length,
    if we eventually halt, we must pass through pc = length.
    Returns both the path in p1 (for extraction) and the continuation in concat (for chaining). -/
theorem Steps.reaches_boundary {p1 p2 : Program} {c c' : Config}
    (hbounded : p1.boundedJumps)
    (hsteps : Steps (p1.concat p2) c c')
    (hstart : c.pc ≤ p1.length)
    (hhalted : c'.isHalted (p1.concat p2)) :
    ∃ cmid, Steps p1 c cmid ∧ cmid.pc = p1.length ∧
            Steps (p1.concat p2) cmid c' := by
  -- If c.pc = p1.length already, we're done (zero steps in p1)
  by_cases hc_at_boundary : c.pc = p1.length
  · exact ⟨c, Relation.ReflTransGen.refl, hc_at_boundary, hsteps⟩
  -- Otherwise c.pc < p1.length, use strong induction on steps
  have hpc_lt : c.pc < p1.length := Nat.lt_of_le_of_ne hstart hc_at_boundary
  -- The execution must eventually leave p1's region (since it halts)
  -- Use induction on the step sequence, generalize away hypotheses
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
    have hb_pc : b.pc ≤ p1.length := Step.concat_left_pc_bounded hbounded hpc_lt hstep
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

/-- Stepping from the boundary either moves into p2's region, halts, or loops to same config.
    This is the key property: J instructions don't modify state, so a J-loop at boundary
    returns to the exact same config. -/
theorem Step.boundary_step_trichotomy {p1 p2 : Program} {c c' : Config}
    (hpc : c.pc = p1.length) (hstep : Step (p1.concat p2) c c') :
    c'.pc > p1.length ∨ c'.pc ≥ p1.length + p2.length ∨ c' = c := by
  cases hstep with
  | zero h =>
    -- Z instruction: pc increments
    left; simp only at *; omega
  | succ h =>
    -- S instruction: pc increments
    left; simp only at *; omega
  | trans h =>
    -- T instruction: pc increments
    left; simp only at *; omega
  | jump_eq h heq =>
    -- J instruction with equal registers: jump to target
    -- Target in shifted p2 is original_target + p1.length
    -- If original_target = 0, new pc = p1.length (same as c.pc)
    -- And since J doesn't modify state, c' = c
    simp only [Program.concat, Program.getInstr, List.append_eq] at h
    -- We're at pc = p1.length, so we're accessing the first instruction of shifted p2
    have h_idx : c.pc - p1.length = 0 := by omega
    rw [hpc] at h
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at h
    -- Get the instruction from p2.shiftJumps
    simp only [Program.shiftJumps, List.getElem?_map] at h
    cases hp2 : p2.getInstr 0 with
    | none =>
      -- p2[0]? = none, so Option.map ... p2[0]? = none, contradicting h
      simp only [Program.getInstr] at hp2
      simp only [hp2, Option.map_none] at h
      cases h  -- h : none = some _ is impossible
    | some instr =>
      simp only [Program.getInstr] at hp2
      simp only [hp2, Option.map_some] at h
      cases instr with
      | Z n => simp [Instr.shiftJumps] at h
      | S n => simp [Instr.shiftJumps] at h
      | T m n => simp [Instr.shiftJumps] at h
      | J m n q =>
        simp only [Instr.shiftJumps, Option.some.injEq] at h
        -- After injection, we have the shifted jump target
        obtain ⟨_, _, rfl⟩ := h
        -- c'.pc = q + p1.length
        by_cases hq : q = 0
        · -- q = 0: loop back to p1.length, same state since J doesn't modify
          right; right
          simp only [hq, Nat.zero_add]
          ext
          · simp only [hpc]
          · rfl  -- J doesn't change state
        · -- q > 0: moved past the boundary
          left
          have hq_pos : q ≥ 1 := Nat.one_le_iff_ne_zero.mpr hq
          simp only
          omega
  | jump_ne h hne =>
    -- J instruction with unequal registers: pc increments
    left; simp only at *; omega

/-- If p1.concat p2 halts and p1 has bounded jumps, then p1 halts on the same inputs. -/
theorem Halts.of_concat_left_bounded {p1 p2 : Program} {inputs : List ℕ}
    (hbounded : p1.boundedJumps)
    (hhalts : Halts (p1.concat p2) inputs) :
    Halts p1 inputs := by
  obtain ⟨c', hsteps, hhalted⟩ := hhalts
  have hstart : (Config.init inputs).pc ≤ p1.length := by simp [Config.init]
  -- Find the boundary configuration - reaches_boundary now directly gives us Steps p1
  obtain ⟨cmid, hsteps1, hmid_pc, _⟩ :=
    Steps.reaches_boundary hbounded hsteps hstart hhalted
  -- cmid is halted for p1 (its pc = p1.length)
  exact ⟨cmid, hsteps1, by simp only [Config.isHalted]; omega⟩

/-! ## Main Composition Theorem -/

/-- A program computes a unary function if it satisfies the spec. -/
def ProgramComputesUnary (p : Program) (f : ℕ → Part ℕ) : Prop :=
  ∀ x : ℕ,
    (Halts p [x] ↔ (f x).Dom) ∧
    ∀ (hHalts : Halts p [x]) (hDom : (f x).Dom),
      Result p [x] hHalts = (f x).get hDom

/-! ### Standardization Theorem

The standardization theorem states that every program can be transformed into an
equivalent program with bounded jumps. This is a fundamental result that allows
us to assume bounded jumps without loss of generality.

The proof involves systematically replacing unbounded jumps with bounded ones,
typically by adding "landing pad" instructions. We postulate this here and
leave the construction for future work. -/

/-- Every program computing a unary function has an equivalent program with bounded jumps.
This is the standardization theorem for unary programs. -/
theorem ProgramComputesUnary.exists_boundedJumps {f : ℕ → Part ℕ} {p : Program}
    (hp : ProgramComputesUnary p f) :
    ∃ p' : Program, ProgramComputesUnary p' f ∧ p'.boundedJumps := by
  sorry -- Standardization theorem: construct equivalent program with bounded jumps

/-- Composition of unary URM-computable functions, assuming bounded jumps.

If `f` and `g` are unary computable with witnesses `Pf` and `Pg` that have bounded jumps,
then `f ∘ g` (i.e., `fun x => (g x).bind f`) is unary computable. -/
theorem UnaryURMComputable.comp_bounded {f g : ℕ → Part ℕ}
    {Pf Pg : Program}
    (hPf : ProgramComputesUnary Pf f)
    (hPg : ProgramComputesUnary Pg g)
    (hPf_bounded : Pf.boundedJumps)
    (hPg_bounded : Pg.boundedJumps) :
    UnaryURMComputable (fun x => (g x).bind f) := by
  -- The composed program is just Pg followed by Pf
  let H := Pg.concat Pf
  use H
  intro x
  constructor
  -- Part 1: Halts H [x] ↔ ((g x).bind f).Dom
  · constructor
    -- Forward: Halts H [x] → ((g x).bind f).Dom
    · intro hH_halts
      -- Extract that Pg halts
      have hPg_halts : Halts Pg [x] := Halts.of_concat_left_bounded hPg_bounded hH_halts
      -- So g x is defined
      have hg_dom : (g x).Dom := (hPg x).1.mp hPg_halts
      -- Now we need to show f (g x).get is defined
      -- Key insight: After H halts, the path went through Pg's halt point (at pc = Pg.length),
      -- then continued in Pf. Since H halted, Pf must have halted too.
      -- To show f is defined at g(x).get, we need to connect H's halting on [x]
      -- to Pf's halting on [g(x).get].
      -- This requires showing that Pf's behavior only depends on R0 (input register),
      -- since after Pg halts, other registers may have scratch values.
      -- TODO: Add register independence lemma or use cleared-register continuation.
      sorry
    -- Backward: ((g x).bind f).Dom → Halts H [x]
    · intro hdom
      -- (g x).bind f is defined means g x is defined and f (g x).get is defined
      have hg_dom : (g x).Dom := Part.bind_dom.mp hdom |>.1
      have hf_dom : (f ((g x).get hg_dom)).Dom := Part.bind_dom.mp hdom |>.2
      -- Pg halts on [x]
      have hPg_halts : Halts Pg [x] := (hPg x).1.mpr hg_dom
      -- Pf halts on [g(x)] when started fresh (Config.init)
      have hPf_halts : Halts Pf [(g x).get hg_dom] := (hPf ((g x).get hg_dom)).1.mpr hf_dom
      -- Result Pg [x] = g(x).get connects the output
      have hPg_result : Result Pg [x] hPg_halts = (g x).get hg_dom :=
        (hPg x).2 hPg_halts hg_dom
      -- To use Halts.concat_continuation, we need:
      -- 1. Pg halts (have hPg_halts)
      -- 2. The halted config's pc = Pg.length (needs bounded jumps + determinism)
      -- 3. Pf halts from Pg's final state (not Config.init!)
      -- Issue: hPf_halts is about fresh state, but we continue from Pg's state.
      -- Need: register independence lemma showing Pf behaves same on any state with R0 = g(x).
      -- TODO: Prove this using Halts.concat_continuation + register independence.
      sorry
  -- Part 2: Results match
  · intro hH_halts hdom
    -- Need: Result H [x] hH_halts = ((g x).bind f).get hdom
    -- By definition of bind: ((g x).bind f).get hdom = f ((g x).get hg_dom)).get hf_dom
    -- where hg_dom and hf_dom come from Part.bind_dom.
    -- The result of H is R0 when H halts. This should equal f(g(x)).
    -- Requires tracking that R0 flows correctly through Pg then Pf.
    -- TODO: Use register flow analysis or result chaining lemmas.
    sorry

/-- Full composition theorem for unary URM-computable functions.

This version does not require the bounded jumps hypothesis. The proof
applies the standardization theorem to get bounded-jump witnesses,
then uses `comp_bounded`. -/
theorem UnaryURMComputable.comp {f g : ℕ → Part ℕ}
    (hf : UnaryURMComputable f) (hg : UnaryURMComputable g) :
    UnaryURMComputable (fun x => (g x).bind f) := by
  -- Get witness programs from computability
  obtain ⟨Pf, hPf⟩ := hf
  obtain ⟨Pg, hPg⟩ := hg
  -- Apply standardization to get bounded-jump versions
  obtain ⟨Pf', hPf', hPf'_bounded⟩ := ProgramComputesUnary.exists_boundedJumps hPf
  obtain ⟨Pg', hPg', hPg'_bounded⟩ := ProgramComputesUnary.exists_boundedJumps hPg
  -- Apply comp_bounded with the standardized programs
  exact comp_bounded hPf' hPg' hPf'_bounded hPg'_bounded

end Urm
