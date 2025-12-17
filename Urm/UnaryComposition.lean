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

/-- In a bounded-jump program, a halting execution ends at exactly pc = length.
    pc ≤ length by bounded execution, pc ≥ length by halting definition. -/
theorem Halts.pc_eq_length {p : Program} {inputs : List ℕ}
    (hbounded : p.boundedJumps) (hhalts : Halts p inputs) :
    (Classical.choose hhalts).pc = p.length := by
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec hhalts
  have hpc_le := Steps.pc_bounded hbounded hsteps (by simp [Config.init])
  simp only [Config.isHalted] at hhalted
  omega

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
    simp only [Program.concat, Program.getInstr] at h
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
    (hσ : ∃ c', Steps p ⟨0, σ⟩ c' ∧ c'.isHalted p) :
    Halts p [y] := by
  -- Build config agreement in the other direction
  have hconfig_agree : (⟨0, σ⟩ : Config).agreesLow (Config.init [y]) p := by
    constructor
    · simp [Config.init]
    · exact hagree
  obtain ⟨c_σ, hsteps_σ, hhalted_σ⟩ := hσ
  -- Mirror execution from σ to fresh
  obtain ⟨c_fresh, hsteps_fresh, hagree'⟩ := Steps.preserves_agreesLow hconfig_agree hsteps_σ
  refine ⟨c_fresh, hsteps_fresh, ?_⟩
  simp only [Config.isHalted] at hhalted_σ ⊢
  -- hagree'.1 : c_σ.pc = c_fresh.pc, so c_fresh.pc = c_σ.pc ≥ p.length
  rw [← hagree'.1]
  exact hhalted_σ

/-- Concatenation of bounded-jump programs has bounded jumps. -/
theorem Program.concat_boundedJumps {p1 p2 : Program}
    (h1 : p1.boundedJumps) (h2 : p2.boundedJumps) :
    (p1.concat p2).boundedJumps := by
  intro i m n q hinstr
  simp only [Program.concat, Program.getInstr] at hinstr
  by_cases hi : i < p1.length
  · -- Instruction from p1
    simp only [List.getElem?_append_left hi] at hinstr
    have hq := h1 i m n q hinstr
    simp only [Program.concat_length]
    omega
  · -- Instruction from p2.shiftJumps p1.length
    simp only [not_lt] at hi
    simp only [List.getElem?_append_right hi, Program.shiftJumps, List.getElem?_map] at hinstr
    cases hp2 : p2.getInstr (i - p1.length) with
    | none =>
      simp only [Program.getInstr] at hp2
      simp only [hp2, Option.map_none] at hinstr
      cases hinstr  -- none ≠ some, contradiction
    | some instr =>
      simp only [Program.getInstr] at hp2
      simp only [hp2, Option.map_some, Option.some.injEq] at hinstr
      cases instr with
      | J m' n' q' =>
        simp only [Instr.shiftJumps, Instr.J.injEq] at hinstr
        obtain ⟨hm_eq, hn_eq, hq_eq⟩ := hinstr
        have hq' := h2 (i - p1.length) m' n' q' hp2
        simp only [Program.concat_length]
        subst hm_eq hn_eq hq_eq
        omega
      | Z _ => simp only [Instr.shiftJumps] at hinstr; cases hinstr
      | S _ => simp only [Instr.shiftJumps] at hinstr; cases hinstr
      | T _ _ => simp only [Instr.shiftJumps] at hinstr; cases hinstr

/-! ## Scratch Register Clearing

For composition, after Pg halts we need to clear scratch registers (R1 through
Pf.maxRegister) before running Pf. This ensures the state agrees with a fresh
input state on all registers that Pf might read. -/

/-- Zero registers R1 through maxReg (preserving R0). Empty if maxReg = 0. -/
def Program.clearScratch (maxReg : ℕ) : Program :=
  if maxReg = 0 then []
  else (List.range maxReg).map fun i => Instr.Z (i + 1)

@[simp]
theorem Program.clearScratch_zero : Program.clearScratch 0 = [] := by
  simp [Program.clearScratch]

@[simp]
theorem Program.clearScratch_length (maxReg : ℕ) :
    (Program.clearScratch maxReg).length = if maxReg = 0 then 0 else maxReg := by
  simp [Program.clearScratch]
  split_ifs <;> simp

/-- clearScratch produces a straight-line program. -/
theorem Program.clearScratch_isStraightLine (maxReg : ℕ) :
    (Program.clearScratch maxReg).isStraightLine = true := by
  simp only [clearScratch]
  split_ifs with h
  · simp [Program.isStraightLine]
  · -- Show all Z instructions are non-jumping
    simp only [Program.isStraightLine, List.all_map, Function.comp_apply,
      Instr.isNonJumping, List.all_eq_true, List.mem_range]
    intro _ _
    trivial

/-- clearScratch has bounded jumps (trivially, since it has no jumps). -/
theorem Program.clearScratch_boundedJumps (maxReg : ℕ) :
    (Program.clearScratch maxReg).boundedJumps :=
  Program.boundedJumps_of_straightLine (clearScratch_isStraightLine maxReg)

/-- clearScratch halts on any inputs. -/
theorem Program.clearScratch_halts (maxReg : ℕ) (inputs : List ℕ) :
    Halts (Program.clearScratch maxReg) inputs :=
  straightLine_halts (clearScratch_isStraightLine maxReg) inputs

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
      -- Z instruction: pc += 1
      simp only [Program.getInstr] at hinstr
      have hlt := List.getElem?_eq_some_iff.mp hinstr |>.1
      simp only at ih ⊢
      omega
    | succ hinstr =>
      -- S instruction: pc += 1
      simp only [Program.getInstr] at hinstr
      have hlt := List.getElem?_eq_some_iff.mp hinstr |>.1
      simp only at ih ⊢
      omega
    | trans hinstr =>
      -- T instruction: pc += 1
      simp only [Program.getInstr] at hinstr
      have hlt := List.getElem?_eq_some_iff.mp hinstr |>.1
      simp only at ih ⊢
      omega
    | jump_eq hinstr _ =>
      -- J instruction in straight-line program: contradiction
      simp only [Program.getInstr] at hinstr
      have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
      have hmem : (Instr.J _ _ _) ∈ p := heq ▸ List.getElem_mem hlt
      exact absurd (hsl _ hmem) (by simp [Instr.isNonJumping])
    | jump_ne hinstr _ =>
      -- J instruction in straight-line program: contradiction
      simp only [Program.getInstr] at hinstr
      have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
      have hmem : (Instr.J _ _ _) ∈ p := heq ▸ List.getElem_mem hlt
      exact absurd (hsl _ hmem) (by simp [Instr.isNonJumping])

/-- Helper: executing a list of Z instructions preserves R0 if they all target > 0. -/
private theorem clearScratch_aux_preserves_R0 (n : ℕ) (σ : State) :
    (executeStraightLine ((List.range n).map fun i => Instr.Z (i + 1)) σ).read 0 = σ.read 0 := by
  induction n generalizing σ with
  | zero => simp [executeStraightLine]
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      executeStraightLine_append]
    simp only [executeStraightLine, List.foldl, State.read, State.write]
    have hne : (0 : ℕ) ≠ k + 1 := by omega
    rw [Function.update_of_ne hne]
    exact ih σ

/-- Execute clearScratch to get the final state. -/
theorem Program.clearScratch_exec (maxReg : ℕ) (σ : State) :
    (executeStraightLine (Program.clearScratch maxReg) σ).read 0 = σ.read 0 := by
  simp only [clearScratch]
  split_ifs with h
  · simp [executeStraightLine]
  · exact clearScratch_aux_preserves_R0 maxReg σ

/-- Helper: after running Z instructions for R1..Rn, register r (1 ≤ r ≤ n) is 0. -/
private theorem clearScratch_aux_zeros (n : ℕ) (σ : State) (r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ n) :
    (executeStraightLine ((List.range n).map fun i => Instr.Z (i + 1)) σ).read r = 0 := by
  induction n generalizing σ r with
  | zero => omega
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      executeStraightLine_append]
    simp only [executeStraightLine, List.foldl, State.read, State.write]
    by_cases heq : r = k + 1
    · -- r = k + 1, the last instruction zeroed it
      subst heq
      rw [Function.update_self]
    · -- r ≠ k + 1, so r ≤ k
      have hr_le_k : r ≤ k := by omega
      rw [Function.update_of_ne heq]
      exact ih σ r hr1 hr_le_k

/-- After clearScratch, registers 1 through maxReg are 0. -/
theorem Program.clearScratch_zeros (maxReg : ℕ) (σ : State) (r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ maxReg) :
    (executeStraightLine (Program.clearScratch maxReg) σ).read r = 0 := by
  simp only [clearScratch]
  split_ifs with h
  · omega
  · exact clearScratch_aux_zeros maxReg σ r hr1 hr2

/-- After clearScratch with R0 = y, state agrees with fromInputs [y] on low registers. -/
theorem Program.clearScratch_agreesLow (maxReg : ℕ) (σ : State) (y : ℕ)
    (hR0 : σ.read 0 = y) :
    (executeStraightLine (Program.clearScratch maxReg) σ).agreesLow
      (State.fromInputs [y]) maxReg := by
  intro r hr
  by_cases hr0 : r = 0
  · -- R0: preserved by clearScratch, and fromInputs [y] has y at R0
    subst hr0
    rw [clearScratch_exec, hR0]
    simp only [State.fromInputs, State.read, List.getD, List.getElem?_cons_zero, Option.getD_some]
  · -- R1..maxReg: zeroed by clearScratch, and fromInputs [y] has 0
    have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    rw [clearScratch_zeros maxReg σ r hr1 hr]
    simp only [State.fromInputs, State.read, List.getD]
    have hlen : ([y] : List ℕ).length ≤ r := by simp; exact hr1
    have hout : [y][r]? = none := List.getElem?_eq_none hlen
    simp only [hout, Option.getD_none]

/-! ## Continuation from Arbitrary States

For composition, we need to chain programs starting from arbitrary states, not just
Config.init. These lemmas generalize the Halts.concat_continuation infrastructure. -/

/-- For straight-line programs, the final state from `straightLine_halts_from_state`
equals `executeStraightLine`. This connects step-based and fold-based semantics.

This is a technical lemma showing that step-based execution (via Steps) produces
the same state as fold-based execution (via executeStraightLine) for programs
without jump instructions. The proof requires showing that after p.length steps,
the state equals foldl over all instructions. -/
-- Helper: for straight-line programs, if we step from pc=k to a halted config,
-- the final state equals executeStraightLine (p.drop k) applied to the starting state.
private theorem straightLine_step_state_drop {p : Program} {k : ℕ} {σ : State} {c' : Config}
    (hsl : p.isStraightLine = true)
    (hsteps : Steps p ⟨k, σ⟩ c')
    (hhalted : c'.isHalted p) :
    c'.state = executeStraightLine (p.drop k) σ := by
  generalize hrem : p.length - k = remaining
  induction remaining generalizing k σ c' with
  | zero =>
    have hk : k = p.length ∨ k > p.length := by omega
    cases hk with
    | inl hk_eq =>
      -- k = p.length, so ⟨k, σ⟩ is already halted
      have hhalted_start : (⟨k, σ⟩ : Config).isHalted p := by
        simp only [Config.isHalted, hk_eq]; exact le_refl _
      -- By halted_no_step, no steps can be taken, so c' = ⟨k, σ⟩
      cases hsteps using Relation.ReflTransGen.head_induction_on with
      | refl =>
        simp only [hk_eq, List.drop_length, executeStraightLine, List.foldl]
      | head hstep _ =>
        exact absurd hstep (Step.halted_no_step hhalted_start)
    | inr hk_gt =>
      -- k > p.length, same reasoning
      have hhalted_start : (⟨k, σ⟩ : Config).isHalted p := by
        simp only [Config.isHalted]; omega
      cases hsteps using Relation.ReflTransGen.head_induction_on with
      | refl =>
        simp only [List.drop_eq_nil_of_le (by omega : p.length ≤ k),
                   executeStraightLine, List.foldl]
      | head hstep _ =>
        exact absurd hstep (Step.halted_no_step hhalted_start)
  | succ rem ih =>
    have hk_lt : k < p.length := by omega
    -- Get the instruction at pc = k
    have hinstr_exists : ∃ instr, p.getInstr k = some instr := by
      simp only [Program.getInstr]
      exact ⟨p[k], List.getElem?_eq_getElem hk_lt⟩
    obtain ⟨instr, hinstr⟩ := hinstr_exists
    -- The instruction is non-jumping
    have hnonjump : instr.isNonJumping = true := by
      simp only [Program.isStraightLine, List.all_eq_true] at hsl
      have hmem : instr ∈ p := by
        simp only [Program.getInstr] at hinstr
        exact List.getElem?_eq_some_iff.mp hinstr |>.2 ▸ List.getElem_mem hk_lt
      exact hsl instr hmem
    -- The configuration ⟨k, σ⟩ is not halted
    have hstart_not_halted : ¬(⟨k, σ⟩ : Config).isHalted p := by
      simp only [Config.isHalted]; omega
    -- Since it's not halted, there must be at least one step
    cases hsteps using Relation.ReflTransGen.head_induction_on with
    | refl =>
      -- c' = ⟨k, σ⟩, but it's halted (contradiction since k < p.length)
      simp only [Config.isHalted] at hhalted
      omega
    | head hstep hrest =>
      -- hstep : Step p ⟨k, σ⟩ c_mid, hrest : Steps p c_mid c'
      -- By the structure of the step on a non-jump instruction:
      cases hstep with
      | zero h =>
        -- New state is σ.write n 0, new pc is k+1
        rename_i n
        have hrem' : p.length - (k + 1) = rem := by omega
        have hstate_eq := ih hrest hhalted hrem'
        simp only [List.drop_eq_getElem_cons hk_lt, executeStraightLine, List.foldl] at hstate_eq ⊢
        simp only [Program.getInstr, List.getElem?_eq_getElem hk_lt, Option.some.injEq] at h
        simp only [h, hstate_eq]
      | succ h =>
        rename_i n
        have hrem' : p.length - (k + 1) = rem := by omega
        have hstate_eq := ih hrest hhalted hrem'
        simp only [List.drop_eq_getElem_cons hk_lt, executeStraightLine, List.foldl] at hstate_eq ⊢
        simp only [Program.getInstr, List.getElem?_eq_getElem hk_lt, Option.some.injEq] at h
        simp only [h, hstate_eq]
      | trans h =>
        rename_i m n
        have hrem' : p.length - (k + 1) = rem := by omega
        have hstate_eq := ih hrest hhalted hrem'
        simp only [List.drop_eq_getElem_cons hk_lt, executeStraightLine, List.foldl] at hstate_eq ⊢
        simp only [Program.getInstr, List.getElem?_eq_getElem hk_lt, Option.some.injEq] at h
        simp only [h, hstate_eq]
      | jump_eq h _ =>
        -- This case is impossible for straight-line programs
        rename_i m n q
        simp only [Program.getInstr, List.getElem?_eq_getElem hk_lt, Option.some.injEq] at hinstr h
        rw [h] at hinstr
        subst hinstr
        simp only [Instr.isNonJumping] at hnonjump
        contradiction
      | jump_ne h _ =>
        -- This case is impossible for straight-line programs
        rename_i m n q
        simp only [Program.getInstr, List.getElem?_eq_getElem hk_lt, Option.some.injEq] at hinstr h
        rw [h] at hinstr
        subst hinstr
        simp only [Instr.isNonJumping] at hnonjump
        contradiction

theorem straightLine_final_state_eq {p : Program} (hsl : p.isStraightLine = true) (σ : State) :
    let h := straightLine_halts_from_state hsl σ
    (Classical.choose h).state = executeStraightLine p σ := by
  have h := straightLine_halts_from_state hsl σ
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec h
  have := straightLine_step_state_drop hsl hsteps hhalted
  simp only [List.drop_zero] at this
  exact this

/-- Continuation for straight-line first program (always ends at pc = length). -/
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
    -- Show pc ≤ length from the steps (straight-line programs only increment pc)
    suffices hsuff : (Classical.choose h1).pc ≤ p1.length by omega
    -- Use straightLine_halts_from_state_at_length for the upper bound
    -- The chosen config from h1 should have the same pc as the one from straightLine_halts_from_state
    have hsteps_from := straightLine_halts_from_state hsl1 σ
    have hpc_eq := straightLine_halts_from_state_at_length hsl1 σ
    -- Both h1 and hsteps_from start from the same config and reach halted configs
    -- By uniqueness of halted configs (Steps.halts_unique), they must be the same
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

/-- Reverse of Step.concat_right: stepping in concat from p2 range gives step in p2.
    Requires bounded jumps to ensure the step stays in range or halts. -/
theorem Step.of_concat_right_bounded {p1 p2 : Program} {pc : ℕ} {σ : State} {c' : Config}
    (_hbounded : p2.boundedJumps)
    (hpc_ge : p1.length ≤ pc)
    (hpc_lt : pc < p1.length + p2.length)
    (hstep : Step (p1.concat p2) ⟨pc, σ⟩ c') :
    ∃ c2 : Config, Step p2 ⟨pc - p1.length, σ⟩ c2 ∧ c'.pc = c2.pc + p1.length ∧ c'.state = c2.state := by
  -- Relate instruction in concat to shifted instruction in p2
  have hinstr_eq : (p1.concat p2).getInstr pc = (p2.shiftJumps p1.length).getInstr (pc - p1.length) :=
    Program.getInstr_concat_right pc hpc_ge hpc_lt
  have hinstr_shift : (p2.shiftJumps p1.length).getInstr (pc - p1.length) =
      (p2.getInstr (pc - p1.length)).map (Instr.shiftJumps p1.length) :=
    Program.getInstr_shiftJumps p1.length p2 (pc - p1.length)
  -- Case split on the step type and use the instruction relation
  cases hstep with
  | zero h =>
    rename_i n
    rw [hinstr_eq, hinstr_shift] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨instr, hinstr, heq⟩ := h
    cases instr with
    | Z n' =>
      simp only [Instr.shiftJumps] at heq
      cases heq  -- After this, n' = n
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
      cases heq  -- After this, n' = n
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

/-- Helper: translate execution from the p2 region to p2.
    Given Steps (p1.concat p2) c c' where c.pc ≥ p1.length and c' is halted,
    produces Steps p2 (corresponding p2 config) (halted p2 config). -/
private theorem halts_at_boundary_aux {p1 p2 : Program} {c c' : Config}
    (hbounded2 : p2.boundedJumps)
    (hpc_ge : p1.length ≤ c.pc)
    (hsteps : Steps (p1.concat p2) c c')
    (hhalted : c'.isHalted (p1.concat p2)) :
    ∃ c_p2, Steps p2 ⟨c.pc - p1.length, c.state⟩ c_p2 ∧ c_p2.isHalted p2 := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- In refl case, c = c', and the goal is stated in terms of c'
    simp only [Config.isHalted, Program.concat_length] at hhalted
    refine ⟨⟨c'.pc - p1.length, c'.state⟩, Relation.ReflTransGen.refl, ?_⟩
    simp only [Config.isHalted]
    omega
  | @head c_mid c_rest hstep hrest ih =>
    -- In this case, the original c is now c_mid
    -- c_mid → c_rest → ... → c', and IH is about c_rest → c'
    by_cases hhalted_c : c_mid.pc ≥ p1.length + p2.length
    · -- c_mid is already halted in the p2 sense
      refine ⟨⟨c_mid.pc - p1.length, c_mid.state⟩, Relation.ReflTransGen.refl, ?_⟩
      simp only [Config.isHalted]
      omega
    · -- c_mid.pc < p1.length + p2.length, can extract a step
      have hpc_lt : c_mid.pc < p1.length + p2.length := by omega
      obtain ⟨c_p2_mid, hstep_p2, hpc_eq, hstate_eq⟩ :=
        Step.of_concat_right_bounded hbounded2 hpc_ge hpc_lt hstep
      -- hpc_eq : c_rest.pc = c_p2_mid.pc + p1.length
      -- hstate_eq : c_rest.state = c_p2_mid.state
      -- For IH, we need p1.length ≤ c_rest.pc
      have hpc_ge_rest : p1.length ≤ c_rest.pc := by omega
      -- Apply IH to c_rest → c'
      obtain ⟨c_p2_final, hsteps_rest, hhalted_final⟩ := ih hpc_ge_rest
      -- hsteps_rest : Steps p2 ⟨c_rest.pc - p1.length, c_rest.state⟩ c_p2_final
      -- Rewrite to start from c_p2_mid
      have hrest_pc : c_rest.pc - p1.length = c_p2_mid.pc := by omega
      have hrest_state : c_rest.state = c_p2_mid.state := hstate_eq
      rw [hrest_pc, hrest_state] at hsteps_rest
      -- Now hsteps_rest : Steps p2 ⟨c_p2_mid.pc, c_p2_mid.state⟩ c_p2_final
      -- But we need ⟨c_p2_mid.pc, c_p2_mid.state⟩ = c_p2_mid
      have hconfig_eq : (⟨c_p2_mid.pc, c_p2_mid.state⟩ : Config) = c_p2_mid := rfl
      rw [hconfig_eq] at hsteps_rest
      -- Chain the steps
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

/-- If p1.concat p2 halts from state σ and p1 has bounded jumps,
then p2 halts from p1's final state. This is the "extraction" lemma. -/
theorem steps_extract_second_bounded {p1 p2 : Program} {σ : State}
    (hbounded1 : p1.boundedJumps)
    (hbounded2 : p2.boundedJumps)
    (h_concat : ∃ c, Steps (p1.concat p2) ⟨0, σ⟩ c ∧ c.isHalted (p1.concat p2))
    (h1 : ∃ c, Steps p1 ⟨0, σ⟩ c ∧ c.isHalted p1) :
    ∃ c, Steps p2 ⟨0, (Classical.choose h1).state⟩ c ∧ c.isHalted p2 := by
  obtain ⟨c_final, hsteps_concat, hhalted_concat⟩ := h_concat
  obtain ⟨hsteps1, hhalted1⟩ := Classical.choose_spec h1
  -- Use reaches_boundary to find when execution crosses from p1 to p2
  have hstart_le : (0 : ℕ) ≤ p1.length := Nat.zero_le _
  obtain ⟨c_mid, hsteps_to_mid, hmid_pc, hsteps_from_mid⟩ :=
    Steps.reaches_boundary hbounded1 hsteps_concat hstart_le hhalted_concat
  -- c_mid is at the boundary: c_mid.pc = p1.length
  -- By uniqueness of halted configs in p1, c_mid.state = (Classical.choose h1).state
  have hc_mid_state : c_mid.state = (Classical.choose h1).state := by
    have hunique := Steps.halts_unique hsteps_to_mid (by simp [Config.isHalted]; omega)
                      hsteps1 hhalted1
    simp only [hunique]
  -- c_mid = ⟨p1.length, (Classical.choose h1).state⟩
  have hc_mid_eq : c_mid = ⟨p1.length, (Classical.choose h1).state⟩ := by
    ext <;> simp only [hmid_pc, hc_mid_state]
  -- Use halts_at_boundary_implies_p2_halts
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
  -- Lift p1's steps to the concatenation
  have hsteps1' := Steps.concat_left_prefix (p2 := p2) hsteps1 hhalted1
  -- Lift p2's steps to the concatenation
  have hsteps2' := Steps.concat_right (p1 := p1) hsteps2 hhalted2
  -- For bounded-jump programs, halted pc = length
  have hc1_pc : (Classical.choose h1).pc = p1.length := by
    simp only [Config.isHalted] at hhalted1
    have hpc_le := Steps.pc_bounded hbounded hsteps1 (by simp)
    omega
  -- Connect the two step sequences
  have hstart_eq : (⟨0 + p1.length, (Classical.choose h1).state⟩ : Config) =
                   ⟨(Classical.choose h1).pc, (Classical.choose h1).state⟩ := by
    simp only [Nat.zero_add, hc1_pc]
  rw [hstart_eq] at hsteps2'
  have hsteps_total := Relation.ReflTransGen.trans hsteps1' hsteps2'
  refine ⟨⟨c2.pc + p1.length, c2.state⟩, hsteps_total, ?_⟩
  simp only [Config.isHalted, Program.concat_length] at hhalted2 ⊢
  omega

/-! ## Main Composition Theorem -/

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
  -- The composed program: Pg, then clear scratch, then Pf
  -- Clearing ensures Pf sees a state that agrees with fresh state on low registers
  let clear := Program.clearScratch Pf.maxRegister
  let H := Pg.concat (clear.concat Pf)
  use H
  intro x
  constructor
  -- Part 1: Halts H [x] ↔ ((g x).bind f).Dom
  · constructor
    -- Forward: Halts H [x] → ((g x).bind f).Dom
    · intro hH_halts
      -- H = Pg.concat (clear.concat Pf), with Pg bounded
      -- Extract that Pg halts
      have hclear_bounded : clear.boundedJumps := Program.clearScratch_boundedJumps _
      have hclear_Pf_bounded : (clear.concat Pf).boundedJumps :=
        Program.concat_boundedJumps hclear_bounded hPf_bounded
      have hPg_halts : Halts Pg [x] := Halts.of_concat_left_bounded hPg_bounded hH_halts
      -- So g x is defined
      have hg_dom : (g x).Dom := (hPg x).1.mp hPg_halts
      -- Prove by contradiction: assume f(g(x)) is not defined
      by_contra hf_not_dom
      -- Then Pf doesn't halt from fresh [g(x).get]
      have hPf_not_halts : ¬Halts Pf [(g x).get hg_dom] := by
        intro hPf_halts
        have hf_dom := (hPf ((g x).get hg_dom)).1.mp hPf_halts
        have hbind_dom : ((g x).bind f).Dom := Part.bind_dom.mpr ⟨hg_dom, hf_dom⟩
        exact hf_not_dom hbind_dom
      -- Setup: Pg halts at pc = Pg.length
      have hPg_pc : (Classical.choose hPg_halts).pc = Pg.length :=
        Halts.pc_eq_length hPg_bounded hPg_halts
      let σ_Pg := (Classical.choose hPg_halts).state
      have hR0_Pg : σ_Pg.read 0 = (g x).get hg_dom := by
        simp only [σ_Pg]
        exact (hPg x).2 hPg_halts hg_dom
      -- Clear halts and produces a state agreeing with fresh [g(x).get]
      have hclear_sl := Program.clearScratch_isStraightLine Pf.maxRegister
      have hclear_from_state : ∃ c, Steps clear ⟨0, σ_Pg⟩ c ∧ c.isHalted clear :=
        straightLine_halts_from_state hclear_sl σ_Pg
      have hclear_state_eq := straightLine_final_state_eq hclear_sl σ_Pg
      have hagree_cleared : (executeStraightLine clear σ_Pg).agreesLow
          (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister :=
        Program.clearScratch_agreesLow Pf.maxRegister σ_Pg ((g x).get hg_dom) hR0_Pg
      have hagree_cleared' : (Classical.choose hclear_from_state).state.agreesLow
          (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister := by
        rw [hclear_state_eq]; exact hagree_cleared
      -- By contrapositive of Halts.to_agreesLow: if Pf doesn't halt from fresh,
      -- then Pf doesn't halt from the cleared state either
      have hPf_not_from_cleared : ¬∃ c', Steps Pf ⟨0, (Classical.choose hclear_from_state).state⟩ c' ∧ c'.isHalted Pf := by
        intro ⟨c', hsteps', hhalted'⟩
        exact hPf_not_halts (Halts.to_agreesLow hagree_cleared' ⟨c', hsteps', hhalted'⟩)
      -- Now we need to show H can't halt, contradicting hH_halts
      -- If clear.concat Pf halts from σ_Pg, then Pf must halt from the cleared state
      -- (since clear always halts and leaves us at pc = clear.length)
      -- Get the halting config for clear from σ_Pg
      have hclear_pc := straightLine_halts_from_state_at_length hclear_sl σ_Pg
      -- If clear.concat Pf were to halt from σ_Pg, after clear's execution,
      -- we'd be at pc = clear.length, and Pf would need to halt from there
      -- Since Pf doesn't halt from the cleared state, clear.concat Pf can't halt
      -- For now, we use a simpler argument via extracting second halting
      -- Since H = Pg.concat (clear.concat Pf) halts, and Pg halts (bounded),
      -- we can extract that clear.concat Pf halts from σ_Pg
      -- Get existence for H halting
      obtain ⟨c_H, hsteps_H, hhalted_H⟩ := hH_halts
      -- Get existence for Pg halting
      have hPg_halts_exists : ∃ c, Steps Pg (Config.init [x]) c ∧ c.isHalted Pg := hPg_halts
      -- Use reaches_boundary to find the boundary where execution enters clear.concat Pf
      obtain ⟨c_mid, hsteps_to_mid, hmid_pc, hsteps_from_mid⟩ :=
        Steps.reaches_boundary hPg_bounded hsteps_H (by simp [Config.init]) hhalted_H
      -- c_mid is at pc = Pg.length, state = σ_Pg (by uniqueness)
      have hc_mid_state : c_mid.state = σ_Pg := by
        have hsteps1 := (Classical.choose_spec hPg_halts).1
        have hhalted1 := (Classical.choose_spec hPg_halts).2
        have hunique := Steps.halts_unique hsteps_to_mid (by simp [Config.isHalted]; omega) hsteps1 hhalted1
        simp only [hunique, σ_Pg]
      -- hsteps_from_mid : Steps H c_mid c_H, where H = Pg.concat (clear.concat Pf)
      -- and c_mid.pc = Pg.length
      -- This means c_mid is at the start of clear.concat Pf in the concatenation
      -- For the execution to halt, clear.concat Pf must have led to halting
      -- Since Pf doesn't halt from the cleared state, we have a contradiction
      -- The key observation: once at pc = Pg.length, execution is entirely within
      -- (clear.concat Pf)'s code. For execution to reach a halted state in H,
      -- the execution in the clear.concat Pf region must also reach a halted state
      -- (i.e., pc ≥ Pg.length + clear.length + Pf.length)
      -- This means Pf halted, but we showed it doesn't - contradiction
      -- Since this is getting complex, we'll use the key insight more directly:
      -- The backward direction shows that if (g x).bind f is defined, then H halts.
      -- By contrapositive: if ¬((g x).bind f).Dom, then ¬Halts H [x].
      -- But we have hH_halts, so (g x).bind f must be defined.
      -- This is a proof by contradiction that completes the forward direction.
      exfalso
      -- We need to show that Pf must halt from the cleared state, contradicting hPf_not_from_cleared
      -- Step 1: c_mid is at the boundary, so we can apply halts_at_boundary_implies_p2_halts
      -- to extract that (clear.concat Pf) halts from σ_Pg
      have hc_mid_eq : c_mid = ⟨Pg.length, σ_Pg⟩ := by
        cases c_mid
        simp only at hmid_pc hc_mid_state
        simp only [hmid_pc, hc_mid_state]
      rw [hc_mid_eq] at hsteps_from_mid
      -- clear.concat Pf has bounded jumps
      have hclear_Pf_halts_from_boundary :
          ∃ c, Steps (clear.concat Pf) ⟨0, σ_Pg⟩ c ∧ c.isHalted (clear.concat Pf) :=
        halts_at_boundary_implies_p2_halts hclear_Pf_bounded ⟨c_H, hsteps_from_mid, hhalted_H⟩
      -- Step 2: From clear.concat Pf halting, extract that Pf halts from the cleared state
      -- clear has bounded jumps (straight-line)
      have hclear_bounded := Program.clearScratch_boundedJumps Pf.maxRegister
      -- clear halts from σ_Pg
      have hclear_from_σ_Pg : ∃ c, Steps clear ⟨0, σ_Pg⟩ c ∧ c.isHalted clear :=
        straightLine_halts_from_state hclear_sl σ_Pg
      -- Extract Pf halting from clear.concat Pf halting
      have hPf_halts_from_cleared :=
        steps_extract_second_bounded hclear_bounded hPf_bounded hclear_Pf_halts_from_boundary hclear_from_σ_Pg
      -- The cleared state matches what we computed
      have hclear_state_same : (Classical.choose hclear_from_σ_Pg).state =
          (Classical.choose hclear_from_state).state := by
        -- Both come from the same straight-line execution from σ_Pg
        have h1_steps := (Classical.choose_spec hclear_from_σ_Pg).1
        have h1_halted := (Classical.choose_spec hclear_from_σ_Pg).2
        have h2_steps := (Classical.choose_spec hclear_from_state).1
        have h2_halted := (Classical.choose_spec hclear_from_state).2
        have hunique := Steps.halts_unique h1_steps h1_halted h2_steps h2_halted
        simp only [hunique]
      -- Step 3: This contradicts hPf_not_from_cleared
      rw [← hclear_state_same] at hPf_not_from_cleared
      exact hPf_not_from_cleared hPf_halts_from_cleared
    -- Backward: ((g x).bind f).Dom → Halts H [x]
    · intro hdom
      -- (g x).bind f is defined means g x is defined and f (g x).get is defined
      have hg_dom : (g x).Dom := Part.bind_dom.mp hdom |>.1
      have hf_dom : (f ((g x).get hg_dom)).Dom := Part.bind_dom.mp hdom |>.2
      -- Pg halts on [x]
      have hPg_halts : Halts Pg [x] := (hPg x).1.mpr hg_dom
      -- Pf halts on [g(x)] when started fresh (Config.init)
      have hPf_halts : Halts Pf [(g x).get hg_dom] := (hPf ((g x).get hg_dom)).1.mpr hf_dom
      -- Result Pg [x] = g(x).get
      have hPg_result : Result Pg [x] hPg_halts = (g x).get hg_dom :=
        (hPg x).2 hPg_halts hg_dom
      -- Pg halts at pc = Pg.length (from bounded jumps)
      have hPg_pc : (Classical.choose hPg_halts).pc = Pg.length :=
        Halts.pc_eq_length hPg_bounded hPg_halts
      -- State after Pg
      let σ_Pg := (Classical.choose hPg_halts).state
      have hR0_Pg : σ_Pg.read 0 = (g x).get hg_dom := by
        simp only [σ_Pg, Result, State.output] at hPg_result ⊢
        exact hPg_result
      -- Clear halts from σ_Pg (straight-line)
      have hclear_sl := Program.clearScratch_isStraightLine Pf.maxRegister
      have hclear_from_state : ∃ c, Steps clear ⟨0, σ_Pg⟩ c ∧ c.isHalted clear :=
        straightLine_halts_from_state hclear_sl σ_Pg
      -- The cleared state equals executeStraightLine
      have hclear_state_eq := straightLine_final_state_eq hclear_sl σ_Pg
      -- After clearing, state agrees with fresh [g(x).get] on low registers
      have hagree_cleared : (executeStraightLine clear σ_Pg).agreesLow
          (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister :=
        Program.clearScratch_agreesLow Pf.maxRegister σ_Pg ((g x).get hg_dom) hR0_Pg
      -- Convert to agreement for the Steps-based state
      have hagree_cleared' : (Classical.choose hclear_from_state).state.agreesLow
          (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister := by
        rw [hclear_state_eq]
        exact hagree_cleared
      -- By Halts.of_agreesLow, Pf halts from the cleared state
      have hPf_from_cleared := Halts.of_agreesLow hagree_cleared' hPf_halts
      obtain ⟨c_Pf, hsteps_Pf, hhalted_Pf, _⟩ := hPf_from_cleared
      -- Chain: clear.concat Pf halts from σ_Pg
      have hclear_Pf_from_state : ∃ c, Steps (clear.concat Pf) ⟨0, σ_Pg⟩ c ∧ c.isHalted (clear.concat Pf) :=
        steps_concat_continuation_straightLine hclear_sl hclear_from_state ⟨c_Pf, hsteps_Pf, hhalted_Pf⟩
      -- Use Halts.concat_continuation to chain Pg with (clear.concat Pf)
      exact Halts.concat_continuation hPg_halts hPg_pc hclear_Pf_from_state
  -- Part 2: Results match
  · intro hH_halts hdom
    -- Need: Result H [x] hH_halts = ((g x).bind f).get hdom
    -- By definition of bind: ((g x).bind f).get hdom = f ((g x).get hg_dom)).get hf_dom
    -- H = Pg; clear; Pf. After Pg, R0 = g(x). Clearing preserves R0.
    -- Pf then runs, and by Halts.of_agreesLow, its output equals f(g(x)).
    have hg_dom : (g x).Dom := Part.bind_dom.mp hdom |>.1
    have hf_dom : (f ((g x).get hg_dom)).Dom := Part.bind_dom.mp hdom |>.2
    -- Setup: same as backward direction
    have hPg_halts : Halts Pg [x] := (hPg x).1.mpr hg_dom
    have hPf_halts : Halts Pf [(g x).get hg_dom] := (hPf ((g x).get hg_dom)).1.mpr hf_dom
    have hPg_result : Result Pg [x] hPg_halts = (g x).get hg_dom := (hPg x).2 hPg_halts hg_dom
    have hPf_result : Result Pf [(g x).get hg_dom] hPf_halts = (f ((g x).get hg_dom)).get hf_dom :=
      (hPf ((g x).get hg_dom)).2 hPf_halts hf_dom
    have hPg_pc : (Classical.choose hPg_halts).pc = Pg.length := Halts.pc_eq_length hPg_bounded hPg_halts
    let σ_Pg := (Classical.choose hPg_halts).state
    have hR0_Pg : σ_Pg.read 0 = (g x).get hg_dom := by
      simp only [σ_Pg, Result, State.output] at hPg_result ⊢; exact hPg_result
    -- Clear halts and its state equals executeStraightLine
    have hclear_sl := Program.clearScratch_isStraightLine Pf.maxRegister
    have hclear_from_state : ∃ c, Steps clear ⟨0, σ_Pg⟩ c ∧ c.isHalted clear :=
      straightLine_halts_from_state hclear_sl σ_Pg
    have hclear_state_eq := straightLine_final_state_eq hclear_sl σ_Pg
    -- Cleared state agrees with fresh [g(x).get]
    have hagree_cleared : (executeStraightLine clear σ_Pg).agreesLow
        (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister :=
      Program.clearScratch_agreesLow Pf.maxRegister σ_Pg ((g x).get hg_dom) hR0_Pg
    have hagree_cleared' : (Classical.choose hclear_from_state).state.agreesLow
        (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister := by
      rw [hclear_state_eq]; exact hagree_cleared
    -- Pf from cleared state gives the same output as from fresh
    have hPf_from_cleared := Halts.of_agreesLow hagree_cleared' hPf_halts
    obtain ⟨c_Pf, hsteps_Pf, hhalted_Pf, hR0_Pf⟩ := hPf_from_cleared
    -- The key: c_Pf.state.read 0 = Result Pf [(g x).get hg_dom] hPf_halts = f(g(x)).get
    have hPf_output : c_Pf.state.read 0 = (f ((g x).get hg_dom)).get hf_dom := by
      rw [hR0_Pf]; exact hPf_result
    -- Now we need to show Result H [x] hH_halts = c_Pf.state.read 0
    -- The halted config for H must have the same R0 as c_Pf (lifted to the concat)
    -- This follows from uniqueness of halted configs and the chaining
    -- For now, we use the key insight that the final R0 matches
    simp only [Result, State.output]
    -- The final state of H is determined by the execution path:
    -- Pg → clear → Pf, and R0 at the end = f(g(x)).get
    -- This is a technical proof connecting the Classical.choose for hH_halts
    -- to the composed execution. We use that the halted config is unique.
    -- Since the backward direction constructs the same execution path,
    -- and halted configs are unique, the result must match.
    -- For technical simplicity, we show this via bind.get equality
    have hbind_get : ((g x).bind f).get hdom = (f ((g x).get hg_dom)).get hf_dom := by
      have heq := Part.Dom.bind hg_dom f
      simp only [heq]
    rw [hbind_get, ← hPf_output]
    -- Now we need: (Classical.choose hH_halts).state.read 0 = c_Pf.state.read 0
    -- We construct the explicit halted config for H and use halts_unique.
    -- After lifting: Pf's execution from cleared state lifts to clear.concat Pf,
    -- then that lifts to H = Pg.concat (clear.concat Pf).
    -- The final config is ⟨c_Pf.pc + Pg.length + clear.length, c_Pf.state⟩
    -- which is halted in H since c_Pf.isHalted Pf.
    -- By halts_unique, this equals Classical.choose hH_halts.
    -- Build the halted config for clear.concat Pf
    have hPf_pc_ge : Pf.length ≤ c_Pf.pc := hhalted_Pf
    have hsteps_Pf' : Steps (clear.concat Pf) ⟨clear.length, (Classical.choose hclear_from_state).state⟩
        ⟨c_Pf.pc + clear.length, c_Pf.state⟩ := by
      have := Steps.concat_right (p1 := clear) hsteps_Pf hhalted_Pf
      simp only [Nat.zero_add] at this
      exact this
    have hhalted_Pf' : (⟨c_Pf.pc + clear.length, c_Pf.state⟩ : Config).isHalted (clear.concat Pf) := by
      simp only [Config.isHalted, Program.concat_length]
      omega
    -- Get the halted config from clear (using Classical.choose)
    let c_clear := Classical.choose hclear_from_state
    have hclear_spec := Classical.choose_spec hclear_from_state
    have hsteps_clear : Steps clear ⟨0, σ_Pg⟩ c_clear := hclear_spec.1
    have hhalted_clear : c_clear.isHalted clear := hclear_spec.2
    have hclear_pc : c_clear.pc = clear.length :=
      straightLine_halts_from_state_at_length hclear_sl σ_Pg
    -- Chain clear and Pf in clear.concat Pf
    have hsteps_clear' : Steps (clear.concat Pf) ⟨0, σ_Pg⟩ c_clear := by
      exact Steps.concat_left_prefix (p2 := Pf) hsteps_clear hhalted_clear
    have hsteps_clear_start : (⟨clear.length, c_clear.state⟩ : Config) =
        ⟨c_clear.pc, c_clear.state⟩ := by
      simp only [hclear_pc]
    rw [hsteps_clear_start] at hsteps_Pf'
    have hsteps_clearPf : Steps (clear.concat Pf) ⟨0, σ_Pg⟩ ⟨c_Pf.pc + clear.length, c_Pf.state⟩ :=
      Steps.trans hsteps_clear' hsteps_Pf'
    -- Now lift to H = Pg.concat (clear.concat Pf)
    have hsteps_clearPf' : Steps H ⟨Pg.length, σ_Pg⟩ ⟨c_Pf.pc + clear.length + Pg.length, c_Pf.state⟩ := by
      have := Steps.concat_right (p1 := Pg) hsteps_clearPf hhalted_Pf'
      simp only [Nat.zero_add] at this
      convert this using 2
    have hhalted_H' : (⟨c_Pf.pc + clear.length + Pg.length, c_Pf.state⟩ : Config).isHalted H := by
      simp only [Config.isHalted, H, Program.concat_length]
      omega
    -- Get the halted config from Pg
    obtain ⟨hsteps_Pg, hhalted_Pg⟩ := Classical.choose_spec hPg_halts
    have hsteps_Pg' : Steps H (Config.init [x]) (Classical.choose hPg_halts) := by
      exact Steps.concat_left_prefix (p2 := clear.concat Pf) hsteps_Pg hhalted_Pg
    have hstart_eq : (⟨Pg.length, σ_Pg⟩ : Config) = Classical.choose hPg_halts := by
      ext
      · exact hPg_pc.symm
      · rfl
    rw [hstart_eq] at hsteps_clearPf'
    have hsteps_H : Steps H (Config.init [x]) ⟨c_Pf.pc + clear.length + Pg.length, c_Pf.state⟩ :=
      Steps.trans hsteps_Pg' hsteps_clearPf'
    -- By uniqueness, Classical.choose hH_halts equals this config
    obtain ⟨hsteps_choose, hhalted_choose⟩ := Classical.choose_spec hH_halts
    have hunique := Steps.halts_unique hsteps_choose hhalted_choose hsteps_H hhalted_H'
    -- Extract the state equality
    have hstate_eq : (Classical.choose hH_halts).state = c_Pf.state := by
      rw [hunique]
    simp only [hstate_eq, State.read]

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
