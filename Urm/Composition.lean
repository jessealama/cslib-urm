/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable

/-! # Composition of URM-Computable Functions

This file proves that URM-computable functions are closed under composition.

## Main definitions

- `Urm.composePartial`: Composition of partial functions
- `Urm.Program.seq`: Sequential composition of URM programs

## Main statements

- `Urm.URMComputable.comp`: Composition of URM-computable functions is URM-computable

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980],
  Chapter 2, Theorem 2.1
-/

namespace Urm

/-! ## Program Combinators -/

namespace Program

/-- Sequential composition of programs: run `p1`, then run `p2`.
Jump targets in `p2` are shifted by `p1.length` so they remain valid. -/
def seq (p1 p2 : Program) : Program :=
  p1 ++ p2.shiftJumps p1.length

@[simp]
theorem seq_length (p1 p2 : Program) : (p1.seq p2).length = p1.length + p2.length := by
  simp [seq, shiftJumps]

theorem seq_getInstr_first (p1 p2 : Program) (i : ℕ) (hi : i < p1.length) :
    (p1.seq p2).getInstr i = p1.getInstr i := by
  simp only [seq, getInstr, List.getElem?_append_left hi]

theorem seq_getInstr_second (p1 p2 : Program) (i : ℕ) (hi : p1.length ≤ i)
    (_hi' : i < p1.length + p2.length) :
    (p1.seq p2).getInstr i = (p2.shiftJumps p1.length).getInstr (i - p1.length) := by
  simp only [seq, getInstr, List.getElem?_append_right hi, shiftJumps, List.getElem?_map]

end Program

/-! ## Register Copy Operations -/

/-- Copy a single register value from `src` to `dst`. -/
def copyReg (src dst : ℕ) : Program := [Instr.T src dst]

/-- Copy `n` consecutive registers starting from `srcBase` to `dstBase`.
Copies srcBase → dstBase, srcBase+1 → dstBase+1, ..., srcBase+(n-1) → dstBase+(n-1). -/
def copyRegs (n : ℕ) (srcBase dstBase : ℕ) : Program :=
  (List.finRange n).map fun i => Instr.T (srcBase + i.val) (dstBase + i.val)

@[simp]
theorem copyRegs_length (n srcBase dstBase : ℕ) : (copyRegs n srcBase dstBase).length = n := by
  simp [copyRegs]

/-- Zero out a single register. -/
def zeroReg (n : ℕ) : Program := [Instr.Z n]

/-! ## Composition of Partial Functions -/

/-- Collect outputs from partial functions into a vector.
Returns `Part.some outputs` if all functions are defined, where `outputs i = (g i inputs).get _`.
Returns `Part.none` if any function is undefined. -/
def collectOutputs {m n : ℕ} (g : Fin m → (Fin n → ℕ) → Part ℕ) (inputs : Fin n → ℕ) :
    Part (Fin m → ℕ) :=
  Part.mk
    (∀ i, (g i inputs).Dom)
    (fun h => fun i => (g i inputs).get (h i))

/-- Composition of partial functions: `h(x) = f(g₀(x), ..., gₘ₋₁(x))`.

The composition is defined (has a value) iff:
- All `gᵢ(x)` are defined, and
- `f` is defined on the collected outputs `(g₀(x), ..., gₘ₋₁(x))`

This follows the standard definition of composition for partial functions. -/
def composePartial {m n : ℕ}
    (f : (Fin m → ℕ) → Part ℕ)
    (g : Fin m → (Fin n → ℕ) → Part ℕ) : (Fin n → ℕ) → Part ℕ :=
  fun inputs => (collectOutputs g inputs).bind f

theorem collectOutputs_dom {m n : ℕ}
    {g : Fin m → (Fin n → ℕ) → Part ℕ} {inputs : Fin n → ℕ} :
    (collectOutputs g inputs).Dom ↔ ∀ i, (g i inputs).Dom := by
  simp only [collectOutputs]

theorem collectOutputs_get {m n : ℕ}
    {g : Fin m → (Fin n → ℕ) → Part ℕ} {inputs : Fin n → ℕ}
    (h : (collectOutputs g inputs).Dom) (i : Fin m) :
    (collectOutputs g inputs).get h i = (g i inputs).get (collectOutputs_dom.mp h i) := by
  simp only [collectOutputs]

theorem composePartial_dom {m n : ℕ}
    {f : (Fin m → ℕ) → Part ℕ} {g : Fin m → (Fin n → ℕ) → Part ℕ}
    {inputs : Fin n → ℕ} :
    (composePartial f g inputs).Dom ↔
      (∀ i, (g i inputs).Dom) ∧
      ∃ (hg : ∀ i, (g i inputs).Dom), (f (fun i => (g i inputs).get (hg i))).Dom := by
  simp only [composePartial, Part.bind_dom, collectOutputs_dom]
  constructor
  · intro ⟨hg, hf⟩
    exact ⟨hg, hg, hf⟩
  · intro ⟨hg, _, hf⟩
    exact ⟨hg, hf⟩

/-! ## Lemmas about Shifted Programs -/

namespace Instr

/-- Shifting jump targets by 0 is the identity. -/
@[simp]
theorem shiftJumps_zero (i : Instr) : i.shiftJumps 0 = i := by
  cases i <;> simp [shiftJumps]

end Instr

namespace Program

/-- Shifting all jump targets in a program by 0 is the identity. -/
@[simp]
theorem shiftJumps_zero (p : Program) : p.shiftJumps 0 = p := by
  simp only [shiftJumps]
  induction p with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, Instr.shiftJumps_zero, ih]

end Program

namespace Step

variable {p : Program}

/-- If `i < p.length`, the instruction at `i` in the shifted program is the shifted instruction. -/
theorem shiftJumps_getInstr (offset : ℕ) (i : ℕ) (_hi : i < p.length) :
    (p.shiftJumps offset).getInstr i = (p.getInstr i).map (Instr.shiftJumps offset) := by
  simp only [Program.shiftJumps, Program.getInstr, List.getElem?_map]

theorem shiftRegisters_getInstr (offset : ℕ) (i : ℕ) (_hi : i < p.length) :
    (p.shiftRegisters offset).getInstr i = (p.getInstr i).map (Instr.shiftRegisters offset) := by
  simp only [Program.shiftRegisters, Program.getInstr, List.getElem?_map]

end Step

/-! ## Execution in Sequential Programs -/

namespace Steps

variable {p₁ p₂ : Program}

/-- A step in `p₁` is also a step in `p₁.seq p₂`, as long as we stay within `p₁`. -/
theorem seq_step_first {c c' : Config} (hstep : Step p₁ c c') (hpc : c.pc < p₁.length) :
    Step (p₁.seq p₂) c c' := by
  cases hstep with
  | zero h =>
    have heq : (p₁.seq p₂).getInstr c.pc = p₁.getInstr c.pc :=
      Program.seq_getInstr_first p₁ p₂ c.pc hpc
    exact Step.zero (heq ▸ h)
  | succ h =>
    have heq : (p₁.seq p₂).getInstr c.pc = p₁.getInstr c.pc :=
      Program.seq_getInstr_first p₁ p₂ c.pc hpc
    exact Step.succ (heq ▸ h)
  | trans h =>
    have heq : (p₁.seq p₂).getInstr c.pc = p₁.getInstr c.pc :=
      Program.seq_getInstr_first p₁ p₂ c.pc hpc
    exact Step.trans (heq ▸ h)
  | jump_eq h heq' =>
    have heq : (p₁.seq p₂).getInstr c.pc = p₁.getInstr c.pc :=
      Program.seq_getInstr_first p₁ p₂ c.pc hpc
    exact Step.jump_eq (heq ▸ h) heq'
  | jump_ne h hne =>
    have heq : (p₁.seq p₂).getInstr c.pc = p₁.getInstr c.pc :=
      Program.seq_getInstr_first p₁ p₂ c.pc hpc
    exact Step.jump_ne (heq ▸ h) hne

/-- If we can step from c, then c.pc is within the program bounds. -/
private theorem step_implies_in_bounds {c c' : Config} (hstep : Step p₁ c c') :
    c.pc < p₁.length := by
  cases hstep with
  | zero h => exact (List.getElem?_eq_some_iff.mp h).1
  | succ h => exact (List.getElem?_eq_some_iff.mp h).1
  | trans h => exact (List.getElem?_eq_some_iff.mp h).1
  | jump_eq h _ => exact (List.getElem?_eq_some_iff.mp h).1
  | jump_ne h _ => exact (List.getElem?_eq_some_iff.mp h).1

/-- Steps in `p₁` transfer to `p₁.seq p₂`, as long as we stay within `p₁`.
This is a key lemma for proving that sequential composition works correctly. -/
theorem seq_steps_first {c c' : Config} (hsteps : Steps p₁ c c')
    (hpc : c.pc < p₁.length) (_hpc' : c'.pc ≤ p₁.length) :
    Steps (p₁.seq p₂) c c' := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hstep hrest ih =>
    -- hstep : Step p₁ c c_mid
    -- hrest : Steps p₁ c_mid c'
    -- Need to show: Steps (p₁.seq p₂) c c'
    rename_i c_mid
    -- First, show the step works in the seq program
    have hstep_seq := seq_step_first (p₂ := p₂) hstep hpc
    -- Now we need to show c_mid.pc < p₁.length to continue
    -- If c_mid.pc >= p₁.length, then c_mid is halted in p₁, so hrest must be refl
    by_cases h : c_mid.pc < p₁.length
    · -- c_mid.pc < p₁.length, so we can apply IH
      exact Relation.ReflTransGen.head hstep_seq (ih h)
    · -- c_mid.pc >= p₁.length, so c_mid is halted in p₁
      -- This means c_mid = c' (hrest must be reflexive since c_mid is halted)
      have h_halted : c_mid.isHalted p₁ := Nat.not_lt.mp h
      -- Since c_mid is halted, hrest must be Relation.ReflTransGen.refl
      cases hrest using Relation.ReflTransGen.head_induction_on with
      | refl =>
        -- c_mid = c', so just one step
        exact Relation.ReflTransGen.single hstep_seq
      | head hstep' _ =>
        -- Can't step from halted config
        exact absurd hstep' (Step.halted_no_step h_halted)

/-- Get the instruction at position `offset + i` in `p₁.seq p₂` where `i < p₂.length`. -/
private theorem seq_getInstr_second_eq (p₁ p₂ : Program) (i : ℕ) (_hi : i < p₂.length) :
    (p₁.seq p₂).getInstr (p₁.length + i) = (p₂.getInstr i).map (Instr.shiftJumps p₁.length) := by
  simp only [Program.seq, Program.getInstr]
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Program.shiftJumps, List.getElem?_map, Nat.add_sub_cancel_left]

/-- A step in `p₂` at PC `i` corresponds to a step in `p₁.seq p₂` at PC `p₁.length + i`.
The key insight is that jump targets in p₂ are shifted by p₁.length, so jumps
within the second portion stay within the second portion. -/
theorem seq_step_second {c c' : Config} (hstep : Step p₂ c c') :
    Step (p₁.seq p₂) ⟨p₁.length + c.pc, c.state⟩ ⟨p₁.length + c'.pc, c'.state⟩ := by
  have hpc : c.pc < p₂.length := step_implies_in_bounds hstep
  have hinstr := seq_getInstr_second_eq p₁ p₂ c.pc hpc
  cases hstep with
  | zero h =>
    rw [h, Option.map_some] at hinstr
    simp only [Instr.shiftJumps] at hinstr
    have hstep' := Step.zero (p := p₁.seq p₂) (c := ⟨p₁.length + c.pc, c.state⟩) hinstr
    convert hstep' using 2
  | succ h =>
    rw [h, Option.map_some] at hinstr
    simp only [Instr.shiftJumps] at hinstr
    have hstep' := Step.succ (p := p₁.seq p₂) (c := ⟨p₁.length + c.pc, c.state⟩) hinstr
    convert hstep' using 2
  | trans h =>
    rw [h, Option.map_some] at hinstr
    simp only [Instr.shiftJumps] at hinstr
    have hstep' := Step.trans (p := p₁.seq p₂) (c := ⟨p₁.length + c.pc, c.state⟩) hinstr
    convert hstep' using 2
  | jump_eq h heq =>
    rw [h, Option.map_some] at hinstr
    simp only [Instr.shiftJumps] at hinstr
    have hstep' := Step.jump_eq (p := p₁.seq p₂) (c := ⟨p₁.length + c.pc, c.state⟩) hinstr heq
    convert hstep' using 2
    simp only [Nat.add_comm]
  | jump_ne h hne =>
    rw [h, Option.map_some] at hinstr
    simp only [Instr.shiftJumps] at hinstr
    have hstep' := Step.jump_ne (p := p₁.seq p₂) (c := ⟨p₁.length + c.pc, c.state⟩) hinstr hne
    convert hstep' using 2

/-- Steps in `p₂` lift to steps in `p₁.seq p₂` with PC offset by `p₁.length`. -/
theorem seq_steps_second {c c' : Config} (hsteps : Steps p₂ c c') :
    Steps (p₁.seq p₂) ⟨p₁.length + c.pc, c.state⟩ ⟨p₁.length + c'.pc, c'.state⟩ := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hstep _ ih =>
    exact Relation.ReflTransGen.head (seq_step_second hstep) ih

/-- Sequential composition of halting programs: if p₁ reaches state σ at pc = p₁.length,
and p₂ halts starting from state σ at pc = 0, then p₁.seq p₂ halts.

This directly connects the execution of two programs without requiring state agreement. -/
theorem seq_halts_compose {inputs : List ℕ} {σ : State} {c₂ : Config}
    (h₁_steps : Steps p₁ (Config.init inputs) ⟨p₁.length, σ⟩)
    (h₂_steps : Steps p₂ ⟨0, σ⟩ c₂)
    (h₂_halted : c₂.isHalted p₂) :
    Halts (p₁.seq p₂) inputs := by
  -- Build steps in p₁.seq p₂:
  -- 1. Run p₁ from init to ⟨p₁.length, σ⟩
  have hsteps₁_seq : Steps (p₁.seq p₂) (Config.init inputs) ⟨p₁.length, σ⟩ := by
    by_cases hp₁ : p₁.length = 0
    · -- p₁ is empty: steps from init to ⟨0, σ⟩ must preserve state
      -- Config.init inputs = ⟨0, σ_init⟩ and ⟨p₁.length, σ⟩ = ⟨0, σ⟩
      -- Since p₁ is empty, no steps can be taken, so σ = σ_init
      have h_eq : (Config.init inputs).pc = p₁.length := by simp [Config.init, hp₁]
      -- Check if the steps are reflexive
      have h_halted : (Config.init inputs).isHalted p₁ := by
        simp [Config.isHalted, Config.init, hp₁]
      -- If init is halted, h₁_steps must be refl
      have h_refl : Config.init inputs = ⟨p₁.length, σ⟩ :=
        halts_unique (Relation.ReflTransGen.refl) h_halted h₁_steps (by simp [Config.isHalted, hp₁])
      rw [← h_refl]
    · -- p₁ is non-empty
      apply seq_steps_first h₁_steps
      · simp [Config.init]; omega
      · exact Nat.le_refl _
  -- 2. Run p₂ from ⟨0, σ⟩ to c₂, lifted to p₁.seq p₂ from ⟨p₁.length, σ⟩
  have hsteps₂_seq : Steps (p₁.seq p₂) ⟨p₁.length, σ⟩ ⟨p₁.length + c₂.pc, c₂.state⟩ := by
    have := seq_steps_second (p₁ := p₁) h₂_steps
    simp only [Nat.add_zero] at this
    exact this
  -- Combine the two execution phases
  have hsteps_combined := trans hsteps₁_seq hsteps₂_seq
  -- Show the final config is halted in p₁.seq p₂
  have hhalted_seq : (⟨p₁.length + c₂.pc, c₂.state⟩ : Config).isHalted (p₁.seq p₂) := by
    simp only [Config.isHalted, Program.seq_length]
    -- c₂.isHalted p₂ means p₂.length ≤ c₂.pc
    -- Need: p₁.length + p₂.length ≤ p₁.length + c₂.pc
    have : p₂.length ≤ c₂.pc := h₂_halted
    omega
  exact ⟨⟨p₁.length + c₂.pc, c₂.state⟩, hsteps_combined, hhalted_seq⟩

end Steps

/-! ## Well-Formed Programs -/

/-- A program has bounded jumps if all jump targets are at most the program length.
Such programs always halt at exactly pc = p.length when they halt. -/
def JumpsBounded (p : Program) : Prop :=
  ∀ i < p.length, ∀ m n q, p.getInstr i = some (Instr.J m n q) → q ≤ p.length

namespace JumpsBounded

variable {p : Program}

/-- Empty program trivially has bounded jumps. -/
theorem nil : JumpsBounded ([] : Program) := by
  intro i hi
  simp at hi

/-- A single non-jump instruction has bounded jumps. -/
theorem singleton_nonjump (instr : Instr) (h : ∀ m n q, instr ≠ Instr.J m n q) :
    JumpsBounded [instr] := by
  intro i hi m n q hinstr
  simp only [List.length_singleton, Nat.lt_one_iff] at hi
  subst hi
  simp only [Program.getInstr, List.getElem?_cons_zero, Option.some.injEq] at hinstr
  exact absurd hinstr (h m n q)

/-- Helper: stepping preserves the invariant pc ≤ p.length when jumps are bounded. -/
private theorem step_preserves_pc_bound (hbounded : JumpsBounded p)
    {c c' : Config} (hstep : Step p c c') (_h : c.pc ≤ p.length) : c'.pc ≤ p.length := by
  -- For non-jump steps: c'.pc = c.pc + 1, and c.pc < p.length (since we can step)
  -- For jump steps: c'.pc = q, and q ≤ p.length by boundedness
  cases hstep with
  | zero hinstr =>
    have hpc := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega
  | succ hinstr =>
    have hpc := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega
  | trans hinstr =>
    have hpc := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega
  | jump_eq hinstr _ =>
    have hpc := (List.getElem?_eq_some_iff.mp hinstr).1
    exact hbounded _ hpc _ _ _ hinstr
  | jump_ne hinstr _ =>
    have hpc := (List.getElem?_eq_some_iff.mp hinstr).1
    show _ + 1 ≤ _
    omega

/-- Helper: all configs reachable from init have pc ≤ p.length when jumps are bounded. -/
private theorem pc_le_length_of_steps (hbounded : JumpsBounded p)
    {c₀ c : Config} (hsteps : Steps p c₀ c) (h₀ : c₀.pc ≤ p.length) :
    c.pc ≤ p.length := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact h₀
  | head hstep _hrest ih =>
    exact ih (step_preserves_pc_bound hbounded hstep h₀)

/-- If a program has bounded jumps and halts, it halts at exactly pc = p.length. -/
theorem halts_at_length (hbounded : JumpsBounded p)
    {inputs : List ℕ} {c : Config}
    (hsteps : Steps p (Config.init inputs) c) (hhalted : c.isHalted p) :
    c.pc = p.length := by
  have h_ge : p.length ≤ c.pc := hhalted
  have h_le : c.pc ≤ p.length := by
    apply pc_le_length_of_steps hbounded hsteps
    simp [Config.init]
  omega

end JumpsBounded

/-- Zero out registers 1 through k (used to prepare clean state for composition). -/
def clearRegsFrom1 (k : ℕ) : Program :=
  (List.range k).map fun i => Instr.Z (i + 1)

@[simp]
theorem clearRegsFrom1_length (k : ℕ) : (clearRegsFrom1 k).length = k := by
  simp [clearRegsFrom1]

/-- The instruction at position i in clearRegsFrom1 k is Z (i+1). -/
theorem clearRegsFrom1_getInstr (k i : ℕ) (hi : i < k) :
    (clearRegsFrom1 k).getInstr i = some (Instr.Z (i + 1)) := by
  simp only [clearRegsFrom1, Program.getInstr, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp; exact hi)]
  simp [List.getElem_range]

/-- clearRegsFrom1 k has bounded jumps (it has no jumps at all). -/
theorem clearRegsFrom1_bounded (k : ℕ) : JumpsBounded (clearRegsFrom1 k) := by
  intro i hi m n q hinstr
  simp only [clearRegsFrom1, Program.getInstr, List.getElem?_map] at hinstr
  rw [clearRegsFrom1_length] at hi
  rw [List.getElem?_eq_getElem (by simp; exact hi)] at hinstr
  simp only [List.getElem_range, Option.map_some] at hinstr
  -- hinstr : some (Instr.Z (i + 1)) = some (Instr.J m n q) - contradiction
  cases hinstr

/-- The clearing program halts in exactly k steps. -/
theorem clearRegsFrom1_haltsIn (k : ℕ) (inputs : List ℕ) :
    HaltsIn (clearRegsFrom1 k) k inputs := by
  -- We construct the execution: starting at PC=0, each Z instruction advances PC by 1
  -- After k steps, PC=k which equals the program length, so we're halted
  -- Define the state after executing i instructions
  let stateAfter (σ : State) (i : ℕ) := (List.range i).foldl (fun s j => s.write (j + 1) 0) σ
  -- Prove by induction that after i steps, we reach PC=i with the appropriate state
  have hsteps : ∀ i ≤ k, ∀ σ : State,
      StepsN (clearRegsFrom1 k) i ⟨0, σ⟩ ⟨i, stateAfter σ i⟩ := by
    intro i
    induction i with
    | zero =>
      intro _ σ
      simp only [stateAfter, List.range_zero, List.foldl_nil]
      exact StepsN.zero _
    | succ j ihj =>
      intro hj σ
      have hj' : j ≤ k := Nat.le_of_succ_le hj
      have hjbound : j < k := Nat.lt_of_succ_le hj
      -- First take j steps to reach PC=j
      have steps_j := ihj hj' σ
      -- Then take one more step: execute Z (j+1)
      have hinstr : (clearRegsFrom1 k).getInstr j = some (Instr.Z (j + 1)) :=
        clearRegsFrom1_getInstr k j hjbound
      have hstep : Step (clearRegsFrom1 k) ⟨j, stateAfter σ j⟩ ⟨j + 1, (stateAfter σ j).write (j + 1) 0⟩ :=
        Step.zero hinstr
      -- Show that stateAfter σ (j+1) = (stateAfter σ j).write (j+1) 0
      have hstate_eq : stateAfter σ (j + 1) = (stateAfter σ j).write (j + 1) 0 := by
        simp only [stateAfter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      -- Combine using StepsN.add
      rw [hstate_eq]
      exact StepsN.add steps_j (StepsN.succ hstep (StepsN.zero _))
  -- Apply with i = k
  refine ⟨⟨k, stateAfter (State.fromInputs inputs) k⟩, hsteps k (Nat.le_refl k) _, ?_⟩
  -- Prove halted: PC = k = length
  simp [Config.isHalted]

/-- The clearing program halts on any state. -/
theorem clearRegsFrom1_halts (k : ℕ) (inputs : List ℕ) : Halts (clearRegsFrom1 k) inputs :=
  (clearRegsFrom1_haltsIn k inputs).toHalts

/-- State after clearing registers 1..k: R[0] unchanged, R[1..k] = 0. -/
def State.clearFrom1 (σ : State) (k : ℕ) : State :=
  fun n => if n = 0 then σ 0 else if n ≤ k then 0 else σ n

/-- Helper: the foldl-based state computation equals clearFrom1. -/
private theorem foldl_write_eq_clearFrom1 (σ : State) (k : ℕ) :
    (List.range k).foldl (fun s j => s.write (j + 1) 0) σ = σ.clearFrom1 k := by
  funext n
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, State.clearFrom1]
    split_ifs with h1 h2
    · subst h1; rfl
    · omega  -- n ≠ 0 but n ≤ 0
    · rfl
  | succ k ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    -- LHS: ((foldl ... σ (range k)).write (k+1) 0) n
    -- RHS: (σ.clearFrom1 (k+1)) n
    simp only [State.clearFrom1]
    by_cases h_eq : n = k + 1
    · -- n = k+1: LHS writes 0, RHS gives 0 since n ≤ k+1
      simp only [h_eq, if_true, Nat.le_refl, if_neg (Nat.succ_ne_zero k)]
      simp only [State.write, Function.update_self]
    · -- n ≠ k+1: LHS reads from foldl result
      have h_update : ((List.range k).foldl (fun s j => s.write (j + 1) 0) σ).write (k + 1) 0 n =
                      (List.range k).foldl (fun s j => s.write (j + 1) 0) σ n := by
        simp only [State.write, Function.update, h_eq, dite_false]
      rw [h_update, ih]
      simp only [State.clearFrom1]
      -- σ.clearFrom1 k n = if n = 0 then σ 0 else if n ≤ k+1 then 0 else σ n
      -- LHS: if n = 0 then σ 0 else if n ≤ k then 0 else σ n
      split_ifs with h0 hle_k1 hle_k
      · rfl  -- n = 0
      · rfl  -- n ≠ 0, n ≤ k+1, n ≤ k: both give 0
      · omega  -- n ≠ 0, n ≤ k+1, n > k: n = k+1, contradicts h_eq
      · omega  -- n ≠ 0, n > k+1, n ≤ k: impossible
      · rfl  -- n ≠ 0, n > k+1, n > k: both give σ n

/-- Running clearRegsFrom1 k from state σ reaches state σ.clearFrom1 k at PC = k. -/
theorem clearRegsFrom1_reaches_clearFrom1 (k : ℕ) (σ : State) :
    Steps (clearRegsFrom1 k) ⟨0, σ⟩ ⟨k, σ.clearFrom1 k⟩ := by
  -- Use the same construction as clearRegsFrom1_haltsIn
  let stateAfter (σ' : State) (i : ℕ) := (List.range i).foldl (fun s j => s.write (j + 1) 0) σ'
  -- Prove steps to stateAfter σ k
  have hsteps : ∀ i ≤ k, StepsN (clearRegsFrom1 k) i ⟨0, σ⟩ ⟨i, stateAfter σ i⟩ := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [stateAfter, List.range_zero, List.foldl_nil]
      exact StepsN.zero _
    | succ j ihj =>
      intro hj
      have hj' : j ≤ k := Nat.le_of_succ_le hj
      have hjbound : j < k := Nat.lt_of_succ_le hj
      have steps_j := ihj hj'
      have hinstr : (clearRegsFrom1 k).getInstr j = some (Instr.Z (j + 1)) :=
        clearRegsFrom1_getInstr k j hjbound
      have hstep : Step (clearRegsFrom1 k) ⟨j, stateAfter σ j⟩ ⟨j + 1, (stateAfter σ j).write (j + 1) 0⟩ :=
        Step.zero hinstr
      have hstate_eq : stateAfter σ (j + 1) = (stateAfter σ j).write (j + 1) 0 := by
        simp only [stateAfter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hstate_eq]
      exact StepsN.add steps_j (StepsN.succ hstep (StepsN.zero _))
  -- stateAfter σ k = σ.clearFrom1 k by foldl_write_eq_clearFrom1
  have hstate : stateAfter σ k = σ.clearFrom1 k := foldl_write_eq_clearFrom1 σ k
  rw [← hstate]
  exact (hsteps k (Nat.le_refl _)).toSteps

/-- A cleared state agrees with `State.fromInputs [v]` on registers 0..k when R[0] = v. -/
theorem State.clearFrom1_eq_fromInputs_on_range (σ : State) (k : ℕ) (n : ℕ) (hn : n ≤ k) :
    (σ.clearFrom1 k) n = (State.fromInputs [σ 0]) n := by
  simp only [clearFrom1, fromInputs, List.getD]
  cases n with
  | zero => simp
  | succ n' =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_le_iff] at hn ⊢
    simp [hn]

/-- The output of a cleared state equals the original output. -/
@[simp]
theorem State.clearFrom1_output (σ : State) (k : ℕ) : (σ.clearFrom1 k).output = σ.output := by
  simp [clearFrom1, output]

/-! ## State Agreement Lemmas -/

/-- Two states agree on registers 0..k. -/
def State.agreeUpTo (σ₁ σ₂ : State) (k : ℕ) : Prop :=
  ∀ n, n ≤ k → σ₁ n = σ₂ n

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

/-! ## Program Construction for Composition -/

/-- Shift a state by `offset`: register `n + offset` in the shifted state
    equals register `n` in the original state. -/
def State.shift (σ : State) (offset : ℕ) : State :=
  fun n => if n < offset then 0 else σ (n - offset)

/-- Unshift a state: register `n` in the unshifted state equals register `n + offset`
    in the original state. -/
def State.unshift (σ : State) (offset : ℕ) : State :=
  fun n => σ (n + offset)

/-! ## Main Composition Theorem -/

namespace URMComputable

/-- Unary composition: compose f with a single function g.
    This is a simpler case that can be proven directly.

    The composed program:
    1. Run pg (result in R[0])
    2. Clear registers R[1..k] where k = pf.maxRegister
    3. Run pf (now sees a clean state matching State.fromInputs [v])

    Proof outline:
    - Forward direction (halting → function defined):
      * If the composed program halts, then pg must have halted (first segment)
      * After pg halts, clearing runs and halts (finite program)
      * Then pf runs and halts on the cleared state
      * By `Halts.agree_halts`, pf halting on cleared state ↔ pf halting on [v]
      * So both g and f are defined

    - Backward direction (function defined → halting):
      * If g(inputs) is defined, pg halts with R[0] = v
      * Clearing always halts
      * After clearing, state agrees with fromInputs [v] on registers 0..k
      * If f([v]) is defined, pf halts on fromInputs [v]
      * By `Halts.agree_halts`, pf halts on cleared state too
      * So the composed program halts

    - Result equality:
      * Both produce the same R[0] value by `Halts.agree_halts`

    Remaining proof obligations (marked with sorry):
    * Forward direction requires a lemma about seq programs (first must halt)
    * Standard form: programs should have bounded jumps (JumpsBounded)
      - Cutland proves every program has an equivalent standard-form program
      - All basic programs (zero, succ, proj) are naturally in standard form
    * Result equality -/
theorem comp_unary {n : ℕ}
    {f : (Fin 1 → ℕ) → Part ℕ} {g : (Fin n → ℕ) → Part ℕ}
    (hf : URMComputable 1 f) (hg : URMComputable n g) :
    URMComputable n (fun inputs => (g inputs).bind (fun v => f (fun _ => v))) := by
  -- Extract programs
  obtain ⟨pf, hpf⟩ := hf
  obtain ⟨pg, hpg⟩ := hg
  -- The composed program: run pg, clear non-R[0] registers, then run pf
  let k := pf.maxRegister
  use pg.seq ((clearRegsFrom1 k).seq pf)
  intro inputs
  let inputList := List.ofFn inputs

  -- First prove the iff for halting ↔ domain, then the result equality
  refine ⟨⟨?halts_imp_dom, ?dom_imp_halts⟩, ?result_eq⟩

  case halts_imp_dom =>
    -- Forward: Halts → Domain
    -- This direction requires showing that if composite halts, both g and f are defined
    intro hHalts

    -- The composed function is defined iff g is defined AND f is defined on g's output
    -- Goal: ((g inputs).bind (fun v => f (fun _ => v))).Dom
    -- Which unfolds to: ∃ hg : (g inputs).Dom, (f (fun _ => (g inputs).get hg)).Dom

    -- Get the halting spec for composite
    obtain ⟨cFinal, hstepsFinal, hhaltedFinal⟩ := hHalts

    -- pg halts iff g is defined
    have hgSpec := hpg inputs
    have hgIff := hgSpec.1

    -- We claim g must be defined. If not, pg doesn't halt.
    -- If pg doesn't halt, composite can't halt (pg runs first)
    -- TODO: This needs a lemma about seq programs (seq_first_must_halt)
    -- For now, we leave this direction as sorry
    sorry

  case dom_imp_halts =>
    -- Backward: Domain → Halts
    intro hDom
    simp only [Part.bind_dom] at hDom
    obtain ⟨hgDom, hfDom⟩ := hDom

    -- Get the value v = g(inputs)
    let v := (g inputs).get hgDom

    -- pg halts with output v
    have hgSpec := hpg inputs
    have hpgHalts : Halts pg inputList := hgSpec.1.mpr hgDom

    -- The result of pg is v
    have hpgResult : Result pg inputList hpgHalts = v := hgSpec.2 hpgHalts hgDom

    -- Use the chosen halted config directly
    let cg := Classical.choose hpgHalts
    have hcg_spec := Classical.choose_spec hpgHalts
    have hstepsg : Steps pg (Config.init inputList) cg := hcg_spec.1
    have hhaltedg : cg.isHalted pg := hcg_spec.2

    -- cg.state.output = v
    have hcg_output : cg.state.output = v := by
      simp only [Result, State.output] at hpgResult
      exact hpgResult

    -- Let σg = cg.state (state after pg halts)
    let σg := cg.state

    -- Run clearRegsFrom1 k from state σg
    have hclearSteps : Steps (clearRegsFrom1 k) ⟨0, σg⟩ ⟨k, σg.clearFrom1 k⟩ :=
      clearRegsFrom1_reaches_clearFrom1 k σg

    -- The cleared state agrees with fromInputs [v] on registers 0..k
    have hagree : (σg.clearFrom1 k).agreeUpTo (State.fromInputs [v]) k := by
      intro r hr
      by_cases h0 : r = 0
      · -- r = 0: cleared state gives σg 0 = v, fromInputs gives v
        subst h0
        simp only [State.clearFrom1, ↓reduceIte, State.fromInputs, List.getD, List.getElem?_cons_zero,
                   Option.getD_some]
        simp only [State.output] at hcg_output
        exact hcg_output
      · -- r > 0: both give 0
        simp only [State.clearFrom1, h0, ↓reduceIte, hr]
        simp only [State.fromInputs, List.getD]
        have hout : [v].length ≤ r := by simp; omega
        rw [List.getElem?_eq_none hout]
        simp

    -- Since k = pf.maxRegister, the cleared state agrees with fromInputs [v] on 0..pf.maxRegister
    have hagree' : (σg.clearFrom1 k).agreeUpTo (State.fromInputs [v]) pf.maxRegister := hagree

    -- pf halts on fromInputs [v] because f is defined at (fun _ => v)
    have hfSpec := hpf (fun _ => v)
    have hpfHalts : Halts pf (List.ofFn (fun _ : Fin 1 => v)) := hfSpec.1.mpr hfDom

    -- List.ofFn (fun _ : Fin 1 => v) = [v]
    have hListEq : List.ofFn (fun _ : Fin 1 => v) = [v] := by
      rfl

    have hpfHalts' : Halts pf [v] := by rw [← hListEq]; exact hpfHalts

    -- Get execution of pf from [v]
    obtain ⟨cf, hstepsf, hhaltedf⟩ := hpfHalts'

    -- Use agree_steps to get execution from σg.clearFrom1 k
    have hagreeInit : (State.fromInputs [v]).agreeUpTo (σg.clearFrom1 k) pf.maxRegister := by
      intro r hr
      exact (hagree' r hr).symm

    obtain ⟨cf', hstepsf', hpceq, _⟩ := Steps.agree_steps hstepsf hagreeInit

    -- cf' is halted because it has same PC as cf
    have hhaltedf' : cf'.isHalted pf := by
      simp only [Config.isHalted] at hhaltedf ⊢
      omega

    -- Build the inner composition steps: (clearRegsFrom1 k).seq pf
    have hinner_halts : Steps ((clearRegsFrom1 k).seq pf)
        ⟨0, σg⟩ ⟨k + cf'.pc, cf'.state⟩ := by
      by_cases hk : k = 0
      · -- k = 0: clearRegsFrom1 is empty, σg.clearFrom1 0 = σg
        simp only [hk, Nat.zero_add]
        -- clearRegsFrom1 0 = []
        have hclear_empty : clearRegsFrom1 0 = [] := by simp [clearRegsFrom1]
        -- σg.clearFrom1 0 = σg (they're equal as functions)
        have hstate_eq : σg.clearFrom1 0 = σg := by
          funext r
          simp only [State.clearFrom1]
          split_ifs with h0 hle
          · subst h0; rfl
          · omega  -- r ≠ 0 but r ≤ 0 is impossible
          · rfl
        -- The clearing program is empty, so [].seq pf = pf
        have hseq_eq : (clearRegsFrom1 0).seq pf = pf := by
          simp only [hclear_empty, Program.seq, List.nil_append, List.length_nil,
                     Program.shiftJumps_zero]
        rw [hseq_eq]
        -- hstepsf' : Steps pf ⟨0, σg.clearFrom1 k⟩ cf' with k = 0
        -- So hstepsf' : Steps pf ⟨0, σg⟩ cf'
        simp only [hk, hstate_eq, Config.init] at hstepsf'
        exact hstepsf'
      · -- k > 0: normal case
        have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
        -- First phase: clearing
        have hphase1 : Steps ((clearRegsFrom1 k).seq pf) ⟨0, σg⟩ ⟨k, σg.clearFrom1 k⟩ := by
          apply Steps.seq_steps_first hclearSteps
          · simp only [clearRegsFrom1_length]; exact hk_pos
          · simp
        -- Second phase: pf runs
        have hphase2 : Steps ((clearRegsFrom1 k).seq pf)
            ⟨k, σg.clearFrom1 k⟩
            ⟨k + cf'.pc, cf'.state⟩ := by
          have := Steps.seq_steps_second (p₁ := clearRegsFrom1 k) hstepsf'
          simp only [clearRegsFrom1_length] at this
          exact this
        exact Steps.trans hphase1 hphase2

    have hinner_halted : (⟨k + cf'.pc, cf'.state⟩ : Config).isHalted
        ((clearRegsFrom1 k).seq pf) := by
      simp only [Config.isHalted, Program.seq_length, clearRegsFrom1_length]
      have : pf.length ≤ cf'.pc := hhaltedf'
      omega

    -- For the outer composition, we need cg.pc = pg.length
    -- This requires pg to be in "standard form" (bounded jumps) per Cutland.
    -- With JumpsBounded pg, we could use: JumpsBounded.halts_at_length hpg_bounded hstepsg hhaltedg
    -- A complete formalization would prove that every URMComputable function
    -- has a standard-form witness, making this assumption implicit.
    have hcg_at_length : cg.pc = pg.length := by
      have _h_ge : pg.length ≤ cg.pc := hhaltedg
      sorry

    have hstepsg_exact : Steps pg (Config.init inputList) ⟨pg.length, σg⟩ := by
      -- Show cg = ⟨pg.length, σg⟩ and substitute
      have heq : cg = ⟨pg.length, σg⟩ := Config.ext hcg_at_length rfl
      rw [heq] at hstepsg
      exact hstepsg

    -- Now apply seq_halts_compose for the outer composition
    exact Steps.seq_halts_compose hstepsg_exact hinner_halts hinner_halted

  case result_eq =>
    -- Result equality
    intro hHalts hDom
    -- hDom : ((g inputs).bind (fun v => f (fun _ => v))).Dom
    -- Need to prove: Result composite inputList hHalts = ((g inputs).bind ...).get hDom

    -- The result of the composed program equals f(g(inputs))
    -- This follows from the structure of execution: pg produces v,
    -- clearing preserves v in R[0], pf produces f(v) in R[0]

    -- TODO: Complete result equality proof
    sorry

/-- URM-computable functions are closed under composition.

Given:
- `f : (Fin m → ℕ) → Part ℕ` is URM-computable (computed by program `pf`)
- For each `i : Fin m`, `g i : (Fin n → ℕ) → Part ℕ` is URM-computable (computed by `pg i`)

Then the composition `h(x) = f(g₀(x), ..., gₘ₋₁(x))` is also URM-computable.

The composed program:
1. Saves the inputs to backup registers
2. For each `i`, runs `pg i` and saves the output
3. Sets up the collected outputs as inputs to `pf`
4. Runs `pf`
5. The result is in register 0

This is Theorem 2.1 in Cutland, Chapter 2. -/
theorem comp {m n : ℕ}
    {f : (Fin m → ℕ) → Part ℕ} {g : Fin m → (Fin n → ℕ) → Part ℕ}
    (hf : URMComputable m f) (hg : ∀ i : Fin m, URMComputable n (g i)) :
    URMComputable n (composePartial f g) := by
  -- Extract programs from hypotheses
  obtain ⟨pf, hpf⟩ := hf
  choose pg hpg using hg
  -- Register layout:
  -- R[0..n-1]: inputs (preserved in backup)
  -- R[n..n+m-1]: collected outputs from g_0, ..., g_{m-1}
  -- R[n+m..n+m+n-1]: backup of inputs
  -- R[n+m+n..]: working space for running programs
  let inputBackupBase := n + m  -- Where to save inputs
  let workBase := n + m + n     -- Where shifted programs work

  -- Build the composed program:
  -- 1. Copy inputs R[0..n-1] to backup R[inputBackupBase..inputBackupBase+n-1]
  -- 2. For each i:
  --    a. Copy backup to R[workBase..workBase+n-1] (inputs for pg i)
  --    b. Run pg i shifted to workBase (result in R[workBase])
  --    c. Copy R[workBase] to R[n+i] (collect output)
  -- 3. Copy collected outputs R[n..n+m-1] to R[workBase..workBase+m-1] (inputs for pf)
  -- 4. Run pf shifted to workBase (result in R[workBase])
  -- 5. Copy R[workBase] to R[0] (final output)

  -- This construction is complex; we defer the full proof
  sorry

end URMComputable

end Urm
