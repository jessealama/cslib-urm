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

end Steps

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

    TODO: Needs lemmas about sequential program execution:
    * `seq_halts_of_first_halts`: When p₁ halts in p₁.seq p₂, execution continues at p₁.length
    * `seq_steps_from_junction`: Steps in p₂ starting from p₁.length in p₁.seq p₂
    * `clearRegsFrom1_halts`: The clearing program always halts
    * `clearRegsFrom1_result`: The final state after clearing -/
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
  -- The key lemmas needed:
  -- 1. seq execution: p₁.seq p₂ first runs p₁, then if p₁ halts, runs p₂
  -- 2. clearRegsFrom1_halts: the clearing program always halts
  -- 3. Halts.agree_halts: states agreeing on registers 0..k give same halting/results
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
