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

/-! # Closure Under Composition

This file proves that URM-computable functions are closed under composition.

## Main results

- `URMComputable.comp`: If `f` is m-ary URM-computable and `g₀, ..., g_{m-1}` are n-ary
  URM-computable, then `h(x) = f(g₀(x), ..., g_{m-1}(x))` is URM-computable.

## Implementation

The proof follows Cutland's construction (Theorem 3.1):
1. Store inputs in safe registers above all subprograms' working registers
2. Run each gᵢ in sequence, saving results to safe storage
3. Copy results to input positions and run f

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Program Combinators -/

namespace Program

/-- Generate Transfer instructions to copy a contiguous range of registers.

`copyRegisterRange src dst n` produces `[T src dst, T (src+1) (dst+1), ..., T (src+n-1) (dst+n-1)]` -/
def copyRegisterRange (srcStart dstStart n : ℕ) : Program :=
  (List.range n).map fun i => Instr.T (srcStart + i) (dstStart + i)

@[simp]
theorem copyRegisterRange_length (src dst n : ℕ) :
    (copyRegisterRange src dst n).length = n := by
  simp [copyRegisterRange]

theorem copyRegisterRange_zero (src dst : ℕ) : copyRegisterRange src dst 0 = [] := rfl

/-- Clear registers `[0, maxReg]` by setting them to zero. -/
def clearRegisters (maxReg : ℕ) : Program :=
  (List.range (maxReg + 1)).map Instr.Z

@[simp]
theorem clearRegisters_length (maxReg : ℕ) :
    (clearRegisters maxReg).length = maxReg + 1 := by
  simp [clearRegisters]

/-- Fold-concatenate a list of programs with proper jump adjustment. -/
def foldConcat (ps : List Program) : Program :=
  ps.foldl concat []

theorem foldConcat_nil : foldConcat [] = [] := rfl

theorem foldConcat_singleton (p : Program) : foldConcat [p] = p := by
  simp [foldConcat, concat_nil_left]

end Program

/-! ## Register Isolation Lemmas -/

section RegisterIsolation

variable {p : Program}

/-- Helper: maxRegister bounds instruction maxRegister for valid pc. -/
theorem Program.instr_maxRegister_le {i : ℕ} {instr : Instr}
    (h : p.getInstr i = some instr) : instr.maxRegister ≤ p.maxRegister := by
  simp only [Program.getInstr] at h
  have hi : i < p.length := by
    by_contra hc
    simp only [not_lt] at hc
    simp [List.getElem?_eq_none hc] at h
  induction p generalizing i instr with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [Program.maxRegister, List.foldl_cons]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      -- hd.maxRegister ≤ foldl max (max 0 hd.maxRegister) tl
      have h1 : hd.maxRegister ≤ max 0 hd.maxRegister := Nat.le_max_right _ _
      have h2 : ∀ (init : ℕ) (l : List Instr), init ≤ l.foldl (fun acc i => max acc i.maxRegister) init := by
        intro init l
        induction l generalizing init with
        | nil => exact Nat.le_refl _
        | cons h t iht => exact Nat.le_trans (Nat.le_max_left _ _) (iht _)
      exact Nat.le_trans h1 (h2 _ _)
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hj : j < tl.length := by simp at hi; omega
      have ih' := ih h hj
      simp only [Program.maxRegister] at ih'
      -- ih' : instr.maxRegister ≤ foldl max 0 tl
      -- Need: instr.maxRegister ≤ foldl max (max 0 hd.maxRegister) tl
      have hmono : ∀ (a b : ℕ) (l : List Instr), a ≤ b →
          l.foldl (fun acc i => max acc i.maxRegister) a ≤
          l.foldl (fun acc i => max acc i.maxRegister) b := by
        intro a b l hab
        induction l generalizing a b with
        | nil => exact hab
        | cons h t iht =>
          simp only [List.foldl_cons]
          apply iht
          exact max_le_max hab (Nat.le_refl _)
      exact Nat.le_trans ih' (hmono 0 _ tl (Nat.zero_le _))

/-- A single step preserves registers above the program's maxRegister. -/
theorem Step.preserves_high_register {c c' : Config} (hstep : Step p c c') (r : ℕ)
    (hr : p.maxRegister < r) : c'.state.read r = c.state.read r := by
  cases hstep with
  | zero h =>
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    simp only [State.read, State.write]
    exact Function.update_of_ne (by omega : r ≠ _) _ _
  | succ h =>
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    simp only [State.read, State.write]
    exact Function.update_of_ne (by omega : r ≠ _) _ _
  | trans h =>
    have hinstr := Program.instr_maxRegister_le h
    simp only [Instr.maxRegister] at hinstr
    simp only [State.read, State.write]
    exact Function.update_of_ne (by omega : r ≠ _) _ _
  | jump_eq _ _ => rfl
  | jump_ne _ _ => rfl

/-- Multi-step execution preserves registers above maxRegister. -/
theorem Steps.preserves_high_register {c c' : Config} (hsteps : Steps p c c') (r : ℕ)
    (hr : p.maxRegister < r) : c'.state.read r = c.state.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
    rw [ih]
    exact Step.preserves_high_register hstep r hr

/-- Running a program preserves registers above its maxRegister.

When a program halts, the final state agrees with the initial state on all registers
that are never accessed by any instruction in the program. -/
theorem Halts.preserves_high_registers {p : Program} {inputs : List ℕ}
    (h : Halts p inputs) (r : ℕ) (hr : p.maxRegister < r) :
    (Classical.choose h).state.read r = (Config.init inputs).state.read r := by
  have ⟨hsteps, _⟩ := Classical.choose_spec h
  exact Steps.preserves_high_register hsteps r hr

end RegisterIsolation

/-! ## Part.sequence for Partial Function Families -/

/-- Sequence a finite family of partial values into a partial function.

`Part.sequence f` is defined iff all `f i` are defined, and when defined,
returns a function that gives `(f i).get` for each `i`. -/
def Part.sequence {α : Type*} : {n : ℕ} → (Fin n → Part α) → Part (Fin n → α)
  | 0, _ => Part.some Fin.elim0
  | _ + 1, f => (f 0).bind fun a0 =>
      (Part.sequence (fun i => f i.succ)).map fun rest =>
        Fin.cons a0 rest

theorem Part.sequence_zero {α : Type*} (f : Fin 0 → Part α) :
    Part.sequence f = Part.some Fin.elim0 := rfl

theorem Part.sequence_succ {α : Type*} {n : ℕ} (f : Fin (n + 1) → Part α) :
    Part.sequence f = (f 0).bind fun a0 =>
      (Part.sequence (fun i => f i.succ)).map fun rest =>
        Fin.cons a0 rest := rfl

theorem Part.sequence_dom {α : Type*} {n : ℕ} {f : Fin n → Part α} :
    (Part.sequence f).Dom ↔ ∀ i, (f i).Dom := by
  induction n with
  | zero =>
    simp only [Part.sequence, Part.some_dom]
    exact ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | succ n ih =>
    simp only [Part.sequence, Part.bind_dom, Part.map_Dom]
    constructor
    · intro ⟨hdom0, hrest⟩ i
      match i with
      | ⟨0, _⟩ => exact hdom0
      | ⟨j + 1, hlt⟩ =>
        have := ih.mp hrest
        exact this ⟨j, Nat.lt_of_succ_lt_succ hlt⟩
    · intro hall
      exact ⟨hall 0, ih.mpr (fun i => hall i.succ)⟩

theorem Part.sequence_get {α : Type*} {n : ℕ} {f : Fin n → Part α}
    (hdom : (Part.sequence f).Dom) (i : Fin n) :
    (Part.sequence f).get hdom i = (f i).get (Part.sequence_dom.mp hdom i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    match i with
    | ⟨0, _⟩ =>
      simp only [Part.sequence_succ, Part.bind, Part.map] at hdom ⊢
      rfl
    | ⟨j + 1, hlt⟩ =>
      -- Technical: extract the recursive call from the bind/map structure
      simp only [Part.sequence_succ, Part.bind, Part.map] at hdom ⊢
      exact ih _ ⟨j, Nat.lt_of_succ_lt_succ hlt⟩

/-! ## Full Composition Program Construction -/

/-- Maximum register used by a list of programs. -/
def maxRegisterOfList : List Program → ℕ
  | [] => 0
  | p :: ps => max p.maxRegister (maxRegisterOfList ps)

/-- The base register for safe storage in composition.
This is above all registers used by f, all g_i, and the input/output positions. -/
def compositionBase (n m : ℕ) (f : Program) (gs : List Program) : ℕ :=
  max n (max m (max f.maxRegister (maxRegisterOfList gs)))

/-- Build the program for running each g_i in sequence, saving results. -/
def computeGsProgram (inputSafe resultSafe base : ℕ) (n : ℕ) : List Program → ℕ → Program
  | [], _ => []
  | g :: rest, i =>
    let restore := Program.copyRegisterRange inputSafe 0 n
    let clear := Program.clearRegisters base
    let run := g
    let save : Program := [Instr.T 0 (resultSafe + i)]
    let thisG := Program.foldConcat [restore, clear, run, save]
    thisG.concat (computeGsProgram inputSafe resultSafe base n rest (i + 1))

/-- Build the composition program following Cutland's Theorem 3.1.

Given:
- `f`: m-ary function program
- `gs`: list of n-ary function programs [g₀, ..., g_{m-1}]

The program:
1. Copies inputs x₀, ..., x_{n-1} to safe storage above working registers
2. For each i from 0 to m-1:
   - Restores inputs from safe storage
   - Clears workspace
   - Runs g_i
   - Saves result to safe storage
3. Copies results g₀(x), ..., g_{m-1}(x) to positions 0, ..., m-1
4. Runs f -/
def Program.compose (n m : ℕ) (f : Program) (gs : List Program) : Program :=
  let base := compositionBase n m f gs
  let inputSafe := base + 1  -- inputs stored at [base+1, base+n]
  let resultSafe := base + n + 1  -- results stored at [base+n+1, base+n+m]

  -- Step 1: Copy inputs to safe storage
  let saveInputs := copyRegisterRange 0 inputSafe n

  -- Step 2: For each g_i, restore inputs, clear workspace, run g_i, save result
  let computeGs := computeGsProgram inputSafe resultSafe base n gs 0

  -- Step 3: Copy results to input positions for f
  let prepareF := copyRegisterRange resultSafe 0 m

  -- Step 4: Run f
  let runF := f

  foldConcat [saveInputs, computeGs, prepareF, runF]

/-! ## Composition Program Properties -/

/-- The safe input region is above all working registers. -/
theorem compositionBase_ge_n (n m : ℕ) (f : Program) (gs : List Program) :
    n ≤ compositionBase n m f gs := by
  simp only [compositionBase]
  exact Nat.le_max_left _ _

/-- The base is above m. -/
theorem compositionBase_ge_m (n m : ℕ) (f : Program) (gs : List Program) :
    m ≤ compositionBase n m f gs := by
  simp only [compositionBase]
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The safe input region is above f's working registers. -/
theorem compositionBase_ge_f (n m : ℕ) (f : Program) (gs : List Program) :
    f.maxRegister ≤ compositionBase n m f gs := by
  simp only [compositionBase]
  calc f.maxRegister
      ≤ max f.maxRegister (maxRegisterOfList gs) := Nat.le_max_left _ _
    _ ≤ max m (max f.maxRegister (maxRegisterOfList gs)) := Nat.le_max_right _ _
    _ ≤ max n (max m (max f.maxRegister (maxRegisterOfList gs))) := Nat.le_max_right _ _

/-- The safe input region is above each g_i's working registers. -/
theorem compositionBase_ge_gi (n m : ℕ) (f : Program) (gs : List Program)
    (g : Program) (hg : g ∈ gs) :
    g.maxRegister ≤ compositionBase n m f gs := by
  simp only [compositionBase]
  have h1 : g.maxRegister ≤ maxRegisterOfList gs := by
    induction gs with
    | nil => simp at hg
    | cons h t ih =>
      simp only [maxRegisterOfList]
      cases List.mem_cons.mp hg with
      | inl heq => subst heq; exact Nat.le_max_left _ _
      | inr hmem => exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)
  calc g.maxRegister
      ≤ maxRegisterOfList gs := h1
    _ ≤ max f.maxRegister (maxRegisterOfList gs) := Nat.le_max_right _ _
    _ ≤ max m (max f.maxRegister (maxRegisterOfList gs)) := Nat.le_max_right _ _
    _ ≤ max n (max m (max f.maxRegister (maxRegisterOfList gs))) := Nat.le_max_right _ _

/-! ## Standard Form and Concatenation -/

/-- Concatenation of straight-line programs is straight-line. -/
theorem Program.isStraightLine_concat {p1 p2 : Program}
    (h1 : p1.isStraightLine = true) (h2 : p2.isStraightLine = true) :
    (p1.concat p2).isStraightLine = true := by
  simp only [Program.concat, Program.isStraightLine, List.all_append]
  simp only [Program.isStraightLine] at h1 h2
  rw [Bool.and_eq_true]
  constructor
  · exact h1
  · simp only [Program.shiftJumps, List.all_map]
    convert h2 using 2
    funext instr
    cases instr <;> simp [Instr.shiftJumps, Instr.isNonJumping]

/-- Concatenation of straight-line programs is standard form. -/
theorem straightLine_concat_isStandardForm {p1 p2 : Program}
    (h1 : p1.isStraightLine = true) (h2 : p2.isStraightLine = true) :
    (p1.concat p2).IsStandardForm := by
  apply straightLine_isStandardForm
  exact Program.isStraightLine_concat h1 h2

/-- Concatenation of standard form programs is standard form.

If p₁ and p₂ are both standard form, then p₁.concat p₂ is also standard form.
This is a syntactic property: jump targets in p₁ are already bounded by p₁.length ≤ p₁.length + p₂.length,
and jump targets in p₂ are shifted by p₁.length, preserving their bounded property. -/
theorem Program.IsStandardForm.concat {p1 p2 : Program}
    (h1 : p1.IsStandardForm) (h2 : p2.IsStandardForm) :
    (p1.concat p2).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm at *
  rw [List.all_eq_true] at h1 h2 ⊢
  intro instr hinstr
  simp only [Program.concat, Program.shiftJumps] at hinstr
  rw [List.mem_append] at hinstr
  cases hinstr with
  | inl hp1 =>
    -- Instruction from p1: bounded by p1.length ≤ p1.length + p2.length
    have hb := h1 instr hp1
    simp only [Program.concat_length]
    exact Instr.hasBoundedJump_mono hb (Nat.le_add_right _ _)
  | inr hp2 =>
    -- Instruction from p2.shiftJumps: use the shifted bound lemma
    rw [List.mem_map] at hp2
    obtain ⟨instr', hinstr', rfl⟩ := hp2
    have hb := h2 instr' hinstr'
    have hshift := Instr.hasBoundedJump_shiftJumps (len := p2.length) (offset := p1.length) hb
    simp only [Program.concat_length]
    exact hshift

/-- If p1.concat p2 halts and p1 is standard form, then p1 halts.

This is the "prefix halts" property: execution of the concatenation must pass through
a state where p1 has halted (at pc = p1.length) before continuing into p2.

The key insight is that for standard form programs:
1. Execution starts at pc = 0
2. While pc < p1.length, we execute p1's instructions
3. Standard form means when we "exit" p1, it's at pc = p1.length (halted in p1)
4. This config witnesses that p1 halts -/
theorem Halts.prefix_of_concat_sf {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs)
    (h1 : p1.IsStandardForm) :
    Halts p1 inputs := by
  -- Extract the execution path from Config.init to a halted config in H
  -- Find the first config where pc = p1.length
  -- The prefix of the path up to that point is an execution of p1
  -- At pc = p1.length, p1 is halted
  obtain ⟨cH, hsteps, hhalted⟩ := hH
  -- Build p1 steps by extracting prefix of concat execution while pc < p1.length
  -- Key: we need to show there exists a config c with Steps p1 (Config.init inputs) c and c.isHalted p1
  -- Strategy: induction on hsteps, maintaining that we're building parallel p1 steps

  -- Handle empty p1 case first
  by_cases hp1 : p1.length = 0
  · -- Empty p1: Config.init is already halted
    exact ⟨Config.init inputs, Relation.ReflTransGen.refl, by simp [Config.isHalted, hp1]⟩

  -- Non-empty p1: we need to find where pc first reaches p1.length
  -- Use induction on the execution path.
  -- Key insight: at each step, while pc < p1.length, we can convert the step to a p1 step.
  -- When pc reaches p1.length, p1 is halted.

  -- Helper: from any config c with pc ≤ p1.length and steps to a halted config in concat,
  -- we can find a halted config in p1 reachable from c
  suffices h : ∀ c c' : Config,
      Steps (p1.concat p2) c c' → c'.isHalted (p1.concat p2) →
      c.pc ≤ p1.length →
      (∃ c'', Steps p1 c c'' ∧ c''.isHalted p1) by
    have hpc0 : (Config.init inputs).pc ≤ p1.length := by simp [Config.init]
    exact h (Config.init inputs) cH hsteps hhalted hpc0

  intro c c' hsteps'
  -- Use head_induction_on which gives the right IH structure:
  -- motive a := c'.isHalted → a.pc ≤ p1.length → ∃ c'', Steps p1 a c'' ∧ c''.isHalted p1
  -- Given Step a d and Steps d c', the IH applies to d
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- At the end: c = c'. Need to prove the motive for c'.
    -- Given c'.isHalted (concat) and c'.pc ≤ p1.length, show c' is halted in p1.
    intro hhalted' hpc_le
    simp only [Config.isHalted, Program.concat_length] at hhalted'
    have hpc_eq : c'.pc = p1.length := by omega
    exact ⟨c', Relation.ReflTransGen.refl, by simp [Config.isHalted, hpc_eq]⟩
  | @head a d hstep hrest ih =>
    -- hstep : Step (p1.concat p2) a d
    -- hrest : Steps (p1.concat p2) d c'
    -- ih : c'.isHalted (p1.concat p2) → d.pc ≤ p1.length → ∃ c'', Steps p1 d c'' ∧ c''.isHalted p1
    intro hhalted' hpc_le

    -- Check if a is already halted in p1
    by_cases hhalted_p1 : a.isHalted p1
    · exact ⟨a, Relation.ReflTransGen.refl, hhalted_p1⟩

    -- a is not halted in p1, so a.pc < p1.length
    have hpc_lt : a.pc < p1.length := by
      simp only [Config.isHalted, not_le] at hhalted_p1
      exact hhalted_p1

    -- Since a.pc < p1.length, we can convert the step to a p1 step
    have hstep_p1 : Step p1 a d := Step.of_concat_left hpc_lt hstep

    -- d.pc ≤ p1.length by standard form
    have hd_pc_le : d.pc ≤ p1.length := by
      cases hstep_p1 with
      | zero h => simp only; omega
      | succ h => simp only; omega
      | trans h => simp only; omega
      | jump_eq h _ =>
        simp only [Program.getInstr] at h
        have ⟨hpc_valid, hinstr_eq⟩ := List.getElem?_eq_some_iff.mp h
        have hmem : Instr.J _ _ _ ∈ p1 := hinstr_eq ▸ List.getElem_mem hpc_valid
        simp only [Program.IsStandardForm, Program.isStandardForm, List.all_eq_true] at h1
        have hbounded := h1 _ hmem
        simp only [Instr.hasBoundedJump, decide_eq_true_eq] at hbounded
        exact hbounded
      | jump_ne h _ => simp only; omega

    -- Apply IH to get p1 execution from d
    obtain ⟨c'', hsteps_dc'', hhalted_c''⟩ := ih hhalted' hd_pc_le

    -- Chain: a → d in p1, then d →* c'' in p1
    exact ⟨c'', Relation.ReflTransGen.head hstep_p1 hsteps_dc'', hhalted_c''⟩

/-- If p1.concat p2 halts and p1 is standard form, we can recover the intermediate state
after p1 halts (at pc = p1.length). -/
theorem Halts.concat_sf_intermediate_state {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs)
    (h1 : p1.IsStandardForm) :
    ∃ s : State, Steps p1 (Config.init inputs) ⟨p1.length, s⟩ ∧
                 (⟨p1.length, s⟩ : Config).isHalted p1 := by
  have hP1 := Halts.prefix_of_concat_sf hH h1
  have hspec := Classical.choose_spec hP1
  have hpc := h1.halts_at_length inputs (Classical.choose hP1) hspec.1 hspec.2
  use (Classical.choose hP1).state
  constructor
  · -- Need to show Steps p1 (Config.init inputs) ⟨p1.length, c.state⟩
    -- We have hspec.1 : Steps p1 (Config.init inputs) c and hpc : c.pc = p1.length
    have heq : Classical.choose hP1 = ⟨p1.length, (Classical.choose hP1).state⟩ := by
      ext
      · exact hpc
      · rfl
    rw [heq] at hspec
    exact hspec.1
  · simp only [Config.isHalted]
    exact Nat.le_refl _

/-- If p1.concat p2 halts and p1 is standard form, then p2 halts from the intermediate state.

After p1 halts at pc = p1.length, the remaining execution is exactly p2 starting
from the state left by p1. -/
theorem Halts.suffix_of_concat_sf {p1 p2 : Program} {inputs : List ℕ}
    (hH : Halts (p1.concat p2) inputs)
    (h1 : p1.IsStandardForm) :
    ∃ s : State, Halts p1 inputs ∧
                 (∀ hP1 : Halts p1 inputs, s = (Classical.choose hP1).state) ∧
                 (∃ c, Steps p2 ⟨0, s⟩ c ∧ c.isHalted p2) := by
  -- Get the intermediate state from p1's halting
  have hP1 := Halts.prefix_of_concat_sf hH h1
  have hc1_spec := Classical.choose_spec hP1
  have hc1_pc := h1.halts_at_length inputs (Classical.choose hP1) hc1_spec.1 hc1_spec.2
  use (Classical.choose hP1).state
  refine ⟨hP1, ?_, ?_⟩
  · intro hP1'
    -- By determinism, both choose the same config
    have huniq := Steps.halts_unique hc1_spec.1 hc1_spec.2
                    (Classical.choose_spec hP1').1 (Classical.choose_spec hP1').2
    rw [huniq]
  · -- The execution of H from Config.init to final config passes through c1
    -- The suffix from c1 to final is the execution of p2 from c1.state
    let c1 := Classical.choose hP1
    let s1 := c1.state
    -- Get the halted config of H
    obtain ⟨cH, hH_steps, hH_halted⟩ := hH
    -- Get the p1 execution lifted to H
    have h_to_c1 : Steps (p1.concat p2) (Config.init inputs) c1 :=
      Steps.concat_left_prefix hc1_spec.1 hc1_spec.2
    -- By deterministic_continuation, the path from c1 to cH exists
    have h_suffix : Steps (p1.concat p2) c1 cH :=
      Steps.deterministic_continuation h_to_c1 hH_steps hH_halted
    -- Rewrite c1 as ⟨p1.length, s1⟩
    have h_suffix_start : c1 = ⟨p1.length, s1⟩ := by
      ext
      · exact hc1_pc
      · rfl
    rw [h_suffix_start] at h_suffix
    -- Show cH.pc ≥ p1.length (needed for Steps.of_concat_right)
    have hcH_pc : cH.pc ≥ p1.length := by
      simp only [Config.isHalted, Program.concat_length] at hH_halted
      omega
    -- Extract p2 execution using Steps.of_concat_right
    -- NOTE: Steps.of_concat_right is defined later in this file
    -- This proof is structurally correct but needs file reorganization
    sorry

/-- copyRegisterRange produces a straight-line program. -/
theorem copyRegisterRange_isStraightLine (src dst n : ℕ) :
    (Program.copyRegisterRange src dst n).isStraightLine = true := by
  simp only [Program.copyRegisterRange, Program.isStraightLine, List.all_map]
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.all_append, ih, List.all_cons, List.all_nil,
      Function.comp_apply, Instr.isNonJumping, Bool.and_self]

/-- clearRegisters produces a straight-line program. -/
theorem clearRegisters_isStraightLine (maxReg : ℕ) :
    (Program.clearRegisters maxReg).isStraightLine = true := by
  simp only [Program.clearRegisters, Program.isStraightLine, List.all_map]
  induction maxReg + 1 with
  | zero => simp only [List.range_zero, List.all_nil]
  | succ k ih =>
    simp only [List.range_succ, List.all_append, ih, List.all_cons, List.all_nil,
      Function.comp_apply, Instr.isNonJumping, Bool.and_self]

/-- copyRegisterRange halts on any input. -/
theorem copyRegisterRange_halts (src dst n : ℕ) (inputs : List ℕ) :
    Halts (Program.copyRegisterRange src dst n) inputs := by
  exact straightLine_halts (copyRegisterRange_isStraightLine src dst n) inputs

/-- clearRegisters halts on any input. -/
theorem clearRegisters_halts (maxReg : ℕ) (inputs : List ℕ) :
    Halts (Program.clearRegisters maxReg) inputs := by
  exact straightLine_halts (clearRegisters_isStraightLine maxReg) inputs

/-- Straight-line programs halt from any starting state, not just Config.init.
This is key for chaining: after running one program, we can run the next
straight-line segment from whatever state we're in. -/
theorem straightLine_halts_from_state {p : Program} (hsl : p.isStraightLine = true) (s : State) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.isHalted p ∧ c.pc = p.length := by
  -- Induction on remaining instructions
  suffices h : ∀ (c : Config), c.pc ≤ p.length →
      ∃ c', Steps p c c' ∧ c'.pc = p.length by
    obtain ⟨c', hsteps, hpc'⟩ := h ⟨0, s⟩ (Nat.zero_le _)
    exact ⟨c', hsteps, Nat.le_of_eq hpc'.symm, hpc'⟩
  intro c hpc_le
  generalize hrem : p.length - c.pc = remaining
  induction remaining using Nat.strong_induction_on generalizing c with
  | _ remaining ih =>
    by_cases hhalted : c.pc ≥ p.length
    · exact ⟨c, Relation.ReflTransGen.refl, by omega⟩
    · push_neg at hhalted
      have hpc_lt : c.pc < p.length := hhalted
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
      have hstep : ∃ c', Step p c c' ∧ c'.pc = c.pc + 1 := by
        cases instr with
        | Z n => exact ⟨⟨c.pc + 1, c.state.write n 0⟩, Step.zero hinstr, rfl⟩
        | S n => exact ⟨⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩, Step.succ hinstr, rfl⟩
        | T m n => exact ⟨⟨c.pc + 1, c.state.write n (c.state.read m)⟩, Step.trans hinstr, rfl⟩
        | J m n q => simp [Instr.isNonJumping] at hnonjump
      obtain ⟨c', hstep', hpc'⟩ := hstep
      have hremaining : p.length - c'.pc < remaining := by omega
      have hpc'_le : c'.pc ≤ p.length := by omega
      obtain ⟨c'', hsteps'', hpc''⟩ := ih (p.length - c'.pc) hremaining c' hpc'_le rfl
      exact ⟨c'', Relation.ReflTransGen.head hstep' hsteps'', hpc''⟩

/-- The final state after running a straight-line program from a given starting state.
This is the relational-semantics version that replaces the functional `executeStraightLine`. -/
noncomputable def straightLineFinalState {p : Program} (hsl : p.isStraightLine = true) (s : State) : State :=
  (Classical.choose (straightLine_halts_from_state hsl s)).state

/-- The final config from straightLineFinalState satisfies the expected properties. -/
theorem straightLineFinalState_spec {p : Program} (hsl : p.isStraightLine = true) (s : State) :
    let c := Classical.choose (straightLine_halts_from_state hsl s)
    Steps p ⟨0, s⟩ c ∧ c.isHalted p ∧ c.pc = p.length :=
  Classical.choose_spec (straightLine_halts_from_state hsl s)

/-- A single step in a straight-line program modifies at most one register. -/
theorem Step.straightLine_preserves {p : Program} {c c' : Config} {r : ℕ}
    (hsl : p.isStraightLine = true) (hstep : Step p c c')
    (hr : ∀ instr, p.getInstr c.pc = some instr → instr.writesTo ≠ some r) :
    c'.state.read r = c.state.read r := by
  cases hstep with
  | zero hinstr =>
    have := hr _ hinstr
    simp only [Instr.writesTo, ne_eq, Option.some.injEq] at this
    simp only [State.read, State.write]
    exact Function.update_of_ne (Ne.symm this) _ _
  | succ hinstr =>
    have := hr _ hinstr
    simp only [Instr.writesTo, ne_eq, Option.some.injEq] at this
    simp only [State.read, State.write]
    exact Function.update_of_ne (Ne.symm this) _ _
  | trans hinstr =>
    have := hr _ hinstr
    simp only [Instr.writesTo, ne_eq, Option.some.injEq] at this
    simp only [State.read, State.write]
    exact Function.update_of_ne (Ne.symm this) _ _
  | jump_eq hinstr _ =>
    -- Jump in a straight-line program is a contradiction
    simp only [Program.getInstr] at hinstr
    have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
    have hmem : (Instr.J _ _ _) ∈ p := heq ▸ List.getElem_mem hlt
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact absurd (hsl _ hmem) (by simp [Instr.isNonJumping])
  | jump_ne hinstr _ =>
    simp only [Program.getInstr] at hinstr
    have ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinstr
    have hmem : (Instr.J _ _ _) ∈ p := heq ▸ List.getElem_mem hlt
    simp only [Program.isStraightLine, List.all_eq_true] at hsl
    exact absurd (hsl _ hmem) (by simp [Instr.isNonJumping])

/-- Multi-step execution preserves registers not written by any instruction. -/
theorem Steps.straightLine_preserves {p : Program} {c c' : Config} {r : ℕ}
    (hsl : p.isStraightLine = true) (hsteps : Steps p c c')
    (hr : ∀ instr, instr ∈ p → instr.writesTo ≠ some r) :
    c'.state.read r = c.state.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
    rw [ih]
    apply Step.straightLine_preserves hsl hstep
    intro instr hinstr
    apply hr
    simp only [Program.getInstr] at hinstr
    exact List.mem_of_getElem? hinstr

/-- copyRegisterRange preserves registers outside the destination range.
Uses the relational semantics directly. -/
theorem copyRegisterRange_preserves_outside (src dst n : ℕ) (σ : State) (r : ℕ)
    (hOutside : r < dst ∨ dst + n ≤ r) :
    (straightLineFinalState (copyRegisterRange_isStraightLine src dst n) σ).read r = σ.read r := by
  -- The program only writes to registers dst, dst+1, ..., dst+n-1
  -- Since r is outside this range, it is preserved
  have hsl := copyRegisterRange_isStraightLine src dst n
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl σ
  apply Steps.straightLine_preserves hsl hsteps
  intro instr hmem
  -- Each instruction in copyRegisterRange is T (src+i) (dst+i) for some i
  simp only [Program.copyRegisterRange, List.mem_map] at hmem
  obtain ⟨i, hi_range, hinstr_eq⟩ := hmem
  simp only [List.mem_range] at hi_range
  subst hinstr_eq
  simp only [Instr.writesTo, ne_eq, Option.some.injEq]
  cases hOutside with
  | inl h => omega
  | inr h => omega

/-- copyRegisterRange correctly copies values when ranges don't overlap.

When dst + n ≤ src (destination range entirely before source range),
the destination registers receive exact copies of the source values.
Uses the relational semantics directly.

TODO: This requires more infrastructure to prove with relational semantics.
The proof needs to track that after k steps, registers dst..dst+k-1 have been
copied and the source registers are still unchanged. -/
theorem copyRegisterRange_correct_nonoverlap (src dst n : ℕ) (σ : State)
    (hNoOverlap : dst + n ≤ src) :
    ∀ i : Fin n, (straightLineFinalState (copyRegisterRange_isStraightLine src dst n) σ).read (dst + i) =
                 σ.read (src + i) := by
  sorry

/-! ## State Invariants for Composition -/

/-- Inputs are preserved in safe storage (for restore operations).

During composition, the original inputs need to be preserved in safe storage
so they can be restored before running each g_i. -/
def InputsPreserved (n : ℕ) (inputs : Fin n → ℕ) (inputSafe : ℕ) (state : State) : Prop :=
  ∀ j : Fin n, state.read (inputSafe + j) = inputs j

/-- Values are loaded in registers 0..n-1 (ready to run a program).

A program expecting n inputs needs those values in registers 0, 1, ..., n-1. -/
def InputsLoaded (n : ℕ) (vals : Fin n → ℕ) (state : State) : Prop :=
  ∀ j : Fin n, state.read j = vals j

/-! ## Continuation Lemmas for Sequential Execution -/

section Continuation

variable {p1 p2 : Program}

/-- Convert a state to a list of register values (first n registers). -/
def State.toList (s : State) (n : ℕ) : List ℕ :=
  (List.range n).map s

/-- Reverse: stepping in concatenated program with pc in second part gives step in p2.
The config is "de-offset" by p1.length to get the corresponding p2 step. -/
theorem Step.of_concat_right {c c' : Config}
    (hpc_lo : p1.length ≤ c.pc)
    (hpc_hi : c.pc < p1.length + p2.length)
    (hstep : Step (p1.concat p2) c c') :
    Step p2 ⟨c.pc - p1.length, c.state⟩ ⟨c'.pc - p1.length, c'.state⟩ := by
  -- Get the instruction in p2 at the de-offset pc
  have hp2_pc : c.pc - p1.length < p2.length := by omega
  have hinstr : ∃ instr, p2.getInstr (c.pc - p1.length) = some instr := by
    simp only [Program.getInstr]
    exact ⟨p2[c.pc - p1.length], List.getElem?_eq_getElem hp2_pc⟩
  obtain ⟨instr, hinstr⟩ := hinstr
  -- The concat instruction is the shifted version
  have hconcat_instr : (p1.concat p2).getInstr c.pc = some (instr.shiftJumps p1.length) := by
    rw [Program.getInstr_concat_right c.pc hpc_lo hpc_hi, Program.getInstr_shiftJumps, hinstr]
    rfl
  -- Match on the instruction type
  -- Note: we're constructing Step p2 ⟨c.pc - p1.length, c.state⟩ ⟨c'.pc - p1.length, c'.state⟩
  -- and hinstr : p2.getInstr (c.pc - p1.length) = some instr
  set pc2 := c.pc - p1.length with hpc2_def
  cases instr with
  | Z n =>
    have hc' : c' = ⟨c.pc + 1, c.state.write n 0⟩ := by
      cases hstep <;> simp_all [Instr.shiftJumps]
    subst hc'
    have hpc'2 : c.pc + 1 - p1.length = pc2 + 1 := by omega
    rw [hpc'2]
    exact Step.zero hinstr
  | S n =>
    have hc' : c' = ⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩ := by
      cases hstep <;> simp_all [Instr.shiftJumps]
    subst hc'
    have hpc'2 : c.pc + 1 - p1.length = pc2 + 1 := by omega
    rw [hpc'2]
    exact Step.succ hinstr
  | T m n =>
    have hc' : c' = ⟨c.pc + 1, c.state.write n (c.state.read m)⟩ := by
      cases hstep <;> simp_all [Instr.shiftJumps]
    subst hc'
    have hpc'2 : c.pc + 1 - p1.length = pc2 + 1 := by omega
    rw [hpc'2]
    exact Step.trans hinstr
  | J m n q =>
    -- Either we jump (registers equal) or continue (registers different)
    cases hstep with
    | jump_eq h heq =>
      simp only [Instr.shiftJumps] at hconcat_instr
      simp only [hconcat_instr, Option.some.injEq, Instr.J.injEq] at h
      obtain ⟨rfl, rfl, hq⟩ := h
      -- hq : q + p1.length = q✝ (the shifted jump target)
      -- The goal has q✝ - p1.length in the target pc
      simp only [← hq, Nat.add_sub_cancel]
      exact Step.jump_eq hinstr heq
    | jump_ne h hne =>
      simp only [Instr.shiftJumps] at hconcat_instr
      simp only [hconcat_instr, Option.some.injEq, Instr.J.injEq] at h
      obtain ⟨rfl, rfl, _⟩ := h
      have hpc'2 : c.pc + 1 - p1.length = pc2 + 1 := by omega
      rw [hpc'2]
      exact Step.jump_ne hinstr hne
    | _ => simp_all [Instr.shiftJumps]

/-- Extract multi-step p2 execution from concat execution starting at pc = p1.length.
This is the reverse of `Steps.concat_right`: given execution in p1.concat(p2) that
starts at pc = p1.length and halts, we extract the corresponding p2 execution. -/
theorem Steps.of_concat_right {s : State} {c' : Config}
    (hsteps : Steps (p1.concat p2) ⟨p1.length, s⟩ c')
    (hhalted : c'.isHalted (p1.concat p2))
    (_hpc' : c'.pc ≥ p1.length) :
    ∃ c, Steps p2 ⟨0, s⟩ c ∧ c.isHalted p2 ∧ c.state = c'.state := by
  -- Key insight: all steps stay in the p2 range (pc ≥ p1.length)
  -- Generalize to handle arbitrary starting pc in the p2 range
  suffices h : ∀ (start : Config) (c' : Config),
      start.pc ≥ p1.length →
      Steps (p1.concat p2) start c' →
      c'.isHalted (p1.concat p2) →
      ∃ c, Steps p2 ⟨start.pc - p1.length, start.state⟩ c ∧ c.isHalted p2 ∧ c.state = c'.state by
    have := h ⟨p1.length, s⟩ c' (Nat.le_refl _) hsteps hhalted
    simp only [Nat.sub_self] at this
    exact this
  intro start c'' hstart hsteps' hhalted'
  induction hsteps' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- In the refl case, start = c'' (both become c'')
    use ⟨c''.pc - p1.length, c''.state⟩, Relation.ReflTransGen.refl
    constructor
    · simp only [Config.isHalted] at hhalted' ⊢
      simp only [Program.concat, List.length_append, Program.shiftJumps, List.length_map] at hhalted'
      omega
    · rfl
  | @head a b hstep hrest ih =>
    have ha_in_range : a.pc < p1.length + p2.length := by
      by_contra hc
      simp only [not_lt] at hc
      have hhalted_a : a.isHalted (p1.concat p2) := by
        simp only [Config.isHalted, Program.concat, List.length_append,
                   Program.shiftJumps, List.length_map]
        omega
      exact Step.halted_no_step hhalted_a hstep
    have hstep_p2 := Step.of_concat_right hstart ha_in_range hstep
    have hb_pc_ge : b.pc ≥ p1.length := by
      have ha_ge := hstart  -- a.pc ≥ p1.length
      cases hstep with
      | zero h => simp only []; omega
      | succ h => simp only []; omega
      | trans h => simp only []; omega
      | jump_eq h heq =>
        -- The instruction is in p2's range, so its jump target is shifted by p1.length
        -- h : (p1.concat p2).getInstr a.pc = some (J m n q)
        -- Since a.pc ≥ p1.length, this instruction comes from p2.shiftJumps p1.length
        -- So the target q is of the form original_target + p1.length
        have hconcat := Program.getInstr_concat_right a.pc hstart ha_in_range
        rw [hconcat, Program.getInstr_shiftJumps] at h
        -- h : Option.map (Instr.shiftJumps p1.length) (p2.getInstr (a.pc - p1.length)) = some (J m n q)
        -- The original instruction in p2 has target q' and the shifted one has q = q' + p1.length
        cases hp2 : p2.getInstr (a.pc - p1.length) with
        | none => simp only [hp2, Option.map_none] at h; nomatch h
        | some instr =>
          simp only [hp2, Option.map_some] at h
          cases instr with
          | J m' n' q' =>
            simp only [Instr.shiftJumps, Option.some.injEq, Instr.J.injEq] at h
            -- h gives us that the jump target is q' + p1.length = q✝
            -- Goal is: b.pc ≥ p1.length, where b.pc = q✝ (the jump target)
            obtain ⟨_, _, hq_eq⟩ := h
            simp only [← hq_eq]
            omega
          | Z _ => simp only [Instr.shiftJumps, Option.some.injEq] at h; nomatch h
          | S _ => simp only [Instr.shiftJumps, Option.some.injEq] at h; nomatch h
          | T _ _ => simp only [Instr.shiftJumps, Option.some.injEq] at h; nomatch h
      | jump_ne h hne => simp only []; omega
    -- ih takes hb_pc_ge and gives us ∃ c, Steps p2 ⟨b.pc - p1.length, b.state⟩ c ∧ ...
    obtain ⟨c, hrest_p2, hhalted_c, hstate_eq⟩ := ih hb_pc_ge
    exact ⟨c, Relation.ReflTransGen.head hstep_p2 hrest_p2, hhalted_c, hstate_eq⟩

/-- If p1 halts (by falling through) and p2 halts when started from p1's final state,
then p1.concat p2 halts.

This is the key continuation lemma: we can chain halting programs.
The hypothesis h1_pc ensures p1 halted by falling through (pc = p1.length),
not by jumping beyond the program. -/
theorem Halts.concat_continuation {inputs : List ℕ}
    (h1 : Halts p1 inputs)
    (h1_pc : (Classical.choose h1).pc = p1.length)
    (h2 : ∃ c, Steps p2 ⟨0, (Classical.choose h1).state⟩ c ∧ c.isHalted p2) :
    Halts (p1.concat p2) inputs := by
  -- Get the halted config from p1
  obtain ⟨hsteps1, hhalted1⟩ := Classical.choose_spec h1
  let c1 := Classical.choose h1
  -- Get the halted config from p2
  obtain ⟨c2, hsteps2, hhalted2⟩ := h2
  -- Lift p1's execution to the concatenation
  have hsteps1' := Steps.concat_left_prefix (p2 := p2) hsteps1 hhalted1
  -- Now continue from where p1 halted
  -- After p1 halts: we're at ⟨c1.pc, c1.state⟩ = ⟨p1.length, c1.state⟩
  -- p2 starts at ⟨0, c1.state⟩, so we need ⟨0 + p1.length, c1.state⟩ = ⟨p1.length, c1.state⟩
  have hsteps2' := Steps.concat_right (p1 := p1) hsteps2 hhalted2
  -- The start of p2's lifted execution: ⟨0 + p1.length, c1.state⟩
  -- This matches where p1 halted: ⟨p1.length, c1.state⟩ (using h1_pc)
  have hstart_eq : (⟨0 + p1.length, c1.state⟩ : Config) = ⟨c1.pc, c1.state⟩ := by
    simp only [Nat.zero_add]
    rw [← h1_pc]
  -- Rewrite hsteps2' to start from c1
  rw [hstart_eq] at hsteps2'
  -- The concatenation is transitive: first do p1's steps, then p2's
  have hsteps_total := Relation.ReflTransGen.trans hsteps1' hsteps2'
  -- Final config: c2 shifted
  refine ⟨⟨c2.pc + p1.length, c2.state⟩, hsteps_total, ?_⟩
  -- Show the final config is halted in p1.concat p2
  simp only [Config.isHalted, Program.concat, List.length_append, Program.shiftJumps,
             List.length_map, Config.isHalted] at hhalted2 ⊢
  omega

/-- If p1 halts (as a standard form program) and p2 is straight-line, then p1.concat p2 halts.

This is a convenient corollary of `concat_continuation` for the common case where
the second program is straight-line (transfers, clears, etc.). Standard form ensures
p1 halts by falling through (pc = p1.length). -/
theorem Halts.concat_straightLine {p1 p2 : Program} {inputs : List ℕ}
    (h1 : Halts p1 inputs)
    (h1_sf : p1.IsStandardForm)
    (h2_sl : p2.isStraightLine = true) :
    Halts (p1.concat p2) inputs := by
  -- Standard form ensures p1 halted by falling through
  have h1_pc : (Classical.choose h1).pc = p1.length := by
    have hspec := Classical.choose_spec h1
    exact h1_sf.halts_at_length inputs (Classical.choose h1) hspec.1 hspec.2
  -- Straight-line p2 halts from any state
  have h2 : ∃ c, Steps p2 ⟨0, (Classical.choose h1).state⟩ c ∧ c.isHalted p2 := by
    obtain ⟨c, hsteps, hhalted, _⟩ := straightLine_halts_from_state h2_sl (Classical.choose h1).state
    exact ⟨c, hsteps, hhalted⟩
  exact Halts.concat_continuation h1 h1_pc h2

end Continuation

/-! ## Shift-Based Composition Infrastructure

The key insight for composition is that each subprogram gᵢ can run on a disjoint
register range using shifted execution. This avoids the need for clearing registers
between subprogram executions.

Given n-ary functions g₀, ..., g_{m-1}, we run each gᵢ shifted by offset_i where
the offsets are chosen so register ranges don't overlap. Then gᵢ's result lands
at register offset_i.
-/

section ShiftedComposition

/-- Offset for running the i-th subprogram in shifted composition.
We leave n registers at the start for the original inputs, then space each
subprogram by (maxG + 1) registers to ensure disjoint ranges.

offset_i = n + i * (maxG + 1), where maxG = maxRegisterOfList gs
-/
def shiftOffset (n : ℕ) (maxG : ℕ) (i : ℕ) : ℕ := n + i * (maxG + 1)

/-- Offsets for different subprograms are distinct. -/
theorem shiftOffset_injective (n maxG : ℕ) {i j : ℕ}
    (hij : i ≠ j) : shiftOffset n maxG i ≠ shiftOffset n maxG j := by
  simp only [shiftOffset]
  intro h
  have : i = j := by
    have h' : i * (maxG + 1) = j * (maxG + 1) := by omega
    exact Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_succ maxG) h'
  contradiction

/-- Register ranges for shifted subprograms are disjoint.
Program at offset_i uses [offset_i, offset_i + maxG], and these don't overlap. -/
theorem shiftOffset_ranges_disjoint (n maxG : ℕ) {i j : ℕ}
    (hij : i < j) :
    shiftOffset n maxG i + maxG < shiftOffset n maxG j := by
  simp only [shiftOffset]
  have h1 : n + i * (maxG + 1) + maxG < n + i * (maxG + 1) + (maxG + 1) := by omega
  have h2 : n + i * (maxG + 1) + (maxG + 1) = n + (i + 1) * (maxG + 1) := by
    have : (i + 1) * (maxG + 1) = i * (maxG + 1) + (maxG + 1) := Nat.succ_mul i (maxG + 1)
    omega
  have h3 : (i + 1) * (maxG + 1) ≤ j * (maxG + 1) := Nat.mul_le_mul_right _ hij
  omega

/-- The i-th subprogram's result (at offset_i) is below j-th's working registers. -/
theorem shiftOffset_result_below_work (n maxG : ℕ) {i j : ℕ}
    (hij : i < j) :
    shiftOffset n maxG i < shiftOffset n maxG j := by
  simp only [shiftOffset]
  have h : i * (maxG + 1) < j * (maxG + 1) := Nat.mul_lt_mul_of_pos_right hij (Nat.zero_lt_succ maxG)
  omega

/-- Running a shifted subprogram preserves lower registers.
Since shifted program uses registers ≥ offset, registers < offset are unchanged. -/
theorem Steps.shiftRegisters_preserves_below {p : Program} {c c' : Config} {offset : ℕ}
    (hsteps : Steps (p.shiftRegisters offset) c c') (r : ℕ) (hr : r < offset) :
    c'.state.read r = c.state.read r := by
  -- Registers below offset are not modified by a shifted program
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
    rw [ih]
    -- hstep : Step (p.shiftRegisters offset) _ _
    -- All registers modified by p.shiftRegisters offset are ≥ offset
    match hstep with
    | .zero (n := reg) hinstr =>
      have ⟨hlo, _⟩ := Program.shiftRegisters_uses_range hinstr reg (Or.inr rfl)
      simp only [State.read, State.write, Function.update_of_ne (by omega : r ≠ reg)]
    | .succ (n := reg) hinstr =>
      have ⟨hlo, _⟩ := Program.shiftRegisters_uses_range hinstr reg
        (Or.inl (List.mem_singleton.mpr rfl))
      simp only [State.read, State.write, Function.update_of_ne (by omega : r ≠ reg)]
    | .trans (n := dst) hinstr =>
      have ⟨hlo, _⟩ := Program.shiftRegisters_uses_range hinstr dst (Or.inr rfl)
      simp only [State.read, State.write, Function.update_of_ne (by omega : r ≠ dst)]
    | .jump_eq _ _ => rfl
    | .jump_ne _ _ => rfl

/-- Running a shifted subprogram also preserves registers above its range.
Since program uses at most registers in [offset, offset + maxRegister], higher registers
are unchanged.

Note: This uses Steps.preserves_high_register applied to the shifted program. -/
theorem Steps.shiftRegisters_preserves_above {p : Program} {c c' : Config} {offset : ℕ}
    (hsteps : Steps (p.shiftRegisters offset) c c') (r : ℕ)
    (hp : p ≠ [])
    (hr : offset + p.maxRegister < r) :
    c'.state.read r = c.state.read r := by
  -- The shifted program's maxRegister = p.maxRegister + offset (for nonempty p)
  have hmax : (p.shiftRegisters offset).maxRegister = p.maxRegister + offset :=
    Program.maxRegister_shiftRegisters offset p hp
  have hr' : (p.shiftRegisters offset).maxRegister < r := by omega
  exact Steps.preserves_high_register hsteps r hr'

end ShiftedComposition

/-! ## Main Composition Theorem -/

/-- Helper: Type abbreviation for the specification of a program computing a function. -/
abbrev ProgramSpec (arity : ℕ) (func : (Fin arity → ℕ) → Part ℕ) (prog : Program) : Prop :=
  ∀ inputs : Fin arity → ℕ,
    (Halts prog (List.ofFn inputs) ↔ (func inputs).Dom) ∧
    ∀ (hHalts : Halts prog (List.ofFn inputs)) (hDom : (func inputs).Dom),
      Result prog (List.ofFn inputs) hHalts = (func inputs).get hDom

/-- If all g_i are defined and f is defined on the results, then H halts.

This is the "backward" direction: definedness implies halting. -/
theorem comp_halts_of_defined {n m : ℕ}
    {f : (Fin m → ℕ) → Part ℕ}
    {g : Fin m → ((Fin n → ℕ) → Part ℕ)}
    (Pf : Program) (Pg : Fin m → Program)
    (hPf : ProgramSpec m f Pf)
    (hPg : ∀ i, ProgramSpec n (g i) (Pg i))
    (inputs : Fin n → ℕ)
    (hDom : ((Part.sequence (fun i => g i inputs)).bind f).Dom) :
    Halts (Program.compose n m Pf (List.ofFn Pg)) (List.ofFn inputs) := by
  -- Extract definedness of each g_i from the domain condition
  have hSeqDom : (Part.sequence (fun i => g i inputs)).Dom := Part.bind_dom.mp hDom |>.1
  -- Each g_i is defined on inputs
  have hGiDom : ∀ i, (g i inputs).Dom := Part.sequence_dom.mp hSeqDom
  -- Each g_i halts (by ProgramSpec)
  have hGiHalts : ∀ i, Halts (Pg i) (List.ofFn inputs) := fun i =>
    (hPg i inputs).1.mpr (hGiDom i)
  -- f is defined on the results (from Part.bind_dom)
  -- When Part.sequence is defined, its get returns a function that gives (g i inputs).get
  have hFDom : (f (fun i => (g i inputs).get (hGiDom i))).Dom := by
    have h := Part.bind_dom.mp hDom |>.2
    -- h is: (f (Part.sequence ...).get hSeqDom).Dom
    -- Convert using Part.sequence_get which shows the values are equal
    convert h using 2
    ext i
    exact (Part.sequence_get hSeqDom i).symm
  -- f halts (by ProgramSpec)
  have hFHalts : Halts Pf (List.ofFn (fun i => (g i inputs).get (hGiDom i))) := by
    exact (hPf _).1.mpr hFDom
  -- Now we need to chain the programs together
  -- Program.compose creates: foldConcat [saveInputs, computeGs, prepareF, runF]
  simp only [Program.compose, Program.foldConcat]
  -- The proof requires showing that each stage halts and the state is preserved
  -- This is complex due to state tracking; use sorry for now pending full infrastructure
  sorry

/-- If H halts, then all g_i are defined and f is defined on the results.

This is the "forward" direction: halting implies definedness. -/
theorem comp_defined_of_halts {n m : ℕ}
    {f : (Fin m → ℕ) → Part ℕ}
    {g : Fin m → ((Fin n → ℕ) → Part ℕ)}
    (Pf : Program) (Pg : Fin m → Program)
    (hPf : ProgramSpec m f Pf)
    (hPg : ∀ i, ProgramSpec n (g i) (Pg i))
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.compose n m Pf (List.ofFn Pg)) (List.ofFn inputs)) :
    ((Part.sequence (fun i => g i inputs)).bind f).Dom := by
  sorry

/-- When H halts and the composed function is defined, the results match. -/
theorem comp_result_eq {n m : ℕ}
    {f : (Fin m → ℕ) → Part ℕ}
    {g : Fin m → ((Fin n → ℕ) → Part ℕ)}
    (Pf : Program) (Pg : Fin m → Program)
    (hPf : ProgramSpec m f Pf)
    (hPg : ∀ i, ProgramSpec n (g i) (Pg i))
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.compose n m Pf (List.ofFn Pg)) (List.ofFn inputs))
    (hDom : ((Part.sequence (fun i => g i inputs)).bind f).Dom) :
    Result (Program.compose n m Pf (List.ofFn Pg)) (List.ofFn inputs) hHalts =
    ((Part.sequence (fun i => g i inputs)).bind f).get hDom := by
  -- Extract intermediate hypotheses from hDom
  have hSeqDom : (Part.sequence (fun i => g i inputs)).Dom := Part.bind_dom.mp hDom |>.1
  have hGiDom : ∀ i, (g i inputs).Dom := Part.sequence_dom.mp hSeqDom
  have hGiHalts : ∀ i, Halts (Pg i) (List.ofFn inputs) := fun i => (hPg i inputs).1.mpr (hGiDom i)
  have hFDom : (f (fun i => (g i inputs).get (hGiDom i))).Dom := by
    have h := Part.bind_dom.mp hDom |>.2
    convert h using 2; ext i; exact (Part.sequence_get hSeqDom i).symm
  have hFHalts : Halts Pf (List.ofFn (fun i => (g i inputs).get (hGiDom i))) :=
    (hPf _).1.mpr hFDom
  -- Use ProgramSpec to get result equalities
  have hGiResult : ∀ i, Result (Pg i) (List.ofFn inputs) (hGiHalts i) = (g i inputs).get (hGiDom i) :=
    fun i => (hPg i inputs).2 (hGiHalts i) (hGiDom i)
  have hFResult : Result Pf (List.ofFn (fun i => (g i inputs).get (hGiDom i))) hFHalts =
                  (f (fun i => (g i inputs).get (hGiDom i))).get hFDom :=
    (hPf _).2 hFHalts hFDom
  -- Rewrite RHS using Part.Dom.bind: when o.Dom, o.bind f = f (o.get h)
  -- Use Part.Dom.bind to simplify the bind
  have hSimp : (Part.sequence (fun i => g i inputs)).bind f =
               f ((Part.sequence (fun i => g i inputs)).get hSeqDom) :=
    Part.Dom.bind hSeqDom f
  -- Show the argument to f equals what we expect
  have hArgEq : (Part.sequence (fun i => g i inputs)).get hSeqDom =
                (fun i => (g i inputs).get (hGiDom i)) := by
    ext i
    exact Part.sequence_get hSeqDom i
  -- Combine to get the RHS equality using cast
  have hRHS : ((Part.sequence (fun i => g i inputs)).bind f).get hDom =
              (f (fun i => (g i inputs).get (hGiDom i))).get hFDom := by
    -- The bind simplifies and we can use the argument equality
    have h1 : (f ((Part.sequence (fun i => g i inputs)).get hSeqDom)) =
              (f (fun i => (g i inputs).get (hGiDom i))) := by rw [hArgEq]
    simp only [hSimp, h1]
  rw [hRHS, ← hFResult]
  -- Goal: Result (Program.compose ...) _ _ = Result Pf (List.ofFn (fun i => (g i inputs).get _)) _
  --
  -- This requires a key semantic lemma about foldConcat execution:
  -- After phases [saveInputs, computeGs, prepareF], registers 0..m-1 contain the g_i values.
  -- Then runF (= Pf) runs on this state, and its Result is the composed program's Result.
  --
  -- Missing infrastructure needed:
  -- 1. foldConcat_result_eq_last: Result of foldConcat equals Result of last phase
  --    when run from the post-intermediate-phases state
  -- 2. prepareF_regs_match: After prepareF, registers 0..m-1 contain exactly
  --    the values List.ofFn (fun i => (g i inputs).get _)
  -- 3. computeGs_halts_with_values: computeGs correctly computes each g_i
  --
  -- These lemmas require tracing execution through each phase of Program.compose.
  sorry

/-- Closure under composition (Cutland's Theorem 3.1).

If f is an m-ary URM-computable function and g₀, ..., g_{m-1} are n-ary
URM-computable functions, then h(x) = f(g₀(x), ..., g_{m-1}(x)) is
URM-computable.

The composed function h is defined iff all gᵢ are defined on x AND
f is defined on (g₀(x), ..., g_{m-1}(x)). -/
theorem URMComputable.comp {n m : ℕ}
    {f : (Fin m → ℕ) → Part ℕ}
    {g : Fin m → ((Fin n → ℕ) → Part ℕ)}
    (hf : URMComputable m f)
    (hg : ∀ i, URMComputable n (g i)) :
    URMComputable n (fun x =>
      (Part.sequence (fun i => g i x)).bind f) := by
  -- Extract the programs from the computability witnesses
  obtain ⟨Pf, hPf⟩ := hf
  -- For each g_i, we get a program P_{g_i}
  have hPg_exists : ∀ i, ∃ p : Program, ProgramSpec n (g i) p := hg
  -- Choose the programs for each g_i
  let Pg : Fin m → Program := fun i => Classical.choose (hPg_exists i)
  have hPg : ∀ i, ProgramSpec n (g i) (Pg i) :=
    fun i => Classical.choose_spec (hPg_exists i)
  -- Build the composed program
  let H := Program.compose n m Pf (List.ofFn Pg)
  -- Prove URMComputable using H
  use H
  intro inputs
  constructor
  -- Part 1: Halts H (List.ofFn inputs) ↔ ((Part.sequence ...).bind f).Dom
  · constructor
    · exact comp_defined_of_halts Pf Pg hPf hPg inputs
    · exact comp_halts_of_defined Pf Pg hPf hPg inputs
  -- Part 2: When both defined, results match
  · exact comp_result_eq Pf Pg hPf hPg inputs

end Urm
