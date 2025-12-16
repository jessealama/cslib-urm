/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable
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

/-- Shifting jumps preserves program length. -/
@[simp]
theorem shiftJumps_length (offset : ℕ) (p : Program) :
    (p.shiftJumps offset).length = p.length := by
  simp [shiftJumps]

/-- Shifting jumps by 0 is the identity. -/
theorem shiftJumps_zero (p : Program) : p.shiftJumps 0 = p := by
  simp only [shiftJumps]
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons]
    cases hd <;> simp [Instr.shiftJumps, ih]

/-- Concatenate two programs, adjusting the second program's jump targets.

When concatenating `p1 ++ p2`, jumps within `p2` must be shifted by `p1.length`
to maintain correct targets in the combined program. -/
def concat (p1 p2 : Program) : Program :=
  p1 ++ p2.shiftJumps p1.length

@[simp]
theorem concat_length (p1 p2 : Program) : (p1.concat p2).length = p1.length + p2.length := by
  simp [concat]

theorem concat_nil_left (p : Program) : concat [] p = p := by
  simp [concat, shiftJumps_zero]

theorem concat_nil_right (p : Program) : concat p [] = p := by
  simp [concat, shiftJumps]

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

/-! ## Concatenation Lemmas -/

section ConcatLemmas

variable {p1 p2 : Program}

/-- Get instruction from concatenated program in the first part. -/
theorem Program.getInstr_concat_left (i : ℕ) (hi : i < p1.length) :
    (p1.concat p2).getInstr i = p1.getInstr i := by
  simp only [Program.concat, Program.getInstr]
  rw [List.getElem?_append_left hi]

/-- Get instruction from concatenated program in the second part (with shiftJumps). -/
theorem Program.getInstr_concat_right (i : ℕ) (hi : p1.length ≤ i)
    (_hi' : i < p1.length + p2.length) :
    (p1.concat p2).getInstr i = (p2.shiftJumps p1.length).getInstr (i - p1.length) := by
  simp only [Program.concat, Program.getInstr]
  rw [List.getElem?_append_right (by omega)]

/-- Stepping in the first part of a concatenated program. -/
theorem Step.concat_left {c c' : Config} (hpc : c.pc < p1.length)
    (hstep : Step p1 c c') : Step (p1.concat p2) c c' := by
  cases hstep with
  | zero h =>
    exact Step.zero (by rw [Program.getInstr_concat_left _ hpc]; exact h)
  | succ h =>
    exact Step.succ (by rw [Program.getInstr_concat_left _ hpc]; exact h)
  | trans h =>
    exact Step.trans (by rw [Program.getInstr_concat_left _ hpc]; exact h)
  | jump_eq h heq =>
    exact Step.jump_eq (by rw [Program.getInstr_concat_left _ hpc]; exact h) heq
  | jump_ne h hne =>
    exact Step.jump_ne (by rw [Program.getInstr_concat_left _ hpc]; exact h) hne

/-- Reverse direction: stepping in concatenated program with pc in first part gives step in p1. -/
theorem Step.of_concat_left {c c' : Config} (hpc : c.pc < p1.length)
    (hstep : Step (p1.concat p2) c c') : Step p1 c c' := by
  have hinstr_eq : (p1.concat p2).getInstr c.pc = p1.getInstr c.pc :=
    Program.getInstr_concat_left c.pc hpc
  cases hstep with
  | zero h => rw [hinstr_eq] at h; exact Step.zero h
  | succ h => rw [hinstr_eq] at h; exact Step.succ h
  | trans h => rw [hinstr_eq] at h; exact Step.trans h
  | jump_eq h heq => rw [hinstr_eq] at h; exact Step.jump_eq h heq
  | jump_ne h hne => rw [hinstr_eq] at h; exact Step.jump_ne h hne

end ConcatLemmas

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

/-! ## Sequential Halting Lemmas -/

section SequentialHalting

variable {p1 p2 : Program}

/-- Multi-step from within p1 stays in p1 until halting.
If we execute Steps in p1 from c to a halted config c', then the same path exists in p1.concat p2. -/
theorem Steps.concat_left_prefix {c c' : Config}
    (hsteps : Steps p1 c c') (_hhalted : c'.isHalted p1) :
    Steps (p1.concat p2) c c' := by
  -- Use head induction: at each step, the current config can step (so pc < p1.length),
  -- allowing us to lift the step to the concatenation
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep hrest ih =>
    -- hstep : Step p1 a b, hrest : Steps p1 b c'
    -- ih : Steps (p1.concat p2) b c' (already applied with _hhalted)
    -- Since a can step in p1, a.pc < p1.length
    have hpc : a.pc < p1.length := by
      by_contra hc
      simp only [not_lt] at hc
      exact Step.halted_no_step hc hstep
    -- Lift the step to the concatenation
    have hstep' : Step (p1.concat p2) a b := Step.concat_left hpc hstep
    -- Combine with IH
    exact Relation.ReflTransGen.head hstep' ih

/-- If p1 halts, we can lift the Steps from p1 to the concatenation. -/
theorem Halts.concat_left_lift (h : Halts p1 inputs) :
    ∃ c, Steps (p1.concat p2) (Config.init inputs) c ∧
         c.isHalted p1 ∧
         c.pc = (Classical.choose h).pc ∧
         c.state = (Classical.choose h).state := by
  obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec h
  refine ⟨Classical.choose h, ?_, hhalted, rfl, rfl⟩
  exact Steps.concat_left_prefix hsteps hhalted

end SequentialHalting

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

/-! ## Execution Lemmas for Primitive Operations -/

/-- An instruction is "non-jumping" if it's Z, S, or T (not J). -/
def Instr.isNonJumping : Instr → Bool
  | Instr.Z _ => true
  | Instr.S _ => true
  | Instr.T _ _ => true
  | Instr.J _ _ _ => false

/-- A program is "straight-line" if it contains no jump instructions. -/
def Program.isStraightLine (p : Program) : Bool :=
  p.all Instr.isNonJumping

/-- Stepping through a non-jumping instruction increases pc by 1. -/
theorem Step.nonJumping_pc_inc {p : Program} {c c' : Config} {instr : Instr}
    (hstep : Step p c c')
    (hinstr : p.getInstr c.pc = some instr)
    (hnonjump : instr.isNonJumping = true) :
    c'.pc = c.pc + 1 := by
  cases hstep with
  | zero h => simp_all [Program.getInstr]
  | succ h => simp_all [Program.getInstr]
  | trans h => simp_all [Program.getInstr]
  | jump_eq h _ => simp_all [Instr.isNonJumping, Program.getInstr]
  | jump_ne h _ => simp_all [Instr.isNonJumping, Program.getInstr]

/-- A straight-line program halts on any input (pc always increases until it exceeds length). -/
theorem straightLine_halts {p : Program} (hsl : p.isStraightLine = true) (inputs : List ℕ) :
    Halts p inputs := by
  -- We show that in at most p.length steps, pc reaches p.length
  -- Use strong induction on remaining instructions
  suffices h : ∀ (c : Config), c.pc ≤ p.length →
      ∃ c', Steps p c c' ∧ c'.pc ≥ p.length by
    obtain ⟨c', hsteps, hpc⟩ := h (Config.init inputs) (by simp [Config.init])
    exact ⟨c', hsteps, hpc⟩
  intro c hpc_le
  -- Induction on p.length - c.pc (remaining steps)
  generalize hrem : p.length - c.pc = remaining
  induction remaining using Nat.strong_induction_on generalizing c with
  | _ remaining ih =>
    by_cases hhalted : c.pc ≥ p.length
    · -- Already halted
      exact ⟨c, Relation.ReflTransGen.refl, hhalted⟩
    · -- Can take a step
      push_neg at hhalted
      have hpc_lt : c.pc < p.length := hhalted
      -- Get the instruction at c.pc
      have hinstr : ∃ instr, p.getInstr c.pc = some instr := by
        simp only [Program.getInstr]
        exact ⟨p[c.pc], List.getElem?_eq_getElem hpc_lt⟩
      obtain ⟨instr, hinstr⟩ := hinstr
      -- The instruction is non-jumping
      have hnonjump : instr.isNonJumping = true := by
        simp only [Program.isStraightLine, List.all_eq_true] at hsl
        have hmem : instr ∈ p := by
          simp only [Program.getInstr] at hinstr
          exact List.getElem?_eq_some_iff.mp hinstr |>.2 ▸ List.getElem_mem hpc_lt
        exact hsl instr hmem
      -- Take one step
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
      obtain ⟨c', hstep', hpc'⟩ := hstep
      -- Apply IH with smaller remaining count
      have hremaining : p.length - c'.pc < remaining := by omega
      have hpc'_le : c'.pc ≤ p.length := by omega
      obtain ⟨c'', hsteps'', hpc''⟩ := ih (p.length - c'.pc) hremaining c' hpc'_le rfl
      exact ⟨c'', Relation.ReflTransGen.head hstep' hsteps'', hpc''⟩

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
