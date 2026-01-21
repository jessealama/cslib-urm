/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Simulate.EncodedStep
import Mathlib.Computability.Primrec



/-! # Primitive Recursiveness of Step Functions

This file proves that the URM step function, when operating on encoded configurations,
is primitive recursive. This is the key technical lemma for showing that
URM-computable functions are partial recursive.

## Main results

- `nth_encoded_primrec`: `nth_encoded r` is primitive recursive for fixed r
- `nth_encoded_primrec₂`: `nth_encoded` is primitive recursive in both arguments
- `update_nth_encoded_primrec₂`: `update_nth_encoded r` is primitive recursive for fixed r
- `update_nth_encoded_primrec₃`: `update_nth_encoded` is primitive recursive in all three arguments
- `encoded_step_primrec_fixed`: Single step is primitive recursive (for fixed program)
- `encoded_is_halted_nat_primrec_fixed`: Halting check is primitive recursive
- `iterate_encoded_step_primrec_fixed`: Step iteration is primitive recursive

## Strategy

For a fixed program p with bound = p.max_register:
1. Register read/write at fixed indices are primitive recursive
2. Each instruction type (Z, S, T, J) produces a primitive recursive update
3. The full step combines these with primitive recursive case analysis

The key insight is that for a *fixed* program, all the case analyses and
register accesses are at *fixed* positions, making everything primitive recursive.
-/

namespace Urm

open Nat (pair unpair)

/-! ## Primitive Recursive Register Operations -/

/-- For a fixed r, `nth_encoded r` is primitive recursive. -/
theorem nth_encoded_primrec (r : ℕ) : Nat.Primrec (nth_encoded r) := by
  induction r with
  | zero => exact Nat.Primrec.left
  | succ r ih => exact ih.comp Nat.Primrec.right

/-- For a fixed r, `update_nth_encoded r` is primitive recursive in (encoded, newVal). -/
theorem update_nth_encoded_primrec₂ (r : ℕ) :
    Primrec₂ (update_nth_encoded r) := by
  induction r with
  | zero =>
    -- update_nth_encoded 0 n v = pair v n.unpair.2
    apply Primrec₂.natPair.comp
    · exact Primrec₂.right
    · exact (Primrec.snd.comp Primrec.unpair).comp₂ Primrec₂.left
  | succ r ih =>
    -- update_nth_encoded (r+1) n v = pair n.unpair.1 (update_nth_encoded r n.unpair.2 v)
    apply Primrec₂.natPair.comp
    · exact (Primrec.fst.comp Primrec.unpair).comp₂ Primrec₂.left
    · exact ih.comp₂ ((Primrec.snd.comp Primrec.unpair).comp₂ Primrec₂.left) Primrec₂.right

/-! ## Helper Functions for Variable-Position Primitiveness

To prove `nth_encoded` and `update_nth_encoded` are primitive recursive in all arguments,
we use helper functions based on iteration:
- `iterUnpairRight r x` - iterates `.unpair.2` r times
- `iterBuildState r x` - collects prefix left values in a stack while iterating
- `rebuildFromStack r stack y` - reconstructs the encoded list from stack
-/

/-- Iterate .unpair.2 r times on a value. -/
private def iterUnpairRight : ℕ → ℕ → ℕ
  | 0, x => x
  | r + 1, x => iterUnpairRight r x.unpair.2

/-- unpair.2 commutes with iterUnpairRight. -/
private theorem iterUnpairRight_unpair_comm (n x : ℕ) :
    (iterUnpairRight n x).unpair.2 = iterUnpairRight n x.unpair.2 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [iterUnpairRight]; exact ih (x.unpair.2)

/-- iterUnpairRight matches the primitive recursion pattern. -/
private theorem iterUnpairRight_eq_nat_rec (n x : ℕ) :
    Nat.rec (motive := fun _ => ℕ) x (fun _k ih => ih.unpair.2) n = iterUnpairRight n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    calc Nat.rec (motive := fun _ => ℕ) x (fun _k ih => ih.unpair.2) (n + 1)
        = (Nat.rec (motive := fun _ => ℕ) x (fun _k ih => ih.unpair.2) n).unpair.2 := rfl
      _ = (iterUnpairRight n x).unpair.2 := by rw [ih]
      _ = iterUnpairRight n (x.unpair.2) := iterUnpairRight_unpair_comm n x
      _ = iterUnpairRight (n + 1) x := by simp only [iterUnpairRight]

/-- iterUnpairRight is primitive recursive in both arguments. -/
private theorem iterUnpairRight_primrec₂ : Primrec₂ iterUnpairRight := by
  -- Using Primrec.nat_rec with signature:
  --   Primrec₂ (fun a n => Nat.rec (f a) (fun n IH => g a (n, IH)) n)
  have hbase : Primrec (id : ℕ → ℕ) := Primrec.id
  have hstep : Primrec₂ (fun (_x : ℕ) (nIH : ℕ × ℕ) => nIH.2.unpair.2) := by
    exact (Primrec.snd.comp Primrec.unpair).comp₂ (Primrec.snd.comp₂ Primrec₂.right)
  have hprec := Primrec.nat_rec hbase hstep
  -- hprec gives Primrec₂ (fun x n => Nat.rec x (fun k ih => ih.unpair.2) n)
  apply Primrec₂.swap
  apply Primrec₂.of_eq hprec
  intro x n
  exact iterUnpairRight_eq_nat_rec n x

/-- nth_encoded in terms of iterUnpairRight. -/
private theorem nth_encoded_eq_iterUnpairRight (r encoded : ℕ) :
    nth_encoded r encoded = (iterUnpairRight r encoded).unpair.1 := by
  induction r generalizing encoded with
  | zero => rfl
  | succ r ih =>
    simp only [nth_encoded_succ, iterUnpairRight, ih]

/-- nth_encoded is primitive recursive in both arguments. -/
theorem nth_encoded_primrec₂ : Primrec₂ nth_encoded := by
  have h : Primrec₂ (fun r encoded => (iterUnpairRight r encoded).unpair.1) := by
    exact (Primrec.fst.comp Primrec.unpair).comp₂ iterUnpairRight_primrec₂
  apply Primrec₂.of_eq h
  intro r encoded
  exact (nth_encoded_eq_iterUnpairRight r encoded).symm

/-! ## Helper functions for update_nth_encoded primitiveness

To prove `update_nth_encoded` is primitive recursive in all three arguments, we use two helpers:
1. `iterBuildState r x` - iterates forward, collecting prefix left values in a stack
2. `rebuildFromStack r stack y` - pops r elements from stack, pairs them with y

The composition gives: `update_nth_encoded r x v = rebuildFromStack r (iterBuildState r x).2 (pair v (iterUnpairRight r x).unpair.2)`
-/

/-- Forward iteration collecting left values as a stack.
    Returns (position after r steps, stack of r left values in reverse order). -/
private def iterBuildState : ℕ → ℕ → ℕ × ℕ
  | 0, x => (x, 0)
  | r + 1, x =>
    let (pos, acc) := iterBuildState r x
    (pos.unpair.2, pair pos.unpair.1 acc)

/-- iterBuildState returns iterUnpairRight in its first component. -/
private theorem iterBuildState_fst (r x : ℕ) :
    (iterBuildState r x).1 = iterUnpairRight r x := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
    simp only [iterBuildState, iterUnpairRight]
    -- By IH: (iterBuildState r x).1 = iterUnpairRight r x
    -- Goal: (iterUnpairRight r x).unpair.2 = iterUnpairRight r x.unpair.2
    rw [ih, iterUnpairRight_unpair_comm]

/-- iterBuildState matches Nat.rec pattern. -/
private theorem iterBuildState_eq_nat_rec (r x : ℕ) :
    Nat.rec (x, 0) (fun _k (pos, acc) => (pos.unpair.2, pair pos.unpair.1 acc)) r =
    iterBuildState r x := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
    simp only [iterBuildState, ← ih]

/-- iterBuildState is primitive recursive. -/
private theorem iterBuildState_primrec₂ : Primrec₂ iterBuildState := by
  -- Use Primrec.nat_rec: Primrec f → Primrec₂ g → Primrec₂ (fun a n => Nat.rec (f a) (g a) n)
  have hbase : Primrec (fun x : ℕ => (x, 0)) :=
    Primrec.pair Primrec.id (Primrec.const 0)
  -- Step: (pos, acc) => (pos.unpair.2, pair pos.unpair.1 acc)
  -- In nat_rec, step receives (_x : ℕ) and (nIH : ℕ × (ℕ × ℕ)) where nIH = (n, IH) = (n, (pos, acc))
  have hstep : Primrec₂ (fun (_x : ℕ) (nIH : ℕ × (ℕ × ℕ)) =>
      (nIH.2.1.unpair.2, pair nIH.2.1.unpair.1 nIH.2.2)) := by
    -- Work at the Primrec level and convert to Primrec₂
    -- First component: p.2.2.1.unpair.2 (where p = (x, nIH))
    let hfst : Primrec (fun p : ℕ × (ℕ × (ℕ × ℕ)) => p.2.2.1.unpair.2) :=
      (Primrec.snd.comp Primrec.unpair).comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    -- Second component: pair p.2.2.1.unpair.1 p.2.2.2
    let h1 : Primrec (fun p : ℕ × (ℕ × (ℕ × ℕ)) => p.2.2.1.unpair.1) :=
      (Primrec.fst.comp Primrec.unpair).comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    let h2 : Primrec (fun p : ℕ × (ℕ × (ℕ × ℕ)) => p.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    let hsnd : Primrec (fun p : ℕ × (ℕ × (ℕ × ℕ)) => pair p.2.2.1.unpair.1 p.2.2.2) :=
      Primrec₂.natPair.comp h1 h2
    -- Combine into a pair-valued function
    let hpair : Primrec (fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
        (p.2.2.1.unpair.2, pair p.2.2.1.unpair.1 p.2.2.2)) :=
      Primrec.pair hfst hsnd
    -- Convert directly to Primrec₂ using to₂
    exact hpair.to₂
  have hprec := Primrec.nat_rec hbase hstep
  apply Primrec₂.swap
  apply Primrec₂.of_eq hprec
  intro x r
  exact iterBuildState_eq_nat_rec r x

/-- Rebuild from a reversed stack: pop r elements from stack, pairing with accumulator.
    rebuildFromStack r stack y pops r left values from stack, builds pair structure with y at end. -/
private def rebuildFromStack : ℕ → ℕ → ℕ → ℕ
  | 0, _, y => y
  | r + 1, stack, y => rebuildFromStack r stack.unpair.2 (pair stack.unpair.1 y)

/-- Key lemma: stepping the iteration matches the rebuildFromStack recursion. -/
private theorem rebuildFromStack_step (r stack y : ℕ) :
    pair (iterUnpairRight r stack).unpair.1 (rebuildFromStack r stack y)
    = rebuildFromStack r stack.unpair.2 (pair stack.unpair.1 y) := by
  induction r generalizing stack y with
  | zero =>
    -- LHS: pair stack.unpair.1 y
    -- RHS: rebuildFromStack 0 stack.unpair.2 (pair stack.unpair.1 y) = pair stack.unpair.1 y
    simp only [iterUnpairRight, rebuildFromStack]
  | succ r ih =>
    -- LHS: pair (iterUnpairRight (r+1) stack).unpair.1 (rebuildFromStack (r+1) stack y)
    simp only [iterUnpairRight, rebuildFromStack]
    -- After simp (which applies iterUnpairRight_unpair_comm):
    -- LHS = pair (iterUnpairRight r stack.unpair.2).unpair.1 (rebuildFromStack r stack.unpair.2 (pair stack.unpair.1 y))
    -- RHS = rebuildFromStack r (stack.unpair.2).unpair.2 (pair (stack.unpair.2).unpair.1 (pair stack.unpair.1 y))
    -- Apply IH with stack' = stack.unpair.2, y' = pair stack.unpair.1 y
    exact ih stack.unpair.2 (pair stack.unpair.1 y)

/-- rebuildFromStack is primitive recursive via direct Nat.rec formulation. -/
private theorem rebuildFromStack_primrec :
    Primrec fun p : ℕ × ℕ × ℕ => rebuildFromStack p.1 p.2.1 p.2.2 := by
  -- Use Primrec.nat_rec with state = (remaining stack position, accumulated result)
  -- State type: ℕ × ℕ where first is iterUnpairRight k stack, second is partial result
  -- Base: (stack, y)
  -- Step k (stk, acc) => (stk.unpair.2, pair stk.unpair.1 acc)
  -- Final result is second component after r steps
  have hbase : Primrec (fun p : ℕ × ℕ => p) := Primrec.id
  have hstep : Primrec₂ (fun (_p : ℕ × ℕ) (nIH : ℕ × (ℕ × ℕ)) =>
      (nIH.2.1.unpair.2, pair nIH.2.1.unpair.1 nIH.2.2)) := by
    -- Work at the Primrec level (q = (_p, nIH))
    let hfst : Primrec (fun q : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => q.2.2.1.unpair.2) :=
      (Primrec.snd.comp Primrec.unpair).comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    let h1 : Primrec (fun q : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => q.2.2.1.unpair.1) :=
      (Primrec.fst.comp Primrec.unpair).comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    let h2 : Primrec (fun q : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => q.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    let hsnd : Primrec (fun q : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => pair q.2.2.1.unpair.1 q.2.2.2) :=
      Primrec₂.natPair.comp h1 h2
    let hpair : Primrec (fun q : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) =>
        (q.2.2.1.unpair.2, pair q.2.2.1.unpair.1 q.2.2.2)) :=
      Primrec.pair hfst hsnd
    -- Convert directly to Primrec₂ using to₂
    exact hpair.to₂
  have hprec := Primrec.nat_rec hbase hstep
  -- hprec : Primrec₂ (fun (stack, y) r => state after r iterations starting from (stack, y))
  -- First, define the iterated state function
  let iterState : ℕ → ℕ → ℕ → ℕ × ℕ := fun r stack y =>
    Nat.rec (stack, y) (fun _k (stk, acc) => (stk.unpair.2, pair stk.unpair.1 acc)) r
  -- Show iterState r stack y = (iterUnpairRight r stack, rebuildFromStack r stack y)
  have hIterState : ∀ r stack y, iterState r stack y =
      (iterUnpairRight r stack, rebuildFromStack r stack y) := by
    intro r
    induction r with
    | zero => intro stack y; rfl
    | succ r ih =>
      intro stack y
      simp only [iterState, iterUnpairRight, rebuildFromStack]
      specialize ih stack y
      simp only [iterState] at ih
      conv_lhs => rw [ih]
      -- LHS = ((iterUnpairRight r stack).unpair.2, pair (iterUnpairRight r stack).unpair.1 (rebuildFromStack r stack y))
      -- RHS = (iterUnpairRight r stack.unpair.2, rebuildFromStack r stack.unpair.2 (pair stack.unpair.1 y))
      ext
      · -- First component
        exact iterUnpairRight_unpair_comm r stack
      · -- Second component
        exact rebuildFromStack_step r stack y
  -- Now compose
  have hswap : Primrec₂ (fun r (p : ℕ × ℕ) => iterState r p.1 p.2) := by
    apply Primrec₂.of_eq (Primrec₂.swap hprec)
    intro r p
    rfl
  have hTriple : Primrec fun p : ℕ × ℕ × ℕ => iterState p.1 p.2.1 p.2.2 :=
    hswap.comp Primrec.fst Primrec.snd
  have hResult : Primrec fun p : ℕ × ℕ × ℕ => (iterState p.1 p.2.1 p.2.2).2 :=
    Primrec.snd.comp hTriple
  apply Primrec.of_eq hResult
  intro p
  rw [hIterState]

/-- Key structural property: relates rebuilding from shifted stacks. -/
private theorem rebuildFromStack_shift (r encoded y : ℕ) :
    pair encoded.unpair.1
      (rebuildFromStack r (iterBuildState r encoded.unpair.2).2 y) =
    rebuildFromStack r (iterBuildState r encoded).2
      (pair (iterUnpairRight r encoded).unpair.1 y) := by
  induction r generalizing encoded y with
  | zero =>
    simp only [rebuildFromStack, iterUnpairRight]
  | succ r ih =>
    -- Unfold one level of each structure
    simp only [iterBuildState, rebuildFromStack, iterUnpairRight]
    -- After unfolding, use iterBuildState_fst to replace (iterBuildState r _).1 with iterUnpairRight
    rw [iterBuildState_fst, iterBuildState_fst]
    simp only [Nat.unpair_pair]
    -- Now the goal matches the IH with y' = pair (iterUnpairRight r encoded.unpair.2).unpair.1 y
    exact ih encoded (pair (iterUnpairRight r encoded.unpair.2).unpair.1 y)

/-- Key relationship: update_nth_encoded equals composition of helpers. -/
private theorem update_nth_encoded_eq_rebuild (r encoded newVal : ℕ) :
    update_nth_encoded r encoded newVal =
    rebuildFromStack r (iterBuildState r encoded).2 (pair newVal (iterUnpairRight r encoded).unpair.2) := by
  induction r generalizing encoded with
  | zero =>
    simp only [update_nth_encoded_zero, rebuildFromStack, iterUnpairRight]
  | succ r ih =>
    simp only [update_nth_encoded_succ, iterBuildState, rebuildFromStack]
    -- LHS: pair encoded.unpair.1 (update_nth_encoded r encoded.unpair.2 newVal)
    -- Apply IH to recursive call
    rw [ih]
    -- Now use rebuildFromStack_shift to transform the LHS
    have h := rebuildFromStack_shift r encoded (pair newVal (iterUnpairRight r encoded.unpair.2).unpair.2)
    rw [h]
    -- Use iterBuildState_fst and iterUnpairRight_unpair_comm to simplify
    rw [iterBuildState_fst]
    simp only [Nat.unpair_pair, iterUnpairRight, iterUnpairRight_unpair_comm]

/-- update_nth_encoded is primitive recursive in all three arguments. -/
theorem update_nth_encoded_primrec₃ : Primrec fun p : ℕ × ℕ × ℕ =>
    update_nth_encoded p.1 p.2.1 p.2.2 := by
  -- Express update_nth_encoded using the helper composition
  have hCompose : Primrec fun p : ℕ × ℕ × ℕ =>
      rebuildFromStack p.1 (iterBuildState p.1 p.2.1).2
        (pair p.2.2 (iterUnpairRight p.1 p.2.1).unpair.2) := by
    -- Build the composition step by step
    -- iterBuildState p.1 p.2.1 is Primrec
    let hIterBuild : Primrec fun p : ℕ × ℕ × ℕ => iterBuildState p.1 p.2.1 :=
      iterBuildState_primrec₂.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
    -- (iterBuildState p.1 p.2.1).2 is Primrec
    let hStack : Primrec fun p : ℕ × ℕ × ℕ => (iterBuildState p.1 p.2.1).2 :=
      Primrec.snd.comp hIterBuild
    -- iterUnpairRight p.1 p.2.1 is Primrec
    let hIterRight : Primrec fun p : ℕ × ℕ × ℕ => iterUnpairRight p.1 p.2.1 :=
      iterUnpairRight_primrec₂.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
    -- (iterUnpairRight p.1 p.2.1).unpair.2 is Primrec
    let hTail : Primrec fun p : ℕ × ℕ × ℕ => (iterUnpairRight p.1 p.2.1).unpair.2 :=
      (Primrec.snd.comp Primrec.unpair).comp hIterRight
    -- pair p.2.2 (iterUnpairRight p.1 p.2.1).unpair.2 is Primrec
    let hNewTail : Primrec fun p : ℕ × ℕ × ℕ =>
        pair p.2.2 (iterUnpairRight p.1 p.2.1).unpair.2 :=
      Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd) hTail
    -- rebuildFromStack p.1 stack newTail is Primrec via composition
    -- We need to build the triple (p.1, stack, newTail) and apply rebuildFromStack_primrec
    let hTriple : Primrec fun p : ℕ × ℕ × ℕ =>
        (p.1, (iterBuildState p.1 p.2.1).2, pair p.2.2 (iterUnpairRight p.1 p.2.1).unpair.2) :=
      Primrec.pair Primrec.fst (Primrec.pair hStack hNewTail)
    exact rebuildFromStack_primrec.comp hTriple
  -- Now show equality
  apply Primrec.of_eq hCompose
  intro p
  exact (update_nth_encoded_eq_rebuild p.1 p.2.1 p.2.2).symm

set_option maxHeartbeats 2000000 in
/-- For fixed progCode and bound, the step function is primitive recursive. -/
theorem encoded_step_primrec_fixed (progCode bound : ℕ) :
    Nat.Primrec (fun configCode => encoded_step progCode bound configCode) := by
  -- Fixed constants from the program
  let progLen := progCode.unpair.1
  let progInstrs := progCode.unpair.2

  -- Step 1: Shared projections (all unary Primrec over configCode)
  have hPc : Primrec (fun c : ℕ => c.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hRegs : Primrec (fun c : ℕ => c.unpair.2) := Primrec.snd.comp Primrec.unpair

  -- Instruction lookup: nth_encoded pc progInstrs
  have hInstr : Primrec (fun c : ℕ => nth_encoded c.unpair.1 progInstrs) :=
    nth_encoded_primrec₂.comp hPc (Primrec.const progInstrs)

  -- Tag and args extraction from instruction
  have hTag : Primrec (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).comp hInstr
  have hArgs : Primrec (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).comp hInstr

  -- pc + 1 (used in most branches)
  have hPcNext : Primrec (fun c : ℕ => c.unpair.1 + 1) :=
    Primrec.nat_add.comp hPc (Primrec.const 1)

  -- Step 2: Default branch - pair (pc + 1) regsCode
  have hDefault : Primrec (fun c : ℕ => pair (c.unpair.1 + 1) c.unpair.2) :=
    Primrec₂.natPair.comp hPcNext hRegs

  -- Step 3: Z case (tag=0)
  -- Z n: if n ≤ bound then pair (pc+1) (update_nth_encoded n regs 0) else pair (pc+1) regs
  -- where n = args
  have hZPred : PrimrecPred (fun c : ℕ =>
      (nth_encoded c.unpair.1 progInstrs).unpair.2 ≤ bound) :=
    Primrec.nat_le.comp hArgs (Primrec.const bound)
  -- The "then" branch: pair (pc+1) (update_nth_encoded n regs 0)
  have hZThen : Primrec (fun c : ℕ =>
      pair (c.unpair.1 + 1) (update_nth_encoded
        (nth_encoded c.unpair.1 progInstrs).unpair.2 c.unpair.2 0)) :=
    Primrec₂.natPair.comp hPcNext
      (update_nth_encoded_primrec₃.comp (Primrec.pair hArgs (Primrec.pair hRegs (Primrec.const 0))))
  have hZ : Primrec (fun c : ℕ =>
      if (nth_encoded c.unpair.1 progInstrs).unpair.2 ≤ bound then
        pair (c.unpair.1 + 1) (update_nth_encoded
          (nth_encoded c.unpair.1 progInstrs).unpair.2 c.unpair.2 0)
      else pair (c.unpair.1 + 1) c.unpair.2) :=
    Primrec.ite hZPred hZThen hDefault

  -- Step 4: S case (tag=1)
  -- S n: if n ≤ bound then pair (pc+1) (update_nth_encoded n regs (nth_encoded n regs + 1)) else default
  -- where n = args
  -- Old value lookup: nth_encoded n regs
  have hSOldVal : Primrec (fun c : ℕ =>
      nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2 c.unpair.2) :=
    nth_encoded_primrec₂.comp hArgs hRegs
  -- New value: oldVal + 1
  have hSNewVal : Primrec (fun c : ℕ =>
      nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2 c.unpair.2 + 1) :=
    Primrec.nat_add.comp hSOldVal (Primrec.const 1)
  -- The "then" branch: pair (pc+1) (update_nth_encoded n regs newVal)
  have hSThen : Primrec (fun c : ℕ =>
      pair (c.unpair.1 + 1) (update_nth_encoded
        (nth_encoded c.unpair.1 progInstrs).unpair.2 c.unpair.2
        (nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2 c.unpair.2 + 1))) :=
    Primrec₂.natPair.comp hPcNext
      (update_nth_encoded_primrec₃.comp (Primrec.pair hArgs (Primrec.pair hRegs hSNewVal)))
  have hS : Primrec (fun c : ℕ =>
      if (nth_encoded c.unpair.1 progInstrs).unpair.2 ≤ bound then
        pair (c.unpair.1 + 1) (update_nth_encoded
          (nth_encoded c.unpair.1 progInstrs).unpair.2 c.unpair.2
          (nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2 c.unpair.2 + 1))
      else pair (c.unpair.1 + 1) c.unpair.2) :=
    Primrec.ite hZPred hSThen hDefault  -- Reuse hZPred since same condition

  -- Step 5: T case (tag=2)
  -- T m n: copy register m to n
  -- if n ≤ bound then pair (pc+1) (update_nth_encoded n regs (if m ≤ bound then nth_encoded m regs else 0)) else default
  -- Extract m and n from args
  have hTM : Primrec (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).comp hArgs
  have hTN : Primrec (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).comp hArgs
  -- Predicate for n ≤ bound
  have hTNPred : PrimrecPred (fun c : ℕ =>
      (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2 ≤ bound) :=
    Primrec.nat_le.comp hTN (Primrec.const bound)
  -- Predicate for m ≤ bound
  have hTMPred : PrimrecPred (fun c : ℕ =>
      (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 ≤ bound) :=
    Primrec.nat_le.comp hTM (Primrec.const bound)
  -- srcVal = if m ≤ bound then nth_encoded m regs else 0
  have hTMVal : Primrec (fun c : ℕ =>
      nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 c.unpair.2) :=
    nth_encoded_primrec₂.comp hTM hRegs
  have hTSrcVal : Primrec (fun c : ℕ =>
      if (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 ≤ bound then
        nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 c.unpair.2
      else 0) :=
    Primrec.ite hTMPred hTMVal (Primrec.const 0)
  -- The "then" branch: pair (pc+1) (update_nth_encoded n regs srcVal)
  have hTThen : Primrec (fun c : ℕ =>
      pair (c.unpair.1 + 1) (update_nth_encoded
        (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2 c.unpair.2
        (if (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 ≤ bound then
          nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 c.unpair.2
        else 0))) :=
    Primrec₂.natPair.comp hPcNext
      (update_nth_encoded_primrec₃.comp (Primrec.pair hTN (Primrec.pair hRegs hTSrcVal)))
  have hT : Primrec (fun c : ℕ =>
      if (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2 ≤ bound then
        pair (c.unpair.1 + 1) (update_nth_encoded
          (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2 c.unpair.2
          (if (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 ≤ bound then
            nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 c.unpair.2
          else 0))
      else pair (c.unpair.1 + 1) c.unpair.2) :=
    Primrec.ite hTNPred hTThen hDefault

  -- Step 6: J case (tag=3)
  -- J m nReg q: if mVal = nVal then pair q regs else pair (pc+1) regs
  -- where mVal = if m ≤ bound then nth_encoded m regs else 0
  --       nVal = if nReg ≤ bound then nth_encoded nReg regs else 0
  -- Extract m, nReg, q from args
  have hJM : Primrec (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).comp hArgs
  have hJNReg : Primrec (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).comp ((Primrec.snd.comp Primrec.unpair).comp hArgs)
  have hJQ : Primrec (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).comp ((Primrec.snd.comp Primrec.unpair).comp hArgs)
  -- Predicate for m ≤ bound
  have hJMPred : PrimrecPred (fun c : ℕ =>
      (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 ≤ bound) :=
    Primrec.nat_le.comp hJM (Primrec.const bound)
  -- Predicate for nReg ≤ bound
  have hJNPred : PrimrecPred (fun c : ℕ =>
      (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.1 ≤ bound) :=
    Primrec.nat_le.comp hJNReg (Primrec.const bound)
  -- mVal = if m ≤ bound then nth_encoded m regs else 0
  have hJMValLookup : Primrec (fun c : ℕ =>
      nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 c.unpair.2) :=
    nth_encoded_primrec₂.comp hJM hRegs
  have hJMVal : Primrec (fun c : ℕ =>
      if (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 ≤ bound then
        nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 c.unpair.2
      else 0) :=
    Primrec.ite hJMPred hJMValLookup (Primrec.const 0)
  -- nVal = if nReg ≤ bound then nth_encoded nReg regs else 0
  have hJNValLookup : Primrec (fun c : ℕ =>
      nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.1 c.unpair.2) :=
    nth_encoded_primrec₂.comp hJNReg hRegs
  have hJNVal : Primrec (fun c : ℕ =>
      if (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.1 ≤ bound then
        nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.1 c.unpair.2
      else 0) :=
    Primrec.ite hJNPred hJNValLookup (Primrec.const 0)
  -- Equality predicate for mVal = nVal
  have hJEqPred : PrimrecPred (fun c : ℕ =>
      (if (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 ≤ bound then
        nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 c.unpair.2
      else 0) =
      (if (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.1 ≤ bound then
        nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.1 c.unpair.2
      else 0)) :=
    Primrec.eq.comp hJMVal hJNVal
  -- "then" branch: pair q regs
  have hJThen : Primrec (fun c : ℕ =>
      pair (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.2 c.unpair.2) :=
    Primrec₂.natPair.comp hJQ hRegs
  -- "else" branch: pair (pc+1) regs (same as hDefault)
  have hJ : Primrec (fun c : ℕ =>
      if (if (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 ≤ bound then
            nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.1 c.unpair.2
          else 0) =
         (if (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.1 ≤ bound then
            nth_encoded (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.1 c.unpair.2
          else 0)
      then pair (nth_encoded c.unpair.1 progInstrs).unpair.2.unpair.2.unpair.2 c.unpair.2
      else pair (c.unpair.1 + 1) c.unpair.2) :=
    Primrec.ite hJEqPred hJThen hDefault

  -- Step 7: Tag dispatch using nested ite
  -- Tag predicates
  have hTagEq0 : PrimrecPred (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.1 = 0) :=
    Primrec.eq.comp hTag (Primrec.const 0)
  have hTagEq1 : PrimrecPred (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.1 = 1) :=
    Primrec.eq.comp hTag (Primrec.const 1)
  have hTagEq2 : PrimrecPred (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.1 = 2) :=
    Primrec.eq.comp hTag (Primrec.const 2)
  have hTagEq3 : PrimrecPred (fun c : ℕ => (nth_encoded c.unpair.1 progInstrs).unpair.1 = 3) :=
    Primrec.eq.comp hTag (Primrec.const 3)

  -- Build dispatch: if tag=0 then Z, else if tag=1 then S, else if tag=2 then T, else if tag=3 then J, else default
  have hExec : Primrec (fun c : ℕ => _) :=
    Primrec.ite hTagEq0 hZ (Primrec.ite hTagEq1 hS (Primrec.ite hTagEq2 hT (Primrec.ite hTagEq3 hJ hDefault)))

  -- Step 8: Outer halted check
  have hNotHalted : PrimrecPred (fun c : ℕ => c.unpair.1 < progLen) :=
    Primrec.nat_lt.comp hPc (Primrec.const progLen)

  -- Final: if not halted then execute else return unchanged
  have hFinal : Primrec (fun c : ℕ => _) :=
    Primrec.ite hNotHalted hExec Primrec.id

  -- Convert to Nat.Primrec and show equality with encoded_step
  apply Primrec.nat_iff.mp
  apply hFinal.of_eq
  intro c
  -- Now that encoded_step uses if-then-else instead of match,
  -- both sides have the same structure and the proof is direct.
  -- Note: progLen = (unpair progCode).1 and progInstrs = (unpair progCode).2 by definition
  rfl

/-- For fixed progCode, the halting check is primitive recursive. -/
theorem encoded_is_halted_nat_primrec_fixed (progCode : ℕ) :
    Nat.Primrec (fun configCode => encoded_is_halted_nat progCode configCode) := by
  -- encoded_is_halted_nat progCode configCode =
  --   if progCode.unpair.1 ≤ configCode.unpair.1 then 1 else 0
  -- This equals (decide (progCode.unpair.1 ≤ configCode.unpair.1)).toNat
  -- where progCode.unpair.1 is a constant K
  let K := progCode.unpair.1
  -- Step 1: Show the predicate (K ≤ configCode.unpair.1) is PrimrecPred
  have hPred : PrimrecPred (fun (configCode : ℕ) => K ≤ configCode.unpair.1) :=
    Primrec.nat_le.comp (Primrec.const K) (Primrec.fst.comp Primrec.unpair)
  -- Step 2: Convert to Primrec function returning Bool
  have hBool : Primrec (fun (configCode : ℕ) => decide (K ≤ configCode.unpair.1)) :=
    hPred.decide
  -- Step 3: Compose with Bool.toNat (any function from Bool is Primrec)
  have hToNat : Primrec Bool.toNat := Primrec.dom_bool _
  have hComp : Primrec (fun (configCode : ℕ) => (decide (K ≤ configCode.unpair.1)).toNat) :=
    hToNat.comp hBool
  -- Step 4: Show this equals encoded_is_halted_nat progCode
  -- Since K = progCode.unpair.1 by definition, the equality is definitional
  have hEq : ∀ (configCode : ℕ), (decide (K ≤ configCode.unpair.1)).toNat =
      encoded_is_halted_nat progCode configCode := fun configCode => by
    simp only [encoded_is_halted_nat, encoded_is_halted, Bool.toNat, Bool.cond_decide,
               decide_eq_true_eq, K]
  -- Step 5: Convert to Nat.Primrec using nat_iff
  exact Primrec.nat_iff.mp (hComp.of_eq hEq)

/-! ## Iteration -/

/-- Iterate the step function n times on an encoded configuration. -/
def iterate_encoded_step (progCode bound : ℕ) : ℕ → ℕ → ℕ
  | 0, configCode => configCode
  | n + 1, configCode => iterate_encoded_step progCode bound n (encoded_step progCode bound configCode)

/-- iterate_encoded_step equals Function.iterate. -/
theorem iterate_encoded_step_eq_iterate (progCode bound n configCode : ℕ) :
    iterate_encoded_step progCode bound n configCode =
    (encoded_step progCode bound)^[n] configCode := by
  induction n generalizing configCode with
  | zero => rfl
  | succ n ih =>
    simp only [iterate_encoded_step, Function.iterate_succ_apply]
    exact ih (encoded_step progCode bound configCode)

/-- For fixed progCode and bound, iteration is primitive recursive. -/
theorem iterate_encoded_step_primrec_fixed (progCode bound : ℕ) :
    Primrec₂ (iterate_encoded_step progCode bound) := by
  -- Convert Nat.Primrec to Primrec
  have hStep : Primrec (encoded_step progCode bound) :=
    Primrec.nat_iff.mpr (encoded_step_primrec_fixed progCode bound)
  -- Build Primrec₂ for the constant step function
  have hStep₂ : Primrec₂ (fun (_ : ℕ × ℕ) (c : ℕ) => encoded_step progCode bound c) :=
    hStep.comp₂ Primrec₂.right
  -- Apply nat_iterate: (h a)^[f a] (g a) with f=fst, g=snd, h=const step
  have hIter : Primrec fun p : ℕ × ℕ => (encoded_step progCode bound)^[p.1] p.2 :=
    Primrec.nat_iterate Primrec.fst Primrec.snd hStep₂
  -- Convert to Primrec₂ using equality
  exact Primrec₂.of_eq hIter fun n c =>
    (iterate_encoded_step_eq_iterate progCode bound n c).symm

/-- Iteration correctness: iterating n times corresponds to StepsN. -/
theorem iterate_encoded_step_correct (p : Program) (n : ℕ) (c c' : Config)
    (hsteps : StepsN p n c c') :
    let bound := p.max_register
    let progCode := encode_program p
    iterate_encoded_step progCode bound n (encode_config bound c) = encode_config bound c' := by
  -- Induction on the step count
  induction hsteps with
  | zero =>
    -- 0 steps: c' = c, and iterate_encoded_step _ _ 0 x = x
    rfl
  | @succ n' c0 c1 c2 hstep hrest ih =>
    -- n'+1 steps: Step c0 to c1, then n' steps from c1 to c2
    -- iterate_encoded_step _ _ (n'+1) x = iterate_encoded_step _ _ n' (encoded_step _ _ x)
    simp only [iterate_encoded_step]
    -- encoded_step on encoded c0 gives encoded c1 (by encoded_step_correct)
    rw [encoded_step_correct p c0 c1 hstep]
    -- Now apply IH: iterate_encoded_step on encoded c1 gives encoded c2
    exact ih

end Urm
