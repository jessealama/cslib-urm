/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Execution

/-! # URM Program Examples

This file provides worked examples of URM programs and their execution,
demonstrating the step semantics defined in `Urm.Execution`.

## Main definitions

- `cutlandSub`: Cutland's subtraction program from page 12

## Notation

- `P ↓ inputs`: Program P converges (halts) on inputs
- `P ↑ inputs`: Program P diverges on inputs

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980], page 12
-/

namespace Urm

/-- Convergence notation: `P ↓ inputs` means program P halts on inputs. -/
scoped notation:50 P " ↓ " inputs => Halts P inputs

/-- Divergence notation: `P ↑ inputs` means program P diverges on inputs. -/
scoped notation:50 P " ↑ " inputs => Diverges P inputs

namespace Examples

/-! ## Cutland's Subtraction Program

This section presents Cutland's example program from page 12 of his textbook.
The program computes `m - n` when `n ≤ m`, but diverges when `n > m`.

Note: This is NOT truncated subtraction (which would return 0 when n > m).
-/

section DivergentSubtraction

/-- Cutland's example program from page 12.

This program computes `m - n` when `n ≤ m`, but diverges when `n > m`.

With initial state R[0]=m, R[1]=n, R[2]=0:
- Loop increments R[1] and R[2] until R[1] = m
- When n ≤ m: terminates after (m - n) iterations with R[2] = m - n
- When n > m: R[1] can never reach R[0] by incrementing, so diverges

Program listing:
```
0: J(0, 1, 5)  -- if R[0] = R[1], jump to 5
1: S(1)        -- R[1]++
2: S(2)        -- R[2]++
3: J(0, 1, 5)  -- if R[0] = R[1], jump to 5
4: J(0, 0, 1)  -- unconditional jump to 1
5: T(2, 0)     -- R[0] := R[2]
```
-/
def cutlandSub : Program := [
  Instr.J 0 1 5,  -- 0: if R[0] = R[1], jump to 5
  Instr.S 1,      -- 1: R[1]++
  Instr.S 2,      -- 2: R[2]++
  Instr.J 0 1 5,  -- 3: if R[0] = R[1], jump to 5
  Instr.J 0 0 1,  -- 4: unconditional jump to 1
  Instr.T 2 0     -- 5: R[0] := R[2]
]

/-! ### Execution trace: cutlandSub ↓ [5, 3]

Initial: pc=0, R[0]=5, R[1]=3, R[2]=0

Step 1: J(0,1,5) - R[0]=5 ≠ R[1]=3, continue
        pc=1, R=[5,3,0]

Step 2: S(1) - R[1]++
        pc=2, R=[5,4,0]

Step 3: S(2) - R[2]++
        pc=3, R=[5,4,1]

Step 4: J(0,1,5) - R[0]=5 ≠ R[1]=4, continue
        pc=4, R=[5,4,1]

Step 5: J(0,0,1) - unconditional jump to 1
        pc=1, R=[5,4,1]

Step 6: S(1) - R[1]++
        pc=2, R=[5,5,1]

Step 7: S(2) - R[2]++
        pc=3, R=[5,5,2]

Step 8: J(0,1,5) - R[0]=5 = R[1]=5, jump to 5
        pc=5, R=[5,5,2]

Step 9: T(2,0) - R[0] := R[2]
        pc=6, R=[2,5,2]

Halted: pc=6 ≥ length(cutlandSub)=6
Output: R[0] = 2 = 5 - 3 ✓
-/

/-! ### Loop invariant and convergence proof -/

/-- When n = m initially, program halts immediately after jumping to T and executing it. -/
theorem init_halts_when_equal (m : ℕ) :
    ∃ c, Steps cutlandSub (Config.init [m, m]) c ∧ c.isHalted cutlandSub ∧ c.state.output = 0 := by
  -- First step: J(0,1,5) succeeds since R[0] = R[1] = m, jump to pc=5
  set init := Config.init [m, m] with hinit
  have h_r0 : init.state.read 0 = m := by simp [hinit, Config.init, State.fromInputs, State.read]
  have h_r1 : init.state.read 1 = m := by simp [hinit, Config.init, State.fromInputs, State.read]
  have h_r2 : init.state.read 2 = 0 := by simp [hinit, Config.init, State.fromInputs, State.read]
  have h_instr0 : cutlandSub.getInstr 0 = some (Instr.J 0 1 5) := rfl
  have step1 : Step cutlandSub init ⟨5, init.state⟩ := Step.jump_eq h_instr0 (by rw [h_r0, h_r1])
  -- Second step: T(2,0) copies R[2]=0 to R[0], pc becomes 6
  have h_instr5 : cutlandSub.getInstr 5 = some (Instr.T 2 0) := rfl
  set final_state := init.state.write 0 (init.state.read 2) with hfinal
  have step2 : Step cutlandSub ⟨5, init.state⟩ ⟨6, final_state⟩ := Step.trans h_instr5
  -- Final state output
  have h_output : final_state.output = 0 := by
    simp only [hfinal, State.output, State.write, Function.update_self, h_r2]
  refine ⟨⟨6, final_state⟩, ?_, ?_, h_output⟩
  · exact Relation.ReflTransGen.head step1 (Relation.ReflTransGen.single step2)
  · simp [Config.isHalted, cutlandSub]

/-- Helper: the loop state after k iterations. R[0]=m, R[1]=n+k, R[2]=k -/
def loopState (m n k : ℕ) : State := fun i =>
  match i with
  | 0 => m
  | 1 => n + k
  | 2 => k
  | _ => 0

/-- Helper: configuration at pc=1 with loop state. -/
def atPc1 (m n k : ℕ) : Config := ⟨1, loopState m n k⟩

/-- One loop iteration when we don't exit: from pc=1 when n+k+1 < m, return to pc=1 with k+1. -/
theorem loop_body_step (m n k : ℕ) (hlt : n + k + 1 < m) :
    ∃ c', StepsN cutlandSub 4 (atPc1 m n k) c' ∧ c' = atPc1 m n (k + 1) := by
  -- Step 1: S(1) at pc=1
  have h_instr1 : cutlandSub.getInstr 1 = some (Instr.S 1) := rfl
  let σ0 := loopState m n k
  let σ1 := σ0.write 1 (n + k + 1)
  have step1 : Step cutlandSub (atPc1 m n k) ⟨2, σ1⟩ := by
    simp only [atPc1]
    exact Step.succ h_instr1
  -- Step 2: S(2) at pc=2
  have h_instr2 : cutlandSub.getInstr 2 = some (Instr.S 2) := rfl
  have h_r2_1 : σ1.read 2 = k := by
    simp only [σ1, State.read, State.write]
    rw [Function.update_of_ne (by decide : (2 : ℕ) ≠ 1)]
    rfl
  let σ2 := σ1.write 2 (k + 1)
  have hσ2 : σ2 = σ1.write 2 (σ1.read 2 + 1) := by simp only [σ2, h_r2_1]
  have step2 : Step cutlandSub ⟨2, σ1⟩ ⟨3, σ2⟩ := by
    rw [hσ2]
    exact Step.succ h_instr2
  -- Step 3: J(0,1,5) at pc=3, fails since R[0] = m ≠ R[1] = n+k+1
  have h_instr3 : cutlandSub.getInstr 3 = some (Instr.J 0 1 5) := rfl
  have h_r0_2 : σ2.read 0 = m := by
    simp only [σ2, σ1, State.read, State.write]
    rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 2)]
    rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 1)]
    rfl
  have h_r1_2 : σ2.read 1 = n + k + 1 := by
    simp only [σ2, σ1, State.read, State.write]
    rw [Function.update_of_ne (by decide : (1 : ℕ) ≠ 2)]
    rw [Function.update_self]
  have step3 : Step cutlandSub ⟨3, σ2⟩ ⟨4, σ2⟩ := by
    apply Step.jump_ne h_instr3
    simp only [h_r0_2, h_r1_2]
    omega
  -- Step 4: J(0,0,1) at pc=4, unconditional jump to 1
  have h_instr4 : cutlandSub.getInstr 4 = some (Instr.J 0 0 1) := rfl
  have step4 : Step cutlandSub ⟨4, σ2⟩ ⟨1, σ2⟩ := by
    apply Step.jump_eq h_instr4
    rfl
  -- Combine steps
  have hsteps : StepsN cutlandSub 4 (atPc1 m n k) ⟨1, σ2⟩ :=
    StepsN.succ step1 (StepsN.succ step2 (StepsN.succ step3 (StepsN.succ step4 (StepsN.zero _))))
  -- Show σ2 = loopState m n (k + 1)
  have hσ2_eq : σ2 = loopState m n (k + 1) := by
    funext i
    simp only [σ2, σ1, σ0, State.write, loopState, Function.update]
    split <;> split <;> simp_all [Nat.add_assoc]
    -- Remaining case: i ≠ 2 and i ≠ 1
    rename_i h1 h2
    -- Since i ≠ 1 and i ≠ 2, either i = 0 or i ≥ 3. Both sides are equal.
    match i with
    | 0 => rfl  -- both give m
    | 1 => exact absurd rfl h2
    | 2 => exact absurd rfl h1
    | _ + 3 => rfl  -- both give 0
  refine ⟨⟨1, σ2⟩, hsteps, ?_⟩
  simp only [atPc1, hσ2_eq]

/-- Exit from loop: when n + k + 1 = m, we halt in 4 steps with output k + 1 = m - n. -/
theorem loop_exit_step (m n k : ℕ) (heq : n + k + 1 = m) :
    ∃ c', StepsN cutlandSub 4 (atPc1 m n k) c' ∧ c'.isHalted cutlandSub ∧ c'.state.output = k + 1 := by
  -- Step 1: S(1) at pc=1
  have h_instr1 : cutlandSub.getInstr 1 = some (Instr.S 1) := rfl
  let σ0 := loopState m n k
  have h_r1_0 : σ0.read 1 = n + k := rfl
  let σ1 := σ0.write 1 (n + k + 1)
  have step1 : Step cutlandSub (atPc1 m n k) ⟨2, σ1⟩ := by
    simp only [atPc1]
    exact Step.succ h_instr1
  -- Step 2: S(2) at pc=2
  have h_instr2 : cutlandSub.getInstr 2 = some (Instr.S 2) := rfl
  have h_r2_1 : σ1.read 2 = k := by
    simp only [σ1, State.read, State.write]
    rw [Function.update_of_ne (by decide : (2 : ℕ) ≠ 1)]
    rfl
  let σ2 := σ1.write 2 (k + 1)
  have hσ2 : σ2 = σ1.write 2 (σ1.read 2 + 1) := by simp only [σ2, h_r2_1]
  have step2 : Step cutlandSub ⟨2, σ1⟩ ⟨3, σ2⟩ := by
    rw [hσ2]
    exact Step.succ h_instr2
  -- Step 3: J(0,1,5) at pc=3, succeeds since R[0] = m = R[1] = n+k+1
  have h_instr3 : cutlandSub.getInstr 3 = some (Instr.J 0 1 5) := rfl
  have h_r0_2 : σ2.read 0 = m := by
    simp only [σ2, σ1, State.read, State.write]
    rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 2)]
    rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 1)]
    rfl
  have h_r1_2 : σ2.read 1 = n + k + 1 := by
    simp only [σ2, σ1, State.read, State.write]
    rw [Function.update_of_ne (by decide : (1 : ℕ) ≠ 2)]
    rw [Function.update_self]
  have step3 : Step cutlandSub ⟨3, σ2⟩ ⟨5, σ2⟩ := by
    apply Step.jump_eq h_instr3
    simp only [h_r0_2, h_r1_2, heq]
  -- Step 4: T(2,0) at pc=5
  have h_instr5 : cutlandSub.getInstr 5 = some (Instr.T 2 0) := rfl
  have h_r2_2 : σ2.read 2 = k + 1 := by
    simp only [σ2, State.read, State.write]
    rw [Function.update_self]
  let σ3 := σ2.write 0 (σ2.read 2)
  have step4 : Step cutlandSub ⟨5, σ2⟩ ⟨6, σ3⟩ := Step.trans h_instr5
  -- Combine steps
  have hsteps : StepsN cutlandSub 4 (atPc1 m n k) ⟨6, σ3⟩ :=
    StepsN.succ step1 (StepsN.succ step2 (StepsN.succ step3 (StepsN.succ step4 (StepsN.zero _))))
  -- Show halted and output
  have hhalted : (⟨6, σ3⟩ : Config).isHalted cutlandSub := by simp [Config.isHalted, cutlandSub]
  have houtput : σ3.output = k + 1 := by
    simp only [σ3, State.output, State.write, Function.update_self, h_r2_2]
  exact ⟨⟨6, σ3⟩, hsteps, hhalted, houtput⟩

/-- From pc=1 with n + k < m, we eventually halt with output m - n.
    Note: we require strict inequality because at pc=1, we need room for at least one S(1). -/
theorem loop_terminates (m n k : ℕ) (hlt : n + k < m) :
    ∃ c, Steps cutlandSub (atPc1 m n k) c ∧ c.isHalted cutlandSub ∧ c.state.output = m - n := by
  -- Induction on m - n - k - 1 (the remaining full iterations before exit)
  obtain ⟨d, hd⟩ : ∃ d, d = m - n - k - 1 := ⟨_, rfl⟩
  induction d using Nat.strong_induction_on generalizing k with
  | _ d ih =>
    by_cases hexit : n + k + 1 = m
    · -- Base case: n + k + 1 = m, we exit immediately
      obtain ⟨c', hsteps, hhalted, hout⟩ := loop_exit_step m n k hexit
      have hout' : c'.state.output = m - n := by
        rw [hout]
        omega
      exact ⟨c', hsteps.toSteps, hhalted, hout'⟩
    · -- Inductive case: n + k + 1 < m, do one iteration then recurse
      have hlt' : n + k + 1 < m := Nat.lt_of_le_of_ne (by omega) hexit
      obtain ⟨c', hsteps, hc'⟩ := loop_body_step m n k hlt'
      have hlt'' : n + (k + 1) < m := by omega
      have hd' : m - n - (k + 1) - 1 < d := by omega
      obtain ⟨cfinal, hsteps', hhalted, hout⟩ := ih (m - n - (k + 1) - 1) hd' (k + 1) hlt'' rfl
      refine ⟨cfinal, ?_, hhalted, hout⟩
      rw [hc'] at hsteps
      exact Relation.ReflTransGen.trans hsteps.toSteps hsteps'

/-- Cutland's program converges when n ≤ m. -/
theorem cutlandSub_converges (m n : ℕ) (h : n ≤ m) : cutlandSub ↓ [m, n] := by
  by_cases heq : n = m
  · -- Equal case: immediate halt
    subst heq
    obtain ⟨c, hsteps, hhalted, _⟩ := init_halts_when_equal n
    exact ⟨c, hsteps, hhalted⟩
  · -- n < m: first step goes to pc=1, then loop terminates
    have hlt : n < m := Nat.lt_of_le_of_ne h heq
    -- First step: J(0,1,5) fails since n ≠ m, goes to pc=1
    set init := Config.init [m, n] with hinit
    have h_r0 : init.state.read 0 = m := by simp [hinit, Config.init, State.fromInputs, State.read]
    have h_r1 : init.state.read 1 = n := by simp [hinit, Config.init, State.fromInputs, State.read]
    have h_instr0 : cutlandSub.getInstr 0 = some (Instr.J 0 1 5) := rfl
    have hne : m ≠ n := Ne.symm heq
    have step1 : Step cutlandSub init ⟨1, init.state⟩ :=
      Step.jump_ne h_instr0 (by rw [h_r0, h_r1]; exact hne)
    -- Show init.state = loopState m n 0
    have hstate : init.state = loopState m n 0 := by
      funext i
      simp only [hinit, Config.init, State.fromInputs, loopState]
      match i with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | i + 3 => simp [List.getD]
    -- Now use loop_terminates (we have n < m, so n + 0 < m)
    have hlt' : n + 0 < m := by omega
    rw [hstate] at step1
    obtain ⟨cfinal, hsteps, hhalted, _⟩ := loop_terminates m n 0 hlt'
    refine ⟨cfinal, ?_, hhalted⟩
    exact Relation.ReflTransGen.head step1 hsteps

/-- Invariant for divergent case: when in the loop with R[1] > R[0], the program stays in the loop.
    The invariant is: pc ∈ {0,1,2,3,4} and R[0] = m and R[1] > m -/
private def LoopInvariant (m : ℕ) (c : Config) : Prop :=
  c.pc ≤ 4 ∧ c.state.read 0 = m ∧ c.state.read 1 > m

/-- The loop invariant is preserved by Step when active. -/
private theorem loop_invariant_preserved {m : ℕ} {c c' : Config}
    (hinv : LoopInvariant m c) (hstep : Step cutlandSub c c') : LoopInvariant m c' := by
  obtain ⟨hpc, hr0, hr1⟩ := hinv
  simp only [State.read] at hr0 hr1
  -- Case analysis on pc value (0, 1, 2, 3, or 4)
  match hpc_val : c.pc with
  | 0 =>
    -- pc=0: J(0,1,5) - The jump requires R[0]=R[1], but R[1] > R[0]=m
    cases hstep with
    | jump_ne h _ =>
      simp only [LoopInvariant, State.read]
      exact ⟨by omega, hr0, hr1⟩
    | jump_eq h heq =>
      have : cutlandSub.getInstr 0 = some (Instr.J 0 1 5) := rfl
      rw [hpc_val, this] at h
      cases h
      simp only [State.read] at heq
      omega
    | zero h | succ h | trans h =>
      have : cutlandSub.getInstr 0 = some (Instr.J 0 1 5) := rfl
      rw [hpc_val, this] at h
      cases h
  | 1 =>
    -- pc=1: S(1) - increment R[1], go to pc=2
    cases hstep with
    | succ h =>
      have : cutlandSub.getInstr 1 = some (Instr.S 1) := rfl
      rw [hpc_val, this] at h
      cases h
      simp only [LoopInvariant, State.read, State.write, Function.update]
      exact ⟨by omega, by simp [hr0], by simp; omega⟩
    | zero h | trans h | jump_eq h _ | jump_ne h _ =>
      have : cutlandSub.getInstr 1 = some (Instr.S 1) := rfl
      rw [hpc_val, this] at h
      cases h
  | 2 =>
    -- pc=2: S(2) - increment R[2], go to pc=3
    cases hstep with
    | succ h =>
      have : cutlandSub.getInstr 2 = some (Instr.S 2) := rfl
      rw [hpc_val, this] at h
      cases h
      simp only [LoopInvariant, State.read, State.write, Function.update]
      exact ⟨by omega, by simp [hr0], by simp [hr1]⟩
    | zero h | trans h | jump_eq h _ | jump_ne h _ =>
      have : cutlandSub.getInstr 2 = some (Instr.S 2) := rfl
      rw [hpc_val, this] at h
      cases h
  | 3 =>
    -- pc=3: J(0,1,5) - The jump requires R[0]=R[1], but R[1] > R[0]=m
    cases hstep with
    | jump_ne h _ =>
      simp only [LoopInvariant, State.read]
      exact ⟨by omega, hr0, hr1⟩
    | jump_eq h heq =>
      have : cutlandSub.getInstr 3 = some (Instr.J 0 1 5) := rfl
      rw [hpc_val, this] at h
      cases h
      simp only [State.read] at heq
      omega
    | zero h | succ h | trans h =>
      have : cutlandSub.getInstr 3 = some (Instr.J 0 1 5) := rfl
      rw [hpc_val, this] at h
      cases h
  | 4 =>
    -- pc=4: J(0,0,1) - unconditional jump to 1
    cases hstep with
    | jump_eq h _ =>
      have : cutlandSub.getInstr 4 = some (Instr.J 0 0 1) := rfl
      rw [hpc_val, this] at h
      cases h
      simp only [LoopInvariant, State.read]
      exact ⟨by omega, hr0, hr1⟩
    | jump_ne h hne =>
      have : cutlandSub.getInstr 4 = some (Instr.J 0 0 1) := rfl
      rw [hpc_val, this] at h
      cases h
      simp only [State.read] at hne
      exact absurd rfl hne
    | zero h | succ h | trans h =>
      have : cutlandSub.getInstr 4 = some (Instr.J 0 0 1) := rfl
      rw [hpc_val, this] at h
      cases h
  | n + 5 =>
    omega

/-- When n > m, the initial configuration satisfies the loop invariant (after first step). -/
private theorem init_step_satisfies_invariant {m n : ℕ} (hgt : n > m) :
    ∃ c', Step cutlandSub (Config.init [m, n]) c' ∧ LoopInvariant m c' := by
  -- First step: J(0,1,5) fails since n > m, goes to pc=1
  have h_instr0 : cutlandSub.getInstr 0 = some (Instr.J 0 1 5) := rfl
  set init_cfg := Config.init [m, n] with hinit
  have h_r0 : init_cfg.state.read 0 = m := rfl
  have h_r1 : init_cfg.state.read 1 = n := rfl
  have hne : m ≠ n := by omega
  have step1 : Step cutlandSub init_cfg ⟨1, init_cfg.state⟩ :=
    Step.jump_ne h_instr0 (by rw [h_r0, h_r1]; exact hne)
  refine ⟨⟨1, init_cfg.state⟩, step1, ?_, ?_, ?_⟩
  · show (1 : ℕ) ≤ 4; decide
  · exact h_r0
  · show init_cfg.state 1 > m; rw [show init_cfg.state 1 = n from rfl]; omega

/-- Configurations satisfying the invariant are not halted. -/
private theorem loop_invariant_not_halted {m : ℕ} {c : Config} (hinv : LoopInvariant m c) :
    ¬c.isHalted cutlandSub := by
  obtain ⟨hpc, _, _⟩ := hinv
  simp only [Config.isHalted, cutlandSub, List.length_cons, List.length_nil, not_le]
  omega

/-- Key lemma: when n > m, all configurations reachable via Steps satisfy the invariant
    (after the first step). -/
private theorem steps_preserve_invariant {m : ℕ} {c c' : Config}
    (hinv : LoopInvariant m c) (hsteps : Steps cutlandSub c c') : LoopInvariant m c' := by
  induction hsteps with
  | refl => exact hinv
  | tail _ hstep ih => exact loop_invariant_preserved ih hstep

/-- When n > m, Cutland's program diverges. -/
theorem cutlandSub_diverges (m n : ℕ) (hgt : n > m) : cutlandSub ↑ [m, n] := by
  intro ⟨c_halt, hsteps, hhalted⟩
  -- Get the first step which satisfies the invariant
  obtain ⟨c', hstep_first, hinv_first⟩ := init_step_satisfies_invariant hgt
  -- The first step must be part of any non-empty path to c_halt
  cases hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- Config.init is halted - contradiction since pc=0 < 6
    simp [Config.isHalted, cutlandSub, Config.init] at hhalted
  | head hstep hrest =>
    -- By determinism, the first step goes to c'
    have heq := Step.deterministic hstep hstep_first
    subst heq
    -- All subsequent configs satisfy the invariant
    have hinv_halt := steps_preserve_invariant hinv_first hrest
    -- But configs satisfying the invariant aren't halted
    exact loop_invariant_not_halted hinv_halt hhalted

/-- Cutland's program converges iff n ≤ m.

The reverse direction (halts → n ≤ m) requires showing that when n > m,
the program diverges. This follows because:
- R[1] starts at n > m = R[0] and only increases via S(1)
- Therefore R[1] > R[0] is an invariant of all reachable configurations
- The J checks at pc=0 and pc=3 never succeed, so the loop runs forever
-/
theorem cutlandSub_converges_iff (m n : ℕ) : (cutlandSub ↓ [m, n]) ↔ n ≤ m := by
  constructor
  · intro hhalts
    by_contra hgt
    push_neg at hgt
    exact cutlandSub_diverges m n hgt hhalts
  · exact cutlandSub_converges m n

/-- When Cutland's program converges, the result is m - n.

The proof requires showing that the halting configuration chosen by Classical.choose
has output m - n. Since Step is deterministic, all executions from the initial
configuration reach the same halting configuration, which our proof of
`loop_terminates` shows has output = m - n.
-/
theorem cutlandSub_result (m n : ℕ) (h : n ≤ m) :
    Result cutlandSub [m, n] (cutlandSub_converges m n h) = m - n := by
  -- Get the configuration chosen by Classical.choose
  have hspec := Classical.choose_spec (cutlandSub_converges m n h)
  -- hspec : Steps cutlandSub (Config.init [m, n]) c ∧ c.isHalted cutlandSub
  obtain ⟨hsteps_chosen, hhalted_chosen⟩ := hspec
  -- Construct a halting config with the known output
  by_cases heq : n = m
  · -- Case n = m: output should be 0
    subst heq
    obtain ⟨c_proven, hsteps_proven, hhalted_proven, hout_proven⟩ := init_halts_when_equal n
    -- By halts_unique, c_chosen = c_proven
    have heq_configs :=
      Steps.halts_unique hsteps_chosen hhalted_chosen hsteps_proven hhalted_proven
    simp only [Result, heq_configs, hout_proven, Nat.sub_self]
  · -- Case n < m: use the loop termination proof
    have hlt : n < m := Nat.lt_of_le_of_ne h heq
    -- First step: J(0,1,5) fails since n ≠ m, goes to pc=1
    set init := Config.init [m, n] with hinit
    have h_r0 : init.state.read 0 = m := by simp [hinit, Config.init, State.fromInputs, State.read]
    have h_r1 : init.state.read 1 = n := by simp [hinit, Config.init, State.fromInputs, State.read]
    have h_instr0 : cutlandSub.getInstr 0 = some (Instr.J 0 1 5) := rfl
    have hne : m ≠ n := Ne.symm heq
    have step1 : Step cutlandSub init ⟨1, init.state⟩ :=
      Step.jump_ne h_instr0 (by rw [h_r0, h_r1]; exact hne)
    -- Show init.state = loopState m n 0
    have hstate : init.state = loopState m n 0 := by
      funext i
      simp only [hinit, Config.init, State.fromInputs, loopState]
      match i with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | i + 3 => simp [List.getD]
    -- Now use loop_terminates
    have hlt' : n + 0 < m := by omega
    rw [hstate] at step1
    obtain ⟨c_proven, hsteps_loop, hhalted_proven, hout_proven⟩ := loop_terminates m n 0 hlt'
    -- Combine first step with loop steps
    have hsteps_proven : Steps cutlandSub init c_proven :=
      Relation.ReflTransGen.head step1 hsteps_loop
    -- By halts_unique, c_chosen = c_proven
    have heq_configs :=
      Steps.halts_unique hsteps_chosen hhalted_chosen hsteps_proven hhalted_proven
    simp only [Result, heq_configs, hout_proven]

end DivergentSubtraction

end Examples

end Urm
