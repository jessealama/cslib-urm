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

- `P`: Cutland's subtraction program from page 12

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

The `@[simp]` attribute enables automatic instruction lookup in proofs.
Array indexing works with compile-time bounds checking: `P[0]`, `P[5]`, etc. -/
@[simp] def P : Program := [
  Instr.J 0 1 5,  -- 0: if R[0] = R[1], jump to 5
  Instr.S 1,      -- 1: R[1]++
  Instr.S 2,      -- 2: R[2]++
  Instr.J 0 1 5,  -- 3: if R[0] = R[1], jump to 5
  Instr.J 0 0 1,  -- 4: unconditional jump to 1
  Instr.T 2 0     -- 5: R[0] := R[2]
]

/-! ### Example: `P ↓ [5, 3]` yields `2`

The loop iterates twice (R[1]: 3→4→5, R[2]: 0→1→2), then outputs R[2] = 2 = 5 - 3. -/

/-! ### Loop invariant and convergence proof -/

/-- When n = m initially, program halts immediately after jumping to T and executing it. -/
theorem init_halts_when_equal (m : ℕ) :
    ∃ c, Steps P (Config.init [m, m]) c ∧ c.isHalted P ∧ c.state.output = 0 := by
  -- First step: J(0,1,5) succeeds since R[0] = R[1] = m, jump to pc=5
  set init := Config.init [m, m] with hinit
  have h_r0 : init.state.read 0 = m := by simp [hinit, Config.init, State.fromInputs, State.read]
  have h_r1 : init.state.read 1 = m := by simp [hinit, Config.init, State.fromInputs, State.read]
  have h_r2 : init.state.read 2 = 0 := by simp [hinit, Config.init, State.fromInputs, State.read]
  have h_instr0 : P.getInstr 0 = some (Instr.J 0 1 5) := rfl
  have step1 : Step P init ⟨5, init.state⟩ := Step.jump_eq h_instr0 (by rw [h_r0, h_r1])
  -- Second step: T(2,0) copies R[2]=0 to R[0], pc becomes 6
  have h_instr5 : P.getInstr 5 = some (Instr.T 2 0) := rfl
  set final_state := init.state.write 0 (init.state.read 2) with hfinal
  have step2 : Step P ⟨5, init.state⟩ ⟨6, final_state⟩ := Step.trans h_instr5
  -- Final state output
  have h_output : final_state.output = 0 := by
    simp only [hfinal, State.output, State.write, Function.update_self, h_r2]
  refine ⟨⟨6, final_state⟩, ?_, ?_, h_output⟩
  · exact Relation.ReflTransGen.head step1 (Relation.ReflTransGen.single step2)
  · simp [Config.isHalted, P]

/-- Helper: the loop state after k iterations. R[0]=m, R[1]=n+k, R[2]=k -/
def loopState (m n k : ℕ) : State := fun i =>
  match i with
  | 0 => m
  | 1 => n + k
  | 2 => k
  | _ => 0

/-- Helper: configuration at pc=1 with loop state. -/
def atPc1 (m n k : ℕ) : Config := ⟨1, loopState m n k⟩

/-- State after incrementing R[1] and R[2]: R[0]=m, R[1]=n+k+1, R[2]=k+1 -/
private def stateAfterIncr (m n k : ℕ) : State := fun i =>
  match i with
  | 0 => m
  | 1 => n + k + 1
  | 2 => k + 1
  | _ => 0

/-- Execute S(1); S(2) from pc=1, reaching pc=3 with incremented R[1] and R[2]. -/
private theorem loop_incr_steps (m n k : ℕ) :
    StepsN P 2 (atPc1 m n k) ⟨3, stateAfterIncr m n k⟩ := by
  have h_instr1 : P.getInstr 1 = some (Instr.S 1) := rfl
  have h_instr2 : P.getInstr 2 = some (Instr.S 2) := rfl
  let σ0 := loopState m n k
  let σ1 := σ0.write 1 (n + k + 1)
  have step1 : Step P (atPc1 m n k) ⟨2, σ1⟩ := Step.succ h_instr1
  have h_r2_1 : σ1.read 2 = k := by
    simp only [σ1, State.read, State.write, Function.update_of_ne (by decide : (2 : ℕ) ≠ 1)]
    rfl
  let σ2 := σ1.write 2 (k + 1)
  have step2 : Step P ⟨2, σ1⟩ ⟨3, σ2⟩ := by
    have heq : σ2 = σ1.write 2 (σ1.read 2 + 1) := by simp only [σ2, h_r2_1]
    rw [heq]; exact Step.succ h_instr2
  have hσ2_eq : σ2 = stateAfterIncr m n k := by
    funext i; simp only [σ2, σ1, σ0, State.write, loopState, stateAfterIncr, Function.update]
    match i with
    | 0 => simp
    | 1 => simp [Nat.add_assoc]
    | 2 => simp
    | _ + 3 => simp
  rw [← hσ2_eq]
  exact StepsN.succ step1 (StepsN.succ step2 (StepsN.zero _))

/-- Register reads from stateAfterIncr. -/
private theorem stateAfterIncr_read (m n k : ℕ) :
    (stateAfterIncr m n k).read 0 = m ∧
    (stateAfterIncr m n k).read 1 = n + k + 1 ∧
    (stateAfterIncr m n k).read 2 = k + 1 := ⟨rfl, rfl, rfl⟩

/-- One loop iteration when we don't exit: from pc=1 when n+k+1 < m, return to pc=1 with k+1. -/
theorem loop_body_step (m n k : ℕ) (hlt : n + k + 1 < m) :
    ∃ c', StepsN P 4 (atPc1 m n k) c' ∧ c' = atPc1 m n (k + 1) := by
  have steps12 := loop_incr_steps m n k
  set σ2 := stateAfterIncr m n k with hσ2_def
  have h_r0 : σ2.read 0 = m := rfl
  have h_r1 : σ2.read 1 = n + k + 1 := rfl
  -- Step 3: J(0,1,5) fails since R[0] = m ≠ R[1] = n+k+1
  have h_instr3 : P.getInstr 3 = some (Instr.J 0 1 5) := rfl
  have step3 : Step P ⟨3, σ2⟩ ⟨4, σ2⟩ :=
    Step.jump_ne h_instr3 (by rw [h_r0, h_r1]; omega)
  -- Step 4: J(0,0,1) unconditional jump to 1
  have h_instr4 : P.getInstr 4 = some (Instr.J 0 0 1) := rfl
  have step4 : Step P ⟨4, σ2⟩ ⟨1, σ2⟩ := Step.jump_eq h_instr4 rfl
  -- Combine and show σ2 = loopState m n (k + 1)
  have hσ2_loop : σ2 = loopState m n (k + 1) := by
    funext i; simp only [hσ2_def, stateAfterIncr, loopState]
    match i with | 0 | 1 | 2 | _ + 3 => rfl
  refine ⟨⟨1, σ2⟩, StepsN.add steps12 (StepsN.succ step3 (StepsN.succ step4 (StepsN.zero _))), ?_⟩
  simp only [atPc1, hσ2_loop]

/-- Exit from loop: when n + k + 1 = m, we halt in 4 steps with output k + 1 = m - n. -/
theorem loop_exit_step (m n k : ℕ) (heq : n + k + 1 = m) :
    ∃ c', StepsN P 4 (atPc1 m n k) c' ∧ c'.isHalted P ∧ c'.state.output = k + 1 := by
  have steps12 := loop_incr_steps m n k
  set σ2 := stateAfterIncr m n k with hσ2_def
  have h_r0 : σ2.read 0 = m := rfl
  have h_r1 : σ2.read 1 = n + k + 1 := rfl
  have h_r2 : σ2.read 2 = k + 1 := rfl
  -- Step 3: J(0,1,5) succeeds since R[0] = m = R[1] = n+k+1
  have h_instr3 : P.getInstr 3 = some (Instr.J 0 1 5) := rfl
  have step3 : Step P ⟨3, σ2⟩ ⟨5, σ2⟩ :=
    Step.jump_eq h_instr3 (by rw [h_r0, h_r1, heq])
  -- Step 4: T(2,0) copies R[2] to R[0]
  have h_instr5 : P.getInstr 5 = some (Instr.T 2 0) := rfl
  set σ3 := σ2.write 0 (σ2.read 2) with hσ3_def
  have step4 : Step P ⟨5, σ2⟩ ⟨6, σ3⟩ := Step.trans h_instr5
  -- Combine and verify
  have hhalted : (⟨6, σ3⟩ : Config).isHalted P := by simp [Config.isHalted, P]
  have houtput : σ3.output = k + 1 := by
    simp only [hσ3_def, State.output, State.write, Function.update_self, h_r2]
  exact ⟨⟨6, σ3⟩, StepsN.add steps12 (StepsN.succ step3 (StepsN.succ step4 (StepsN.zero _))),
         hhalted, houtput⟩

/-- From pc=1 with n + k < m, we eventually halt with output m - n.
    Note: we require strict inequality because at pc=1, we need room for at least one S(1). -/
theorem loop_terminates (m n k : ℕ) (hlt : n + k < m) :
    ∃ c, Steps P (atPc1 m n k) c ∧ c.isHalted P ∧ c.state.output = m - n := by
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

/-- Helper: initial state equals loopState m n 0. -/
private theorem init_state_eq_loopState (m n : ℕ) :
    (Config.init [m, n]).state = loopState m n 0 := by
  funext i; simp only [Config.init, State.fromInputs, loopState]
  match i with | 0 | 1 | 2 => simp | _ + 3 => simp [List.getD]

/-- Helper: when n < m, first step enters loop, then terminates with output m - n. -/
private theorem enters_loop_and_halts (m n : ℕ) (hlt : n < m) :
    ∃ c, Steps P (Config.init [m, n]) c ∧ c.isHalted P ∧ c.state.output = m - n := by
  have h_instr0 : P.getInstr 0 = some (Instr.J 0 1 5) := rfl
  have step1 : Step P (Config.init [m, n]) ⟨1, (Config.init [m, n]).state⟩ :=
    Step.jump_ne h_instr0 (by simp [Config.init, State.fromInputs, State.read]; omega)
  rw [init_state_eq_loopState] at step1
  obtain ⟨c, hsteps, hhalted, hout⟩ := loop_terminates m n 0 (by omega : n + 0 < m)
  exact ⟨c, Relation.ReflTransGen.head step1 hsteps, hhalted, hout⟩

/-- Cutland's program converges when n ≤ m. -/
theorem P_converges (m n : ℕ) (h : n ≤ m) : P ↓ [m, n] := by
  rcases h.eq_or_lt with rfl | hlt
  · obtain ⟨c, hsteps, hhalted, _⟩ := init_halts_when_equal n; exact ⟨c, hsteps, hhalted⟩
  · obtain ⟨c, hsteps, hhalted, _⟩ := enters_loop_and_halts m n hlt; exact ⟨c, hsteps, hhalted⟩

/-- Invariant for divergent case: when in the loop with R[1] > R[0], the program stays in the loop.
    The invariant is: pc ∈ {0,1,2,3,4} and R[0] = m and R[1] > m -/
private def LoopInvariant (m : ℕ) (c : Config) : Prop :=
  c.pc ≤ 4 ∧ c.state.read 0 = m ∧ c.state.read 1 > m

/-- The loop invariant is preserved by Step when active. -/
private theorem loop_invariant_preserved {m : ℕ} {c c' : Config}
    (hinv : LoopInvariant m c) (hstep : Step P c c') : LoopInvariant m c' := by
  obtain ⟨hpc, hr0, hr1⟩ := hinv
  simp only [State.read] at hr0 hr1
  -- Case split on Step constructor, then dispatch on pc value
  cases hstep with
  | zero h =>
    match hpc_val : c.pc with
    | 0 | 1 | 2 | 3 | 4 => simp_all [Program.getInstr]  -- No Z instructions at these positions
    | _ + 5 => omega
  | trans h =>
    match hpc_val : c.pc with
    | 0 | 1 | 2 | 3 | 4 => simp_all [Program.getInstr]  -- No T instructions at these positions
    | _ + 5 => omega
  | succ h =>
    match hpc_val : c.pc with
    | 0 | 3 | 4 => simp_all [Program.getInstr]  -- No S instructions at these positions
    | 1 =>
      simp only [hpc_val] at h; cases h
      refine ⟨(by decide : (2 : ℕ) ≤ 4), ?_, ?_⟩
      · simp only [State.write, State.read, Function.update_of_ne (by decide : (0 : ℕ) ≠ 1), hr0]
      · simp only [State.write, State.read, Function.update_self]; omega
    | 2 =>
      simp only [hpc_val] at h; cases h
      refine ⟨(by decide : (3 : ℕ) ≤ 4), ?_, ?_⟩
      · simp only [State.write, State.read, Function.update_of_ne (by decide : (0 : ℕ) ≠ 2), hr0]
      · simp only [State.write, State.read, Function.update_of_ne (by decide : (1 : ℕ) ≠ 2), hr1]
    | _ + 5 => omega
  | jump_eq h heq =>
    match hpc_val : c.pc with
    | 1 | 2 => simp_all [Program.getInstr]  -- No J instructions at these positions
    | 0 | 3 =>
      simp only [hpc_val] at h; cases h
      simp only [State.read] at heq; omega
    | 4 =>
      simp only [hpc_val] at h; cases h
      exact ⟨(by decide : (1 : ℕ) ≤ 4), hr0, hr1⟩
    | _ + 5 => omega
  | jump_ne h hne =>
    match hpc_val : c.pc with
    | 1 | 2 => simp_all [Program.getInstr]  -- No J instructions at these positions
    | 0 => exact ⟨(by decide : (1 : ℕ) ≤ 4), hr0, hr1⟩
    | 3 => exact ⟨(by decide : (4 : ℕ) ≤ 4), hr0, hr1⟩
    | 4 =>
      simp only [hpc_val] at h; cases h
      simp only [State.read] at hne; exact absurd rfl hne
    | _ + 5 => omega

/-- When n > m, the initial configuration satisfies the loop invariant (after first step). -/
private theorem init_step_satisfies_invariant {m n : ℕ} (hgt : n > m) :
    ∃ c', Step P (Config.init [m, n]) c' ∧ LoopInvariant m c' := by
  -- First step: J(0,1,5) fails since n > m, goes to pc=1
  have h_instr0 : P.getInstr 0 = some (Instr.J 0 1 5) := rfl
  set init_cfg := Config.init [m, n] with hinit
  have h_r0 : init_cfg.state.read 0 = m := rfl
  have h_r1 : init_cfg.state.read 1 = n := rfl
  have hne : m ≠ n := by omega
  have step1 : Step P init_cfg ⟨1, init_cfg.state⟩ :=
    Step.jump_ne h_instr0 (by rw [h_r0, h_r1]; exact hne)
  refine ⟨⟨1, init_cfg.state⟩, step1, ?_, ?_, ?_⟩
  · show (1 : ℕ) ≤ 4; decide
  · exact h_r0
  · show init_cfg.state 1 > m; rw [show init_cfg.state 1 = n from rfl]; omega

/-- Configurations satisfying the invariant are not halted. -/
private theorem loop_invariant_not_halted {m : ℕ} {c : Config} (hinv : LoopInvariant m c) :
    ¬c.isHalted P := by
  obtain ⟨hpc, _, _⟩ := hinv
  simp only [Config.isHalted, P, List.length_cons, List.length_nil, not_le]
  omega

/-- Key lemma: when n > m, all configurations reachable via Steps satisfy the invariant
    (after the first step). -/
private theorem steps_preserve_invariant {m : ℕ} {c c' : Config}
    (hinv : LoopInvariant m c) (hsteps : Steps P c c') : LoopInvariant m c' := by
  induction hsteps with
  | refl => exact hinv
  | tail _ hstep ih => exact loop_invariant_preserved ih hstep

/-- When n > m, Cutland's program diverges. -/
theorem P_diverges (m n : ℕ) (hgt : n > m) : P ↑ [m, n] := by
  intro ⟨c_halt, hsteps, hhalted⟩
  -- Get the first step which satisfies the invariant
  obtain ⟨c', hstep_first, hinv_first⟩ := init_step_satisfies_invariant hgt
  -- The first step must be part of any non-empty path to c_halt
  cases hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- Config.init is halted - contradiction since pc=0 < 6
    simp [Config.isHalted, P, Config.init] at hhalted
  | head hstep hrest =>
    -- By determinism, the first step goes to c'
    have heq := Step.deterministic hstep hstep_first
    subst heq
    -- All subsequent configs satisfy the invariant
    have hinv_halt := steps_preserve_invariant hinv_first hrest
    -- But configs satisfying the invariant aren't halted
    exact loop_invariant_not_halted hinv_halt hhalted

/-- Cutland's program converges iff n ≤ m. -/
theorem P_converges_iff (m n : ℕ) : (P ↓ [m, n]) ↔ n ≤ m := by
  constructor
  · intro hhalts
    by_contra hgt
    push_neg at hgt
    exact P_diverges m n hgt hhalts
  · exact P_converges m n

/-- When Cutland's program converges, the result is m - n. -/
theorem P_result (m n : ℕ) (h : n ≤ m) :
    Result P [m, n] (P_converges m n h) = m - n := by
  obtain ⟨hsteps_chosen, hhalted_chosen⟩ := Classical.choose_spec (P_converges m n h)
  rcases h.eq_or_lt with rfl | hlt
  · -- Case n = m: output is 0
    obtain ⟨c, hsteps, hhalted, hout⟩ := init_halts_when_equal n
    simp [Result, Steps.halts_unique hsteps_chosen hhalted_chosen hsteps hhalted, hout]
  · -- Case n < m: use enters_loop_and_halts
    obtain ⟨c, hsteps, hhalted, hout⟩ := enters_loop_and_halts m n hlt
    simp [Result, Steps.halts_unique hsteps_chosen hhalted_chosen hsteps hhalted, hout]

end DivergentSubtraction

end Examples

end Urm
