/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Part

/-! # URM Execution Semantics

Single-step and multi-step execution semantics for URMs.

## Main definitions

- `Urm.Step`: Single-step execution relation
- `Urm.Steps`: Multi-step execution (reflexive-transitive closure of `Step`)
- `Urm.Halts`: A program halts on given inputs
- `Urm.Diverges`: A program diverges on given inputs

## Main statements

- `Step.deterministic`: The step relation is deterministic
- `halted_no_step`: Halted configurations have no successor

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

variable (p : Program)

/-- Single-step execution relation for URMs.

Each constructor corresponds to one of the four instruction types:
- `zero`: Execute `Z n` (set register n to 0)
- `succ`: Execute `S n` (increment register n)
- `trans`: Execute `T m n` (copy register m to register n)
- `jump_eq`: Execute `J m n q` when registers m and n are equal (jump to q)
- `jump_ne`: Execute `J m n q` when registers m and n differ (proceed to next)
-/
inductive Step : Config → Config → Prop where
  | zero {c : Config} {n : ℕ}
      (h : p.getInstr c.pc = some (Instr.Z n)) :
      Step c ⟨c.pc + 1, c.state.write n 0⟩
  | succ {c : Config} {n : ℕ}
      (h : p.getInstr c.pc = some (Instr.S n)) :
      Step c ⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩
  | trans {c : Config} {m n : ℕ}
      (h : p.getInstr c.pc = some (Instr.T m n)) :
      Step c ⟨c.pc + 1, c.state.write n (c.state.read m)⟩
  | jump_eq {c : Config} {m n q : ℕ}
      (h : p.getInstr c.pc = some (Instr.J m n q))
      (heq : c.state.read m = c.state.read n) :
      Step c ⟨q, c.state⟩
  | jump_ne {c : Config} {m n q : ℕ}
      (h : p.getInstr c.pc = some (Instr.J m n q))
      (hne : c.state.read m ≠ c.state.read n) :
      Step c ⟨c.pc + 1, c.state⟩

/-- Multi-step execution: the reflexive-transitive closure of `Step`. -/
abbrev Steps : Config → Config → Prop := Relation.ReflTransGen (Step p)

namespace Step

variable {p : Program}

/-- The step relation is deterministic: each configuration has at most one successor. -/
theorem deterministic {c c' c'' : Config} (h1 : Step p c c') (h2 : Step p c c'') : c' = c'' := by
  cases h1 <;> cases h2 <;> simp_all

/-- A halted configuration has no successor in the step relation. -/
theorem halted_no_step {c c' : Config} (hhalted : c.isHalted p) : ¬Step p c c' := by
  intro hstep
  cases hstep <;> simp_all [Config.isHalted, Program.getInstr]

/-- If a step exists from config c, then c.pc < p.length (contrapositive of halted_no_step). -/
theorem pc_lt_length {c c' : Config} (hstep : Step p c c') : c.pc < p.length := by
  by_contra hc; exact halted_no_step (Nat.not_lt.mp hc) hstep

end Step

namespace Steps

variable {p : Program}

/-- Steps compose transitively. -/
theorem trans {c₁ c₂ c₃ : Config} (h1 : Steps p c₁ c₂) (h2 : Steps p c₂ c₃) : Steps p c₁ c₃ :=
  Relation.ReflTransGen.trans h1 h2

/-- One step implies multi-step. -/
theorem single {c c' : Config} (h : Step p c c') : Steps p c c' :=
  Relation.ReflTransGen.single h

/-- Zero steps: reflexivity. -/
theorem refl (c : Config) : Steps p c c :=
  Relation.ReflTransGen.refl

/-- If two halted configurations are reachable from the same start, they are equal.

This follows from the determinism of `Step`: any two execution paths from the same
initial configuration must be prefixes of each other (or identical if both terminate). -/
theorem halts_unique {init c₁ c₂ : Config}
    (h1 : Steps p init c₁) (hh1 : c₁.isHalted p)
    (h2 : Steps p init c₂) (hh2 : c₂.isHalted p) : c₁ = c₂ := by
  induction h1 using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- c₁ = init, so init is halted
    -- By halted_no_step, init cannot step, so h2 must also be refl
    cases h2 using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hstep _ => exact absurd hstep (Step.halted_no_step hh1)
  | head hstep_c hrest ih =>
    -- init → c → ... → c₁, where hstep_c : Step p init c
    -- init is not halted (it can step)
    cases h2 using Relation.ReflTransGen.head_induction_on with
    | refl =>
      -- c₂ = init is halted, but init can step - contradiction
      exact absurd hstep_c (Step.halted_no_step hh2)
    | head hstep_c' hrest' =>
      -- init → c' → ... → c₂
      -- By determinism, c = c'
      have heq : _ = _ := Step.deterministic hstep_c hstep_c'
      subst heq
      exact ih hrest'

/-- If c is reachable from init and c' is a halted config also reachable from init,
    then c' is reachable from c.

    This is the "continuation" lemma: since execution is deterministic, the path
    to a halted state must pass through any intermediate reachable state. -/
theorem deterministic_continuation {init c c' : Config}
    (h1 : Steps p init c) (h2 : Steps p init c') (hh2 : c'.isHalted p) :
    Steps p c c' := by
  induction h1 using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- c = init, so c' is directly reachable
    exact h2
  | head hstep_c hrest ih =>
    -- init → c_mid → ... → c
    -- We need to show h2's path goes through c_mid
    cases h2 using Relation.ReflTransGen.head_induction_on with
    | refl =>
      -- init = c' is halted, but init can step - contradiction
      exact absurd hstep_c (Step.halted_no_step hh2)
    | head hstep_c' hrest' =>
      -- init → c' → ... → c''
      -- By determinism, the intermediate configs match
      have heq : _ = _ := Step.deterministic hstep_c hstep_c'
      subst heq
      exact ih hrest'

end Steps

/-- A program halts on given inputs if there exists a halted configuration reachable from
the initial configuration. -/
def Halts (inputs : List ℕ) : Prop :=
  ∃ c, Steps p (Config.init inputs) c ∧ c.isHalted p

/-- A program diverges on given inputs if it does not halt. -/
def Diverges (inputs : List ℕ) : Prop := ¬Halts p inputs

namespace Halts

variable {p : Program}

/-- The empty program halts immediately on any input. -/
theorem empty_halts (inputs : List ℕ) : Halts [] inputs := by
  refine ⟨Config.init inputs, Steps.refl _, ?_⟩
  simp [Config.init]

end Halts

/-- The result of a halting computation is the value in register 0 when halted.

This is a partial function: it is only defined when the program halts. -/
noncomputable def Result (inputs : List ℕ) (h : Halts p inputs) : ℕ :=
  (Classical.choose h).state.output

/-- Evaluation as a partial function using `Part`. -/
noncomputable def eval (inputs : List ℕ) : Part ℕ :=
  ⟨Halts p inputs, fun h => Result p inputs h⟩

/-- Number of steps to reach a configuration (if it exists). -/
inductive StepsN : ℕ → Config → Config → Prop where
  | zero (c : Config) : StepsN 0 c c
  | succ {n : ℕ} {c c' c'' : Config}
      (hstep : Step p c c') (hrest : StepsN n c' c'') :
      StepsN (n + 1) c c''

namespace StepsN

variable {p : Program}

/-- StepsN implies Steps. -/
theorem toSteps {n : ℕ} {c c' : Config} (h : StepsN p n c c') : Steps p c c' := by
  induction h with
  | zero => exact Relation.ReflTransGen.refl
  | succ hstep _ ih => exact Relation.ReflTransGen.head hstep ih

/-- Addition of step counts. -/
theorem add {m n : ℕ} {c₁ c₂ c₃ : Config}
    (h1 : StepsN p m c₁ c₂) (h2 : StepsN p n c₂ c₃) :
    StepsN p (m + n) c₁ c₃ := by
  induction h1 with
  | zero => simp only [Nat.zero_add]; exact h2
  | succ hstep _ ih =>
    simp only [Nat.succ_add]
    exact succ hstep (ih h2)

/-- Steps implies there exists some n for StepsN. -/
theorem fromSteps {c c' : Config} (h : Steps p c c') : ∃ n, StepsN p n c c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, StepsN.zero c'⟩
  | head hstep _ ih =>
    obtain ⟨m, hstepsN⟩ := ih
    exact ⟨m + 1, StepsN.succ hstep hstepsN⟩

/-- If StepsN 0, then the configs are equal. -/
theorem zero_inv {c c' : Config} (hzero : n = 0) (h : StepsN p n c c') : c' = c := by
  subst hzero; cases h; rfl

/-- If StepsN with n > 0, decompose into first step. -/
theorem succ_inv {c c' : Config} (hn : n ≠ 0) (h : StepsN p n c c') :
    ∃ c'' m, Step p c c'' ∧ StepsN p m c'' c' ∧ n = m + 1 := by
  cases h with
  | zero => exact absurd rfl hn
  | succ hstep hrest => exact ⟨_, _, hstep, hrest, rfl⟩

/-- Step counts are unique when reaching a halted configuration.
    If StepsN p n1 c final and StepsN p n2 c final with final halted, then n1 = n2. -/
theorem stepsN_unique_halted : ∀ {c final : Config} {n1 n2 : ℕ},
    StepsN p n1 c final → StepsN p n2 c final → final.isHalted p → n1 = n2 := by
  intro c final n1
  induction n1 generalizing c with
  | zero =>
    intro n2 h1 h2 h_halted
    -- n1 = 0 means c = final
    cases h1
    -- final is halted, so n2 must also be 0
    cases h2 with
    | zero => rfl
    | succ hstep _ => exact absurd hstep (Step.halted_no_step h_halted)
  | succ n1' ih =>
    intro n2 h1 h2 h_halted
    -- n1 > 0, decompose h1
    cases h1 with
    | succ hstep1 hrest1 =>
      cases h2 with
      | zero =>
        -- n2 = 0 means c = final, but c can step - contradiction
        exact absurd hstep1 (Step.halted_no_step h_halted)
      | succ hstep2 hrest2 =>
        -- Both step, by determinism they go to same config
        have heq : _ = _ := Step.deterministic hstep1 hstep2
        subst heq
        have h_eq := ih hrest1 hrest2 h_halted
        omega

/-- Split a step count path at an intermediate point that is on the deterministic path to a halted config.
    Returns step counts for both segments. -/
theorem split_at_intermediate {init mid final : Config} {n : ℕ}
    (h_total : StepsN p n init final)
    (h_mid : Steps p init mid)
    (h_halted : final.isHalted p) :
    ∃ m1 m2, StepsN p m1 init mid ∧ StepsN p m2 mid final ∧ m1 + m2 = n := by
  -- Get step count for first segment
  obtain ⟨m1, hm1⟩ := fromSteps h_mid
  -- Get steps from mid to final using deterministic continuation
  have h_mid_to_final : Steps p mid final :=
    Steps.deterministic_continuation h_mid h_total.toSteps h_halted
  -- Get step count for second segment
  obtain ⟨m2, hm2⟩ := fromSteps h_mid_to_final
  use m1, m2, hm1, hm2
  -- The combined path has step count m1 + m2
  have h_combined : StepsN p (m1 + m2) init final := add hm1 hm2
  -- By uniqueness, n = m1 + m2
  exact stepsN_unique_halted h_combined h_total h_halted

/-- If we take at least one step to reach mid, then remaining steps to halted final is strictly less. -/
theorem split_strictly_smaller {init mid final : Config} {n : ℕ}
    (h_total : StepsN p n init final)
    (h_mid : Steps p init mid)
    (h_halted : final.isHalted p)
    (h_moved : init ≠ mid) :
    ∃ m, m < n ∧ StepsN p m mid final := by
  obtain ⟨m1, m2, hm1, hm2, heq⟩ := split_at_intermediate h_total h_mid h_halted
  use m2, ?_, hm2
  -- Need m2 < n, i.e., m2 < m1 + m2, i.e., m1 > 0
  have hm1_pos : m1 > 0 := by
    by_contra hm1_zero
    push_neg at hm1_zero
    have hm1_eq_zero : m1 = 0 := Nat.le_zero.mp hm1_zero
    -- m1 = 0 means init = mid
    have : mid = init := zero_inv hm1_eq_zero hm1
    exact h_moved this.symm
  omega

end StepsN

end Urm
