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

/-- If a configuration can step, it is not halted. -/
theorem not_halted_of_step {c c' : Config} (h : Step p c c') : ¬c.isHalted p :=
  fun hhalted => halted_no_step hhalted h

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

/-- If a program steps to a halted configuration, it halts. -/
theorem of_steps_to_halted {inputs : List ℕ} {c : Config}
    (hsteps : Steps p (Config.init inputs) c) (hhalted : c.isHalted p) :
    Halts p inputs :=
  ⟨c, hsteps, hhalted⟩

/-- The empty program halts immediately on any input. -/
theorem empty_halts (inputs : List ℕ) : Halts [] inputs := by
  refine ⟨Config.init inputs, Steps.refl _, ?_⟩
  simp [Config.isHalted, Config.init]

end Halts

/-- The result of a halting computation is the value in register 0 when halted.

This is a partial function: it is only defined when the program halts. -/
noncomputable def Result (inputs : List ℕ) (h : Halts p inputs) : ℕ :=
  (Classical.choose h).state.output

/-- Evaluation as a partial function using `Part`. -/
noncomputable def eval (inputs : List ℕ) : Part ℕ :=
  ⟨Halts p inputs, fun h => Result p inputs h⟩

namespace eval

variable {p : Program}

/-- `eval` is defined iff the program halts. -/
theorem dom_iff_halts (inputs : List ℕ) : (eval p inputs).Dom ↔ Halts p inputs := Iff.rfl

end eval

/-- Number of steps to reach a configuration (if it exists). -/
inductive StepsN : ℕ → Config → Config → Prop where
  | zero (c : Config) : StepsN 0 c c
  | succ {n : ℕ} {c c' c'' : Config}
      (hstep : Step p c c') (hrest : StepsN n c' c'') :
      StepsN (n + 1) c c''

namespace StepsN

variable {p : Program}

/-- StepsN 0 is identity. -/
theorem zero_iff {c c' : Config} : StepsN p 0 c c' ↔ c = c' := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; exact zero c

/-- StepsN 1 is a single step. -/
theorem one_iff {c c' : Config} : StepsN p 1 c c' ↔ Step p c c' := by
  constructor
  · intro h; cases h with | succ hstep hrest => cases hrest; exact hstep
  · intro h; exact succ h (zero c')

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

end StepsN

/-- A program halts in n steps if it reaches a halted configuration in exactly n steps. -/
def HaltsIn (n : ℕ) (inputs : List ℕ) : Prop :=
  ∃ c, StepsN p n (Config.init inputs) c ∧ c.isHalted p

namespace HaltsIn

variable {p : Program}

/-- If a program halts in n steps, it halts. -/
theorem toHalts {n : ℕ} {inputs : List ℕ} (h : HaltsIn p n inputs) : Halts p inputs := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  exact ⟨c, hsteps.toSteps, hhalted⟩

/-- The empty program halts in 0 steps. -/
theorem empty_halts_in_zero (inputs : List ℕ) : HaltsIn [] 0 inputs := by
  refine ⟨Config.init inputs, StepsN.zero _, ?_⟩
  simp [Config.isHalted, Config.init]

end HaltsIn

end Urm
