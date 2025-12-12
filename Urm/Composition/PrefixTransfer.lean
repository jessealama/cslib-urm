/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.StateShift

/-! # Prefix Step Transfer

This file proves that steps in a prefix program transfer to a concatenated program.
This is useful when we have a program p₁ ++ p₂ and want to reason about execution
in p₁ while knowing the result extends to the concatenation.

## Main statements

- `Urm.Step.prefix_transfer`: Single step transfer from prefix to concatenation
- `Urm.Steps.prefix_transfer`: Multi-step transfer from prefix to concatenation
-/

namespace Urm

/-- A single step in a prefix program transfers to the concatenated program when PC < prefix length. -/
theorem Step.prefix_transfer {p₁ p₂ : Program} {c c' : Config}
    (hstep : Step p₁ c c')
    (hpc : c.pc < p₁.length) :
    Step (p₁ ++ p₂) c c' := by
  have hinstr_eq : ∀ instr, p₁.getInstr c.pc = some instr → (p₁ ++ p₂).getInstr c.pc = some instr := by
    intro instr h
    simp only [Program.getInstr, List.getElem?_append_left hpc]
    exact h
  match hstep with
  | Step.zero h => exact Step.zero (hinstr_eq _ h)
  | Step.succ h => exact Step.succ (hinstr_eq _ h)
  | Step.trans h => exact Step.trans (hinstr_eq _ h)
  | Step.jump_eq h heq => exact Step.jump_eq (hinstr_eq _ h) heq
  | Step.jump_ne h hne => exact Step.jump_ne (hinstr_eq _ h) hne

/-- Steps in a prefix program transfer to the concatenated program when any config
    that can take a step has pc < prefix length. -/
theorem Steps.prefix_transfer {p₁ p₂ : Program} {c c' : Config}
    (hsteps : Steps p₁ c c')
    (hbound : ∀ c₀ c₁, Steps p₁ c c₀ → Step p₁ c₀ c₁ → c₀.pc < p₁.length) :
    Steps (p₁ ++ p₂) c c' := by
  induction hsteps with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c_final hrest hstep ih =>
    -- hrest : Steps p₁ c b, hstep : Step p₁ b c_final
    -- ih : Steps (p₁ ++ p₂) c b (from induction on hrest with same bound)
    -- Need pc bound for b to transfer the step
    have hpc_b : b.pc < p₁.length := hbound b c_final hrest hstep
    have hstep' := Step.prefix_transfer (p₂ := p₂) hstep hpc_b
    exact Relation.ReflTransGen.tail ih hstep'

end Urm
