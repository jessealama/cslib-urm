/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.SeqExecution

/-! # JumpsBounded: Well-Formed Programs

This file defines the JumpsBounded predicate for URM programs.

## Main definitions

- `Urm.JumpsBounded`: A program has bounded jumps if all jump targets are ≤ program length
-/

namespace Urm

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

end JumpsBounded

end Urm
