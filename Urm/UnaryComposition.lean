/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Basic

/-! # Unary-Unary Composition

This file proves that the composition of two unary URM-computable functions is URM-computable.
This is the simplest non-trivial composition case and is now a direct corollary of the
general composition theorem.

## Main results

- `URMComputable.comp_unary`: If `f` and `g` are unary URM-computable, then `f ∘ g` is
  URM-computable.

## Construction

Given programs `Pf` computing `f` and `Pg` computing `g`, the composed program is:
```
Pg ++ clearRegistersFrom 1 maxReg(Pf) ++ Pf
```

The key steps:
1. Run `Pg` to compute `g(x)` in R[0]
2. Clear registers R[1]..R[maxReg(Pf)] to simulate fresh start for `Pf`
3. Run `Pf` on R[0] = g(x) to compute `f(g(x))`

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Unary composition program construction -/

/-- Compose two unary programs: run Pg, clear working registers, run Pf.
The clearing step ensures Pf sees a "fresh" state (all registers 0 except R[0]). -/
def Program.composeUnary (Pf Pg : Program) : Program :=
  let maxF := Pf.maxRegister
  -- Run Pg, then clear R[1]..R[maxF], then run Pf
  Pg.concat ((clearRegistersFrom 1 maxF).concat Pf)

/-! ## Main theorem: Unary-unary composition -/

/-- Helper lemma: For Fin 1, Part.sequence simplifies to binding with Fin.cons. -/
private theorem sequence_fin1_eq (p : Part ℕ) :
    Part.sequence (fun (_ : Fin 1) => p) = p.bind fun v => Part.some (fun _ => v) := by
  -- Part.sequence for n=1 is: (f 0).bind (fun a0 => (Part.some Fin.elim0).map (Fin.cons a0))
  rw [Part.sequence_succ]
  simp only [Part.sequence_zero]
  -- Now we have: p.bind (fun a0 => (Part.some Fin.elim0).map (Fin.cons a0))
  -- = p.bind (fun a0 => Part.some (Fin.cons a0 Fin.elim0))
  congr 1
  funext a0
  simp only [Part.map_some]
  -- Fin.cons a0 Fin.elim0 = (fun _ => a0)
  congr 1
  funext i
  have : i = 0 := Fin.ext (by omega : i.val = 0)
  simp [this]

/-- Composition of unary URM-computable functions is URM-computable (standard form version).

If `f` and `g` are unary partial functions computed by standard form URM programs,
then `f ∘ g` (i.e., `fun x => (g x).bind (fun y => f (fun _ => y))`) is URM-computable
by a standard form program.

This is a special case of the general composition theorem `URMComputableSF.comp_general`
with m = 1 (unary f) and n = 1 (unary g). -/
theorem URMComputableSF.comp_unary
    {f g : (Fin 1 → ℕ) → Part ℕ}
    (hf : URMComputableSF 1 f)
    (hg : URMComputableSF 1 g) :
    URMComputableSF 1 (fun x => (g x).bind (fun y => f (fun _ => y))) := by
  -- Define gs as the singleton tuple containing just g
  let gs : Fin 1 → (Fin 1 → ℕ) → Part ℕ := fun _ => g
  -- Prove computability for gs
  have hgs : ∀ i, URMComputableSF 1 (gs i) := fun _ => hg
  -- Apply general composition
  have := URMComputableSF.comp_general hf hgs
  -- Convert to the desired form
  convert this using 2
  ext x
  simp only [compFunction, gs]
  rw [sequence_fin1_eq, Part.bind_assoc]
  simp only [Part.bind_some]

end Urm
