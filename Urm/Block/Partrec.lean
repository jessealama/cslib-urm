/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Block.Basic
import Urm.Block.Compose
import Urm.Block.Prec
import Urm.Block.Min
import Urm.Partrec
import Mathlib.Computability.Partrec

/-! # URMBlock and Partial Recursive Functions

This file establishes the connection between URMBlock computability and
Mathlib's `Nat.Partrec` definition of partial recursive functions.

## Main results

- `URMBlockComputable.toURMComputable`: URMBlock-computable implies URM-computable
- `URMBlock.closure_compose`: URMBlockComputable is closed under composition
- `URMBlock.closure_prec`: URMBlockComputable is closed under primitive recursion
- `URMBlock.closure_min`: URMBlockComputable is closed under minimization

## Strategy

The URMBlock abstraction provides:
1. Base functions: zero, successor, projections (proven in Basic.lean)
2. Closure under composition (Compose.lean)
3. Closure under primitive recursion (Prec.lean)
4. Closure under minimization (Min.lean)

Together these establish that all partial recursive functions are URMBlock-computable.

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
* Mathlib's `Mathlib.Computability.Partrec`
-/

namespace Urm

open URMBlock

/-! ## Basic URMBlockComputable Functions -/

/-- Zero constant is URMBlockComputable. -/
theorem URMBlockComputable.zero_const :
    URMBlockComputable 0 (fun _ => Part.some 0) :=
  ⟨URMBlock.zero, rfl, zero_computes⟩

/-- Successor is URMBlockComputable. -/
theorem URMBlockComputable.succ_fn :
    URMBlockComputable 1 (fun inputs => Part.some (inputs 0 + 1)) :=
  ⟨URMBlock.succ, rfl, succ_computes⟩

/-- Projection is URMBlockComputable. -/
theorem URMBlockComputable.proj_fn (n : ℕ) (k : Fin n) :
    URMBlockComputable n (fun inputs => Part.some (inputs k)) :=
  ⟨URMBlock.proj n k, rfl, proj_computes n k⟩

/-- Identity (1-ary) is URMBlockComputable. -/
theorem URMBlockComputable.identity_fn :
    URMBlockComputable 1 (fun inputs => Part.some (inputs 0)) :=
  ⟨URMBlock.identity, rfl, identity_computes⟩

/-! ## Closure Properties -/

/-- URMBlockComputable is closed under composition.

If f : (Fin m → ℕ) → Part ℕ and each gᵢ : (Fin n → ℕ) → Part ℕ are
URMBlockComputable, then h(x) = f(g₁(x), ..., gₘ(x)) is URMBlockComputable. -/
theorem URMBlockComputable.comp {n m : ℕ} [NeZero m]
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hf : URMBlockComputable m f)
    (hgs : ∀ i, URMBlockComputable n (gs i)) :
    URMBlockComputable n (URMBlock.compFunction n m f gs) := by
  obtain ⟨bf, hf_arity, hf_comp⟩ := hf
  choose bgs hgs_arity hgs_comp using hgs
  refine ⟨compose n bf m bgs hf_arity hgs_arity, rfl, ?_⟩
  exact compose_correct n bf m bgs f gs hf_arity hgs_arity hf_comp hgs_comp

/-- URMBlockComputable is closed under primitive recursion.

If f : (Fin n → ℕ) → Part ℕ and g : (Fin (n+2) → ℕ) → Part ℕ are
URMBlockComputable, then Pr(f,g) is URMBlockComputable. -/
theorem URMBlockComputable.primRec {n : ℕ}
    {f : (Fin n → ℕ) → Part ℕ}
    {g : (Fin (n + 2) → ℕ) → Part ℕ}
    (hf : URMBlockComputable n f)
    (hg : URMBlockComputable (n + 2) g) :
    URMBlockComputable (n + 1) (precFunction n f g) := by
  obtain ⟨bf, hf_arity, hf_comp⟩ := hf
  obtain ⟨bg, hg_arity, hg_comp⟩ := hg
  refine ⟨prec n bf bg hf_arity hg_arity, rfl, ?_⟩
  exact prec_correct n bf bg f g hf_arity hg_arity hf_comp hg_comp

/-- URMBlockComputable is closed under minimization.

If f : (Fin (n+1) → ℕ) → Part ℕ is URMBlockComputable, then
μy[f(x,y) = 0] is URMBlockComputable. -/
theorem URMBlockComputable.minimize {n : ℕ}
    {f : (Fin (n + 1) → ℕ) → Part ℕ}
    (hf : URMBlockComputable (n + 1) f) :
    URMBlockComputable n (minFunction n f) := by
  obtain ⟨bf, hf_arity, hf_comp⟩ := hf
  refine ⟨min n bf hf_arity, rfl, ?_⟩
  exact min_correct n bf f hf_arity hf_comp

/-! ## Unary Wrapper -/

/-- A unary partial function is URMBlock-computable. -/
def URMBlockComputable1 (f : ℕ →. ℕ) : Prop :=
  URMBlockComputable 1 (fun x => f (x 0))

/-- URMBlockComputable1 implies URMComputable1. -/
theorem URMBlockComputable1.toURMComputable1 {f : ℕ →. ℕ}
    (h : URMBlockComputable1 f) : Urm.URMComputable1 f := by
  unfold Urm.URMComputable1
  exact h.toURMComputable

end Urm
