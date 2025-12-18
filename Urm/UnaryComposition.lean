/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Computable
import Urm.Composition
import Urm.CompositionHelpers

/-! # Unary Composition

This file proves that unary URM-computable functions are closed under composition.
This is a simpler case of the general composition theorem (Cutland's Theorem 3.1),
handling functions `ℕ → Part ℕ` rather than `(Fin n → ℕ) → Part ℕ`.

## Main results

- `UnaryURMComputable.comp_bounded`: Composition closure assuming bounded jumps
- `UnaryURMComputable.comp`: Full composition closure (requires standardization theorem)

## Implementation notes

The key insight is that for unary functions, the composed program `H = Pg.concat Pf`
requires no register shuffling: both programs use R0 for input and output.

The proof requires a `boundedJumps` hypothesis to ensure that when `Pg.concat Pf` halts,
we can extract that `Pg` halted (didn't escape via a jump into `Pf`'s code).
This hypothesis can be dropped once we prove the standardization theorem:
every program has an equivalent program with bounded jumps.

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Unary Computability -/

/-- Unary URM computability for partial functions `ℕ → Part ℕ`.

A function `f : ℕ → Part ℕ` is unary URM-computable if there exists a program `p`
such that for all inputs `x`:
- `p` halts on `[x]` iff `f x` is defined
- When both hold, `Result p [x]` equals `(f x).get` -/
def UnaryURMComputable (f : ℕ → Part ℕ) : Prop :=
  ∃ p : Program, ∀ x : ℕ,
    (Halts p [x] ↔ (f x).Dom) ∧
    ∀ (hHalts : Halts p [x]) (hDom : (f x).Dom),
      Result p [x] hHalts = (f x).get hDom

/-- Equivalence between UnaryURMComputable and URMComputable for arity 1. -/
theorem unaryURMComputable_iff_urmComputable (f : ℕ → Part ℕ) :
    UnaryURMComputable f ↔ URMComputable 1 (fun inputs => f (inputs 0)) := by
  constructor
  · intro ⟨p, hp⟩
    use p
    intro inputs
    have hinputs : List.ofFn inputs = [inputs 0] := by
      simp only [List.ofFn]
      rfl
    rw [hinputs]
    exact hp (inputs 0)
  · intro ⟨p, hp⟩
    use p
    intro x
    have hinputs : List.ofFn (fun _ : Fin 1 => x) = [x] := by
      simp only [List.ofFn]
      rfl
    specialize hp (fun _ => x)
    rw [hinputs] at hp
    simp only at hp
    exact hp

/-- A program computes a unary function if it satisfies the spec. -/
def ProgramComputesUnary (p : Program) (f : ℕ → Part ℕ) : Prop :=
  ∀ x : ℕ,
    (Halts p [x] ↔ (f x).Dom) ∧
    ∀ (hHalts : Halts p [x]) (hDom : (f x).Dom),
      Result p [x] hHalts = (f x).get hDom

/-! ### Standardization Theorem

The standardization theorem states that every program can be transformed into an
equivalent program with bounded jumps. This is a fundamental result that allows
us to assume bounded jumps without loss of generality.

The proof involves systematically replacing unbounded jumps with bounded ones,
typically by adding "landing pad" instructions. We postulate this here and
leave the construction for future work. -/

/-- Every program computing a unary function has an equivalent program with bounded jumps.
This is the standardization theorem for unary programs. -/
theorem ProgramComputesUnary.exists_boundedJumps {f : ℕ → Part ℕ} {p : Program}
    (hp : ProgramComputesUnary p f) :
    ∃ p' : Program, ProgramComputesUnary p' f ∧ p'.boundedJumps := by
  sorry -- Standardization theorem: construct equivalent program with bounded jumps

/-! ## Main Composition Theorem -/

/-- Composition of unary URM-computable functions, assuming bounded jumps.

If `f` and `g` are unary computable with witnesses `Pf` and `Pg` that have bounded jumps,
then `f ∘ g` (i.e., `fun x => (g x).bind f`) is unary computable. -/
theorem UnaryURMComputable.comp_bounded {f g : ℕ → Part ℕ}
    {Pf Pg : Program}
    (hPf : ProgramComputesUnary Pf f)
    (hPg : ProgramComputesUnary Pg g)
    (hPf_bounded : Pf.boundedJumps)
    (hPg_bounded : Pg.boundedJumps) :
    UnaryURMComputable (fun x => (g x).bind f) := by
  -- The composed program: Pg, then clear scratch, then Pf
  -- Clearing ensures Pf sees a state that agrees with fresh state on low registers
  let clear := Program.clearScratch Pf.maxRegister
  let H := Pg.concat (clear.concat Pf)
  use H
  intro x
  constructor
  -- Part 1: Halts H [x] ↔ ((g x).bind f).Dom
  · constructor
    -- Forward: Halts H [x] → ((g x).bind f).Dom
    · intro hH_halts
      -- H = Pg.concat (clear.concat Pf), with Pg bounded
      -- Extract that Pg halts
      have hclear_bounded : clear.boundedJumps := Program.clearScratch_boundedJumps _
      have hclear_Pf_bounded : (clear.concat Pf).boundedJumps :=
        Program.concat_boundedJumps hclear_bounded hPf_bounded
      have hPg_halts : Halts Pg [x] := Halts.of_concat_left_bounded hPg_bounded hH_halts
      -- So g x is defined
      have hg_dom : (g x).Dom := (hPg x).1.mp hPg_halts
      -- Prove by contradiction: assume f(g(x)) is not defined
      by_contra hf_not_dom
      -- Then Pf doesn't halt from fresh [g(x).get]
      have hPf_not_halts : ¬Halts Pf [(g x).get hg_dom] := by
        intro hPf_halts
        have hf_dom := (hPf ((g x).get hg_dom)).1.mp hPf_halts
        have hbind_dom : ((g x).bind f).Dom := Part.bind_dom.mpr ⟨hg_dom, hf_dom⟩
        exact hf_not_dom hbind_dom
      -- Setup: Pg halts at pc = Pg.length
      have hPg_pc : (Classical.choose hPg_halts).pc = Pg.length :=
        Halts.pc_eq_length hPg_bounded hPg_halts
      let σ_Pg := (Classical.choose hPg_halts).state
      have hR0_Pg : σ_Pg.read 0 = (g x).get hg_dom := by
        simp only [σ_Pg]
        exact (hPg x).2 hPg_halts hg_dom
      -- Clear halts and produces a state agreeing with fresh [g(x).get]
      have hclear_sl := Program.clearScratch_isStraightLine Pf.maxRegister
      have hclear_from_state : ∃ c, Steps clear ⟨0, σ_Pg⟩ c ∧ c.isHalted clear :=
        straightLine_halts_from_state hclear_sl σ_Pg
      have hclear_state_eq := straightLine_final_state_eq hclear_sl σ_Pg
      have hagree_cleared : (executeStraightLine clear σ_Pg).agreesLow
          (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister :=
        Program.clearScratch_agreesLow Pf.maxRegister σ_Pg ((g x).get hg_dom) hR0_Pg
      have hagree_cleared' : (Classical.choose hclear_from_state).state.agreesLow
          (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister := by
        rw [hclear_state_eq]; exact hagree_cleared
      -- By contrapositive of Halts.to_agreesLow: if Pf doesn't halt from fresh,
      -- then Pf doesn't halt from the cleared state either
      have hPf_not_from_cleared : ¬∃ c', Steps Pf ⟨0, (Classical.choose hclear_from_state).state⟩ c' ∧ c'.isHalted Pf := by
        intro ⟨c', hsteps', hhalted'⟩
        exact hPf_not_halts (Halts.to_agreesLow hagree_cleared' ⟨c', hsteps', hhalted'⟩)
      -- Now we need to show H can't halt, contradicting hH_halts
      -- If clear.concat Pf halts from σ_Pg, then Pf must halt from the cleared state
      -- (since clear always halts and leaves us at pc = clear.length)
      -- Get the halting config for clear from σ_Pg
      have hclear_pc := straightLine_halts_from_state_at_length hclear_sl σ_Pg
      -- If clear.concat Pf were to halt from σ_Pg, after clear's execution,
      -- we'd be at pc = clear.length, and Pf would need to halt from there
      -- Since Pf doesn't halt from the cleared state, clear.concat Pf can't halt
      -- For now, we use a simpler argument via extracting second halting
      -- Since H = Pg.concat (clear.concat Pf) halts, and Pg halts (bounded),
      -- we can extract that clear.concat Pf halts from σ_Pg
      -- Get existence for H halting
      obtain ⟨c_H, hsteps_H, hhalted_H⟩ := hH_halts
      -- Get existence for Pg halting
      have hPg_halts_exists : ∃ c, Steps Pg (Config.init [x]) c ∧ c.isHalted Pg := hPg_halts
      -- Use reaches_boundary to find the boundary where execution enters clear.concat Pf
      obtain ⟨c_mid, hsteps_to_mid, hmid_pc, hsteps_from_mid⟩ :=
        Steps.reaches_boundary hPg_bounded hsteps_H (by simp [Config.init]) hhalted_H
      -- c_mid is at pc = Pg.length, state = σ_Pg (by uniqueness)
      have hc_mid_state : c_mid.state = σ_Pg := by
        have hsteps1 := (Classical.choose_spec hPg_halts).1
        have hhalted1 := (Classical.choose_spec hPg_halts).2
        have hunique := Steps.halts_unique hsteps_to_mid (by simp [Config.isHalted]; omega) hsteps1 hhalted1
        simp only [hunique, σ_Pg]
      -- hsteps_from_mid : Steps H c_mid c_H, where H = Pg.concat (clear.concat Pf)
      -- and c_mid.pc = Pg.length
      -- This means c_mid is at the start of clear.concat Pf in the concatenation
      -- For the execution to halt, clear.concat Pf must have led to halting
      -- Since Pf doesn't halt from the cleared state, we have a contradiction
      -- The key observation: once at pc = Pg.length, execution is entirely within
      -- (clear.concat Pf)'s code. For execution to reach a halted state in H,
      -- the execution in the clear.concat Pf region must also reach a halted state
      -- (i.e., pc ≥ Pg.length + clear.length + Pf.length)
      -- This means Pf halted, but we showed it doesn't - contradiction
      -- Since this is getting complex, we'll use the key insight more directly:
      -- The backward direction shows that if (g x).bind f is defined, then H halts.
      -- By contrapositive: if ¬((g x).bind f).Dom, then ¬Halts H [x].
      -- But we have hH_halts, so (g x).bind f must be defined.
      -- This is a proof by contradiction that completes the forward direction.
      exfalso
      -- We need to show that Pf must halt from the cleared state, contradicting hPf_not_from_cleared
      -- Step 1: c_mid is at the boundary, so we can apply halts_at_boundary_implies_p2_halts
      -- to extract that (clear.concat Pf) halts from σ_Pg
      have hc_mid_eq : c_mid = ⟨Pg.length, σ_Pg⟩ := by
        cases c_mid
        simp only at hmid_pc hc_mid_state
        simp only [hmid_pc, hc_mid_state]
      rw [hc_mid_eq] at hsteps_from_mid
      -- clear.concat Pf has bounded jumps
      have hclear_Pf_halts_from_boundary :
          ∃ c, Steps (clear.concat Pf) ⟨0, σ_Pg⟩ c ∧ c.isHalted (clear.concat Pf) :=
        halts_at_boundary_implies_p2_halts hclear_Pf_bounded ⟨c_H, hsteps_from_mid, hhalted_H⟩
      -- Step 2: From clear.concat Pf halting, extract that Pf halts from the cleared state
      -- clear has bounded jumps (straight-line)
      have hclear_bounded := Program.clearScratch_boundedJumps Pf.maxRegister
      -- clear halts from σ_Pg
      have hclear_from_σ_Pg : ∃ c, Steps clear ⟨0, σ_Pg⟩ c ∧ c.isHalted clear :=
        straightLine_halts_from_state hclear_sl σ_Pg
      -- Extract Pf halting from clear.concat Pf halting
      have hPf_halts_from_cleared :=
        steps_extract_second_bounded hclear_bounded hPf_bounded hclear_Pf_halts_from_boundary hclear_from_σ_Pg
      -- The cleared state matches what we computed
      have hclear_state_same : (Classical.choose hclear_from_σ_Pg).state =
          (Classical.choose hclear_from_state).state := by
        -- Both come from the same straight-line execution from σ_Pg
        have h1_steps := (Classical.choose_spec hclear_from_σ_Pg).1
        have h1_halted := (Classical.choose_spec hclear_from_σ_Pg).2
        have h2_steps := (Classical.choose_spec hclear_from_state).1
        have h2_halted := (Classical.choose_spec hclear_from_state).2
        have hunique := Steps.halts_unique h1_steps h1_halted h2_steps h2_halted
        simp only [hunique]
      -- Step 3: This contradicts hPf_not_from_cleared
      rw [← hclear_state_same] at hPf_not_from_cleared
      exact hPf_not_from_cleared hPf_halts_from_cleared
    -- Backward: ((g x).bind f).Dom → Halts H [x]
    · intro hdom
      -- (g x).bind f is defined means g x is defined and f (g x).get is defined
      have hg_dom : (g x).Dom := Part.bind_dom.mp hdom |>.1
      have hf_dom : (f ((g x).get hg_dom)).Dom := Part.bind_dom.mp hdom |>.2
      -- Pg halts on [x]
      have hPg_halts : Halts Pg [x] := (hPg x).1.mpr hg_dom
      -- Pf halts on [g(x)] when started fresh (Config.init)
      have hPf_halts : Halts Pf [(g x).get hg_dom] := (hPf ((g x).get hg_dom)).1.mpr hf_dom
      -- Result Pg [x] = g(x).get
      have hPg_result : Result Pg [x] hPg_halts = (g x).get hg_dom :=
        (hPg x).2 hPg_halts hg_dom
      -- Pg halts at pc = Pg.length (from bounded jumps)
      have hPg_pc : (Classical.choose hPg_halts).pc = Pg.length :=
        Halts.pc_eq_length hPg_bounded hPg_halts
      -- State after Pg
      let σ_Pg := (Classical.choose hPg_halts).state
      have hR0_Pg : σ_Pg.read 0 = (g x).get hg_dom := by
        simp only [σ_Pg, Result, State.output] at hPg_result ⊢
        exact hPg_result
      -- Clear halts from σ_Pg (straight-line)
      have hclear_sl := Program.clearScratch_isStraightLine Pf.maxRegister
      have hclear_from_state : ∃ c, Steps clear ⟨0, σ_Pg⟩ c ∧ c.isHalted clear :=
        straightLine_halts_from_state hclear_sl σ_Pg
      -- The cleared state equals executeStraightLine
      have hclear_state_eq := straightLine_final_state_eq hclear_sl σ_Pg
      -- After clearing, state agrees with fresh [g(x).get] on low registers
      have hagree_cleared : (executeStraightLine clear σ_Pg).agreesLow
          (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister :=
        Program.clearScratch_agreesLow Pf.maxRegister σ_Pg ((g x).get hg_dom) hR0_Pg
      -- Convert to agreement for the Steps-based state
      have hagree_cleared' : (Classical.choose hclear_from_state).state.agreesLow
          (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister := by
        rw [hclear_state_eq]
        exact hagree_cleared
      -- By Halts.of_agreesLow, Pf halts from the cleared state
      have hPf_from_cleared := Halts.of_agreesLow hagree_cleared' hPf_halts
      obtain ⟨c_Pf, hsteps_Pf, hhalted_Pf, _⟩ := hPf_from_cleared
      -- Chain: clear.concat Pf halts from σ_Pg
      have hclear_Pf_from_state : ∃ c, Steps (clear.concat Pf) ⟨0, σ_Pg⟩ c ∧ c.isHalted (clear.concat Pf) :=
        steps_concat_continuation_straightLine hclear_sl hclear_from_state ⟨c_Pf, hsteps_Pf, hhalted_Pf⟩
      -- Use Halts.concat_continuation to chain Pg with (clear.concat Pf)
      exact Halts.concat_continuation hPg_halts hPg_pc hclear_Pf_from_state
  -- Part 2: Results match
  · intro hH_halts hdom
    -- Need: Result H [x] hH_halts = ((g x).bind f).get hdom
    -- By definition of bind: ((g x).bind f).get hdom = f ((g x).get hg_dom)).get hf_dom
    -- H = Pg; clear; Pf. After Pg, R0 = g(x). Clearing preserves R0.
    -- Pf then runs, and by Halts.of_agreesLow, its output equals f(g(x)).
    have hg_dom : (g x).Dom := Part.bind_dom.mp hdom |>.1
    have hf_dom : (f ((g x).get hg_dom)).Dom := Part.bind_dom.mp hdom |>.2
    -- Setup: same as backward direction
    have hPg_halts : Halts Pg [x] := (hPg x).1.mpr hg_dom
    have hPf_halts : Halts Pf [(g x).get hg_dom] := (hPf ((g x).get hg_dom)).1.mpr hf_dom
    have hPg_result : Result Pg [x] hPg_halts = (g x).get hg_dom := (hPg x).2 hPg_halts hg_dom
    have hPf_result : Result Pf [(g x).get hg_dom] hPf_halts = (f ((g x).get hg_dom)).get hf_dom :=
      (hPf ((g x).get hg_dom)).2 hPf_halts hf_dom
    have hPg_pc : (Classical.choose hPg_halts).pc = Pg.length := Halts.pc_eq_length hPg_bounded hPg_halts
    let σ_Pg := (Classical.choose hPg_halts).state
    have hR0_Pg : σ_Pg.read 0 = (g x).get hg_dom := by
      simp only [σ_Pg, Result, State.output] at hPg_result ⊢; exact hPg_result
    -- Clear halts and its state equals executeStraightLine
    have hclear_sl := Program.clearScratch_isStraightLine Pf.maxRegister
    have hclear_from_state : ∃ c, Steps clear ⟨0, σ_Pg⟩ c ∧ c.isHalted clear :=
      straightLine_halts_from_state hclear_sl σ_Pg
    have hclear_state_eq := straightLine_final_state_eq hclear_sl σ_Pg
    -- Cleared state agrees with fresh [g(x).get]
    have hagree_cleared : (executeStraightLine clear σ_Pg).agreesLow
        (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister :=
      Program.clearScratch_agreesLow Pf.maxRegister σ_Pg ((g x).get hg_dom) hR0_Pg
    have hagree_cleared' : (Classical.choose hclear_from_state).state.agreesLow
        (State.fromInputs [(g x).get hg_dom]) Pf.maxRegister := by
      rw [hclear_state_eq]; exact hagree_cleared
    -- Pf from cleared state gives the same output as from fresh
    have hPf_from_cleared := Halts.of_agreesLow hagree_cleared' hPf_halts
    obtain ⟨c_Pf, hsteps_Pf, hhalted_Pf, hR0_Pf⟩ := hPf_from_cleared
    -- The key: c_Pf.state.read 0 = Result Pf [(g x).get hg_dom] hPf_halts = f(g(x)).get
    have hPf_output : c_Pf.state.read 0 = (f ((g x).get hg_dom)).get hf_dom := by
      rw [hR0_Pf]; exact hPf_result
    -- Now we need to show Result H [x] hH_halts = c_Pf.state.read 0
    -- The halted config for H must have the same R0 as c_Pf (lifted to the concat)
    -- This follows from uniqueness of halted configs and the chaining
    -- For now, we use the key insight that the final R0 matches
    simp only [Result, State.output]
    -- The final state of H is determined by the execution path:
    -- Pg → clear → Pf, and R0 at the end = f(g(x)).get
    -- This is a technical proof connecting the Classical.choose for hH_halts
    -- to the composed execution. We use that the halted config is unique.
    -- Since the backward direction constructs the same execution path,
    -- and halted configs are unique, the result must match.
    -- For technical simplicity, we show this via bind.get equality
    have hbind_get : ((g x).bind f).get hdom = (f ((g x).get hg_dom)).get hf_dom := by
      have heq := Part.Dom.bind hg_dom f
      simp only [heq]
    rw [hbind_get, ← hPf_output]
    -- Now we need: (Classical.choose hH_halts).state.read 0 = c_Pf.state.read 0
    -- We construct the explicit halted config for H and use halts_unique.
    -- After lifting: Pf's execution from cleared state lifts to clear.concat Pf,
    -- then that lifts to H = Pg.concat (clear.concat Pf).
    -- The final config is ⟨c_Pf.pc + Pg.length + clear.length, c_Pf.state⟩
    -- which is halted in H since c_Pf.isHalted Pf.
    -- By halts_unique, this equals Classical.choose hH_halts.
    -- Build the halted config for clear.concat Pf
    have hPf_pc_ge : Pf.length ≤ c_Pf.pc := hhalted_Pf
    have hsteps_Pf' : Steps (clear.concat Pf) ⟨clear.length, (Classical.choose hclear_from_state).state⟩
        ⟨c_Pf.pc + clear.length, c_Pf.state⟩ := by
      have := Steps.concat_right (p1 := clear) hsteps_Pf hhalted_Pf
      simp only [Nat.zero_add] at this
      exact this
    have hhalted_Pf' : (⟨c_Pf.pc + clear.length, c_Pf.state⟩ : Config).isHalted (clear.concat Pf) := by
      simp only [Config.isHalted, Program.concat_length]
      omega
    -- Get the halted config from clear (using Classical.choose)
    let c_clear := Classical.choose hclear_from_state
    have hclear_spec := Classical.choose_spec hclear_from_state
    have hsteps_clear : Steps clear ⟨0, σ_Pg⟩ c_clear := hclear_spec.1
    have hhalted_clear : c_clear.isHalted clear := hclear_spec.2
    have hclear_pc : c_clear.pc = clear.length :=
      straightLine_halts_from_state_at_length hclear_sl σ_Pg
    -- Chain clear and Pf in clear.concat Pf
    have hsteps_clear' : Steps (clear.concat Pf) ⟨0, σ_Pg⟩ c_clear := by
      exact Steps.concat_left_prefix (p2 := Pf) hsteps_clear hhalted_clear
    have hsteps_clear_start : (⟨clear.length, c_clear.state⟩ : Config) =
        ⟨c_clear.pc, c_clear.state⟩ := by
      simp only [hclear_pc]
    rw [hsteps_clear_start] at hsteps_Pf'
    have hsteps_clearPf : Steps (clear.concat Pf) ⟨0, σ_Pg⟩ ⟨c_Pf.pc + clear.length, c_Pf.state⟩ :=
      Steps.trans hsteps_clear' hsteps_Pf'
    -- Now lift to H = Pg.concat (clear.concat Pf)
    have hsteps_clearPf' : Steps H ⟨Pg.length, σ_Pg⟩ ⟨c_Pf.pc + clear.length + Pg.length, c_Pf.state⟩ := by
      have := Steps.concat_right (p1 := Pg) hsteps_clearPf hhalted_Pf'
      simp only [Nat.zero_add] at this
      convert this using 2
    have hhalted_H' : (⟨c_Pf.pc + clear.length + Pg.length, c_Pf.state⟩ : Config).isHalted H := by
      simp only [Config.isHalted, H, Program.concat_length]
      omega
    -- Get the halted config from Pg
    obtain ⟨hsteps_Pg, hhalted_Pg⟩ := Classical.choose_spec hPg_halts
    have hsteps_Pg' : Steps H (Config.init [x]) (Classical.choose hPg_halts) := by
      exact Steps.concat_left_prefix (p2 := clear.concat Pf) hsteps_Pg hhalted_Pg
    have hstart_eq : (⟨Pg.length, σ_Pg⟩ : Config) = Classical.choose hPg_halts := by
      ext
      · exact hPg_pc.symm
      · rfl
    rw [hstart_eq] at hsteps_clearPf'
    have hsteps_H : Steps H (Config.init [x]) ⟨c_Pf.pc + clear.length + Pg.length, c_Pf.state⟩ :=
      Steps.trans hsteps_Pg' hsteps_clearPf'
    -- By uniqueness, Classical.choose hH_halts equals this config
    obtain ⟨hsteps_choose, hhalted_choose⟩ := Classical.choose_spec hH_halts
    have hunique := Steps.halts_unique hsteps_choose hhalted_choose hsteps_H hhalted_H'
    -- Extract the state equality
    have hstate_eq : (Classical.choose hH_halts).state = c_Pf.state := by
      rw [hunique]
    simp only [hstate_eq, State.read]

/-- Full composition theorem for unary URM-computable functions.

This version does not require the bounded jumps hypothesis. The proof
applies the standardization theorem to get bounded-jump witnesses,
then uses `comp_bounded`. -/
theorem UnaryURMComputable.comp {f g : ℕ → Part ℕ}
    (hf : UnaryURMComputable f) (hg : UnaryURMComputable g) :
    UnaryURMComputable (fun x => (g x).bind f) := by
  -- Get witness programs from computability
  obtain ⟨Pf, hPf⟩ := hf
  obtain ⟨Pg, hPg⟩ := hg
  -- Apply standardization to get bounded-jump versions
  obtain ⟨Pf', hPf', hPf'_bounded⟩ := ProgramComputesUnary.exists_boundedJumps hPf
  obtain ⟨Pg', hPg', hPg'_bounded⟩ := ProgramComputesUnary.exists_boundedJumps hPg
  -- Apply comp_bounded with the standardized programs
  exact comp_bounded hPf' hPg' hPf'_bounded hPg'_bounded

end Urm
