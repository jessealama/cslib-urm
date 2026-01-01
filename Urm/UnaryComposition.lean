/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Core
import Urm.Shift

/-! # Unary-Unary Composition

This file proves that the composition of two unary URM-computable functions is URM-computable.
This is the simplest non-trivial composition case and serves as a stepping stone toward the
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

/-- Composition of unary URM-computable functions is URM-computable (standard form version).

If `f` and `g` are unary partial functions computed by standard form URM programs,
then `f ∘ g` (i.e., `fun x => (g x).bind (fun y => f (fun _ => y))`) is URM-computable
by a standard form program. -/
theorem URMComputableSF.comp_unary
    {f g : (Fin 1 → ℕ) → Part ℕ}
    (hf : URMComputableSF 1 f)
    (hg : URMComputableSF 1 g) :
    URMComputableSF 1 (fun x => (g x).bind (fun y => f (fun _ => y))) := by
  -- Extract the programs and their standard form properties
  obtain ⟨Pf, hPf_sf, hPf⟩ := hf
  obtain ⟨Pg, hPg_sf, hPg⟩ := hg

  -- The composed program: Pg ++ clearRegistersFrom 1 maxF ++ Pf
  let maxF := Pf.maxRegister
  let clearProg := Program.clearRegistersFrom 1 maxF
  let H := Pg.concat (clearProg.concat Pf)

  -- Show clearProg is straight-line (hence standard form)
  have hClear_sl : clearProg.isStraightLine = true := Program.clearRegistersFrom_isStraightLine 1 maxF

  use H
  constructor
  · -- H is standard form: Pg.concat(clearProg.concat(Pf))
    exact Program.IsStandardForm.concat hPg_sf
      (Program.IsStandardForm.concat (straightLine_isStandardForm hClear_sl) hPf_sf)
  · intro inputs

    constructor
    · -- Halts H ↔ (g inputs).bind (fun y => f (fun _ => y)) is defined
      constructor
      · -- Forward: H halts → composition defined
        intro hHalts
        -- H = Pg.concat(clearProg.concat Pf)
        -- By standard form decomposition, Pg halts
        have hPg_halts : Halts Pg (List.ofFn inputs) :=
          Halts.prefix_of_concat_sf hHalts hPg_sf

        -- Therefore g inputs is defined
        have hg_dom : (g inputs).Dom := (hPg inputs).1.mp hPg_halts

        -- By suffix decomposition, clearProg.concat Pf halts from state after Pg
        have hSuffix := Halts.suffix_of_concat_sf hHalts hPg_sf
        obtain ⟨sPg, _, hsPg_eq, cClearPf, hClearPf_steps, hClearPf_halted⟩ := hSuffix

        -- The state sPg has R[0] = g(inputs)
        have hsPg_r0 : sPg.read 0 = (g inputs).get hg_dom := by
          have h := (hPg inputs).2 hPg_halts hg_dom
          simp only [Result] at h
          rw [hsPg_eq hPg_halts]
          exact h

        -- clearProg is straight-line, so we can further decompose
        -- After clearProg, R[0] = g(inputs) and R[1..maxF] = 0
        -- This matches Config.init [g(inputs)] on relevant registers

        -- Since clearProg.concat Pf halts and clearProg is straight-line (standard form),
        -- Pf halts from the state after clearing.
        -- This state agrees with Config.init [g(inputs)] on registers 0..maxF.
        -- Therefore Pf halts on [g(inputs)], meaning f(g(inputs)) is defined.

        -- Key insight: if H halts, the execution successfully completes Pf,
        -- which means f is defined on g(inputs).
        --
        -- The proof requires:
        -- 1. From hSuffix, clearProg.concat(Pf) halts from sPg
        -- 2. Since clearProg is straight-line (standard form), Pf halts from the
        --    state after clearProg executes
        -- 3. That state agrees with Config.init [g(inputs)] on registers 0..maxF
        --    (R[0] = g(inputs), R[1..maxF] = 0)
        -- 4. By Halts.from_agreeing_state-style reasoning, Pf's halting behavior
        --    is the same as if started from Config.init [g(inputs)]
        -- 5. Therefore Halts Pf [g(inputs)], so f(g(inputs)) is defined
        have hf_dom : (f (fun _ => (g inputs).get hg_dom)).Dom := by
          -- The state after clearProg is straightLineFinalState hClear_sl sPg
          let sClear := straightLineFinalState hClear_sl sPg

          -- This state agrees with Config.init [g(inputs)] on registers 0..maxF
          have hagree_clear : ∀ r, r ≤ Pf.maxRegister →
              sClear.read r = (State.fromInputs [(g inputs).get hg_dom]).read r := by
            intro r hr
            by_cases hr0 : r = 0
            · -- R[0] = g(inputs) (preserved by clearProg)
              subst hr0
              simp only [sClear]
              rw [clearRegistersFrom_preserves_zero 1 maxF sPg (by omega : 0 < 1)]
              simp only [State.fromInputs, State.read, List.getD_cons_zero]
              exact hsPg_r0
            · -- R[r] = 0 for r > 0 (cleared by clearProg, and Config.init has 0)
              have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
              have hr_range : 1 ≤ r ∧ r < 1 + maxF := ⟨hr_pos, by omega⟩
              simp only [sClear]
              rw [clearRegistersFrom_zeros 1 maxF sPg r hr_range]
              symm
              apply State.fromInputs_out_of_range
              simp only [List.length_singleton]
              omega

          -- clearProg halts from sPg at pc = clearProg.length
          have hClear_halts := straightLine_halts_from_state hClear_sl sPg
          obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc⟩ := hClear_halts

          -- The state at cClear equals sClear (by determinism)
          have hClear_state_eq : cClear.state = sClear := by
            have hspec := straightLineFinalState_spec hClear_sl sPg
            have huniq := Steps.halts_unique hClear_steps hClear_halted hspec.1 hspec.2.1
            simp only [straightLineFinalState, huniq, sClear]

          -- Lift clearProg steps to clearProg.concat Pf
          have hClear_steps_in_concat : Steps (clearProg.concat Pf) ⟨0, sPg⟩ cClear :=
            Steps.concat_left_prefix hClear_steps hClear_halted

          -- By deterministic continuation, the path to cClearPf goes through cClear
          have hCont : Steps (clearProg.concat Pf) cClear cClearPf :=
            Steps.deterministic_continuation hClear_steps_in_concat hClearPf_steps hClearPf_halted

          -- The suffix from cClear to cClearPf is Pf execution
          -- cClear.pc = clearProg.length, so we're at the start of Pf in the concat
          -- The remaining steps execute Pf (with pc offset)

          -- Extract that Pf halts from sClear
          -- This is the key decomposition: the suffix execution corresponds to Pf
          have hPf_halts_from_sClear : ∃ c, Steps Pf ⟨0, sClear⟩ c ∧ c.isHalted Pf := by
            -- Rewrite hCont to start from ⟨clearProg.length, sClear⟩
            -- cClear = ⟨clearProg.length, sClear⟩ by hClear_pc and hClear_state_eq
            have hcClear_eq : cClear = ⟨clearProg.length, sClear⟩ :=
              Config.ext hClear_pc hClear_state_eq
            have hCont' : Steps (clearProg.concat Pf) ⟨clearProg.length, sClear⟩ cClearPf := by
              rw [← hcClear_eq]; exact hCont
            -- cClearPf.pc ≥ clearProg.length (it's halted, so pc ≥ total length)
            have hpc' : cClearPf.pc ≥ clearProg.length := by
              simp only [Config.isHalted, Program.concat, List.length_append,
                         Program.shiftJumps, List.length_map] at hClearPf_halted
              omega
            -- Apply the extraction lemma
            obtain ⟨c, hsteps, hhalted, _⟩ := Steps.of_concat_right hCont' hClearPf_halted hpc'
            exact ⟨c, hsteps, hhalted⟩

          obtain ⟨cPf, hPf_steps, hPf_halted⟩ := hPf_halts_from_sClear

          -- Use Halts.of_agreeing_state to conclude Halts Pf [g(inputs)]
          have hPf_halts : Halts Pf [(g inputs).get hg_dom] := by
            have hagree' : ∀ r, r ≤ Pf.maxRegister →
                sClear.read r = (State.fromInputs [(g inputs).get hg_dom]).read r :=
              hagree_clear
            exact Halts.of_agreeing_state hPf_steps hPf_halted hagree'

          -- By URMComputableSF, Halts Pf [g(inputs)] ↔ f is defined
          have hf_halts_iff := (hPf (fun _ => (g inputs).get hg_dom)).1
          have : List.ofFn (fun (_ : Fin 1) => (g inputs).get hg_dom) = [(g inputs).get hg_dom] := by
            simp only [List.ofFn_succ, List.ofFn_zero]
          rw [this] at hf_halts_iff
          exact hf_halts_iff.mp hPf_halts

        -- Combine: bind is defined when both g and f are defined
        apply Part.bind_dom.mpr
        exact ⟨hg_dom, hf_dom⟩
      · -- Backward: composition defined → H halts
        intro hDom
        -- (g inputs).bind f is defined means:
        -- 1. g inputs is defined (so Pg halts)
        -- 2. f (singleton (g inputs).get) is defined (so Pf halts on g(inputs))
        have hg_dom : (g inputs).Dom := Part.bind_dom.mp hDom |>.1
        have hf_dom : (f (fun _ => (g inputs).get hg_dom)).Dom := by
          have h := Part.bind_dom.mp hDom |>.2
          convert h

        -- Step 1: Pg halts on inputs
        have hPg_halts : Halts Pg (List.ofFn inputs) := (hPg inputs).1.mpr hg_dom

        -- Get Pg's final config and use standard form to get pc = length
        let cPg := Classical.choose hPg_halts
        have hPg_spec := Classical.choose_spec hPg_halts
        have hPg_steps : Steps Pg (Config.init (List.ofFn inputs)) cPg := hPg_spec.1
        have hPg_halted : cPg.isHalted Pg := hPg_spec.2
        have hPg_pc : cPg.pc = Pg.length := hPg_sf.halts_at_length (List.ofFn inputs) cPg hPg_steps hPg_halted

        -- Pg's result is g(inputs)
        have hPg_result : cPg.state.output = (g inputs).get hg_dom := by
          have h := (hPg inputs).2 hPg_halts hg_dom
          simp only [Result] at h
          exact h

        -- Step 2: clearProg halts from cPg.state (straight-line program)
        have hClear_halts_from_state : ∃ c, Steps clearProg ⟨0, cPg.state⟩ c ∧
            c.isHalted clearProg ∧ c.pc = clearProg.length :=
          straightLine_halts_from_state hClear_sl cPg.state

        obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc⟩ := hClear_halts_from_state

        -- The final state from cClear equals straightLineFinalState (by determinism)
        have hClear_state_eq : cClear.state = straightLineFinalState hClear_sl cPg.state := by
          have hspec := straightLineFinalState_spec hClear_sl cPg.state
          have huniq := Steps.halts_unique hClear_steps hClear_halted hspec.1 hspec.2.1
          simp only [straightLineFinalState, huniq]

        -- After clearing: R[0] still has g(inputs), R[1..maxF] are 0
        have hClear_state_r0 : cClear.state.read 0 = (g inputs).get hg_dom := by
          rw [hClear_state_eq]
          rw [clearRegistersFrom_preserves_zero 1 maxF cPg.state (by omega : 0 < 1)]
          exact hPg_result

        -- Step 3: Pf halts from cClear.state
        -- The state after clearing matches Config.init [g(inputs)] on registers 0..maxF
        have hPf_halts_input : Halts Pf [((g inputs).get hg_dom)] := by
          have hf_halts_iff := (hPf (fun _ => (g inputs).get hg_dom)).1
          have : List.ofFn (fun (_ : Fin 1) => (g inputs).get hg_dom) = [(g inputs).get hg_dom] := by
            simp only [List.ofFn_succ, List.ofFn_zero]
          rw [this] at hf_halts_iff
          exact hf_halts_iff.mpr hf_dom

        -- Use Halts.from_agreeing_state to show Pf halts from cClear.state
        have hagree : ∀ r, r ≤ Pf.maxRegister →
            cClear.state.read r = (State.fromInputs [((g inputs).get hg_dom)]).read r := by
          intro r hr
          rw [hClear_state_eq]
          by_cases hr0 : r = 0
          · -- R[0] = g(inputs)
            subst hr0
            rw [clearRegistersFrom_preserves_zero 1 maxF cPg.state (by omega : 0 < 1)]
            have h1 : (State.fromInputs [((g inputs).get hg_dom)]).read 0 = (g inputs).get hg_dom := by
              simp only [State.fromInputs, State.read, List.getD_cons_zero]
            rw [h1]
            exact hPg_result
          · -- R[r] = 0 for r > 0 and r ≤ maxF
            have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
            have hr_range : 1 ≤ r ∧ r < 1 + maxF := ⟨hr_pos, by omega⟩
            rw [clearRegistersFrom_zeros 1 maxF cPg.state r hr_range]
            have h2 : (State.fromInputs [((g inputs).get hg_dom)]).read r = 0 := by
              apply State.fromInputs_out_of_range
              simp only [List.length_singleton]
              omega
            rw [h2]

        have ⟨cPf, hPf_steps, hPf_halted, _⟩ :=
          Halts.from_agreeing_state hPf_halts_input hagree

        -- Now chain the programs using standard form
        -- Build Steps through clearProg.concat Pf starting from cPg.state

        -- Lift clearProg steps to clearProg.concat Pf
        have hClear_steps_lifted : Steps (clearProg.concat Pf) ⟨0, cPg.state⟩ cClear :=
          Steps.concat_left_prefix (p2 := Pf) hClear_steps hClear_halted

        -- Lift Pf steps to clearProg.concat Pf (offset by clearProg.length)
        have hPf_steps_lifted : Steps (clearProg.concat Pf)
            ⟨cClear.pc, cClear.state⟩ ⟨cPf.pc + clearProg.length, cPf.state⟩ := by
          have h := Steps.concat_right (p1 := clearProg) hPf_steps hPf_halted
          simp only [Nat.zero_add] at h
          rw [hClear_pc]
          exact h

        -- Combine the steps: clearProg part then Pf part
        have hClearPf_steps : Steps (clearProg.concat Pf) ⟨0, cPg.state⟩
            ⟨cPf.pc + clearProg.length, cPf.state⟩ := by
          have heq : cClear = ⟨cClear.pc, cClear.state⟩ := rfl
          rw [heq] at hClear_steps_lifted
          exact Relation.ReflTransGen.trans hClear_steps_lifted hPf_steps_lifted

        -- The final config is halted in clearProg.concat Pf
        have hClearPf_halted : (⟨cPf.pc + clearProg.length, cPf.state⟩ : Config).isHalted
            (clearProg.concat Pf) := by
          simp only [Config.isHalted, Program.concat_length] at hPf_halted ⊢
          omega

        -- Now use Halts.concat_continuation to chain Pg with (clearProg ++ Pf)
        exact Halts.concat_continuation hPg_halts hPg_pc
          ⟨⟨cPf.pc + clearProg.length, cPf.state⟩, hClearPf_steps, hClearPf_halted⟩

    · -- Result equality
      intro hHalts hDom
      have hg_dom : (g inputs).Dom := Part.bind_dom.mp hDom |>.1
      have hf_dom : (f (fun _ => (g inputs).get hg_dom)).Dom := by
        have h := Part.bind_dom.mp hDom |>.2
        convert h

      have hbind_eq : (g inputs).bind (fun y => f (fun _ => y)) = f (fun _ => (g inputs).get hg_dom) :=
        Part.Dom.bind hg_dom (fun y => f (fun _ => y))
      simp only [hbind_eq]

      -- Step 1: Get Pg's final config with Result = g(inputs)
      have hPg_halts : Halts Pg (List.ofFn inputs) := (hPg inputs).1.mpr hg_dom

      let cPg := Classical.choose hPg_halts
      have hPg_spec := Classical.choose_spec hPg_halts
      have hPg_steps : Steps Pg (Config.init (List.ofFn inputs)) cPg := hPg_spec.1
      have hPg_halted : cPg.isHalted Pg := hPg_spec.2
      have hPg_pc : cPg.pc = Pg.length := hPg_sf.halts_at_length (List.ofFn inputs) cPg hPg_steps hPg_halted

      have hPg_result : cPg.state.output = (g inputs).get hg_dom := by
        have h := (hPg inputs).2 hPg_halts hg_dom
        simp only [Result] at h
        exact h

      -- Step 2: clearProg halts from cPg.state
      have hClear_halts := straightLine_halts_from_state hClear_sl cPg.state
      obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc⟩ := hClear_halts

      have hClear_state_eq : cClear.state = straightLineFinalState hClear_sl cPg.state := by
        have hspec := straightLineFinalState_spec hClear_sl cPg.state
        have huniq := Steps.halts_unique hClear_steps hClear_halted hspec.1 hspec.2.1
        simp only [straightLineFinalState, huniq]

      -- After clearing: R[0] still has g(inputs)
      have hClear_state_r0 : cClear.state.read 0 = (g inputs).get hg_dom := by
        rw [hClear_state_eq]
        rw [clearRegistersFrom_preserves_zero 1 maxF cPg.state (by omega : 0 < 1)]
        exact hPg_result

      -- Step 3: Pf halts from cClear.state with correct result
      have hPf_halts_input : Halts Pf [((g inputs).get hg_dom)] := by
        have hf_halts_iff := (hPf (fun _ => (g inputs).get hg_dom)).1
        have : List.ofFn (fun (_ : Fin 1) => (g inputs).get hg_dom) = [(g inputs).get hg_dom] := by
          simp only [List.ofFn_succ, List.ofFn_zero]
        rw [this] at hf_halts_iff
        exact hf_halts_iff.mpr hf_dom

      -- Build state agreement
      have hagree : ∀ r, r ≤ Pf.maxRegister →
          cClear.state.read r = (State.fromInputs [((g inputs).get hg_dom)]).read r := by
        intro r hr
        rw [hClear_state_eq]
        by_cases hr0 : r = 0
        · subst hr0
          rw [clearRegistersFrom_preserves_zero 1 maxF cPg.state (by omega : 0 < 1)]
          have h1 : (State.fromInputs [((g inputs).get hg_dom)]).read 0 = (g inputs).get hg_dom := by
            simp only [State.fromInputs, State.read, List.getD_cons_zero]
          rw [h1]
          exact hPg_result
        · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
          have hr_range : 1 ≤ r ∧ r < 1 + maxF := ⟨hr_pos, by omega⟩
          rw [clearRegistersFrom_zeros 1 maxF cPg.state r hr_range]
          have h2 : (State.fromInputs [((g inputs).get hg_dom)]).read r = 0 := by
            apply State.fromInputs_out_of_range
            simp only [List.length_singleton]
            omega
          rw [h2]

      -- Use from_agreeing_state and KEEP the output equality
      have ⟨cPf, hPf_steps, hPf_halted, hPf_output⟩ := Halts.from_agreeing_state hPf_halts_input hagree

      -- Step 4: Get Pf's result via hPf.2
      have hPf_result : Result Pf [(g inputs).get hg_dom] hPf_halts_input =
          (f (fun _ => (g inputs).get hg_dom)).get hf_dom := by
        have h := (hPf (fun _ => (g inputs).get hg_dom)).2 hPf_halts_input hf_dom
        have heq : List.ofFn (fun (_ : Fin 1) => (g inputs).get hg_dom) = [(g inputs).get hg_dom] := by
          simp only [List.ofFn_succ, List.ofFn_zero]
        simp only [heq] at h
        exact h

      -- Step 5: Connect H's result to cPf's output
      -- Build the full execution trace for H
      have hClear_steps_lifted : Steps (clearProg.concat Pf) ⟨0, cPg.state⟩ cClear :=
        Steps.concat_left_prefix (p2 := Pf) hClear_steps hClear_halted

      have hPf_steps_lifted : Steps (clearProg.concat Pf)
          ⟨cClear.pc, cClear.state⟩ ⟨cPf.pc + clearProg.length, cPf.state⟩ := by
        have h := Steps.concat_right (p1 := clearProg) hPf_steps hPf_halted
        simp only [Nat.zero_add] at h
        rw [hClear_pc]
        exact h

      have hClearPf_steps : Steps (clearProg.concat Pf) ⟨0, cPg.state⟩
          ⟨cPf.pc + clearProg.length, cPf.state⟩ := by
        have heq : cClear = ⟨cClear.pc, cClear.state⟩ := rfl
        rw [heq] at hClear_steps_lifted
        exact Relation.ReflTransGen.trans hClear_steps_lifted hPf_steps_lifted

      have hClearPf_halted : (⟨cPf.pc + clearProg.length, cPf.state⟩ : Config).isHalted
          (clearProg.concat Pf) := by
        simp only [Config.isHalted, Program.concat_length] at hPf_halted ⊢
        omega

      -- Lift to full H execution
      have hH_halts_built : Halts H (List.ofFn inputs) :=
        Halts.concat_continuation hPg_halts hPg_pc
          ⟨⟨cPf.pc + clearProg.length, cPf.state⟩, hClearPf_steps, hClearPf_halted⟩

      -- H's final config
      let cH := Classical.choose hHalts
      have hH_spec := Classical.choose_spec hHalts
      have hH_steps : Steps H (Config.init (List.ofFn inputs)) cH := hH_spec.1
      have hH_halted : cH.isHalted H := hH_spec.2

      -- The final config we built
      let cH_built : Config := ⟨cPf.pc + clearProg.length + Pg.length, cPf.state⟩

      -- Show cH_built is halted
      have hH_built_halted : cH_built.isHalted H := by
        simp only [Config.isHalted, H, Program.concat_length, cH_built]
        simp only [Config.isHalted] at hPf_halted
        omega

      -- Build steps to cH_built
      have hPg_steps_lifted : Steps H (Config.init (List.ofFn inputs)) ⟨Pg.length, cPg.state⟩ := by
        have hPg_pc_eq : cPg = ⟨Pg.length, cPg.state⟩ := Config.ext hPg_pc rfl
        rw [← hPg_pc_eq]
        exact Steps.concat_left_prefix (p2 := clearProg.concat Pf) hPg_steps hPg_halted

      have hClearPf_steps_lifted : Steps H ⟨Pg.length, cPg.state⟩ cH_built := by
        have h := Steps.concat_right (p1 := Pg) hClearPf_steps hClearPf_halted
        simp only [Nat.zero_add, cH_built] at h ⊢
        convert h using 2

      have hH_steps_built : Steps H (Config.init (List.ofFn inputs)) cH_built :=
        Relation.ReflTransGen.trans hPg_steps_lifted hClearPf_steps_lifted

      -- By determinism, cH = cH_built
      have hcH_eq : cH = cH_built := Steps.halts_unique hH_steps hH_halted hH_steps_built hH_built_halted

      -- Final chain
      calc Result H (List.ofFn inputs) hHalts
          = cH.state.output := rfl
        _ = cH_built.state.output := by rw [hcH_eq]
        _ = cPf.state.output := rfl
        _ = Result Pf [(g inputs).get hg_dom] hPf_halts_input := hPf_output
        _ = (f (fun _ => (g inputs).get hg_dom)).get hf_dom := hPf_result

end Urm
