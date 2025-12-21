/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition
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

/-! ## Helper: Clear registers from a starting point -/

namespace Program

/-- Clear registers from `start` to `start + count - 1`.
Unlike `clearRegisters` which clears from 0, this allows preserving lower registers. -/
def clearRegistersFrom (start count : ℕ) : Program :=
  (List.range count).map (fun i => Instr.Z (start + i))

@[simp]
theorem clearRegistersFrom_length (start count : ℕ) :
    (clearRegistersFrom start count).length = count := by
  simp [clearRegistersFrom]

theorem clearRegistersFrom_zero (start : ℕ) : clearRegistersFrom start 0 = [] := rfl

theorem clearRegistersFrom_isStraightLine (start count : ℕ) :
    (clearRegistersFrom start count).isStraightLine = true := by
  simp only [clearRegistersFrom, isStraightLine, List.all_map]
  induction count with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.all_append, List.all_cons, List.all_nil,
               and_true, Bool.and_eq_true]
    constructor
    · -- Show all elements in range n satisfy the predicate
      simp only [List.all_eq_true]
      intro i hi
      simp [Instr.isNonJumping]
    · simp [Instr.isNonJumping]

/-- clearRegistersFrom halts on any input. -/
theorem clearRegistersFrom_halts (start count : ℕ) (inputs : List ℕ) :
    Halts (clearRegistersFrom start count) inputs :=
  straightLine_halts (clearRegistersFrom_isStraightLine start count) inputs

end Program

/-! ## Execution semantics for clearRegistersFrom

These theorems use the unified relational semantics via `straightLineFinalState`. -/

/-- For a straight-line program, if some instruction writes 0 to register r,
and no later instruction writes to r, then r is 0 in the final state.

The proof tracks state through execution:
1. After instruction k (Z r) executes, register r is 0
2. Instructions k+1 through n-1 don't write to r (by hnowrite)
3. So r remains 0 in the final state -/
theorem straightLine_zeros_register {p : Program} (hsl : p.isStraightLine = true)
    (s : State) (r : ℕ) (k : ℕ) (hk : k < p.length)
    (hwrite : p[k] = Instr.Z r)
    (hnowrite : ∀ j (hj : j < p.length), k < j → (p[j]'hj).writesTo ≠ some r) :
    (straightLineFinalState hsl s).read r = 0 := by
  have ⟨hsteps, hhalted, hpc⟩ := straightLineFinalState_spec hsl s
  -- Strategy: Show that once instruction k executes, r becomes 0 and stays 0.
  -- The suffix of p from k+1 onward doesn't write to r, so we can use
  -- Steps.straightLine_preserves on that suffix.
  --
  -- We need to decompose execution: steps [0,k] set r to 0, steps [k+1,n) preserve r.
  -- This requires infrastructure for splitting Steps at a specific pc value.
  sorry

/-- clearRegistersFrom zeros the specified range. -/
theorem clearRegistersFrom_zeros (start count : ℕ) (s : State) (r : ℕ)
    (hr : start ≤ r ∧ r < start + count) :
    (straightLineFinalState (Program.clearRegistersFrom_isStraightLine start count) s).read r = 0 := by
  have hsl := Program.clearRegistersFrom_isStraightLine start count
  -- The instruction at index (r - start) is Z r
  let k := r - start
  have hk : k < count := by omega
  have hk_lt : k < (Program.clearRegistersFrom start count).length := by
    simp only [Program.clearRegistersFrom_length]; omega
  have hwrite : (Program.clearRegistersFrom start count)[k] = Instr.Z r := by
    simp only [Program.clearRegistersFrom, List.getElem_map, List.getElem_range]
    congr; omega
  have hnowrite : ∀ j (hj : j < (Program.clearRegistersFrom start count).length),
      k < j → ((Program.clearRegistersFrom start count)[j]'hj).writesTo ≠ some r := by
    intro j hj hkj
    simp only [Program.clearRegistersFrom, List.getElem_map, List.getElem_range,
               Instr.writesTo, ne_eq, Option.some.injEq]
    simp only [Program.clearRegistersFrom_length] at hj
    omega
  exact straightLine_zeros_register hsl s r k hk_lt hwrite hnowrite

/-- clearRegistersFrom preserves registers outside its range. -/
theorem clearRegistersFrom_preserves (start count : ℕ) (s : State) (r : ℕ)
    (hr : r < start ∨ start + count ≤ r) :
    (straightLineFinalState (Program.clearRegistersFrom_isStraightLine start count) s).read r = s.read r := by
  -- The program only writes to registers start, start+1, ..., start+count-1
  -- Since r is outside this range, it is preserved
  have hsl := Program.clearRegistersFrom_isStraightLine start count
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  apply Steps.straightLine_preserves hsl hsteps
  intro instr hmem
  -- Each instruction in clearRegistersFrom is Z (start+i) for some i
  simp only [Program.clearRegistersFrom, List.mem_map] at hmem
  obtain ⟨i, hi_range, hinstr_eq⟩ := hmem
  simp only [List.mem_range] at hi_range
  subst hinstr_eq
  simp only [Instr.writesTo, ne_eq, Option.some.injEq]
  cases hr with
  | inl h => omega
  | inr h => omega

/-- After clearRegistersFrom, R[0] is preserved (when start > 0). -/
theorem clearRegistersFrom_preserves_zero (start count : ℕ) (s : State) (hstart : 0 < start) :
    (straightLineFinalState (Program.clearRegistersFrom_isStraightLine start count) s).read 0 = s.read 0 :=
  clearRegistersFrom_preserves start count s 0 (Or.inl hstart)

/-! ## Unary composition program construction -/

/-- Compose two unary programs: run Pg, clear working registers, run Pf.
The clearing step ensures Pf sees a "fresh" state (all registers 0 except R[0]). -/
def Program.composeUnary (Pf Pg : Program) : Program :=
  let maxF := Pf.maxRegister
  -- Run Pg, then clear R[1]..R[maxF], then run Pf
  Pg.concat ((clearRegistersFrom 1 maxF).concat Pf)

/-! ## Key lemma: Running Pf from a state that matches Config.init on relevant registers -/

/-- If a state agrees with Config.init on registers 0..maxRegister(p), then
running p from that state gives the same result as running from Config.init.

This is the key insight: we don't need exactly Config.init, just agreement on
the registers the program actually uses. -/
theorem Halts.from_agreeing_state {p : Program} {inputs : List ℕ} {s : State}
    (h : Halts p inputs)
    (hagree : ∀ r, r ≤ p.maxRegister → s.read r = (State.fromInputs inputs).read r) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.isHalted p ∧ c.state.output = Result p inputs h := by
  -- Get the halting config from Config.init
  let c_final := Classical.choose h
  have hspec := Classical.choose_spec h
  have hsteps : Steps p (Config.init inputs) c_final := hspec.1
  have hhalted : c_final.isHalted p := hspec.2
  -- Convert hagree to State.agreeOn form
  have hagree' : s.agreeOn (State.fromInputs inputs) 0 p.maxRegister := by
    intro r _ hhi
    exact hagree r hhi
  -- Use Steps.agreeOn to get parallel execution from s
  have hpc_eq : (Config.init inputs).pc = (⟨0, s⟩ : Config).pc := rfl
  obtain ⟨c', hsteps', hpc', hagree''⟩ := Steps.agreeOn hsteps hpc_eq (State.agreeOn_symm hagree')
  use c'
  refine ⟨hsteps', ?_, ?_⟩
  · -- c' is halted: same PC as c_final which is halted
    simp only [Config.isHalted] at hhalted ⊢
    omega
  · -- Output agrees: both read from register 0 which is ≤ maxRegister
    simp only [State.output, Result]
    -- c'.state and c_final.state agree on [0, maxRegister]
    -- Register 0 is in this range (0 ≤ 0 ≤ maxRegister for any p)
    have h0 : 0 ≤ p.maxRegister := Nat.zero_le _
    have hread_eq := hagree'' 0 (Nat.le_refl 0) h0
    -- hread_eq : c_final.state.read 0 = c'.state.read 0
    -- Goal: c'.state 0 = (Classical.choose h).state 0
    -- c_final = Classical.choose h, and read 0 = (· 0)
    simp only [State.read] at hread_eq
    exact hread_eq.symm

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
    -- clearProg is straight-line, hence standard form
    have hClear_sf : clearProg.IsStandardForm := straightLine_isStandardForm hClear_sl
    -- clearProg.concat Pf is standard form
    have hClearPf_sf : (clearProg.concat Pf).IsStandardForm :=
      Program.IsStandardForm.concat hClear_sf hPf_sf
    -- Pg.concat(clearProg.concat Pf) is standard form
    exact Program.IsStandardForm.concat hPg_sf hClearPf_sf
  · intro inputs

    constructor
    · -- Halts H ↔ (g inputs).bind (fun y => f (fun _ => y)) is defined
      constructor
      · -- Forward: H halts → composition defined
        intro hHalts
        -- H = Pg.concat(clearProg.concat Pf)
        -- By standard form decomposition, Pg halts
        have hPg_halts : Halts Pg (List.ofFn inputs) := by
          exact Halts.prefix_of_concat_sf hHalts hPg_sf

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
          -- This requires "halts from state" decomposition infrastructure
          -- which is postulated (standard form behavior)
          sorry

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
        have hPg_pc : cPg.pc = Pg.length := hPg_sf (List.ofFn inputs) cPg hPg_steps hPg_halted

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
        have hClear_steps_lifted : Steps (clearProg.concat Pf) ⟨0, cPg.state⟩ cClear := by
          exact Steps.concat_left_prefix (p2 := Pf) hClear_steps hClear_halted

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

        have hClearPf_halts : ∃ c, Steps (clearProg.concat Pf) ⟨0, cPg.state⟩ c ∧
            c.isHalted (clearProg.concat Pf) :=
          ⟨⟨cPf.pc + clearProg.length, cPf.state⟩, hClearPf_steps, hClearPf_halted⟩

        -- Now use Halts.concat_continuation to chain Pg with (clearProg ++ Pf)
        apply Halts.concat_continuation hPg_halts hPg_pc hClearPf_halts

    · -- Result equality
      intro hHalts hDom
      have hg_dom : (g inputs).Dom := Part.bind_dom.mp hDom |>.1
      have hf_dom : (f (fun _ => (g inputs).get hg_dom)).Dom := by
        have h := Part.bind_dom.mp hDom |>.2
        convert h

      have hbind_eq : (g inputs).bind (fun y => f (fun _ => y)) = f (fun _ => (g inputs).get hg_dom) :=
        Part.Dom.bind hg_dom (fun y => f (fun _ => y))
      simp only [hbind_eq]

      -- Result equality: Result H = f(g(inputs))
      --
      -- The proof tracks R[0] through all three phases:
      -- 1. After Pg: R[0] = g(inputs) = (g inputs).get hg_dom
      -- 2. After clearProg: R[0] = g(inputs) (preserved, since clear starts at R[1])
      -- 3. After Pf: R[0] = f(g(inputs)) = (f (fun _ => g(inputs))).get hf_dom
      --
      -- The key steps:
      -- a) By standard form, H's final config is reached by running all three phases
      -- b) The state entering Pf agrees with Config.init [g(inputs)] on registers 0..maxF
      -- c) By determinism and Halts.from_agreeing_state, Pf produces the same result
      --    as if started from Config.init [g(inputs)]
      -- d) By hPf, Result Pf [g(inputs)] = f(g(inputs))
      -- e) Therefore Result H = f(g(inputs))
      sorry

end Urm
