/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Block.Basic
import Urm.StraightLine

/-! # Pseudo-Instructions Library

Useful URM program fragments that serve as building blocks for higher-level
combinators. Each pseudo-instruction is either a straight-line program or
a small looping program with explicit workspace requirements.

## Main definitions

- `copyProgram`: Copy one register to another (single T instruction)
- `zeroProgram`: Zero one register (single Z instruction)
- `clearRangeProgram`: Zero a range of registers (straight-line)
- `copyRangeProgram`: Copy a range of registers (straight-line)
- `decrementProgram`: Decrement a register using workspace
- `addToProgram`: Add one register to another using workspace

## Key theorems

Each program has:
- A halts theorem showing it always terminates
- A result theorem showing the computed value
- A preserves theorem showing which registers are untouched

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

/-! ## Single-instruction programs -/

/-- Copy register `src` to register `dst`. -/
def copyProgram (src dst : ℕ) : Program := [Instr.T src dst]

/-- Zero register `n`. -/
def zeroProgram (n : ℕ) : Program := [Instr.Z n]

/-- Increment register `n`. -/
def succProgram (n : ℕ) : Program := [Instr.S n]

namespace copyProgram

@[simp] theorem length_eq (src dst : ℕ) : (copyProgram src dst).length = 1 := rfl
@[simp] theorem getInstr_0 (src dst : ℕ) : (copyProgram src dst).getInstr 0 = some (Instr.T src dst) := rfl

theorem isStraightLine (src dst : ℕ) : (copyProgram src dst).isStraightLine = true := by
  simp [copyProgram, Program.isStraightLine, Instr.isNonJumping]

theorem halts (src dst : ℕ) (s : State) :
    ∃ c, Steps (copyProgram src dst) ⟨0, s⟩ c ∧ c.isHalted (copyProgram src dst) := by
  obtain ⟨c, hsteps, hhalted, _⟩ := straightLine_halts_from_state (isStraightLine src dst) s
  exact ⟨c, hsteps, hhalted⟩

theorem result (src dst : ℕ) (s : State) :
    (straightLineFinalState (isStraightLine src dst) s).read dst = s.read src := by
  have hsl := isStraightLine src dst
  have ⟨hsteps, hhalted, _⟩ := straightLineFinalState_spec hsl s
  -- The program is [T src dst], so after one step we have copied src to dst
  have hstep : Step (copyProgram src dst) ⟨0, s⟩ ⟨1, s.write dst (s.read src)⟩ := Step.trans rfl
  have hhalted' : (⟨1, s.write dst (s.read src)⟩ : Config).isHalted (copyProgram src dst) := by simp
  have heq := Steps.halts_unique hsteps hhalted (Steps.single hstep) hhalted'
  show (Classical.choose (straightLine_halts_from_state hsl s)).state.read dst = s.read src
  simp only [heq, State.read, State.write, Function.update_self]

theorem preserves (src dst r : ℕ) (s : State) (hr : r ≠ dst) :
    (straightLineFinalState (isStraightLine src dst) s).read r = s.read r := by
  have hsl := isStraightLine src dst
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  apply Steps.straightLine_preserves hsl hsteps
  intro instr hmem
  simp only [copyProgram, List.mem_singleton] at hmem
  simp only [hmem, Instr.writesTo, ne_eq, Option.some.injEq]
  exact Ne.symm hr

end copyProgram

namespace zeroProgram

@[simp] theorem length_eq (n : ℕ) : (zeroProgram n).length = 1 := rfl
@[simp] theorem getInstr_0 (n : ℕ) : (zeroProgram n).getInstr 0 = some (Instr.Z n) := rfl

theorem isStraightLine (n : ℕ) : (zeroProgram n).isStraightLine = true := by
  simp [zeroProgram, Program.isStraightLine, Instr.isNonJumping]

theorem halts (n : ℕ) (s : State) :
    ∃ c, Steps (zeroProgram n) ⟨0, s⟩ c ∧ c.isHalted (zeroProgram n) := by
  obtain ⟨c, hsteps, hhalted, _⟩ := straightLine_halts_from_state (isStraightLine n) s
  exact ⟨c, hsteps, hhalted⟩

theorem result (n : ℕ) (s : State) :
    (straightLineFinalState (isStraightLine n) s).read n = 0 := by
  have hsl := isStraightLine n
  have hk : 0 < (zeroProgram n).length := by simp
  have hwrite : (zeroProgram n)[0] = Instr.Z n := rfl
  have hnowrite : ∀ j (hj : j < (zeroProgram n).length), 0 < j →
      ((zeroProgram n)[j]'hj).writesTo ≠ some n := by
    intro j hj hjgt; simp at hj; omega
  exact straightLine_zeros_register hsl s n 0 hk hwrite hnowrite

theorem preserves (n r : ℕ) (s : State) (hr : r ≠ n) :
    (straightLineFinalState (isStraightLine n) s).read r = s.read r := by
  have hsl := isStraightLine n
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  apply Steps.straightLine_preserves hsl hsteps
  intro instr hmem
  simp only [zeroProgram, List.mem_singleton] at hmem
  simp only [hmem, Instr.writesTo, ne_eq, Option.some.injEq]
  exact Ne.symm hr

end zeroProgram

namespace succProgram

@[simp] theorem length_eq (n : ℕ) : (succProgram n).length = 1 := rfl
@[simp] theorem getInstr_0 (n : ℕ) : (succProgram n).getInstr 0 = some (Instr.S n) := rfl

theorem isStraightLine (n : ℕ) : (succProgram n).isStraightLine = true := by
  simp [succProgram, Program.isStraightLine, Instr.isNonJumping]

theorem halts (n : ℕ) (s : State) :
    ∃ c, Steps (succProgram n) ⟨0, s⟩ c ∧ c.isHalted (succProgram n) := by
  obtain ⟨c, hsteps, hhalted, _⟩ := straightLine_halts_from_state (isStraightLine n) s
  exact ⟨c, hsteps, hhalted⟩

theorem result (n : ℕ) (s : State) :
    (straightLineFinalState (isStraightLine n) s).read n = s.read n + 1 := by
  have hsl := isStraightLine n
  have ⟨hsteps, hhalted, _⟩ := straightLineFinalState_spec hsl s
  have hstep : Step (succProgram n) ⟨0, s⟩ ⟨1, s.write n (s.read n + 1)⟩ := Step.succ rfl
  have hhalted' : (⟨1, s.write n (s.read n + 1)⟩ : Config).isHalted (succProgram n) := by simp
  have heq := Steps.halts_unique hsteps hhalted (Steps.single hstep) hhalted'
  show (Classical.choose (straightLine_halts_from_state hsl s)).state.read n = s.read n + 1
  simp only [heq, State.read, State.write, Function.update_self]

theorem preserves (n r : ℕ) (s : State) (hr : r ≠ n) :
    (straightLineFinalState (isStraightLine n) s).read r = s.read r := by
  have hsl := isStraightLine n
  have ⟨hsteps, _, _⟩ := straightLineFinalState_spec hsl s
  apply Steps.straightLine_preserves hsl hsteps
  intro instr hmem
  simp only [succProgram, List.mem_singleton] at hmem
  simp only [hmem, Instr.writesTo, ne_eq, Option.some.injEq]
  exact Ne.symm hr

end succProgram

/-! ## Range programs (re-exported from StraightLine) -/

/-- Clear registers from `start` to `start + count - 1`.
This is `Program.clearRegistersFrom` from StraightLine.lean. -/
abbrev clearRangeProgram := Program.clearRegistersFrom

/-- Copy `count` registers from `src` to `dst`.
This is `Program.copyRegisterRange` from StraightLine.lean. -/
abbrev copyRangeProgram := Program.copyRegisterRange

/-! ## Looping programs

These programs use loops and require workspace registers. The proofs are more complex
due to tracking register state through iterations.
-/

/-- Decrement program: decrements R[target] using R[ws] and R[ws+1] as workspace.

After execution: R[target] = R[target] - 1 (saturating at 0).

The algorithm counts from 0 up to target's value, with ws tracking one behind.
When the counter equals target, ws contains target-1, which is then copied to target. -/
def decrementProgram (target ws : ℕ) : Program := [
  Instr.Z ws,                       -- 0: Clear workspace (will hold result)
  Instr.Z (ws + 1),                 -- 1: Clear counter
  Instr.J target (ws + 1) 7,        -- 2: If target = counter, exit (result in ws)
  Instr.S ws,                       -- 3: Increment result
  Instr.S (ws + 1),                 -- 4: Increment counter
  Instr.J 0 0 2,                    -- 5: Unconditional jump back
  Instr.T ws target                 -- 6: Copy result to target
]

namespace decrementProgram

@[simp] theorem length_eq (target ws : ℕ) : (decrementProgram target ws).length = 7 := rfl
@[simp] theorem getInstr_0 (target ws : ℕ) :
    (decrementProgram target ws).getInstr 0 = some (Instr.Z ws) := rfl
@[simp] theorem getInstr_1 (target ws : ℕ) :
    (decrementProgram target ws).getInstr 1 = some (Instr.Z (ws + 1)) := rfl
@[simp] theorem getInstr_2 (target ws : ℕ) :
    (decrementProgram target ws).getInstr 2 = some (Instr.J target (ws + 1) 7) := rfl
@[simp] theorem getInstr_3 (target ws : ℕ) :
    (decrementProgram target ws).getInstr 3 = some (Instr.S ws) := rfl
@[simp] theorem getInstr_4 (target ws : ℕ) :
    (decrementProgram target ws).getInstr 4 = some (Instr.S (ws + 1)) := rfl
@[simp] theorem getInstr_5 (target ws : ℕ) :
    (decrementProgram target ws).getInstr 5 = some (Instr.J 0 0 2) := rfl
@[simp] theorem getInstr_6 (target ws : ℕ) :
    (decrementProgram target ws).getInstr 6 = some (Instr.T ws target) := rfl

/-- Full execution: decrement R[target] by 1 (saturating at 0). -/
theorem full_execution (target ws : ℕ) (s : State) (n : ℕ) (hn : s.read target = n)
    (hws_ne : target ≠ ws) (hctr_ne : target ≠ ws + 1) (hws_ws1 : ws ≠ ws + 1) :
    ∃ s', Steps (decrementProgram target ws) ⟨0, s⟩ ⟨7, s'⟩ ∧
          s'.read target = n - 1 ∧
          (⟨7, s'⟩ : Config).isHalted (decrementProgram target ws) := by
  sorry

theorem halts (target ws : ℕ) (s : State)
    (hws_ne : target ≠ ws) (hctr_ne : target ≠ ws + 1) :
    ∃ c, Steps (decrementProgram target ws) ⟨0, s⟩ c ∧
         c.isHalted (decrementProgram target ws) := by
  have hws_ws1 : ws ≠ ws + 1 := by omega
  obtain ⟨s', hsteps, _, hhalted⟩ := full_execution target ws s (s.read target) rfl hws_ne hctr_ne hws_ws1
  exact ⟨⟨7, s'⟩, hsteps, hhalted⟩

theorem result (target ws : ℕ) (s : State)
    (hws_ne : target ≠ ws) (hctr_ne : target ≠ ws + 1) :
    ∃ s', Steps (decrementProgram target ws) ⟨0, s⟩ ⟨7, s'⟩ ∧
          s'.read target = s.read target - 1 ∧
          (⟨7, s'⟩ : Config).isHalted (decrementProgram target ws) := by
  have hws_ws1 : ws ≠ ws + 1 := by omega
  exact full_execution target ws s (s.read target) rfl hws_ne hctr_ne hws_ws1

/-- decrementProgram is in standard form (all jumps target valid positions). -/
theorem isStandardForm (target ws : ℕ) : (decrementProgram target ws).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm decrementProgram
  simp only [List.all_cons, List.all_nil, List.length_cons, List.length_nil,
             Instr.hasBoundedJump, Bool.and_true, Bool.true_and]
  decide

end decrementProgram

/-- Add program: adds R[b] to R[a] using R[ws] as workspace (counter).

After execution: R[a] = R[a] + R[b], R[b] unchanged. -/
def addToProgram (a b ws : ℕ) : Program := [
  Instr.Z ws,           -- 0: Clear counter
  Instr.J ws b 5,       -- 1: If counter = b, exit
  Instr.S a,            -- 2: Increment a
  Instr.S ws,           -- 3: Increment counter
  Instr.J 0 0 1         -- 4: Unconditional jump back
]

namespace addToProgram

@[simp] theorem length_eq (a b ws : ℕ) : (addToProgram a b ws).length = 5 := rfl
@[simp] theorem getInstr_0 (a b ws : ℕ) :
    (addToProgram a b ws).getInstr 0 = some (Instr.Z ws) := rfl
@[simp] theorem getInstr_1 (a b ws : ℕ) :
    (addToProgram a b ws).getInstr 1 = some (Instr.J ws b 5) := rfl
@[simp] theorem getInstr_2 (a b ws : ℕ) :
    (addToProgram a b ws).getInstr 2 = some (Instr.S a) := rfl
@[simp] theorem getInstr_3 (a b ws : ℕ) :
    (addToProgram a b ws).getInstr 3 = some (Instr.S ws) := rfl
@[simp] theorem getInstr_4 (a b ws : ℕ) :
    (addToProgram a b ws).getInstr 4 = some (Instr.J 0 0 1) := rfl

/-- Full execution: R[a] := R[a] + R[b]. -/
theorem full_execution (a b ws : ℕ) (s : State) (x y : ℕ)
    (ha : s.read a = x) (hb : s.read b = y)
    (hws_ne_b : ws ≠ b) (ha_ne_ws : a ≠ ws) :
    ∃ s', Steps (addToProgram a b ws) ⟨0, s⟩ ⟨5, s'⟩ ∧
          s'.read a = x + y ∧
          s'.read b = y ∧
          (⟨5, s'⟩ : Config).isHalted (addToProgram a b ws) := by
  sorry

theorem halts (a b ws : ℕ) (s : State)
    (hws_ne_b : ws ≠ b) (ha_ne_ws : a ≠ ws) :
    ∃ c, Steps (addToProgram a b ws) ⟨0, s⟩ c ∧
         c.isHalted (addToProgram a b ws) := by
  obtain ⟨s', hsteps, _, _, hhalted⟩ :=
    full_execution a b ws s (s.read a) (s.read b) rfl rfl hws_ne_b ha_ne_ws
  exact ⟨⟨5, s'⟩, hsteps, hhalted⟩

theorem result (a b ws : ℕ) (s : State)
    (hws_ne_b : ws ≠ b) (ha_ne_ws : a ≠ ws) :
    ∃ s', Steps (addToProgram a b ws) ⟨0, s⟩ ⟨5, s'⟩ ∧
          s'.read a = s.read a + s.read b ∧
          (⟨5, s'⟩ : Config).isHalted (addToProgram a b ws) := by
  obtain ⟨s', hsteps, ha', _, hhalted⟩ :=
    full_execution a b ws s (s.read a) (s.read b) rfl rfl hws_ne_b ha_ne_ws
  exact ⟨s', hsteps, ha', hhalted⟩

/-- addToProgram is in standard form (all jumps target valid positions). -/
theorem isStandardForm (a b ws : ℕ) : (addToProgram a b ws).IsStandardForm := by
  unfold Program.IsStandardForm Program.isStandardForm addToProgram
  simp only [List.all_cons, List.all_nil, List.length_cons, List.length_nil,
             Instr.hasBoundedJump, Bool.and_true, Bool.true_and]
  decide

end addToProgram

/-! ## URMBlock versions of pseudo-instructions -/

namespace URMBlock

/-- Zero block: output 0 regardless of inputs. -/
def const_zero (n : ℕ) : URMBlock where
  program := [Instr.Z 0]
  arity := n
  h_sf := straightLine_isStandardForm (by rfl)

theorem const_zero_computes (n : ℕ) :
    (const_zero n).ComputesN n (fun _ => Part.some 0) := by
  intro inputs
  simp only [const_zero]
  let inputList := List.ofFn inputs
  let finalState := (State.fromInputs inputList).write 0 0
  have hstep : Step [Instr.Z 0] (Config.init inputList) ⟨1, finalState⟩ := Step.zero rfl
  have hhalted : (⟨1, finalState⟩ : Config).isHalted [Instr.Z 0] := by simp
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨⟨1, finalState⟩, Steps.single hstep, hhalted⟩
  · intro hHalts _
    simp only [Result, Part.get_some]
    have ⟨hsteps, hhalted'⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps hhalted' (Steps.single hstep) hhalted
    simp only [heq, finalState, Config.init, State.output, State.write, Function.update_self]

/-- Decrement block: compute pred(x) = x - 1 (saturating at 0).
Uses registers 0 (input/output), 1, 2 as workspace. -/
def decrement : URMBlock where
  program := decrementProgram 0 1
  arity := 1
  h_sf := decrementProgram.isStandardForm 0 1

theorem decrement_computes :
    decrement.ComputesN 1 (fun inputs => Part.some (inputs 0 - 1)) := by
  intro inputs
  simp only [decrement]
  sorry

/-- Add block: compute x + y where x is in R₀ and y is in R₁.
Uses registers 0 (first input/output), 1 (second input), 2 (workspace). -/
def add : URMBlock where
  program := addToProgram 0 1 2
  arity := 2
  h_sf := addToProgram.isStandardForm 0 1 2

theorem add_computes :
    add.ComputesN 2 (fun inputs => Part.some (inputs 0 + inputs 1)) := by
  intro inputs
  simp only [add]
  sorry

end URMBlock

end Urm
