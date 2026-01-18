/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Block.Basic
import Urm.Block.Compile
import Urm.Concat

/-! # Block Sequencing (Glue)

Lemmas for sequencing compiled blocks. When two blocks are compiled at
disjoint register offsets and concatenated, their executions compose properly.

## Main results

- `URMBlock.disjoint_registers`: Two blocks at different offsets use disjoint registers
- `URMBlock.seq`: Concatenate two compiled blocks
- `URMBlock.seq_first_halts`: First block's execution lifts to the sequence
- `URMBlock.seq_second_start`: Second block's execution in the sequence

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

namespace Urm

namespace URMBlock

/-- Two blocks compiled at disjoint offsets don't interfere.
Block A at offset 0 uses registers 0..maxRegA.
Block B at offset (maxRegA + 1 + gap) uses registers beyond A's range. -/
theorem disjoint_registers (bA bB : URMBlock) (gap : ℕ) :
    let offsetB := bA.maxReg + 1 + gap
    ∀ r, r ≤ bA.maxReg → ∀ s, s ≤ bB.maxReg → r + 0 ≠ s + offsetB := by
  intro offsetB r hr s hs
  omega

/-- Concatenate two compiled blocks at given offsets. -/
def seq (bA bB : URMBlock) (offsetA offsetB : ℕ) : Program :=
  (bA.compile offsetA).concat (bB.compile offsetB)

/-- Length of sequenced blocks. -/
@[simp]
theorem seq_length (bA bB : URMBlock) (offsetA offsetB : ℕ) :
    (seq bA bB offsetA offsetB).length = bA.program.length + bB.program.length := by
  simp only [seq, Program.concat_length, compile_length]

/-- If block A halts, we can lift its steps to the concatenated program. -/
theorem seq_first_halts (bA bB : URMBlock) (offsetA offsetB : ℕ) (σ : State)
    (c : Config) (hsteps : Steps (bA.compile offsetA) ⟨0, σ⟩ c)
    (_hhalted : c.isHalted (bA.compile offsetA)) :
    Steps (seq bA bB offsetA offsetB) ⟨0, σ⟩ c := by
  exact Steps.concat_left_prefix_interior hsteps

/-- After block A halts at exactly pc = length, block B can start. -/
theorem seq_second_start (bA bB : URMBlock) (offsetA offsetB : ℕ)
    (σA : State) (cB : Config)
    (hstepsB : Steps (bB.compile offsetB) ⟨0, σA⟩ cB)
    (hhaltedB : cB.isHalted (bB.compile offsetB)) :
    let startB : Config := ⟨bA.program.length, σA⟩
    let finalB : Config := ⟨cB.pc + bA.program.length, cB.state⟩
    Steps (seq bA bB offsetA offsetB) startB finalB := by
  simp only [seq]
  cases hbB : bB.program with
  | nil =>
    -- Empty program: cB = ⟨0, σA⟩ and startB = finalB (up to pc offset)
    simp only [compile, hbB, Program.shiftRegisters, List.map_nil] at hstepsB hhaltedB
    have hcB_pc : cB.pc = 0 := by
      cases hstepsB using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hstep => exact absurd hstep (Step.halted_no_step (by simp [Config.isHalted]))
    have hcB_state : cB.state = σA := by
      cases hstepsB using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hstep => exact absurd hstep (Step.halted_no_step (by simp [Config.isHalted]))
    simp only [hcB_pc, hcB_state, Nat.zero_add]
    exact Relation.ReflTransGen.refl
  | cons hd tl =>
    have hpc_start : (⟨0, σA⟩ : Config).pc < (bB.compile offsetB).length := by
      simp only [compile_length, hbB, List.length_cons]
      omega
    convert Steps.concat_right (p1 := bA.compile offsetA) hstepsB hhaltedB using 2 <;> simp

/-- If block A halts with pc exactly at length, block B can follow. -/
theorem seq_halts_from_exact_pc (bA bB : URMBlock) (offsetA offsetB : ℕ) (σ : State)
    (cA cB : Config)
    (hstepsA : Steps (bA.compile offsetA) ⟨0, σ⟩ cA)
    (hpcA : cA.pc = bA.program.length)
    (hstepsB : Steps (bB.compile offsetB) ⟨0, cA.state⟩ cB)
    (hhaltedB : cB.isHalted (bB.compile offsetB)) :
    let finalConfig : Config := ⟨cB.pc + bA.program.length, cB.state⟩
    ∃ c, Steps (seq bA bB offsetA offsetB) ⟨0, σ⟩ c ∧
         c.isHalted (seq bA bB offsetA offsetB) ∧
         c.state = cB.state := by
  let startB : Config := ⟨bA.program.length, cA.state⟩
  let finalConfig : Config := ⟨cB.pc + bA.program.length, cB.state⟩
  have hhaltedA : cA.isHalted (bA.compile offsetA) := by
    simp only [Config.isHalted, compile_length, hpcA, le_refl]
  have hstepsA' := seq_first_halts bA bB offsetA offsetB σ cA hstepsA hhaltedA
  have hcA_eq_startB : cA = startB := by
    ext
    · exact hpcA
    · rfl
  rw [hcA_eq_startB] at hstepsA'
  have hstepsB' := seq_second_start bA bB offsetA offsetB cA.state cB hstepsB hhaltedB
  refine ⟨finalConfig, ?_, ?_, rfl⟩
  · exact Relation.ReflTransGen.trans hstepsA' hstepsB'
  · simp only [Config.isHalted, seq_length, finalConfig]
    simp only [Config.isHalted, compile_length] at hhaltedB
    omega

/-- Halted configuration at pc ≥ total length is halted in concatenation. -/
theorem concat_isHalted {p1 p2 : Program} {c : Config}
    (hpc : c.pc ≥ p1.length + p2.length) :
    c.isHalted (p1.concat p2) := by
  simp only [Config.isHalted, Program.concat_length]
  exact hpc

end URMBlock

end Urm
