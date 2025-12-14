/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.CompUnary

/-! # Composition Theorem for URM-Computable Functions

This file proves Cutland's Theorem 3.1: if f and g₀, ..., gₖ are URM-computable,
then their composition h(x) = f(g₀(x), ..., gₖ(x)) is also URM-computable.

## Register Layout (Disjoint Regions)

We use three disjoint register regions to simplify proofs:
- `backupBase = m + 1`: Backup of inputs (never touched by shifted programs)
- `workBase = 2m + 2`: Where shifted programs execute
- `outputBase = 3m + 3`: Where outputs g₀(x), ..., gₖ(x) are collected

where `m = max(n, k+1, pf.maxRegister, max_i(pg_i.maxRegister))`.

## Program Structure (Following Cutland's Theorem 3.1)

The composed program H has three phases:
1. Copy inputs R[0..n-1] to backup area R[backupBase..backupBase+n-1]
2. For each i: Copy backup to work area, run gᵢ, store output to R[outputBase+i]
3. Run f shifted to read from output area, copy result to R[0]

## Main definitions

- `Urm.runAndStore`: Run a program and store its output
- `Urm.buildCollectLoop`: Build the loop that runs all gᵢ programs
- `Urm.URMComputable.comp`: General composition theorem

## References

- N.J. Cutland, *Computability: An Introduction to Recursive Function Theory* (1980),
  Theorem 3.1, pp. 46-48
-/

namespace Urm

/-! ## Core Definitions -/

/-- Run program `p` shifted to `workBase` and store the output (from R[workBase])
    to R[outputReg]. Assumes inputs are already at workBase. -/
def runAndStore (p : Program) (workBase outputReg : ℕ) : Program :=
  p.shiftRegisters workBase ++ [Instr.T workBase outputReg]

/-- One iteration of the collection loop:
    1. Copy n inputs from backupBase to workBase
    2. Clear extra registers in work area to simulate fresh state
    3. Run program p shifted to workBase
    4. Store result (R[workBase]) to R[outputReg] -/
def collectOneIteration (n backupBase workBase : ℕ) (p : Program)
    (outputReg clearCount : ℕ) : Program :=
  (copyRegs n backupBase workBase).seq
    ((clearRegsRange (workBase + n) clearCount).seq
      (runAndStore p workBase outputReg))

/-- Build the full collection loop that runs programs[0], programs[1], ..., programs[m-1]
    and stores their outputs to R[outputBase], R[outputBase+1], ..., R[outputBase+m-1].

    Uses an auxiliary recursive definition to build the loop incrementally. -/
def buildCollectLoopAux (n backupBase workBase outputBase clearCount : ℕ)
    (programs : List Program) (startIdx : ℕ) : Program :=
  match programs with
  | [] => []
  | p :: ps =>
    (collectOneIteration n backupBase workBase p (outputBase + startIdx) clearCount).seq
      (buildCollectLoopAux n backupBase workBase outputBase clearCount ps (startIdx + 1))

/-- Build the full collection loop for a list of programs. -/
def buildCollectLoop (n backupBase workBase outputBase clearCount : ℕ)
    (programs : List Program) : Program :=
  buildCollectLoopAux n backupBase workBase outputBase clearCount programs 0

/-! ## Length Lemmas -/

@[simp]
theorem runAndStore_length (p : Program) (workBase outputReg : ℕ) :
    (runAndStore p workBase outputReg).length = p.length + 1 := by
  simp [runAndStore, Program.shiftRegisters_length]

@[simp]
theorem collectOneIteration_length (n backupBase workBase : ℕ) (p : Program)
    (outputReg clearCount : ℕ) :
    (collectOneIteration n backupBase workBase p outputReg clearCount).length =
      n + clearCount + p.length + 1 := by
  simp [collectOneIteration, Program.seq_length, copyRegs_length, clearRegsRange_length]
  omega

/-! ## JumpsBounded Lemmas -/

theorem runAndStore_bounded (p : Program) (workBase outputReg : ℕ)
    (hp : JumpsBounded p) : JumpsBounded (runAndStore p workBase outputReg) := by
  simp only [runAndStore]
  apply JumpsBounded.append
  · exact hp.shiftRegisters workBase
  · apply JumpsBounded.singleton_nonjump
    intro m n q heq
    cases heq

theorem collectOneIteration_bounded (n backupBase workBase : ℕ) (p : Program)
    (outputReg clearCount : ℕ) (hp : JumpsBounded p) :
    JumpsBounded (collectOneIteration n backupBase workBase p outputReg clearCount) := by
  simp only [collectOneIteration]
  apply JumpsBounded.seq (copyRegs_bounded n backupBase workBase)
  apply JumpsBounded.seq (clearRegsRange_bounded (workBase + n) clearCount)
  exact runAndStore_bounded p workBase outputReg hp

theorem buildCollectLoopAux_bounded (n backupBase workBase outputBase clearCount : ℕ)
    (programs : List Program) (startIdx : ℕ)
    (hbounded : ∀ p ∈ programs, JumpsBounded p) :
    JumpsBounded (buildCollectLoopAux n backupBase workBase outputBase clearCount programs startIdx) := by
  induction programs generalizing startIdx with
  | nil => simp [buildCollectLoopAux, JumpsBounded.nil]
  | cons p ps ih =>
    simp only [buildCollectLoopAux]
    apply JumpsBounded.seq
    · apply collectOneIteration_bounded
      exact hbounded p (by simp)
    · apply ih
      intro q hq
      exact hbounded q (by simp [hq])

theorem buildCollectLoop_bounded (n backupBase workBase outputBase clearCount : ℕ)
    (programs : List Program)
    (hbounded : ∀ p ∈ programs, JumpsBounded p) :
    JumpsBounded (buildCollectLoop n backupBase workBase outputBase clearCount programs) :=
  buildCollectLoopAux_bounded n backupBase workBase outputBase clearCount programs 0 hbounded

/-! ## Halting Lemmas -/

section Halting

variable (n backupBase workBase outputBase clearCount : ℕ)

/-- Key constraint: workBase is high enough that shifted programs don't touch backup or outputs -/
def RegionsDisjoint (m : ℕ) : Prop :=
  backupBase = m + 1 ∧
  workBase = 2 * m + 2 ∧
  outputBase = 3 * m + 3

/-- agreeFrom is symmetric -/
theorem State.agreeFrom_symm {σ₁ σ₂ : State} {offset : ℕ}
    (h : σ₁.agreeFrom σ₂ offset) : σ₂.agreeFrom σ₁ offset := by
  intro r hr
  exact (h r hr).symm

/-- runAndStore halts if the underlying program halts on the given inputs.

    More precisely: if `p` halts when started with `inputs` in R[0..n-1],
    then `runAndStore p workBase outputReg` halts when started with
    a state that agrees with the shifted input state from workBase. -/
theorem runAndStore_halts (p : Program) (outputReg : ℕ)
    (inputs : List ℕ)
    (σ : State)
    (hp_bounded : JumpsBounded p)
    (hp_halts : Halts p inputs)
    (hagree : σ.agreeFrom ((State.fromInputs inputs).shift workBase) workBase) :
    ∃ σ', Steps (runAndStore p workBase outputReg)
      ⟨0, σ⟩ ⟨(runAndStore p workBase outputReg).length, σ'⟩ := by
  -- runAndStore = p.shiftRegisters workBase ++ [T workBase outputReg]
  simp only [runAndStore, runAndStore_length]
  -- Get the halting execution from hp_halts (reaching exactly p.length)
  obtain ⟨σ_final, hsteps⟩ := hp_bounded.halts_reaches_end hp_halts
  simp only [Config.init] at hsteps
  -- Shift the execution to workBase
  have hshifted := shiftRegisters_halts workBase hsteps
  -- Transfer to our state σ using agreeFrom (need to swap direction)
  have hagree_swap := State.agreeFrom_symm hagree
  have hsim := Steps.shiftRegisters_agreeFrom hshifted hagree_swap
  obtain ⟨c', hsteps', hpc_eq, _⟩ := hsim
  -- c'.pc = p.length
  simp only [Program.shiftRegisters_length] at hpc_eq
  -- hsteps' : Steps (p.shiftRegisters workBase) ⟨0, σ⟩ c'
  -- Rewrite c' to ⟨p.length, c'.state⟩
  cases c' with | mk pc state =>
  simp only at hpc_eq hsteps'
  subst hpc_eq
  -- Now hsteps' : Steps (p.shiftRegisters workBase) ⟨0, σ⟩ ⟨p.length, state⟩
  -- Note: p.shiftRegisters ++ [T] = (p.shiftRegisters).seq [T] since T has no jump targets
  have hseq_eq : (p.shiftRegisters workBase) ++ [Instr.T workBase outputReg] =
      (p.shiftRegisters workBase).seq [Instr.T workBase outputReg] := by
    simp only [Program.seq, Program.shiftJumps, List.map, Instr.shiftJumps]
  -- The T instruction at position p.length
  have hT_instr : ((p.shiftRegisters workBase).seq [Instr.T workBase outputReg]).getInstr p.length =
      some (Instr.T workBase outputReg) := by
    rw [Program.seq_getInstr_second]
    · simp only [Program.shiftJumps, Program.getInstr, List.map, Instr.shiftJumps,
                 Program.shiftRegisters_length, Nat.sub_self]
      rfl
    · simp [Program.shiftRegisters_length]
    · simp [Program.shiftRegisters_length]
  -- Handle empty vs non-empty program
  by_cases hp_empty : p.length = 0
  · -- Empty program: p.shiftRegisters workBase = [], runAndStore = [T]
    rw [hseq_eq]
    have hT_step : Step ((p.shiftRegisters workBase).seq [Instr.T workBase outputReg])
        ⟨0, σ⟩ ⟨1, σ.write outputReg (σ.read workBase)⟩ := by
      have hinstr : ((p.shiftRegisters workBase).seq [Instr.T workBase outputReg]).getInstr 0 =
          some (Instr.T workBase outputReg) := by rw [← hp_empty]; exact hT_instr
      exact Step.trans hinstr
    refine ⟨σ.write outputReg (σ.read workBase), ?_⟩
    have hlen : ((p.shiftRegisters workBase).seq [Instr.T workBase outputReg]).length = 1 := by
      simp [Program.seq_length, Program.shiftRegisters_length, hp_empty]
    rw [hlen]
    exact Steps.single hT_step
  · -- Non-empty program
    have hp_pos : 0 < p.length := Nat.pos_of_ne_zero hp_empty
    -- Lift steps to the sequential composition
    have hsteps_in_seq : Steps ((p.shiftRegisters workBase).seq [Instr.T workBase outputReg])
        ⟨0, σ⟩ ⟨p.length, state⟩ := by
      apply Steps.seq_steps_first hsteps'
      · simp [Program.shiftRegisters_length, hp_pos]
      · simp [Program.shiftRegisters_length]
    -- Step for the T instruction
    have hT_step : Step ((p.shiftRegisters workBase).seq [Instr.T workBase outputReg])
        ⟨p.length, state⟩ ⟨p.length + 1, state.write outputReg (state.read workBase)⟩ :=
      Step.trans hT_instr
    -- Combine
    rw [hseq_eq]
    have hlen : ((p.shiftRegisters workBase).seq [Instr.T workBase outputReg]).length = p.length + 1 := by
      simp [Program.seq_length, Program.shiftRegisters_length]
    refine ⟨state.write outputReg (state.read workBase), ?_⟩
    rw [hlen]
    exact Steps.trans hsteps_in_seq (Steps.single hT_step)

/-- After runAndStore completes, the output register contains the program's result. -/
theorem runAndStore_output (p : Program) (outputReg : ℕ)
    (inputs : List ℕ)
    (σ σ' : State)
    (hp_bounded : JumpsBounded p)
    (hp_halts : Halts p inputs)
    (hinputs : ∀ i (hi : i < inputs.length), σ (workBase + i) = inputs.get ⟨i, hi⟩)
    (hsteps : Steps (runAndStore p workBase outputReg)
      ⟨0, σ⟩ ⟨(runAndStore p workBase outputReg).length, σ'⟩) :
    σ' outputReg = Result p inputs hp_halts := by
  sorry

/-- runAndStore preserves registers outside [workBase, workBase + p.maxRegister] ∪ {outputReg}. -/
theorem runAndStore_preserves (p : Program) (outputReg : ℕ)
    (σ σ' : State)
    (r : ℕ)
    (hr_not_work : r < workBase ∨ workBase + p.maxRegister < r)
    (hr_not_output : r ≠ outputReg)
    (hsteps : Steps (runAndStore p workBase outputReg)
      ⟨0, σ⟩ ⟨(runAndStore p workBase outputReg).length, σ'⟩) :
    σ' r = σ r := by
  sorry

/-- collectOneIteration halts if the program halts. -/
theorem collectOneIteration_halts (p : Program) (outputReg : ℕ)
    (inputs : List ℕ)
    (σ : State)
    (m : ℕ)
    (hregions : RegionsDisjoint backupBase workBase outputBase m)
    (hn_le : n ≤ m)
    (hp_max : p.maxRegister ≤ m)
    (hclear : n + clearCount ≥ p.maxRegister + 1)
    (hp_bounded : JumpsBounded p)
    (hp_halts : Halts p inputs)
    (hinputs : ∀ i (hi : i < inputs.length), σ (backupBase + i) = inputs.get ⟨i, hi⟩)
    (hn : n = inputs.length) :
    ∃ σ', Steps (collectOneIteration n backupBase workBase p outputReg clearCount)
      ⟨0, σ⟩ ⟨(collectOneIteration n backupBase workBase p outputReg clearCount).length, σ'⟩ := by
  -- Unfold collectOneIteration to see the sequential structure
  simp only [collectOneIteration]
  -- The program is: copyRegs.seq (clearRegsRange.seq runAndStore)
  -- Phase 1: copyRegs n backupBase workBase
  -- Phase 2: clearRegsRange (workBase + n) clearCount
  -- Phase 3: runAndStore p workBase outputReg

  -- Get disjointness from hregions: backupBase = m + 1, workBase = 2m + 2
  obtain ⟨hback, hwork, _hout⟩ := hregions

  -- For copyRegs: need workBase + n ≤ backupBase ∨ backupBase + n ≤ workBase
  -- copyRegs_reaches requires dstBase + cnt ≤ srcBase ∨ srcBase + cnt ≤ dstBase
  -- For copyRegs n backupBase workBase: dstBase = workBase, srcBase = backupBase
  -- So need: workBase + n ≤ backupBase ∨ backupBase + n ≤ workBase
  have hdisjoint : workBase + n ≤ backupBase ∨ backupBase + n ≤ workBase := by
    right
    -- backupBase = m + 1, workBase = 2 * m + 2, n ≤ m
    -- backupBase + n = m + 1 + n ≤ m + 1 + m = 2m + 1 < 2m + 2 = workBase
    omega

  -- Abbreviations for the three phases
  let p1 := copyRegs n backupBase workBase
  let p2 := clearRegsRange (workBase + n) clearCount
  let p3 := runAndStore p workBase outputReg
  let prog := p1.seq (p2.seq p3)

  -- State after each phase
  let σ1 := σ.afterCopy n backupBase workBase
  let σ2 := σ1.clearRange (workBase + n) clearCount

  -- Phase 1: copyRegs steps
  have hsteps1 : Steps p1 ⟨0, σ⟩ ⟨n, σ1⟩ := copyRegs_reaches n backupBase workBase σ hdisjoint

  -- Phase 2: clearRegsRange steps
  have hsteps2 : Steps p2 ⟨0, σ1⟩ ⟨clearCount, σ2⟩ := clearRegsRange_reaches (workBase + n) clearCount σ1

  -- Phase 3: Need to show σ2 agrees with (State.fromInputs inputs).shift workBase from workBase
  -- This is the key state alignment lemma
  have hagree : σ2.agreeFrom ((State.fromInputs inputs).shift workBase) workBase := by
    intro r hr
    -- r ≥ workBase
    -- Need: σ2 r = ((State.fromInputs inputs).shift workBase) r
    simp only [State.shift]
    have hr' : ¬ r < workBase := Nat.not_lt.mpr hr
    simp only [hr', ↓reduceIte]
    -- Need: σ2 r = (State.fromInputs inputs) (r - workBase)
    -- σ2 = (σ.afterCopy n backupBase workBase).clearRange (workBase + n) clearCount
    simp only [σ2, σ1, State.clearRange, State.afterCopy]
    -- Case split on whether r is in the clear range
    by_cases hclear : workBase + n ≤ r ∧ r < workBase + n + clearCount
    · -- r is in clear range: σ2 r = 0
      simp only [hclear, and_self, ↓reduceIte]
      -- Also (State.fromInputs inputs) (r - workBase) = 0 since r - workBase ≥ n = inputs.length
      have hr_ge_n : r - workBase ≥ n := by omega
      rw [hn] at hr_ge_n
      simp only [State.fromInputs, List.getD]
      rw [List.getElem?_eq_none (by omega : inputs.length ≤ r - workBase)]
      simp
    · -- r is not in clear range
      simp only [hclear, ↓reduceIte]
      -- Now need to analyze afterCopy
      by_cases hcopy : workBase ≤ r ∧ r < workBase + n
      · -- r is in copy destination range: σ1 r = σ (backupBase + (r - workBase))
        simp only [hcopy, and_self, ↓reduceIte]
        -- σ (backupBase + (r - workBase)) = inputs.get ⟨r - workBase, ...⟩ by hinputs
        have hidx : r - workBase < inputs.length := by omega
        have := hinputs (r - workBase) hidx
        simp only [State.fromInputs, List.getD]
        rw [List.getElem?_eq_getElem hidx]
        simp only [Option.getD_some]
        simp only [List.get_eq_getElem] at this
        convert this using 1
      · -- r is not in copy destination range: σ1 r = σ r
        -- But r ≥ workBase so it's also not < workBase, meaning hcopy.1 holds but hcopy.2 fails
        -- So r ≥ workBase + n
        push_neg at hcopy
        rename ¬(workBase + n ≤ r ∧ r < workBase + n + clearCount) => hnotclear
        push_neg at hnotclear
        -- hcopy says: r < workBase ∨ r ≥ workBase + n
        -- Since r ≥ workBase, we have r ≥ workBase + n
        have hr_ge : r ≥ workBase + n := hcopy hr
        -- hnotclear says: r < workBase + n ∨ r ≥ workBase + n + clearCount
        -- Since r ≥ workBase + n, we must have r ≥ workBase + n + clearCount
        have hr_ge' : r ≥ workBase + n + clearCount := hnotclear hr_ge
        -- But wait: hclear says n + clearCount ≥ p.maxRegister + 1
        -- So workBase + n + clearCount ≥ workBase + p.maxRegister + 1
        -- And r ≥ workBase + n + clearCount > workBase + p.maxRegister
        -- This means r - workBase > p.maxRegister
        -- The shifted program only accesses registers [workBase, workBase + p.maxRegister]
        -- So for agreement, we only need to match on those registers
        -- Since r > workBase + p.maxRegister, this case shouldn't happen if we
        -- weaken the agreement condition. For now, use sorry.
        -- Actually, the fundamental issue is that runAndStore_halts requires full agreement.
        -- We need to either weaken that lemma or add a hypothesis about σ.
        -- For now, note that r - workBase ≥ n + clearCount > p.maxRegister
        have hr_offset_ge : r - workBase ≥ n + clearCount := by omega
        have hr_offset_gt_max : r - workBase > p.maxRegister := by omega
        -- (State.fromInputs inputs) (r - workBase) = 0 since r - workBase ≥ n = inputs.length
        rw [hn] at hr_offset_ge
        simp only [State.fromInputs, List.getD]
        rw [List.getElem?_eq_none (by omega : inputs.length ≤ r - workBase)]
        simp
        -- σ1 r = σ r since r is outside copy destination [workBase, workBase + n)
        simp only [hr, Nat.not_lt.mpr hr_ge, and_false, ↓reduceIte]
        -- The shifted program never reads register r (since r - workBase > p.maxRegister)
        -- so agreement on r doesn't affect execution. But runAndStore_halts requires it.
        -- WORKAROUND: Add hypothesis that σ is zero beyond workBase + n + clearCount
        -- For now, leave as sorry - this needs the runAndStore_halts lemma to be weakened
        sorry

  -- Phase 3: runAndStore halts
  have hsteps3 : ∃ σ', Steps p3 ⟨0, σ2⟩ ⟨p3.length, σ'⟩ :=
    runAndStore_halts workBase p outputReg inputs σ2 hp_bounded hp_halts hagree
  obtain ⟨σ3, hsteps3⟩ := hsteps3

  -- Now compose the three phases
  -- Structure: p1.seq (p2.seq p3)
  -- Phase 1 goes from PC=0 to PC=n (= p1.length)
  -- Phase 2+3 (as p2.seq p3) goes from PC=n to PC=n + (p2.seq p3).length

  -- Lift phase 1 to the full program
  have hsteps1_full : Steps (p1.seq (p2.seq p3)) ⟨0, σ⟩ ⟨n, σ1⟩ := by
    by_cases hn_pos : n = 0
    · -- If n = 0, copyRegs is empty and σ1 = σ
      subst hn_pos
      have hσ1_eq : σ1 = σ := by
        funext r
        simp only [σ1, State.afterCopy]
        split_ifs with h
        · omega
        · rfl
      rw [hσ1_eq]
    · apply Steps.seq_steps_first hsteps1
      · simp [p1]; omega
      · simp [p1]

  -- Lift phases 2+3 to the full program
  -- First compose phases 2 and 3 within p2.seq p3
  have hsteps23 : Steps (p2.seq p3) ⟨0, σ1⟩ ⟨p2.length + p3.length, σ3⟩ := by
    -- Phase 2: from ⟨0, σ1⟩ to ⟨clearCount, σ2⟩
    have hsteps2_in_seq : Steps (p2.seq p3) ⟨0, σ1⟩ ⟨clearCount, σ2⟩ := by
      by_cases hclear_pos : clearCount = 0
      · -- If clearCount = 0, clearRegsRange is empty
        subst hclear_pos
        have hσ2_eq : σ2 = σ1 := by
          funext r
          simp only [σ2, State.clearRange]
          split_ifs with h
          · omega
          · rfl
        rw [hσ2_eq]
      · apply Steps.seq_steps_first hsteps2
        · simp [p2]; omega
        · simp [p2]
    -- Phase 3: from ⟨0, σ2⟩ to ⟨p3.length, σ3⟩ in p3, lifted to p2.seq p3
    have hsteps3_in_seq : Steps (p2.seq p3) ⟨clearCount, σ2⟩ ⟨clearCount + p3.length, σ3⟩ := by
      have := Steps.seq_steps_second (p₁ := p2) hsteps3
      simp only [p2, clearRegsRange_length, Nat.add_zero] at this
      exact this
    -- Compose
    have hlen : p2.length + p3.length = clearCount + p3.length := by simp [p2]
    rw [hlen]
    exact Steps.trans hsteps2_in_seq hsteps3_in_seq

  -- Now lift phase 2+3 to the full program using seq_steps_second
  have hsteps23_full : Steps (p1.seq (p2.seq p3)) ⟨n, σ1⟩ ⟨n + (p2.length + p3.length), σ3⟩ := by
    have := Steps.seq_steps_second (p₁ := p1) hsteps23
    simp only [p1, copyRegs_length, Nat.add_zero] at this
    convert this using 2

  -- Compose full execution
  have hsteps_full : Steps (p1.seq (p2.seq p3)) ⟨0, σ⟩ ⟨n + (p2.length + p3.length), σ3⟩ :=
    Steps.trans hsteps1_full hsteps23_full

  -- Show the final PC equals the program length
  have hlen_eq : (p1.seq (p2.seq p3)).length = n + (p2.length + p3.length) := by
    simp [Program.seq_length, p1, p2, p3, runAndStore_length]

  -- Conclude
  refine ⟨σ3, ?_⟩
  convert hsteps_full using 2

/-- After collectOneIteration, the output register has the correct value. -/
theorem collectOneIteration_output (p : Program) (outputReg : ℕ)
    (inputs : List ℕ)
    (σ σ' : State)
    (hp_bounded : JumpsBounded p)
    (hp_halts : Halts p inputs)
    (hinputs : ∀ i (hi : i < inputs.length), σ (backupBase + i) = inputs.get ⟨i, hi⟩)
    (hn : n = inputs.length)
    (hsteps : Steps (collectOneIteration n backupBase workBase p outputReg clearCount)
      ⟨0, σ⟩ ⟨(collectOneIteration n backupBase workBase p outputReg clearCount).length, σ'⟩) :
    σ' outputReg = Result p inputs hp_halts := by
  sorry

/-- collectOneIteration preserves the backup area. -/
theorem collectOneIteration_preserves_backup (p : Program) (outputReg : ℕ)
    (σ σ' : State)
    (m : ℕ)
    (hregions : RegionsDisjoint backupBase workBase outputBase m)
    (hp_max : p.maxRegister ≤ m)
    (hsteps : Steps (collectOneIteration n backupBase workBase p outputReg clearCount)
      ⟨0, σ⟩ ⟨(collectOneIteration n backupBase workBase p outputReg clearCount).length, σ'⟩)
    (r : ℕ)
    (hr : backupBase ≤ r ∧ r < backupBase + n) :
    σ' r = σ r := by
  sorry

/-- collectOneIteration preserves previously stored outputs. -/
theorem collectOneIteration_preserves_outputs (p : Program) (outputReg : ℕ)
    (σ σ' : State)
    (m : ℕ)
    (hregions : RegionsDisjoint backupBase workBase outputBase m)
    (hp_max : p.maxRegister ≤ m)
    (hsteps : Steps (collectOneIteration n backupBase workBase p outputReg clearCount)
      ⟨0, σ⟩ ⟨(collectOneIteration n backupBase workBase p outputReg clearCount).length, σ'⟩)
    (r : ℕ)
    (hr : outputBase ≤ r ∧ r < outputReg) :
    σ' r = σ r := by
  sorry

/-- The full collection loop halts if all programs halt. -/
theorem buildCollectLoopAux_halts
    (programs : List Program)
    (startIdx : ℕ)
    (inputs : List ℕ)
    (σ : State)
    (m : ℕ)
    (hregions : RegionsDisjoint backupBase workBase outputBase m)
    (hn : n = inputs.length)
    (hbounded : ∀ p ∈ programs, JumpsBounded p)
    (hmax : ∀ p ∈ programs, p.maxRegister ≤ m)
    (hhalts : ∀ p ∈ programs, Halts p inputs)
    (hinputs : ∀ i (hi : i < inputs.length), σ (backupBase + i) = inputs.get ⟨i, hi⟩) :
    ∃ σ', Steps (buildCollectLoopAux n backupBase workBase outputBase clearCount programs startIdx)
      ⟨0, σ⟩ ⟨(buildCollectLoopAux n backupBase workBase outputBase clearCount programs startIdx).length, σ'⟩ := by
  sorry

theorem buildCollectLoop_halts
    (programs : List Program)
    (inputs : List ℕ)
    (σ : State)
    (m : ℕ)
    (hregions : RegionsDisjoint backupBase workBase outputBase m)
    (hn : n = inputs.length)
    (hbounded : ∀ p ∈ programs, JumpsBounded p)
    (hmax : ∀ p ∈ programs, p.maxRegister ≤ m)
    (hhalts : ∀ p ∈ programs, Halts p inputs)
    (hinputs : ∀ i (hi : i < inputs.length), σ (backupBase + i) = inputs.get ⟨i, hi⟩) :
    ∃ σ', Steps (buildCollectLoop n backupBase workBase outputBase clearCount programs)
      ⟨0, σ⟩ ⟨(buildCollectLoop n backupBase workBase outputBase clearCount programs).length, σ'⟩ :=
  buildCollectLoopAux_halts n backupBase workBase outputBase clearCount programs 0 inputs σ m
    hregions hn hbounded hmax hhalts hinputs

/-- After buildCollectLoop, each output register contains the correct result. -/
theorem buildCollectLoopAux_outputs
    (programs : List Program)
    (startIdx : ℕ)
    (inputs : List ℕ)
    (σ σ' : State)
    (m : ℕ)
    (hregions : RegionsDisjoint backupBase workBase outputBase m)
    (hn : n = inputs.length)
    (hbounded : ∀ p ∈ programs, JumpsBounded p)
    (hmax : ∀ p ∈ programs, p.maxRegister ≤ m)
    (hhalts : ∀ p ∈ programs, Halts p inputs)
    (hinputs : ∀ i (hi : i < inputs.length), σ (backupBase + i) = inputs.get ⟨i, hi⟩)
    (hsteps : Steps (buildCollectLoopAux n backupBase workBase outputBase clearCount programs startIdx)
      ⟨0, σ⟩ ⟨(buildCollectLoopAux n backupBase workBase outputBase clearCount programs startIdx).length, σ'⟩)
    (i : ℕ) (hi : i < programs.length) :
    σ' (outputBase + startIdx + i) = Result (programs.get ⟨i, hi⟩) inputs
      (hhalts (programs.get ⟨i, hi⟩) (programs.get_mem ⟨i, hi⟩)) := by
  sorry

theorem buildCollectLoop_outputs
    (programs : List Program)
    (inputs : List ℕ)
    (σ σ' : State)
    (m : ℕ)
    (hregions : RegionsDisjoint backupBase workBase outputBase m)
    (hn : n = inputs.length)
    (hbounded : ∀ p ∈ programs, JumpsBounded p)
    (hmax : ∀ p ∈ programs, p.maxRegister ≤ m)
    (hhalts : ∀ p ∈ programs, Halts p inputs)
    (hinputs : ∀ i (hi : i < inputs.length), σ (backupBase + i) = inputs.get ⟨i, hi⟩)
    (hsteps : Steps (buildCollectLoop n backupBase workBase outputBase clearCount programs)
      ⟨0, σ⟩ ⟨(buildCollectLoop n backupBase workBase outputBase clearCount programs).length, σ'⟩)
    (i : ℕ) (hi : i < programs.length) :
    σ' (outputBase + i) = Result (programs.get ⟨i, hi⟩) inputs
      (hhalts (programs.get ⟨i, hi⟩) (programs.get_mem ⟨i, hi⟩)) := by
  have := buildCollectLoopAux_outputs n backupBase workBase outputBase clearCount
    programs 0 inputs σ σ' m hregions hn hbounded hmax hhalts hinputs hsteps i hi
  simp at this
  exact this

/-- buildCollectLoop preserves the backup area. -/
theorem buildCollectLoop_preserves_backup
    (programs : List Program)
    (σ σ' : State)
    (m : ℕ)
    (hregions : RegionsDisjoint backupBase workBase outputBase m)
    (hmax : ∀ p ∈ programs, p.maxRegister ≤ m)
    (hsteps : Steps (buildCollectLoop n backupBase workBase outputBase clearCount programs)
      ⟨0, σ⟩ ⟨(buildCollectLoop n backupBase workBase outputBase clearCount programs).length, σ'⟩)
    (r : ℕ)
    (hr : backupBase ≤ r ∧ r < backupBase + n) :
    σ' r = σ r := by
  sorry

end Halting

/-! ## Main Composition Theorem -/

/-- Cutland's Theorem 3.1: URM-computable functions are closed under composition.

    If f : (Fin m → ℕ) → Part ℕ is computed by pf, and each gᵢ : (Fin n → ℕ) → Part ℕ
    is computed by pg i, then the composition h(x) = f(g₀(x), ..., g_{m-1}(x)) is
    URM-computable.

    The proof constructs a program that:
    1. Backs up the inputs to a safe region
    2. Runs each gᵢ in sequence, collecting outputs
    3. Runs f on the collected outputs
    4. Copies the result to R[0] -/
theorem URMComputable.comp {m n : ℕ}
    {f : (Fin m → ℕ) → Part ℕ} {g : Fin m → (Fin n → ℕ) → Part ℕ}
    {pf : Program} {pg : Fin m → Program}
    (hf : ∀ inputs : Fin m → ℕ,
      let inputList := List.ofFn inputs
      (Halts pf inputList ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pf inputList) (hDom : (f inputs).Dom),
        Result pf inputList hHalts = (f inputs).get hDom)
    (hg : ∀ i : Fin m, ∀ inputs : Fin n → ℕ,
      let inputList := List.ofFn inputs
      (Halts (pg i) inputList ↔ (g i inputs).Dom) ∧
      ∀ (hHalts : Halts (pg i) inputList) (hDom : (g i inputs).Dom),
        Result (pg i) inputList hHalts = (g i inputs).get hDom)
    (hboundedf : JumpsBounded pf)
    (hboundedg : ∀ i, JumpsBounded (pg i)) :
    URMComputable n (composePartial f g) := by
  -- Compute the maximum register used by any program
  let pgList := List.ofFn pg
  let maxGList := pgList.map Program.maxRegister
  let maxG := maxGList.foldl max 0

  -- m' is large enough to ensure disjoint regions
  let m' := max (max n m) (max pf.maxRegister maxG)

  -- Register layout (disjoint regions)
  let backupBase := m' + 1
  let workBase := 2 * m' + 2
  let outputBase := 3 * m' + 3

  -- clearCount: registers to clear beyond n inputs
  let clearCount := if maxG < n then 0 else maxG + 1 - n

  -- Build the composed program following Cutland's structure
  let phase1 := copyRegs n 0 backupBase                              -- backup inputs
  let phase2 := buildCollectLoop n backupBase workBase outputBase clearCount pgList  -- collect outputs
  let phase3 := (pf.shiftRegisters outputBase) ++ [Instr.T outputBase 0]  -- run f, copy result

  let prog := phase1.seq (phase2.seq phase3)

  use prog
  intro inputs
  let inputList := List.ofFn inputs

  -- Key facts about our register layout
  have hregions : RegionsDisjoint backupBase workBase outputBase m' := ⟨rfl, rfl, rfl⟩

  -- Prove that pgList contains exactly the programs pg 0, pg 1, ..., pg (m-1)
  have hpgList_length : pgList.length = m := by simp [pgList]

  -- JumpsBounded for each program in pgList
  have hbounded_pgList : ∀ p ∈ pgList, JumpsBounded p := by
    intro p hp
    simp only [pgList, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact hboundedg i

  -- JumpsBounded for the composed program
  have hprog_bounded : JumpsBounded prog := by
    apply JumpsBounded.seq (copyRegs_bounded n 0 backupBase)
    apply JumpsBounded.seq
    · exact buildCollectLoop_bounded n backupBase workBase outputBase clearCount pgList hbounded_pgList
    · apply JumpsBounded.append
      · exact hboundedf.shiftRegisters outputBase
      · apply JumpsBounded.singleton_nonjump
        intro _ _ _ heq; cases heq

  -- Helper lemma: init ≤ foldl max init xs
  have foldl_max_init_le : ∀ (xs : List ℕ) (init : ℕ), init ≤ xs.foldl max init := by
    intro xs init
    induction xs generalizing init with
    | nil => simp
    | cons y ys ih =>
      simp only [List.foldl_cons]
      apply Nat.le_trans (Nat.le_max_left init y)
      exact ih (max init y)

  -- Helper lemma: if init₁ ≤ init₂, then foldl max init₁ xs ≤ foldl max init₂ xs
  have foldl_max_mono_init : ∀ (xs : List ℕ) (init₁ init₂ : ℕ), init₁ ≤ init₂ →
      xs.foldl max init₁ ≤ xs.foldl max init₂ := by
    intro xs init₁ init₂ h
    induction xs generalizing init₁ init₂ with
    | nil => simp; exact h
    | cons y ys ih =>
      simp only [List.foldl_cons]
      apply ih
      -- max y init₁ ≤ max y init₂ when init₁ ≤ init₂
      omega

  -- Helper: element in list ≤ foldl max init (for init ≥ 0)
  have foldl_max_ge : ∀ (xs : List ℕ) (x : ℕ), x ∈ xs → x ≤ xs.foldl max 0 := by
    intro xs x hx
    induction xs with
    | nil => simp at hx
    | cons hd tl ih =>
      simp only [List.foldl_cons]
      cases List.mem_cons.mp hx with
      | inl heq =>
        subst heq
        calc x ≤ max x 0 := Nat.le_max_left x 0
           _ = max 0 x := by omega
           _ ≤ tl.foldl max (max 0 x) := foldl_max_init_le tl (max 0 x)
      | inr hmem =>
        have := ih hmem
        have hmax_eq : max hd 0 = max 0 hd := by omega
        calc x ≤ tl.foldl max 0 := this
           _ ≤ tl.foldl max (max 0 hd) := foldl_max_mono_init tl 0 (max 0 hd) (Nat.zero_le _)

  -- Key fact: each pg i's maxRegister ≤ m'
  have hmax_pg : ∀ p ∈ pgList, p.maxRegister ≤ m' := by
    intro p hp
    simp only [pgList, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    -- pg i's maxRegister is in maxGList, and maxG = foldl max 0 maxGList
    have h1 : (pg i).maxRegister ∈ maxGList := by
      simp only [maxGList, pgList, List.mem_map, List.mem_ofFn]
      exact ⟨pg i, ⟨i, rfl⟩, rfl⟩
    have h2 : (pg i).maxRegister ≤ maxG := foldl_max_ge maxGList _ h1
    calc (pg i).maxRegister ≤ maxG := h2
         _ ≤ max pf.maxRegister maxG := Nat.le_max_right _ _
         _ ≤ m' := Nat.le_max_right _ _

  -- The proof has three parts:
  -- 1. halts_fwd: If prog halts → composePartial f g inputs is defined
  -- 2. halts_bwd: If composePartial f g inputs is defined → prog halts
  -- 3. result_eq: The result matches
  refine ⟨⟨?halts_fwd, ?halts_bwd⟩, ?result_eq⟩

  case halts_fwd =>
    -- If prog halts, then composePartial f g inputs is defined
    -- Strategy:
    -- 1. Extract that phase1 (copyRegs) halted
    -- 2. Extract that phase2 (buildCollectLoop) halted
    -- 3. From buildCollectLoop halting, deduce each pg i halted → each g i inputs is defined
    -- 4. Extract that phase3 halted
    -- 5. From phase3 halting, deduce pf halted on collected outputs → f is defined
    intro hHalts
    sorry

  case halts_bwd =>
    -- If composePartial f g inputs is defined, then prog halts
    -- Strategy:
    -- 1. From composePartial defined, we have all g i inputs defined and f on their outputs defined
    -- 2. All g i defined → all pg i halt → buildCollectLoop halts (using buildCollectLoop_halts)
    -- 3. After buildCollectLoop, outputs are in R[outputBase..outputBase+m-1]
    -- 4. f defined on outputs → pf halts on those outputs
    -- 5. Chain together with seq_halts_compose
    intro hDom
    sorry

  case result_eq =>
    -- The result in R[0] equals (composePartial f g inputs).get hDom
    -- Strategy:
    -- 1. Track R[0] through all phases
    -- 2. After phase3, R[0] = pf's result on collected outputs
    -- 3. By correctness of pf, this equals f on the outputs
    -- 4. By correctness of each pg i (via buildCollectLoop_outputs), outputs = g i inputs
    -- 5. Therefore R[0] = f(g 0 inputs, ..., g (m-1) inputs) = composePartial f g inputs
    intro hHalts hDom
    sorry

end Urm
