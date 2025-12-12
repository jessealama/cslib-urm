/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.CompUnary

/-! # Collection Loop Construction

For multi-ary composition, we need to run each gᵢ and collect outputs.
The collection loop iterates through the programs, restoring inputs from backup
before each execution and saving results to the output collection area.

## Main definitions

- `Urm.runAndStore`: Run a program and store its output
- `Urm.collectOneIteration`: One iteration of the collection loop
- `Urm.buildCollectLoop`: Build the full collection loop
- `Urm.URMComputable.comp`: General composition theorem

## Main statements

- `Urm.collectOneIteration_halts`: One iteration halts if the program halts
- `Urm.buildCollectLoop_halts`: The full loop halts if all programs halt
- `Urm.URMComputable.comp`: URM-computable functions are closed under composition
-/

namespace Urm

/-- Build a program segment that runs `p` with inputs at `workBase` and stores
    the result (from R[workBase]) to R[outputReg]. Requires inputs already at workBase. -/
def runAndStore (p : Program) (workBase outputReg : ℕ) : Program :=
  (p.shiftRegisters workBase) ++ [Instr.T workBase outputReg]

/-- Build a program segment for one iteration of the collection loop:
    1. Copy n inputs from backupBase to workBase
    2. Clear working registers (workBase+n to workBase+n+clearCount-1) to match fromInputs
    3. Run program p shifted to workBase
    4. Store result (R[workBase]) to R[outputReg]

    The clearCount parameter specifies how many registers beyond the n inputs to zero out.
    This ensures the execution state matches State.fromInputs when unshifted. -/
def collectOneIteration (n backupBase workBase : ℕ) (p : Program) (outputReg clearCount : ℕ) : Program :=
  (copyRegs n backupBase workBase).seq
  ((clearRegsRange (workBase + n) clearCount).seq
   (runAndStore p workBase outputReg))

/-- Build the full collection loop that runs programs pg[0], pg[1], ..., pg[m-1]
    and stores their outputs to R[outputBase], R[outputBase+1], ..., R[outputBase+m-1].

    Parameters:
    - n: number of input registers (inputs are backed up at backupBase)
    - backupBase: where inputs are backed up (R[backupBase..backupBase+n-1])
    - workBase: where shifted programs execute
    - outputBase: where to store collected outputs
    - clearCount: number of working registers to clear before each program run
    - pg: list of programs to run
    - startIdx: current index (for recursive definition) -/
def buildCollectLoopAux (n backupBase workBase outputBase clearCount : ℕ) (pg : List Program) (startIdx : ℕ) : Program :=
  match pg with
  | [] => []
  | p :: ps =>
    collectOneIteration n backupBase workBase p (outputBase + startIdx) clearCount ++
    buildCollectLoopAux n backupBase workBase outputBase clearCount ps (startIdx + 1)

/-- Build the full collection loop starting at index 0. -/
def buildCollectLoop (n backupBase workBase outputBase clearCount : ℕ) (pg : List Program) : Program :=
  buildCollectLoopAux n backupBase workBase outputBase clearCount pg 0

/-- Length of runAndStore. -/
theorem runAndStore_length (p : Program) (workBase outputReg : ℕ) :
    (runAndStore p workBase outputReg).length = p.length + 1 := by
  simp [runAndStore, Program.shiftRegisters]

/-- Length of one collection iteration. -/
theorem collectOneIteration_length (n backupBase workBase : ℕ) (p : Program) (outputReg clearCount : ℕ) :
    (collectOneIteration n backupBase workBase p outputReg clearCount).length = n + clearCount + p.length + 1 := by
  simp [collectOneIteration, Program.seq_length, copyRegs_length, clearRegsRange_length, runAndStore_length]
  omega

/-- JumpsBounded for runAndStore. -/
theorem runAndStore_bounded (p : Program) (workBase outputReg : ℕ) (hp : JumpsBounded p) :
    JumpsBounded (runAndStore p workBase outputReg) := by
  apply JumpsBounded.append
  · exact hp.shiftRegisters workBase
  · -- The second part is a single T instruction, which has no jumps
    intro i hi m' n' q hinstr
    simp only [List.length_singleton] at hi
    have hi' : i = 0 := Nat.lt_one_iff.mp hi
    subst hi'
    simp only [Program.getInstr, List.getElem?_cons_zero] at hinstr
    cases hinstr

/-- JumpsBounded for one collection iteration. -/
theorem collectOneIteration_bounded (n backupBase workBase : ℕ) (p : Program) (outputReg clearCount : ℕ)
    (hp : JumpsBounded p) :
    JumpsBounded (collectOneIteration n backupBase workBase p outputReg clearCount) := by
  simp only [collectOneIteration]
  -- Structure: copyRegs.seq (clearRegsRange.seq runAndStore)
  apply JumpsBounded.seq (copyRegs_bounded n backupBase workBase)
  apply JumpsBounded.seq (clearRegsRange_bounded (workBase + n) clearCount)
  exact runAndStore_bounded p workBase outputReg hp

/-- JumpsBounded for the auxiliary collection loop. -/
theorem buildCollectLoopAux_bounded (n backupBase workBase outputBase clearCount : ℕ)
    (pg : List Program) (startIdx : ℕ)
    (hpg : ∀ p ∈ pg, JumpsBounded p) :
    JumpsBounded (buildCollectLoopAux n backupBase workBase outputBase clearCount pg startIdx) := by
  induction pg generalizing startIdx with
  | nil =>
    simp only [buildCollectLoopAux]
    exact JumpsBounded.nil
  | cons p ps ih =>
    simp only [buildCollectLoopAux]
    apply JumpsBounded.append
    · apply collectOneIteration_bounded
      exact hpg p (List.mem_cons.mpr (Or.inl rfl))
    · apply ih
      intro p' hp'
      exact hpg p' (List.mem_cons.mpr (Or.inr hp'))

/-- JumpsBounded for the full collection loop. -/
theorem buildCollectLoop_bounded (n backupBase workBase outputBase clearCount : ℕ) (pg : List Program)
    (hpg : ∀ p ∈ pg, JumpsBounded p) :
    JumpsBounded (buildCollectLoop n backupBase workBase outputBase clearCount pg) := by
  simp only [buildCollectLoop]
  exact buildCollectLoopAux_bounded n backupBase workBase outputBase clearCount pg 0 hpg

/-- The runAndStore program halts if the underlying program halts on the unshifted state.

Note: We prove this by showing that p.shiftRegisters workBase running from σ
matches p running from σ.unshift workBase, because they access corresponding registers. -/
theorem runAndStore_halts {p : Program} {σ : State} (workBase outputReg : ℕ)
    (_hp_bounded : JumpsBounded p)
    (hp_halts : ∃ σ', Steps p ⟨0, σ.unshift workBase⟩ ⟨p.length, σ'⟩) :
    ∃ σ'', Steps (runAndStore p workBase outputReg) ⟨0, σ⟩
           ⟨(runAndStore p workBase outputReg).length, σ''⟩ := by
  obtain ⟨σ', hsteps⟩ := hp_halts
  -- By shiftRegisters_halts, we get p.shiftRegisters halts from (σ.unshift workBase).shift workBase
  have hshifted := shiftRegisters_halts workBase hsteps
  -- Key: (σ.unshift workBase).shift workBase agrees with σ on registers >= workBase
  -- And p.shiftRegisters workBase only accesses registers >= workBase
  -- So the executions from σ and (σ.unshift workBase).shift workBase are identical
  have hstates_agree : ∀ r, workBase ≤ r →
      (σ.unshift workBase).shift workBase r = σ r := by
    intro r hr
    simp only [State.unshift, State.shift]
    simp only [Nat.not_lt.mpr hr, if_false]
    congr 1
    omega
  -- The shifted program only accesses registers >= workBase, so execution from σ
  -- is the same as from (σ.unshift workBase).shift workBase
  -- Convert hstates_agree to State.agreeFrom form
  have hagree : ((σ.unshift workBase).shift workBase).agreeFrom σ workBase :=
    fun r hr => hstates_agree r hr
  -- Apply the state agreement lemma to get execution from σ
  obtain ⟨c₂', hsteps_from_σ, hpc_eq, _⟩ := Steps.shiftRegisters_agreeFrom hshifted hagree
  -- c₂'.pc = p.length by hpc_eq
  -- We'll use c₂' as our intermediate state
  have hshifted_from_σ : Steps (p.shiftRegisters workBase) ⟨0, σ⟩
      ⟨p.length, c₂'.state⟩ := by
    convert hsteps_from_σ using 2 <;> simp [hpc_eq]
  -- runAndStore = p.shiftRegisters workBase ++ [T workBase outputReg]
  -- After p.shiftRegisters halts at pc = p.length, we execute the T instruction
  have hT_step : Step (runAndStore p workBase outputReg)
      ⟨p.length, c₂'.state⟩
      ⟨p.length + 1, c₂'.state.write outputReg (c₂'.state.read workBase)⟩ := by
    refine Step.trans ?_
    simp only [runAndStore, Program.getInstr]
    rw [List.getElem?_append_right (by simp [Program.shiftRegisters_length])]
    simp [Program.shiftRegisters_length]
  -- Lift the shifted program's steps to runAndStore using prefix transfer
  have hrunAndStore_steps : Steps (runAndStore p workBase outputReg) ⟨0, σ⟩
      ⟨p.length, c₂'.state⟩ := by
    -- p.shiftRegisters workBase is a prefix of runAndStore
    apply Steps.prefix_transfer hshifted_from_σ
    -- Need to show: any config that takes a step has pc < p.length
    intro c₀ c₁ _ hstep₀
    -- If c₀ can take a step, then c₀.pc points to a valid instruction
    -- Valid instructions have index < p.shiftRegisters.length
    -- Step requires getInstr c₀.pc = some _, which means c₀.pc < p.shiftRegisters.length
    cases hstep₀ with
    | zero h => exact (List.getElem?_eq_some_iff.mp h).1
    | succ h => exact (List.getElem?_eq_some_iff.mp h).1
    | trans h => exact (List.getElem?_eq_some_iff.mp h).1
    | jump_eq h _ => exact (List.getElem?_eq_some_iff.mp h).1
    | jump_ne h _ => exact (List.getElem?_eq_some_iff.mp h).1
  -- Combine
  refine ⟨c₂'.state.write outputReg (c₂'.state.read workBase), ?_⟩
  apply Relation.ReflTransGen.tail hrunAndStore_steps
  convert hT_step using 1
  simp [runAndStore_length]

/-! ### Collection Loop Halting -/

/-- One iteration of the collection loop halts if the underlying program halts.

The key insight is:
1. copyRegs copies inputs from backup to work registers (halts in n steps)
2. clearRegsRange zeros the working registers beyond the n inputs (halts in clearCount steps)
3. After these, the unshifted state matches State.fromInputs
4. runAndStore then halts because p halts on that state

Parameters:
- n: number of input registers
- backupBase: where inputs are backed up
- workBase: where shifted programs execute (must have workBase >= backupBase + n for disjointness)
- p: program to run
- outputReg: where to store the result
- clearCount: number of working registers to clear (must cover p.maxRegister - n)
- σ: initial state (backup registers at backupBase..backupBase+n-1 contain the inputs)
-/
theorem collectOneIteration_halts (n backupBase workBase : ℕ) (p : Program) (outputReg clearCount : ℕ)
    (σ : State)
    (hp_bounded : JumpsBounded p)
    (hdisjoint : backupBase + n ≤ workBase)
    (hclear_enough : p.maxRegister < n + clearCount)
    (hp_halts : ∃ σ', Steps p ⟨0, State.fromInputs (List.ofFn (fun i : Fin n => σ (backupBase + i)))⟩
                       ⟨p.length, σ'⟩) :
    ∃ σ'', Steps (collectOneIteration n backupBase workBase p outputReg clearCount) ⟨0, σ⟩
           ⟨(collectOneIteration n backupBase workBase p outputReg clearCount).length, σ''⟩ := by
  simp only [collectOneIteration]
  have hcopy_bounded := copyRegs_bounded n backupBase workBase
  have hcopy_halts := copyRegs_reaches n backupBase workBase σ
  have hclear_bounded := clearRegsRange_bounded (workBase + n) clearCount
  let σ_copy := σ.afterCopy n backupBase workBase
  have hclear_halts := clearRegsRange_reaches (workBase + n) clearCount σ_copy
  let σ_clear := σ_copy.clearRange (workBase + n) clearCount
  let inputs := List.ofFn (fun i : Fin n => σ (backupBase + i))
  have hagree : (σ_clear.unshift workBase).agreeUpTo (State.fromInputs inputs) p.maxRegister := by
    intro r hr
    have hr_bound : r < n + clearCount := Nat.lt_of_le_of_lt hr hclear_enough
    simp only [State.unshift, σ_clear, State.clearRange, σ_copy, State.afterCopy,
      State.fromInputs, inputs, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split_ifs with h1 h2 h3
    all_goals (first | omega | simp_all)
  obtain ⟨σ_hp, hsteps_hp⟩ := hp_halts
  have hagree_sym : (State.fromInputs inputs).agreeUpTo (σ_clear.unshift workBase) p.maxRegister :=
    fun r hr => (hagree r hr).symm
  obtain ⟨c_transferred, hsteps_transferred, hpc_eq, _⟩ := Steps.agree_steps hsteps_hp hagree_sym
  have hp_halts_clear : ∃ σ', Steps p ⟨0, σ_clear.unshift workBase⟩ ⟨p.length, σ'⟩ := by
    refine ⟨c_transferred.state, ?_⟩
    convert hsteps_transferred using 2
  have hphase3 := runAndStore_halts workBase outputReg hp_bounded hp_halts_clear
  obtain ⟨σ_final, hphase3_steps⟩ := hphase3
  let outer := (copyRegs n backupBase workBase).seq
      ((clearRegsRange (workBase + n) clearCount).seq (runAndStore p workBase outputReg))
  let inner := (clearRegsRange (workBase + n) clearCount).seq (runAndStore p workBase outputReg)
  have hphase1 : Steps outer ⟨0, σ⟩ ⟨n, σ_copy⟩ := by
    apply Steps.copyRegs_in_seq
    exact Or.inr hdisjoint
  have hphase2_inner : Steps inner ⟨0, σ_copy⟩ ⟨clearCount, σ_clear⟩ :=
    Steps.clearRegsRange_in_seq (workBase + n) clearCount (runAndStore p workBase outputReg) σ_copy
  have hphase2 : Steps outer ⟨n, σ_copy⟩ ⟨n + clearCount, σ_clear⟩ := by
    have h := Steps.seq_steps_second (p₁ := copyRegs n backupBase workBase) hphase2_inner
    simp only [copyRegs_length, Nat.add_zero] at h
    exact h
  have hphase3_inner : Steps inner ⟨clearCount, σ_clear⟩
      ⟨clearCount + (runAndStore p workBase outputReg).length, σ_final⟩ := by
    have h := Steps.seq_steps_second (p₁ := clearRegsRange (workBase + n) clearCount) hphase3_steps
    simp only [clearRegsRange_length, Nat.add_zero] at h
    exact h
  have hphase3_outer : Steps outer ⟨n + clearCount, σ_clear⟩
      ⟨n + (clearCount + (runAndStore p workBase outputReg).length), σ_final⟩ := by
    have h := Steps.seq_steps_second (p₁ := copyRegs n backupBase workBase) hphase3_inner
    simp only [copyRegs_length, Nat.add_zero] at h
    exact h
  have hsteps_all := Relation.ReflTransGen.trans hphase1
    (Relation.ReflTransGen.trans hphase2 hphase3_outer)
  refine ⟨σ_final, ?_⟩
  convert hsteps_all using 2
  simp only [collectOneIteration_length, runAndStore_length, Program.seq_length,
    copyRegs_length, clearRegsRange_length]

/-- The auxiliary collection loop halts if all component programs halt. -/
theorem buildCollectLoopAux_halts (n backupBase workBase outputBase clearCount : ℕ)
    (pg : List Program) (startIdx : ℕ) (σ : State)
    (hpg_bounded : ∀ p ∈ pg, JumpsBounded p)
    (hdisjoint : backupBase + n ≤ workBase)
    (hclear_enough : ∀ p ∈ pg, p.maxRegister < n + clearCount)
    (hpg_halts : ∀ p ∈ pg, ∃ σ', Steps p ⟨0, State.fromInputs (List.ofFn (fun i : Fin n => σ (backupBase + i)))⟩
                                 ⟨p.length, σ'⟩) :
    ∃ σ'', Steps (buildCollectLoopAux n backupBase workBase outputBase clearCount pg startIdx) ⟨0, σ⟩
           ⟨(buildCollectLoopAux n backupBase workBase outputBase clearCount pg startIdx).length, σ''⟩ := by
  induction pg generalizing startIdx σ with
  | nil =>
    simp only [buildCollectLoopAux]
    exact ⟨σ, Relation.ReflTransGen.refl⟩
  | cons p ps ih =>
    simp only [buildCollectLoopAux]
    -- First, collectOneIteration halts
    have hiter_halts := collectOneIteration_halts n backupBase workBase p (outputBase + startIdx) clearCount σ
      (hpg_bounded p (List.mem_cons.mpr (Or.inl rfl)))
      hdisjoint
      (hclear_enough p (List.mem_cons.mpr (Or.inl rfl)))
      (hpg_halts p (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨σ', hiter_steps⟩ := hiter_halts
    -- Then the rest of the loop halts
    -- Key: backup registers are preserved after collectOneIteration
    have hbackup_preserved : ∀ i : Fin n, σ' (backupBase + i) = σ (backupBase + i) := by
      -- collectOneIteration only modifies workBase+ registers and outputReg
      -- Since backupBase + n ≤ workBase and outputReg ≥ outputBase (typically > backupBase),
      -- backup registers are preserved
      sorry  -- Need to trace through collectOneIteration's register modifications
    -- With backup preserved, the remaining programs still halt
    have hrest_halts : ∃ σ'', Steps (buildCollectLoopAux n backupBase workBase outputBase clearCount ps (startIdx + 1)) ⟨0, σ'⟩
        ⟨(buildCollectLoopAux n backupBase workBase outputBase clearCount ps (startIdx + 1)).length, σ''⟩ := by
      apply ih (startIdx + 1) σ'
      · intro p' hp'
        exact hpg_bounded p' (List.mem_cons.mpr (Or.inr hp'))
      · intro p' hp'
        exact hclear_enough p' (List.mem_cons.mpr (Or.inr hp'))
      · intro p' hp'
        -- Rewrite using hbackup_preserved
        have h := hpg_halts p' (List.mem_cons.mpr (Or.inr hp'))
        -- The states agree on backup registers, so fromInputs produces the same state
        have heq : (List.ofFn (fun i : Fin n => σ' (backupBase + i))) =
                   (List.ofFn (fun i : Fin n => σ (backupBase + i))) := by
          apply List.ext_getElem
          · simp
          · intro j h1 h2
            simp only [List.getElem_ofFn]
            exact hbackup_preserved ⟨j, by simp at h1; exact h1⟩
        simp only [heq]; exact h
    obtain ⟨σ'', hrest_steps⟩ := hrest_halts
    -- Combine: collectOneIteration ++ buildCollectLoopAux (direct append)
    -- The programs are designed so jumps are bounded within each piece
    -- We need to transfer steps from each part to the concatenation
    -- For now, use sorry as the combination requires careful step transfer lemmas
    -- for direct appends (not shiftJumps-based seq)
    sorry

/-- The collection loop halts if all component programs halt on the backed-up inputs. -/
theorem buildCollectLoop_halts (n backupBase workBase outputBase clearCount : ℕ)
    (pg : List Program) (σ : State)
    (hpg_bounded : ∀ p ∈ pg, JumpsBounded p)
    (hdisjoint : backupBase + n ≤ workBase)
    (hclear_enough : ∀ p ∈ pg, p.maxRegister < n + clearCount)
    (hpg_halts : ∀ p ∈ pg, ∃ σ', Steps p ⟨0, State.fromInputs (List.ofFn (fun i : Fin n => σ (backupBase + i)))⟩
                                 ⟨p.length, σ'⟩) :
    ∃ σ'', Steps (buildCollectLoop n backupBase workBase outputBase clearCount pg) ⟨0, σ⟩
           ⟨(buildCollectLoop n backupBase workBase outputBase clearCount pg).length, σ''⟩ := by
  simp only [buildCollectLoop]
  exact buildCollectLoopAux_halts n backupBase workBase outputBase clearCount pg 0 σ hpg_bounded hdisjoint hclear_enough hpg_halts

namespace URMComputable

/-- URM-computable functions are closed under composition.

Given:
- `f : (Fin m → ℕ) → Part ℕ` is URM-computable (computed by program `pf`)
- For each `i : Fin m`, `g i : (Fin n → ℕ) → Part ℕ` is URM-computable (computed by `pg i`)

Then the composition `h(x) = f(g₀(x), ..., gₘ₋₁(x))` is also URM-computable.

The composed program:
1. Saves the inputs to backup registers
2. For each `i`, runs `pg i` and saves the output
3. Sets up the collected outputs as inputs to `pf`
4. Runs `pf`
5. The result is in register 0

This is Theorem 2.1 in Cutland, Chapter 2. -/
theorem comp {m n : ℕ}
    {f : (Fin m → ℕ) → Part ℕ} {g : Fin m → (Fin n → ℕ) → Part ℕ}
    (hf : URMComputable m f) (hg : ∀ i : Fin m, URMComputable n (g i)) :
    URMComputable n (composePartial f g) := by
  -- Extract programs from hypotheses
  obtain ⟨pf, hpf⟩ := hf
  choose pg hpg using hg
  -- Register layout:
  -- R[0..n-1]: inputs (preserved in backup)
  -- R[n..n+m-1]: collected outputs from g_0, ..., g_{m-1}
  -- R[n+m..n+m+n-1]: backup of inputs
  -- R[n+m+n..]: working space for running programs
  let inputBackupBase := n + m  -- Where to save inputs
  let workBase := n + m + n     -- Where shifted programs work

  -- Build the composed program:
  -- 1. Copy inputs R[0..n-1] to backup R[inputBackupBase..inputBackupBase+n-1]
  -- 2. For each i:
  --    a. Copy backup to R[workBase..workBase+n-1] (inputs for pg i)
  --    b. Run pg i shifted to workBase (result in R[workBase])
  --    c. Copy R[workBase] to R[n+i] (collect output)
  -- 3. Copy collected outputs R[n..n+m-1] to R[workBase..workBase+m-1] (inputs for pf)
  -- 4. Run pf shifted to workBase (result in R[workBase])
  -- 5. Copy R[workBase] to R[0] (final output)

  -- This construction is complex; we defer the full proof
  sorry

end URMComputable

end Urm
