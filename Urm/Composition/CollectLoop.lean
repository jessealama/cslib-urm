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
    (collectOneIteration n backupBase workBase p (outputBase + startIdx) clearCount).seq
    (buildCollectLoopAux n backupBase workBase outputBase clearCount ps (startIdx + 1))

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
    apply JumpsBounded.seq
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
    convert hsteps_from_σ using 2
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

/-- A single step of a shifted program preserves registers below the shift offset. -/
private theorem shiftRegisters_step_preserves_below {p : Program} {c c' : Config} {offset : ℕ}
    (hstep : Step (p.shiftRegisters offset) c c')
    (r : ℕ) (hr : r < offset) : c'.state r = c.state r := by
  cases hstep with
  | zero h =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr c.pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | Z n =>
        simp only [Instr.shiftRegisters] at h
        cases h
        simp only [State.write, Function.update]
        split_ifs with heq
        · omega  -- r = n + offset contradicts r < offset
        · rfl
      | S _ => simp [Instr.shiftRegisters] at h
      | T _ _ => simp [Instr.shiftRegisters] at h
      | J _ _ _ => simp [Instr.shiftRegisters] at h
  | succ h =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr c.pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | S n =>
        simp only [Instr.shiftRegisters] at h
        cases h
        simp only [State.write, Function.update]
        split_ifs with heq
        · omega
        · rfl
      | Z _ => simp [Instr.shiftRegisters] at h
      | T _ _ => simp [Instr.shiftRegisters] at h
      | J _ _ _ => simp [Instr.shiftRegisters] at h
  | trans h =>
    simp only [Program.getInstr_shiftRegisters] at h
    cases hget : p.getInstr c.pc with
    | none => simp [hget] at h
    | some instr =>
      simp [hget] at h
      cases instr with
      | T m n =>
        simp only [Instr.shiftRegisters] at h
        cases h
        simp only [State.write, Function.update]
        split_ifs with heq
        · omega
        · rfl
      | Z _ => simp [Instr.shiftRegisters] at h
      | S _ => simp [Instr.shiftRegisters] at h
      | J _ _ _ => simp [Instr.shiftRegisters] at h
  | jump_eq h _ | jump_ne h _ =>
    -- Jump doesn't modify state
    rfl

/-- Shifted program execution preserves registers below the shift offset.
    Key insight: p.shiftRegisters offset only accesses registers ≥ offset. -/
private theorem shiftRegisters_preserves_below {p : Program} {c c' : Config} {offset : ℕ}
    (hsteps : Steps (p.shiftRegisters offset) c c')
    (r : ℕ) (hr : r < offset) : c'.state r = c.state r := by
  induction hsteps with
  | refl => rfl
  | tail hrest hstep ih =>
    rw [shiftRegisters_step_preserves_below hstep r hr]
    exact ih

/-- A single step in runAndStore preserves registers below workBase that aren't outputReg. -/
private theorem runAndStore_step_preserves_below {p : Program} {c c' : Config}
    {workBase outputReg : ℕ}
    (hstep : Step (runAndStore p workBase outputReg) c c')
    (r : ℕ) (hr_below : r < workBase) (hr_not_output : r ≠ outputReg) :
    c'.state r = c.state r := by
  -- runAndStore = p.shiftRegisters workBase ++ [T workBase outputReg]
  simp only [runAndStore] at hstep
  let prog := p.shiftRegisters workBase ++ [Instr.T workBase outputReg]
  -- Determine which part of the program the step is in based on pc
  by_cases hpc : c.pc < (p.shiftRegisters workBase).length
  · -- Step is in the shifted program part
    -- Convert to a step in p.shiftRegisters
    have hstep_shifted : Step (p.shiftRegisters workBase) c c' := by
      have hinstr : prog.getInstr c.pc = (p.shiftRegisters workBase).getInstr c.pc := by
        simp only [prog, Program.getInstr, List.getElem?_append_left hpc]
      cases hstep with
      | zero h =>
        rw [hinstr] at h
        exact Step.zero h
      | succ h =>
        rw [hinstr] at h
        exact Step.succ h
      | trans h =>
        rw [hinstr] at h
        exact Step.trans h
      | jump_eq h heq =>
        rw [hinstr] at h
        exact Step.jump_eq h heq
      | jump_ne h hne =>
        rw [hinstr] at h
        exact Step.jump_ne h hne
    exact shiftRegisters_step_preserves_below hstep_shifted r hr_below
  · -- Step is in the T instruction part (pc >= p.shiftRegisters.length)
    have hpc_ge : (p.shiftRegisters workBase).length ≤ c.pc := Nat.not_lt.mp hpc
    -- The T instruction part only has one instruction
    have hT_instr : prog.getInstr (p.shiftRegisters workBase).length =
                    some (Instr.T workBase outputReg) := by
      simp only [prog, Program.getInstr, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem?_cons_zero]
    cases hstep with
    | zero h =>
      -- Z instruction can't come from T part
      simp only [Program.getInstr, List.getElem?_append_right hpc_ge] at h
      have hlen : [Instr.T workBase outputReg].length = 1 := rfl
      have hpc_bound : c.pc - (p.shiftRegisters workBase).length < 1 := by
        have := (List.getElem?_eq_some_iff.mp h).1
        simp only [hlen] at this
        exact this
      have hpc_eq : c.pc - (p.shiftRegisters workBase).length = 0 := by omega
      rw [hpc_eq] at h
      simp at h
    | succ h =>
      simp only [Program.getInstr, List.getElem?_append_right hpc_ge] at h
      have hlen : [Instr.T workBase outputReg].length = 1 := rfl
      have hpc_bound : c.pc - (p.shiftRegisters workBase).length < 1 := by
        have := (List.getElem?_eq_some_iff.mp h).1
        simp only [hlen] at this
        exact this
      have hpc_eq : c.pc - (p.shiftRegisters workBase).length = 0 := by omega
      rw [hpc_eq] at h
      simp at h
    | trans h =>
      simp only [Program.getInstr, List.getElem?_append_right hpc_ge] at h
      have hlen : [Instr.T workBase outputReg].length = 1 := rfl
      have hpc_bound : c.pc - (p.shiftRegisters workBase).length < 1 := by
        have := (List.getElem?_eq_some_iff.mp h).1
        simp only [hlen] at this
        exact this
      have hpc_eq : c.pc - (p.shiftRegisters workBase).length = 0 := by omega
      rw [hpc_eq] at h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      -- h : Instr.T workBase outputReg = Instr.T m n
      -- c' = ⟨c.pc + 1, c.state.write n (c.state.read m)⟩
      obtain ⟨rfl, rfl⟩ := Instr.T.inj h
      simp only [State.write, Function.update]
      split_ifs with heq
      · exact (hr_not_output heq).elim
      · rfl
    | jump_eq h _ | jump_ne h _ =>
      -- Jump instruction - but the T part only has T, contradiction
      simp only [Program.getInstr, List.getElem?_append_right hpc_ge] at h
      have hpc_bound : c.pc - (p.shiftRegisters workBase).length < 1 := by
        have := (List.getElem?_eq_some_iff.mp h).1
        simp only [List.length_singleton] at this
        exact this
      have hpc_eq : c.pc - (p.shiftRegisters workBase).length = 0 := by omega
      simp only [hpc_eq, List.getElem?_cons_zero, Option.some.injEq] at h
      -- h : Instr.T = Instr.J, contradiction
      cases h

/-- runAndStore preserves registers below workBase that aren't outputReg (general version). -/
private theorem runAndStore_preserves_below' {p : Program} {c c' : Config}
    {workBase outputReg : ℕ}
    (hsteps : Steps (runAndStore p workBase outputReg) c c')
    (r : ℕ) (hr_below : r < workBase) (hr_not_output : r ≠ outputReg) :
    c'.state r = c.state r := by
  induction hsteps with
  | refl => rfl
  | tail hrest hstep ih =>
    rw [runAndStore_step_preserves_below hstep r hr_below hr_not_output]
    exact ih

/-- runAndStore preserves registers below workBase that aren't outputReg.
    Key insight: p.shiftRegisters only writes to [workBase, ...), and T only writes to outputReg. -/
private theorem runAndStore_preserves_below {p : Program} {σ σ' : State}
    {workBase outputReg : ℕ}
    (hsteps : Steps (runAndStore p workBase outputReg) ⟨0, σ⟩
              ⟨(runAndStore p workBase outputReg).length, σ'⟩)
    (r : ℕ) (hr_below : r < workBase) (hr_not_output : r ≠ outputReg) :
    σ' r = σ r :=
  runAndStore_preserves_below' hsteps r hr_below hr_not_output

/-- Strengthened version of collectOneIteration_halts that also proves backup preservation.
    This combines halting and backup preservation into one theorem to avoid duplication. -/
theorem collectOneIteration_halts' (n backupBase workBase : ℕ) (p : Program) (outputReg clearCount : ℕ)
    (σ : State)
    (hp_bounded : JumpsBounded p)
    (hdisjoint : backupBase + n ≤ workBase)
    (houtput_outside : backupBase + n ≤ outputReg)
    (hclear_enough : p.maxRegister < n + clearCount)
    (hp_halts : ∃ σ', Steps p ⟨0, State.fromInputs (List.ofFn (fun i : Fin n => σ (backupBase + i)))⟩
                       ⟨p.length, σ'⟩) :
    ∃ σ'', Steps (collectOneIteration n backupBase workBase p outputReg clearCount) ⟨0, σ⟩
           ⟨(collectOneIteration n backupBase workBase p outputReg clearCount).length, σ''⟩ ∧
           ∀ i : Fin n, σ'' (backupBase + i) = σ (backupBase + i) := by
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
    simp only [copyRegs_length] at h
    exact h
  have hsteps_all := Relation.ReflTransGen.trans hphase1
    (Relation.ReflTransGen.trans hphase2 hphase3_outer)

  -- Now prove backup preservation
  -- The final state σ_final comes from runAndStore_halts
  -- Looking at the proof of runAndStore_halts, σ_final = c₂'.state.write outputReg (...)
  -- where c₂' is the result of running p.shiftRegisters from σ_clear

  -- Backup preservation at each stage:
  -- 1. σ_copy preserves backup (afterCopy_read_other)
  -- 2. σ_clear preserves backup (clearRange outside range)
  -- 3. σ_final preserves backup (shifted program + T preserve it)

  have hbackup : ∀ i : Fin n, σ_final (backupBase + i) = σ (backupBase + i) := by
    intro i
    have hr : backupBase + ↑i < backupBase + n := Nat.add_lt_add_left i.isLt backupBase
    have hr_lt_workBase : backupBase + ↑i < workBase := Nat.lt_of_lt_of_le hr hdisjoint
    have hr_ne_outputReg : backupBase + ↑i ≠ outputReg := by omega

    -- Step 1: copyRegs preserves backup
    have h1 : σ_copy (backupBase + i) = σ (backupBase + i) := by
      apply State.afterCopy_read_other
      left; exact hr_lt_workBase

    -- Step 2: clearRegsRange preserves backup
    have h2 : σ_clear (backupBase + i) = σ_copy (backupBase + i) := by
      simp only [σ_clear, State.clearRange]
      split_ifs with h
      · omega
      · rfl

    -- Step 3: runAndStore preserves backup (this is the key step)
    -- σ_final comes from running runAndStore from σ_clear
    -- runAndStore = p.shiftRegisters ++ [T workBase outputReg]
    -- The shifted program only writes to [workBase, ...),
    -- and T only writes to outputReg
    -- Since backupBase + i < workBase and backupBase + i ≠ outputReg, it's preserved

    have h3 : σ_final (backupBase + i) = σ_clear (backupBase + i) :=
      runAndStore_preserves_below' hphase3_steps (backupBase + i) hr_lt_workBase hr_ne_outputReg

    rw [h3, h2, h1]

  refine ⟨σ_final, ?_, hbackup⟩
  convert hsteps_all using 2
  simp only [runAndStore_length, Program.seq_length,
    copyRegs_length, clearRegsRange_length]

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
    simp only [copyRegs_length] at h
    exact h
  have hsteps_all := Relation.ReflTransGen.trans hphase1
    (Relation.ReflTransGen.trans hphase2 hphase3_outer)
  refine ⟨σ_final, ?_⟩
  convert hsteps_all using 2
  simp only [runAndStore_length, Program.seq_length,
    copyRegs_length, clearRegsRange_length]

/-- The auxiliary collection loop halts if all component programs halt. -/
theorem buildCollectLoopAux_halts (n backupBase workBase outputBase clearCount : ℕ)
    (pg : List Program) (startIdx : ℕ) (σ : State)
    (hpg_bounded : ∀ p ∈ pg, JumpsBounded p)
    (hdisjoint : backupBase + n ≤ workBase)
    (houtput_disjoint : backupBase + n ≤ outputBase)
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
    -- First, collectOneIteration halts (use collectOneIteration_halts' to get backup preservation too)
    have houtput_outside : backupBase + n ≤ outputBase + startIdx := by omega
    have hiter_halts := collectOneIteration_halts' n backupBase workBase p (outputBase + startIdx) clearCount σ
      (hpg_bounded p (List.mem_cons.mpr (Or.inl rfl)))
      hdisjoint
      houtput_outside
      (hclear_enough p (List.mem_cons.mpr (Or.inl rfl)))
      (hpg_halts p (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨σ', hiter_steps, hbackup_preserved⟩ := hiter_halts
    -- Then the rest of the loop halts
    -- Key: backup registers are preserved after collectOneIteration (provided by collectOneIteration_halts')
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
    -- Combine using seq_halts_compose (now that we use .seq instead of ++)
    let iter := collectOneIteration n backupBase workBase p (outputBase + startIdx) clearCount
    let rest := buildCollectLoopAux n backupBase workBase outputBase clearCount ps (startIdx + 1)
    -- hiter_steps : Steps iter ⟨0, σ⟩ ⟨iter.length, σ'⟩
    -- hrest_steps : Steps rest ⟨0, σ'⟩ ⟨rest.length, σ''⟩
    -- Use seq_steps_first and seq_steps_second to combine

    -- Step 1: Lift iter steps to iter.seq rest
    have hiter_in_seq : Steps (iter.seq rest) ⟨0, σ⟩ ⟨iter.length, σ'⟩ := by
      by_cases hlen : iter.length = 0
      · -- If iter is empty, execution is trivial
        have h_eq : (⟨0, σ⟩ : Config) = ⟨iter.length, σ'⟩ := by
          apply Steps.halts_unique (p := iter) Relation.ReflTransGen.refl
          · simp only [Config.isHalted, hlen, Nat.le_refl]
          · exact hiter_steps
          · simp only [Config.isHalted, hlen, Nat.le_refl]
        simp only [hlen] at h_eq ⊢
        rw [← h_eq]
      · apply Steps.seq_steps_first hiter_steps
        · simp only [Nat.pos_iff_ne_zero]; exact hlen
        · exact Nat.le_refl _

    -- Step 2: Lift rest steps to iter.seq rest (with PC offset)
    have hrest_in_seq : Steps (iter.seq rest) ⟨iter.length, σ'⟩
        ⟨iter.length + rest.length, σ''⟩ := by
      have := Steps.seq_steps_second (p₁ := iter) hrest_steps
      simp only [Nat.add_zero] at this
      exact this

    -- Combine
    have hsteps_combined := Relation.ReflTransGen.trans hiter_in_seq hrest_in_seq
    refine ⟨σ'', ?_⟩
    convert hsteps_combined using 2
    simp only [Program.seq_length, iter, rest]

/-- The collection loop halts if all component programs halt on the backed-up inputs. -/
theorem buildCollectLoop_halts (n backupBase workBase outputBase clearCount : ℕ)
    (pg : List Program) (σ : State)
    (hpg_bounded : ∀ p ∈ pg, JumpsBounded p)
    (hdisjoint : backupBase + n ≤ workBase)
    (houtput_disjoint : backupBase + n ≤ outputBase)
    (hclear_enough : ∀ p ∈ pg, p.maxRegister < n + clearCount)
    (hpg_halts : ∀ p ∈ pg, ∃ σ', Steps p ⟨0, State.fromInputs (List.ofFn (fun i : Fin n => σ (backupBase + i)))⟩
                                 ⟨p.length, σ'⟩) :
    ∃ σ'', Steps (buildCollectLoop n backupBase workBase outputBase clearCount pg) ⟨0, σ⟩
           ⟨(buildCollectLoop n backupBase workBase outputBase clearCount pg).length, σ''⟩ := by
  simp only [buildCollectLoop]
  exact buildCollectLoopAux_halts n backupBase workBase outputBase clearCount pg 0 σ hpg_bounded hdisjoint houtput_disjoint hclear_enough hpg_halts

namespace URMComputable

/-- Helper: After clearing n registers starting at 0, the state from any n-ary input
    becomes identical to fromInputs [] (all zeros). -/
private theorem clearRange_eq_fromInputs_empty {n : ℕ} (inputs : Fin n → ℕ) :
    (State.fromInputs (List.ofFn inputs)).clearRange 0 n = State.fromInputs [] := by
  funext r
  simp only [State.clearRange, State.fromInputs, List.getD_eq_getElem?_getD, List.getElem?_nil]
  split_ifs with h
  · rfl
  · -- r is outside [0, n), so r >= n
    -- fromInputs (List.ofFn inputs) has R[r] = 0 for r >= n
    push_neg at h
    have hr_ge : n ≤ r := by omega
    simp only [List.getElem?_ofFn]
    rw [dif_neg (by omega : ¬ r < n)]

/-- URM-computable functions are closed under composition.

Given:
- `f : (Fin m → ℕ) → Part ℕ` is URM-computable (computed by program `pf`)
- For each `i : Fin m`, `g i : (Fin n → ℕ) → Part ℕ` is URM-computable (computed by `pg i`)

Then the composition `h(x) = f(g₀(x), ..., gₘ₋₁(x))` is also URM-computable.

This is Theorem 2.1 in Cutland, Chapter 2.

Proof strategy: Induction on m (the arity of f).
- Base case m = 0: composition reduces to f applied to empty tuple
- Inductive case m + 1: decompose using composePartial_succ and apply comp_unary -/

theorem comp {m n : ℕ}
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
  induction m with
  | zero =>
    -- m = 0: f takes empty tuple, no g functions to evaluate
    -- composePartial f g inputs = f (fun i => Fin.elim0 i) for any inputs
    -- Strategy: use program (clearRegsRange 0 n).seq pf
    -- 1. clearRegsRange clears registers 0..n-1, making state = fromInputs []
    -- 2. pf then runs on this zeroed state, computing f on empty input
    use (clearRegsRange 0 n).seq pf
    intro inputs
    rw [composePartial_zero]
    -- Get the specification for empty input
    let emptyInputs : Fin 0 → ℕ := fun i => i.elim0
    have hspec := hf emptyInputs
    have hinput_empty : List.ofFn emptyInputs = [] := List.ofFn_zero
    simp only [hinput_empty] at hspec
    -- The state after clearing is exactly fromInputs []
    have hcleared : (State.fromInputs (List.ofFn inputs)).clearRange 0 n = State.fromInputs [] :=
      clearRange_eq_fromInputs_empty inputs
    have hclear_bounded := clearRegsRange_bounded 0 n

    refine ⟨⟨?halts_fwd, ?halts_bwd⟩, ?result_eq⟩

    case halts_fwd =>
      -- If composed program halts → f is defined
      intro hHalts
      -- Use seq_second_halts to extract pf halting
      obtain ⟨σ_after_clear, hclear_steps, c_pf, hpf_steps, hpf_halted⟩ :=
        JumpsBounded.seq_second_halts hclear_bounded hboundedf hHalts
      -- σ_after_clear should be (fromInputs (List.ofFn inputs)).clearRange 0 n = fromInputs []
      have hclear_expected := clearRegsRange_reaches 0 n (State.fromInputs (List.ofFn inputs))
      have hclear_halted : (⟨n, (State.fromInputs (List.ofFn inputs)).clearRange 0 n⟩ : Config).isHalted
          (clearRegsRange 0 n) := by simp [Config.isHalted, clearRegsRange_length]
      have hclear_actual_halted : (⟨(clearRegsRange 0 n).length, σ_after_clear⟩ : Config).isHalted
          (clearRegsRange 0 n) := by simp [Config.isHalted]
      have hclear_steps' : Steps (clearRegsRange 0 n) ⟨0, State.fromInputs (List.ofFn inputs)⟩
          ⟨(clearRegsRange 0 n).length, σ_after_clear⟩ := by
        simp only [Config.init] at hclear_steps; exact hclear_steps
      have hstate_eq : σ_after_clear = (State.fromInputs (List.ofFn inputs)).clearRange 0 n := by
        have hunique := Steps.halts_unique hclear_steps' hclear_actual_halted hclear_expected hclear_halted
        simp only [clearRegsRange_length] at hunique
        exact congrArg Config.state hunique
      rw [hstate_eq, hcleared] at hpf_steps
      -- Now pf halts starting from fromInputs []
      have hpf_halts : Halts pf [] := ⟨c_pf, hpf_steps, hpf_halted⟩
      exact hspec.1.mp hpf_halts

    case halts_bwd =>
      -- If f is defined → composed program halts
      intro hDom
      -- pf halts on fromInputs [] (by hspec and hDom)
      have hpf_halts : Halts pf [] := hspec.1.mpr hDom
      obtain ⟨cf, hstepsf, hhaltedf⟩ := hpf_halts
      -- clearRegsRange halts at fromInputs []
      have hclear_steps := clearRegsRange_reaches 0 n (State.fromInputs (List.ofFn inputs))
      -- Use seq_halts_compose
      have hclear_at_length : Steps (clearRegsRange 0 n) (Config.init (List.ofFn inputs))
          ⟨(clearRegsRange 0 n).length, State.fromInputs []⟩ := by
        simp only [Config.init, clearRegsRange_length]
        rw [← hcleared]
        exact hclear_steps
      have hstepsf' : Steps pf ⟨0, State.fromInputs []⟩ cf := hstepsf
      exact Steps.seq_halts_compose hclear_at_length hstepsf' hhaltedf

    case result_eq =>
      intro hHalts hDom
      -- Extract halting configs
      have hpf_halts : Halts pf [] := hspec.1.mpr hDom
      have hpf_result := hspec.2 hpf_halts hDom

      -- Get the halted config for pf
      let cf := Classical.choose hpf_halts
      have hcf_spec := Classical.choose_spec hpf_halts
      have hstepsf : Steps pf (Config.init []) cf := hcf_spec.1
      have hhaltedf : cf.isHalted pf := hcf_spec.2
      have hcf_output : cf.state.output = (f emptyInputs).get hDom := by
        simp only [Result, State.output, cf] at hpf_result ⊢; exact hpf_result

      -- clearRegsRange halts at fromInputs []
      have hclear_steps := clearRegsRange_reaches 0 n (State.fromInputs (List.ofFn inputs))
      have hclear_at_length : Steps (clearRegsRange 0 n) (Config.init (List.ofFn inputs))
          ⟨(clearRegsRange 0 n).length, State.fromInputs []⟩ := by
        simp only [Config.init, clearRegsRange_length]
        rw [← hcleared]
        exact hclear_steps

      -- Build full execution
      have hfull_steps : Steps ((clearRegsRange 0 n).seq pf) (Config.init (List.ofFn inputs))
          ⟨(clearRegsRange 0 n).length + cf.pc, cf.state⟩ := by
        have hsteps_clear_seq : Steps ((clearRegsRange 0 n).seq pf) (Config.init (List.ofFn inputs))
            ⟨(clearRegsRange 0 n).length, State.fromInputs []⟩ := by
          by_cases hn : n = 0
          · -- When n=0, clearRegsRange is empty, program is just pf
            subst hn
            simp only [clearRegsRange_length]
            -- In this case, State.fromInputs (List.ofFn inputs) = State.fromInputs []
            -- because inputs : Fin 0 → ℕ, so List.ofFn inputs = []
            have hinputs_empty : List.ofFn inputs = [] := List.ofFn_zero
            rw [hinputs_empty]
            exact Steps.refl _
          · -- When n>0, use seq_steps_first
            have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
            apply Steps.seq_steps_first hclear_at_length
            · simp only [Config.init, clearRegsRange_length]; exact hn_pos
            · simp only [clearRegsRange_length]; exact Nat.le_refl _
        have hsteps_pf_seq : Steps ((clearRegsRange 0 n).seq pf)
            ⟨(clearRegsRange 0 n).length, State.fromInputs []⟩
            ⟨(clearRegsRange 0 n).length + cf.pc, cf.state⟩ := by
          have := Steps.seq_steps_second (p₁ := clearRegsRange 0 n) hstepsf
          simp only [Nat.add_zero, Config.init] at this
          exact this
        exact Steps.trans hsteps_clear_seq hsteps_pf_seq

      have hfull_halted : (⟨(clearRegsRange 0 n).length + cf.pc, cf.state⟩ : Config).isHalted
          ((clearRegsRange 0 n).seq pf) := by
        simp only [Config.isHalted, Program.seq_length, clearRegsRange_length]
        have : pf.length ≤ cf.pc := hhaltedf
        omega

      -- By uniqueness, the result matches
      simp only [Result, State.output]
      have huniq := Steps.halts_unique (Classical.choose_spec hHalts).1
        (Classical.choose_spec hHalts).2 hfull_steps hfull_halted
      rw [huniq]
      exact hcf_output
  | succ k ih =>
    -- m = k + 1: Build composed program directly using buildCollectLoop infrastructure.
    --
    -- Register layout:
    -- R[0..n-1]:           original inputs
    -- R[n..2n-1]:          backup of inputs
    -- R[2n..2n+W-1]:       work area (W = working registers needed)
    -- R[2n+W..2n+W+k]:     collected outputs (k+1 registers)
    --
    -- Program phases:
    -- 1. copyRegs n 0 n          -- backup inputs to R[n..2n-1]
    -- 2. buildCollectLoop ...    -- run each g_i, store outputs
    -- 3. copyRegs (k+1) outputBase 0  -- copy outputs to R[0..k]
    -- 4. pf                      -- run f on collected outputs

    -- Compute maximum register used by any g program
    let pgList := List.ofFn pg
    let maxGList := pgList.map Program.maxRegister
    let maxG := maxGList.foldl max 0

    -- Working area parameters
    let backupBase := n
    let workBase := 2 * n
    -- clearCount: number of registers to clear beyond the n inputs
    -- We need to clear up to maxG (in the shifted space), so we clear maxG + 1 - n registers
    let clearCount := if maxG < n then 0 else maxG + 1 - n
    -- outputBase: where to store collected outputs (after work area)
    -- Must be at least k+1 for the second copyRegs disjoint condition
    let outputBase := max (workBase + n + clearCount) (k + 1)

    -- clearCountF: number of registers to clear before running pf
    -- After copyRegs (k+1), outputs are at R[0..k]. We need to clear R[k+1..pf.maxRegister]
    -- to match State.fromInputs (List.ofFn outputs)
    let clearCountF := if pf.maxRegister ≤ k then 0 else pf.maxRegister - k

    -- Build the full composed program
    let prog :=
      (copyRegs n 0 backupBase).seq (
        (buildCollectLoop n backupBase workBase outputBase clearCount pgList).seq (
          (copyRegs (k + 1) outputBase 0).seq (
            (clearRegsRange (k + 1) clearCountF).seq pf
          )
        )
      )

    -- The program computes composePartial f g
    use prog

    -- Establish key properties
    -- 1. JumpsBounded for the composed program
    have hprog_bounded : JumpsBounded prog := by
      apply JumpsBounded.seq (copyRegs_bounded n 0 backupBase)
      apply JumpsBounded.seq
      · exact buildCollectLoop_bounded n backupBase workBase outputBase clearCount pgList
          (fun p hp => by
            simp only [pgList, List.mem_ofFn] at hp
            obtain ⟨i, rfl⟩ := hp
            exact hboundedg i)
      · apply JumpsBounded.seq (copyRegs_bounded (k + 1) outputBase 0)
        apply JumpsBounded.seq (clearRegsRange_bounded (k + 1) clearCountF)
        exact hboundedf

    -- 2. Key disjointness properties for buildCollectLoop
    have hdisjoint : backupBase + n ≤ workBase := by simp only [backupBase, workBase]; omega
    have houtput_disjoint : backupBase + n ≤ outputBase := by
      simp only [backupBase, outputBase, workBase, clearCount]
      split_ifs <;> simp only [Nat.max_def] <;> split_ifs <;> omega

    -- 3. Clear count is sufficient for all programs
    have hclear_enough : ∀ p ∈ pgList, p.maxRegister < n + clearCount := by
      intro p hp
      simp only [pgList, List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      simp only [clearCount]
      -- (pg i).maxRegister ≤ maxG, where maxG = foldl max 0 maxGList
      -- maxGList = pgList.map maxRegister, so (pg i).maxRegister ∈ maxGList
      have hmax_le : (pg i).maxRegister ≤ maxG := by
        simp only [maxG, maxGList, pgList]
        -- (pg i).maxRegister is in the mapped list
        have hmem : (pg i).maxRegister ∈ (List.ofFn pg).map Program.maxRegister := by
          rw [List.mem_map]
          exact ⟨pg i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩
        -- Element in list ≤ foldl max 0 of list
        generalize hL : (List.ofFn pg).map Program.maxRegister = L at hmem ⊢
        clear hL
        induction L with
        | nil => simp at hmem
        | cons y ys ih =>
          simp only [List.foldl_cons]
          rcases List.mem_cons.mp hmem with heq | hmem'
          · -- Case: (pg i).maxRegister = y, need y ≤ foldl max y ys
            rw [← heq]
            clear ih heq
            -- x ≤ foldl max x ys for any x
            have hle_foldl : ∀ (L : List ℕ) (x : ℕ), x ≤ L.foldl max x := by
              intro L x
              induction L generalizing x with
              | nil => exact Nat.le_refl _
              | cons z zs ihz =>
                simp only [List.foldl_cons]
                calc x ≤ max x z := le_max_left _ _
                     _ ≤ List.foldl max (max x z) zs := ihz (max x z)
            calc (pg i).maxRegister ≤ max 0 (pg i).maxRegister := le_max_right _ _
                 _ ≤ List.foldl max (max 0 (pg i).maxRegister) ys := hle_foldl ys _
          · -- Case: (pg i).maxRegister ∈ ys
            have hih := ih hmem'
            -- foldl max 0 ys ≤ foldl max (max 0 y) ys since max 0 y ≥ 0
            have hfoldl_mono : ∀ (L : List ℕ) (a b : ℕ), a ≤ b → L.foldl max a ≤ L.foldl max b := by
              intro L a b hab
              induction L generalizing a b with
              | nil => exact hab
              | cons w ws ihw =>
                simp only [List.foldl_cons]
                apply ihw
                -- max a w ≤ max b w when a ≤ b
                simp only [Nat.max_def]; split_ifs <;> omega
            calc (pg i).maxRegister ≤ List.foldl max 0 ys := hih
                 _ ≤ List.foldl max (max 0 y) ys := hfoldl_mono _ _ _ (Nat.zero_le _)
      split_ifs with h
      · -- maxG < n, so any maxRegister ≤ maxG < n ≤ n + 0
        omega
      · -- maxG ≥ n, clearCount = maxG + 1 - n
        omega

    intro inputs

    -- The proof requires tracking state through all phases:
    -- Phase 1: copyRegs copies inputs to backup
    -- Phase 2: buildCollectLoop runs each g_i and stores output at outputBase+i
    -- Phase 3: copyRegs copies collected outputs to R[0..k]
    -- Phase 4: pf runs on these inputs

    -- For the halting equivalence, we need:
    -- Forward: prog halts → extract that each g_i halted → g_i defined → f defined on outputs
    -- Backward: all g_i defined → all halt → buildCollectLoop halts → f defined → pf halts

    -- For the result, we need to track R[0] through all phases.

    -- This requires lemmas about:
    -- - What values are stored by buildCollectLoop at outputBase+i
    -- - What values are at R[0..k] after the second copyRegs
    -- These lemmas would need to be proven separately.

    refine ⟨⟨?halts_fwd, ?halts_bwd⟩, ?result_eq⟩

    case halts_fwd =>
      -- If prog halts, then composePartial is defined
      intro hHalts
      -- prog = copyRegs.seq (buildCollectLoop.seq (copyRegs.seq (clearRegsRange.seq pf)))

      -- Extract that buildCollectLoop.seq (copyRegs.seq (clearRegsRange.seq pf)) halted
      have hcopy1_bounded := copyRegs_bounded n 0 backupBase
      have hloop_bounded := buildCollectLoop_bounded n backupBase workBase outputBase clearCount pgList
        (fun p hp => by simp only [pgList, List.mem_ofFn] at hp; obtain ⟨i, rfl⟩ := hp; exact hboundedg i)
      have hcopy2_bounded := copyRegs_bounded (k + 1) outputBase 0
      have hclearF_bounded := clearRegsRange_bounded (k + 1) clearCountF
      have hinner_bounded := JumpsBounded.seq hloop_bounded
        (JumpsBounded.seq hcopy2_bounded (JumpsBounded.seq hclearF_bounded hboundedf))

      obtain ⟨σ_after_copy1, hcopy1_steps, c_inner, hinner_steps, hinner_halted⟩ :=
        JumpsBounded.seq_second_halts hcopy1_bounded hinner_bounded hHalts

      -- From the inner halting, we know:
      -- - buildCollectLoop halted from σ_after_copy1
      -- - This means all g_i programs halted → all g_i are defined

      -- Use composePartial_dom to show the domain condition
      rw [composePartial_dom]
      -- Need: (∀ i, (g i inputs).Dom) ∧ ∃ hg, (f (fun i => (g i inputs).get (hg i))).Dom

      -- Extract that buildCollectLoop halted by applying seq_first_halts
      -- Note: We need to package the inner execution as a Halts
      -- The inner execution starts at pc=0 from σ_after_copy1

      -- First, show σ_after_copy1 has backed-up inputs equal to original inputs
      have hbackup_eq : ∀ j : Fin n, σ_after_copy1 (backupBase + j) = inputs j := by
        intro j
        -- σ_after_copy1 = (State.fromInputs (List.ofFn inputs)).afterCopy n 0 backupBase
        have hcopy1_unique := Steps.halts_unique hcopy1_steps
          (by simp [Config.isHalted, copyRegs_length])
          (copyRegs_reaches n 0 backupBase (State.fromInputs (List.ofFn inputs))
            (Or.inr (by simp only [backupBase]; omega)))
          (by simp [Config.isHalted, copyRegs_length])
        simp only [copyRegs_length] at hcopy1_unique
        have hstate_eq := congrArg Config.state hcopy1_unique
        simp only at hstate_eq
        rw [hstate_eq]
        simp only [State.afterCopy, backupBase, Nat.zero_add]
        split_ifs with h
        · -- backupBase ≤ backupBase + j ∧ backupBase + j < backupBase + n
          simp only [State.fromInputs, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          have hj : (j : ℕ) < n := j.2
          simp only [Nat.add_sub_cancel_left, hj, ↓reduceDIte, Option.getD_some]
        · -- Not in range - contradiction since j < n
          push_neg at h
          have hj : (j : ℕ) < n := j.2
          omega

      -- From inner halting, we need to extract that buildCollectLoop reached its end
      -- and that each underlying program halted.

      -- Key insight: if buildCollectLoop.seq rest halts, and buildCollectLoop is JumpsBounded,
      -- then buildCollectLoop must reach pc = loop.length before rest starts.

      -- Extract loop halting from inner halting
      let loop := buildCollectLoop n backupBase workBase outputBase clearCount pgList
      let rest := (copyRegs (k + 1) outputBase 0).seq pf
      have hrest_bounded := JumpsBounded.seq hcopy2_bounded hboundedf

      -- The inner part starts at pc=0 and halts
      -- This means loop.seq rest starting at ⟨0, σ_after_copy1⟩ reaches a halted config

      -- Use the semantic characterization: if the composed program halts,
      -- then all component functions must be defined.
      -- This follows from the correctness of the program construction.

      -- For each g_i to be defined, pg_i must halt on the original inputs
      -- The buildCollectLoop runs each pg_i on the backed-up inputs, which equal original inputs

      -- Since inner halts, and inner = loop.seq rest, we can decompose:
      -- 1. loop reaches some final state (completing all iterations)
      -- 2. rest halts from that state

      -- From loop completing, each pg_i program halted on the backed-up inputs
      -- This requires a lemma about buildCollectLoop structure

      -- For now, we use the fact that the programs were constructed to satisfy
      -- the halting-definedness equivalence, and the composite program halts
      -- iff the underlying functions are defined.

      -- The proof requires extracting from "prog halts" that:
      -- 1. All g_i are defined
      -- 2. f is defined on the outputs

      -- Key lemma needed: buildCollectLoop_halts_iff_all_programs_halt
      -- If buildCollectLoop completes from σ_after_copy1, then each pg_i halted
      -- on the backed-up inputs (which equal original inputs by hbackup_eq).

      -- From inner = loop.seq rest halting, extract that loop completed
      -- and rest halted from the post-loop state.

      -- Show all g_i are defined using the program structure
      have hall_g_dom : ∀ i : Fin (k + 1), (g i inputs).Dom := by
        intro i
        -- Use the halting ↔ definedness specification
        rw [← (hg i inputs).1]
        -- Need: Halts (pg i) (List.ofFn inputs)

        -- The key insight: prog halts, so inner halts, so loop completes
        -- Loop completing means each pg_i halted on the backed-up inputs
        -- Backed-up inputs = original inputs (by hbackup_eq)

        -- This requires a converse lemma: if buildCollectLoop.seq rest halts,
        -- and we're in the loop portion, then each underlying pg_i halted.

        -- For the complete proof, we would prove:
        -- buildCollectLoop_halts_implies_all_programs_halt :
        --   Steps (buildCollectLoop ...) ⟨0, σ⟩ ⟨loop.length, σ'⟩ →
        --   ∀ p ∈ pgList, Halts p (List.ofFn (restored_inputs σ))

        -- The formal extraction from hinner_steps uses:
        -- 1. JumpsBounded of loop ensures execution passes through pc = loop.length
        -- 2. buildCollectLoop structure: sequential collectOneIterations
        -- 3. Each collectOneIteration runs pg_i with restored inputs

        sorry

      constructor
      · exact hall_g_dom

      · -- ∃ hg, (f (fun i => (g i inputs).get (hg i))).Dom
        use hall_g_dom
        -- From inner halting, extract that pf halted
        -- pf halting on outputs means f is defined on outputs

        -- After buildCollectLoop completes, outputs are at outputBase+i
        -- After copyRegs, outputs are at R[0..k]
        -- pf runs on this state

        -- The key lemma needed: buildCollectLoop_stores_outputs
        --   After buildCollectLoop, σ(outputBase + i) = (g i inputs).get _

        -- Combined with copyRegs, after phase 3:
        --   σ3(i) = outputs(i) for i < k+1

        -- Then pf halting from σ3 with state agreement implies
        -- pf halts on List.ofFn outputs, so f is defined.

        sorry

    case halts_bwd =>
      -- If composePartial is defined, then prog halts
      intro hDom
      -- composePartial_dom tells us all g_i are defined and f is defined on outputs
      have hcomp_dom := composePartial_dom.mp hDom
      obtain ⟨hall_g_dom, hg_witness, hf_dom⟩ := hcomp_dom

      -- Key: Each g_i is defined on inputs → each pg_i halts on inputs
      have hpg_halts : ∀ i : Fin (k + 1), Halts (pg i) (List.ofFn inputs) := by
        intro i
        exact (hg i inputs).1.mpr (hall_g_dom i)

      -- Phase 1: copyRegs n 0 backupBase always halts
      -- Disjoint: backupBase + n ≤ 0 is false, but 0 + n ≤ backupBase = n is true
      have hcopy1_disjoint : 0 + n ≤ backupBase := by simp only [backupBase]; omega
      let σ0 := State.fromInputs (List.ofFn inputs)
      have hcopy1_steps := copyRegs_reaches n 0 backupBase σ0 (Or.inr hcopy1_disjoint)

      -- State after phase 1 (backup)
      let σ1 := σ0.afterCopy n 0 backupBase
      have hσ1_spec : Steps (copyRegs n 0 backupBase) ⟨0, σ0⟩ ⟨n, σ1⟩ := by
        simp only [σ1] at hcopy1_steps ⊢
        exact hcopy1_steps

      -- Phase 2: buildCollectLoop halts (since all g_i halt)
      -- Need to show that pg_i halts when started with backed-up inputs
      have hloop_pg_halts : ∀ p ∈ pgList, ∃ σ',
          Steps p ⟨0, State.fromInputs (List.ofFn (fun i : Fin n => σ1 (backupBase + i)))⟩
                 ⟨p.length, σ'⟩ := by
        intro p hp
        simp only [pgList, List.mem_ofFn] at hp
        obtain ⟨i, rfl⟩ := hp
        -- σ1 (backupBase + j) = inputs j for all j < n (by copyRegs/afterCopy spec)
        -- So State.fromInputs (List.ofFn (fun j => σ1 (backupBase + j))) = State.fromInputs (List.ofFn inputs)
        have hinputs_eq : (fun j : Fin n => σ1 (backupBase + j)) = inputs := by
          funext j
          simp only [σ1, State.afterCopy, σ0, backupBase]
          have hj : (j : ℕ) < n := j.2
          -- Use split_ifs with decide to handle all the conditionals
          simp only [State.fromInputs, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          split_ifs with h1 h2 h3
          · -- h1: n ≤ n + j ∧ n + j < n + n, h2: 0 + (n + j - n) < n
            simp only [Nat.zero_add, Nat.add_sub_cancel_left, Option.getD_some]
          all_goals omega  -- All other cases are contradictions
        simp only [hinputs_eq]
        -- Use JumpsBounded.halts_reaches_end to get steps to exactly p.length
        have hbounded_i := hboundedg i
        exact JumpsBounded.halts_reaches_end hbounded_i (hpg_halts i)

      have hloop_halts := buildCollectLoop_halts n backupBase workBase outputBase clearCount
        pgList σ1
        (fun p hp => by
          simp only [pgList, List.mem_ofFn] at hp
          obtain ⟨i, rfl⟩ := hp
          exact hboundedg i)
        hdisjoint houtput_disjoint hclear_enough hloop_pg_halts

      -- Phase 3: copyRegs (k+1) outputBase 0 always halts
      let σ2 := Classical.choose hloop_halts
      have hσ2_spec := Classical.choose_spec hloop_halts
      -- Disjoint: 0 + (k+1) ≤ outputBase (guaranteed by max definition)
      have hcopy2_disjoint : 0 + (k + 1) ≤ outputBase := by
        simp only [Nat.zero_add, outputBase]
        exact le_max_right _ _
      have hcopy2_steps := copyRegs_reaches (k + 1) outputBase 0 σ2 (Or.inl hcopy2_disjoint)

      -- Phase 4: pf halts (since f is defined on outputs)
      let σ3 := σ2.afterCopy (k + 1) outputBase 0

      -- For pf to halt, we need f defined on the inputs that pf sees
      -- Key lemma: buildCollectLoop stores output i at outputBase + i
      -- After copyRegs: σ3(i) = σ2(outputBase + i) = (g i inputs).get _

      -- Use hf to get that pf halts on the correct outputs
      let outputs : Fin (k + 1) → ℕ := fun i => (g i inputs).get (hall_g_dom i)
      have hpf_halts : Halts pf (List.ofFn outputs) := (hf outputs).1.mpr hf_dom

      -- Now combine all phases using seq_halts_compose
      -- The structure is:
      -- 1. Phase 1: copyRegs n 0 backupBase → σ1 (backup inputs)
      -- 2. Phase 2: buildCollectLoop → σ2 (collect outputs at outputBase+i)
      -- 3. Phase 3: copyRegs (k+1) outputBase 0 → σ3 (copy outputs to R[0..k])
      -- 4. Phase 4: pf → halts (f is defined on outputs)

      -- Key tracking requirements:
      -- - buildCollectLoop_stores_outputs: σ2(outputBase + i) = (g i inputs).get _
      -- - After phase 3: σ3(i) = σ2(outputBase + i) = (g i inputs).get _
      -- - pf halts from σ3 because σ3 agrees with State.fromInputs (List.ofFn outputs)
      --   on registers 0..k (which is sufficient for JumpsBounded pf)

      -- For now, the full tracking proof is deferred as it requires additional lemmas
      -- about what buildCollectLoop stores at output registers.
      -- The proof structure above shows the approach.
      sorry

    case result_eq =>
      -- Result of prog equals composePartial value
      intro hHalts hDom
      -- Track R[0] through all phases
      -- After phase 4, R[0] = f(g_0(inputs), ..., g_k(inputs))
      sorry

end URMComputable

end Urm
