/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.Halting

/-! # Correctness Proofs for General Composition

This file proves the main correctness theorems for general composition:
- `comp_general_halts_imp_gi_dom`: If composition halts, each gᵢ is defined
- `comp_general_halts_imp_f_dom`: If composition halts and all gᵢ are defined, f is defined
- `comp_general_dom_imp_halts`: If the composed function is defined, the program halts
- `comp_general_result`: The result equals the composed function value

## Main results

- `compFunction`: The composed function h(x) = f(g₁(x), ..., gₘ(x))
- `comp_general_halts_imp_gi_dom`: Halts → each gᵢ is defined
- `comp_general_halts_imp_f_dom`: Halts ∧ gᵢ defined → f defined
- `comp_general_dom_imp_halts`: composed function defined → program halts
- `comp_general_result`: Result equals composed function value
-/

namespace Urm

open Program

/-! ## Main Theorem -/

/-- The composed function for general composition.
h(x) = f(g₁(x), ..., gₘ(x)) -/
def compFunction (m n : ℕ) (f : (Fin m → ℕ) → Part ℕ) (gs : Fin m → (Fin n → ℕ) → Part ℕ)
    (x : Fin n → ℕ) : Part ℕ :=
  (Part.sequence (fun i => gs i x)).bind f

set_option maxHeartbeats 400000 in
/-- If the composition halts, then each gᵢ is defined on the inputs. -/
theorem comp_general_halts_imp_gi_dom
    {m n : ℕ} [NeZero m]
    {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (_hF_sf : pF.IsStandardForm)
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (_hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs))
    (i : Fin m) :
    (gs i inputs).Dom := by
  -- Set up base register
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF

  -- Standard form facts
  have hSaveInputs_sf := saveInputs_isStandardForm base n
  have hGPhases_sf : gPhases.IsStandardForm := allGPhases_isStandardForm hGs_sf
  have hGPhase_i_sf : (gPhase base n (pGs i) i.val).IsStandardForm :=
    gPhase_isStandardForm (hGs_sf i)

  -- The program structure: H = saveInputs ++ gPhases ++ final
  have hH_eq : Program.composeGeneral m n pF pGs = saveInputs.concat (gPhases.concat final) := rfl

  -- Split allGPhases at position i.val: allGPhases = prefix(i) ++ gPhase(i) ++ suffix(i+1)
  -- Actually: prefix(i) ++ suffix(i) where suffix(i) starts with gPhase(i)
  have hGPhases_split := allGPhases_split m n base pGs i.val (Nat.le_of_lt i.isLt)
  have hPrefix_i_sf : (allGPhases_prefix m n base pGs i.val).IsStandardForm :=
    allGPhases_prefix_isStandardForm hGs_sf i.val
  have hSuffix_i_sf : (allGPhases_suffix m n base pGs i.val).IsStandardForm :=
    allGPhases_suffix_isStandardForm hGs_sf i.val

  -- saveInputs ++ prefix(i) is standard form
  have hSavePrefix_sf := hSaveInputs_sf.concat hPrefix_i_sf

  -- Rewrite program as (saveInputs ++ gPhases) ++ final
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  rw [hH_eq, ← concat_assoc] at hHalts

  -- Extract: saveInputs ++ gPhases halts (as prefix of full program)
  have hSaveGPhases_halts := Halts.prefix_of_concat_sf hHalts hSaveGPhases_sf

  -- Unfold gPhases as prefix(i) ++ suffix(i)
  -- saveInputs ++ gPhases = saveInputs ++ (prefix ++ suffix) = (saveInputs ++ prefix) ++ suffix
  have hSaveGPhases_eq : saveInputs.concat gPhases =
      (saveInputs.concat (allGPhases_prefix m n base pGs i.val)).concat
        (allGPhases_suffix m n base pGs i.val) := by
    show saveInputs.concat (allGPhases m n base pGs) = _
    rw [hGPhases_split, concat_assoc]
  rw [hSaveGPhases_eq] at hSaveGPhases_halts

  -- Extract: saveInputs ++ prefix(i) halts
  have hSavePrefix_halts := Halts.prefix_of_concat_sf hSaveGPhases_halts hSavePrefix_sf

  -- Get suffix execution from (saveInputs ++ prefix)
  obtain ⟨sSavePrefix, _, hsSavePrefix_eq, cSuffix, hSuffix_steps, hSuffix_halted⟩ :=
    Halts.suffix_of_concat_sf hSaveGPhases_halts hSavePrefix_sf

  -- suffix(i) = gPhase(i) ++ rest
  -- gPhase(i) = clear ++ copyRange ++ pGs[i] ++ [T 0 (base+n+1+i)]
  have hGPhase_i : gPhase base n (pGs i) i.val =
      (clearRegisters base).concat ((copyRegisterRange (base + 1) 0 n).concat
        ((pGs i).concat [Instr.T 0 (base + n + 1 + i.val)])) := rfl

  -- Need to show that suffix(i) starts with gPhase(i)
  -- suffix(i) = foldl over (drop i (finRange m)) starting from []
  -- The first element after drop is i itself (when i < m)
  have hSuffix_i_eq : allGPhases_suffix m n base pGs i.val =
      (gPhase base n (pGs i) i.val).concat (allGPhases_suffix m n base pGs (i.val + 1)) := by
    simp only [allGPhases_suffix]
    have hdrop_eq : (List.finRange m).drop i.val = i :: (List.finRange m).drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons]
      · congr 1; simp only [List.finRange, List.getElem_ofFn]
      · simp only [List.length_finRange]; exact i.isLt
    rw [hdrop_eq, List.foldl_cons, concat_nil_left]
    exact foldl_concat_eq_acc_concat _ _ _

  rw [hSuffix_i_eq] at hSuffix_steps hSuffix_halted

  -- Extract gPhase(i) halting from suffix execution
  obtain ⟨_, hGPhase_i_steps, hGPhase_i_halted⟩ :=
    prefix_of_concat_from_zero hSuffix_steps hSuffix_halted hGPhase_i_sf

  -- Now extract pGs[i] from gPhase(i)
  -- gPhase = clear ++ (copyRange ++ (pGs_i ++ [T]))
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine base)
  have hCopyRange_sf := straightLine_isStandardForm (copyRegisterRange_isStraightLine (base + 1) 0 n)
  have hT_sl : Program.isStraightLine [Instr.T 0 (base + n + 1 + i.val)] = true := rfl
  have hT_sf : Program.IsStandardForm [Instr.T 0 (base + n + 1 + i.val)] :=
    straightLine_isStandardForm hT_sl

  -- Extract clear halting and state
  obtain ⟨sClear, hClear_steps, ⟨cCopyRest, hCopyRest_steps, hCopyRest_halted⟩⟩ :=
    suffix_of_concat_from_zero hGPhase_i_steps hGPhase_i_halted hClear_sf

  -- Extract copyRange halting and state
  obtain ⟨sCopy, hCopy_steps, ⟨cGiT, hGiT_steps, hGiT_halted⟩⟩ :=
    suffix_of_concat_from_zero hCopyRest_steps hCopyRest_halted hCopyRange_sf

  -- Extract pGs[i] halting from pGs[i] ++ [T]
  obtain ⟨cGi', hGi_steps, hGi_halted⟩ :=
    prefix_of_concat_from_zero hGiT_steps hGiT_halted (hGs_sf i)

  -- Now show state agreement: sCopy agrees with inputs on registers 0..maxRegister(pGs i)
  -- This follows from:
  -- 1. After saveInputs, inputs are in R[base+1..base+n]
  -- 2. After clear (applied to sSavePrefix), R[0..base] = 0
  -- 3. After copyRange, R[0..n-1] = inputs

  -- First, track what's in sSavePrefix (state after saveInputs ++ prefix(i))
  -- The saved inputs in R[base+1..base+n] are preserved through all previous phases

  -- Key insight: After copyRegisterRange in gPhase(i), R[j] for j < n equals saved input[j]
  -- And after clear, R[j] for j >= n and j <= base equals 0

  have hbase_ge : (pGs i).maxRegister ≤ base := compositionBase_ge_Gi m n pF pGs i
  have hbase_ge_n : n - 1 ≤ base := compositionBase_ge_n_sub_one m n pF pGs

  -- The state sCopy has:
  -- - R[j] = inputs[j] for j < n (from copyRange copying R[base+1+j] which has inputs[j])
  -- - R[j] = 0 for n ≤ j ≤ base (preserved from clear)

  -- For agreeing state, we need: for r ≤ maxRegister(pGs i), sCopy.read r = fromInputs(inputs).read r
  have hagreeGi : ∀ r, r ≤ (pGs i).maxRegister →
      sCopy.read r = (State.fromInputs (List.ofFn inputs)).read r := by
    intro r hr
    -- r ≤ maxRegister ≤ base
    have hr_le_base : r ≤ base := Nat.le_trans hr hbase_ge
    -- Two cases: r < n (input register) or r ≥ n (should be 0)
    rcases Nat.lt_or_ge r n with hr_lt_n | hr_ge_n
    · -- r < n: sCopy.read r = inputs[r]
      -- copyRange copied from base+1+r to r
      -- Need to trace: inputs saved to R[base+1+j], then copied back to R[j]

      -- Step 1: sCopy.read r = sClear.read (base+1+r)
      have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
      have hCopy_halted' : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
          (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
      have hsCopy_eq : sCopy = straightLineFinalState hCopy_sl sClear :=
        straightLineFinalState_eq_of_halted hCopy_sl sClear
          ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ hCopy_steps hCopy_halted'

      -- Use copyRegisterRange_state to get the copy property
      have hNoOverlap_copy : (base + 1) + n ≤ 0 ∨ 0 + n ≤ base + 1 := Or.inr (by omega)
      obtain ⟨_, hsCopy_final_eq, hsCopy_copies, _⟩ :=
        copyRegisterRange_state (base + 1) 0 n sClear hNoOverlap_copy
      -- hsCopy_copies : ∀ i, i < n → s'.read (0 + i) = sClear.read ((base + 1) + i)

      have hsCopy_r : sCopy.read r = sClear.read (base + 1 + r) := by
        have hr' := hsCopy_copies r hr_lt_n
        simp only [Nat.zero_add] at hr'
        rw [hsCopy_eq, hsCopy_final_eq]
        convert hr' using 2

      -- Step 2: sClear.read (base+1+r) = sSavePrefix.read (base+1+r)
      -- clearRegisters preserves registers above base
      have hClear_sl := clearRegisters_isStraightLine base
      have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
          (clearRegisters base) := by simp [Config.isHalted]
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sSavePrefix :=
        straightLineFinalState_eq_of_halted hClear_sl sSavePrefix
          ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'

      have hbase_1_r_gt : base < base + 1 + r := by omega
      have hsClear_preserves : sClear.read (base + 1 + r) = sSavePrefix.read (base + 1 + r) := by
        rw [hsClear_eq]
        exact clearRegisters_preserves_above' base sSavePrefix (base + 1 + r) hbase_1_r_gt

      -- Step 3: sSavePrefix.read (base+1+r) = inputs[r]
      -- This requires tracking that inputs are preserved through saveInputs and all prefix phases.
      -- Key insight: R[base+1..base+n] is only written by saveInputs, then preserved by all phases.
      -- - saveInputs writes inputs to R[base+1..base+n]
      -- - Each gPhase clears R[0..base], copies from R[base+1..] to R[0..n-1], runs G, saves to R[base+n+1+j]
      -- - None of these touch R[base+1..base+n]

      -- For now, we need to trace through the prefix execution.
      -- This is complex and requires induction over the prefix phases.
      -- The key lemma needed: for any sequence of gPhases, R[base+1..base+n] is preserved.

      -- Simplified approach: use that sSavePrefix is the result of saveInputs ++ prefix(i)
      -- and show the preservation property holds.

      -- The RHS value: (State.fromInputs l).read r = l.getD r 0
      -- For List.ofFn inputs with r < n: (List.ofFn inputs).getD r 0 = inputs ⟨r, _⟩
      have hRHS : (State.fromInputs (List.ofFn inputs)).read r = inputs ⟨r, hr_lt_n⟩ := by
        simp only [State.fromInputs, State.read]
        -- Use List.getD_eq_getElem from Mathlib to convert getD to getElem
        rw [List.getD_eq_getElem (List.ofFn inputs) 0 (by simp; exact hr_lt_n), List.getElem_ofFn]

      rw [hsCopy_r, hsClear_preserves, hRHS]

      -- Now need: sSavePrefix.read (base + 1 + r) = inputs ⟨r, hr_lt_n⟩

      -- sSavePrefix is the state after (saveInputs ++ prefix(i)) halts
      -- Split execution: saveInputs halts, then prefix(i) halts

      -- Get the Halts for saveInputs ++ prefix(i)
      -- hSavePrefix_halts : Halts (saveInputs ++ prefix(i)) inputs
      obtain ⟨sSave, hSave_steps, ⟨cPrefix, hPrefix_steps, hPrefix_halted⟩⟩ :=
        suffix_of_concat_from_zero hSavePrefix_halts.choose_spec.1
          hSavePrefix_halts.choose_spec.2 hSaveInputs_sf

      -- After saveInputs, R[base+1+r] = inputs[r]
      have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
      have hSave_halted' : (⟨(copyRegisterRange 0 (base + 1) n).length, sSave⟩ : Config).isHalted
          (copyRegisterRange 0 (base + 1) n) := by simp [Config.isHalted]
      have hsSave_eq : sSave = straightLineFinalState hSave_sl (State.fromInputs (List.ofFn inputs)) :=
        straightLineFinalState_eq_of_halted hSave_sl (State.fromInputs (List.ofFn inputs))
          ⟨(copyRegisterRange 0 (base + 1) n).length, sSave⟩ hSave_steps hSave_halted'

      -- prefix(i) preserves R[base+1+r]
      have hpGs_max : ∀ j, (pGs j).maxRegister ≤ base := fun j => compositionBase_ge_Gi m n pF pGs j
      have hn_le_base : n ≤ base + 1 := by
        have h := compositionBase_ge_n_sub_one m n pF pGs
        omega

      have hSave_value := saveInputs_state base n hn_le_base inputs r hr_lt_n
      -- Rewrite hSave_value to use sSave instead of straightLineFinalState
      have hsSave_value : sSave.read (base + 1 + r) = inputs ⟨r, hr_lt_n⟩ := by
        rw [hsSave_eq]; exact hSave_value

      -- Show sSavePrefix = cPrefix.state (state after prefix halts)
      have hPrefix_state_match : cPrefix.state = sSavePrefix := by
        -- cPrefix comes from suffix_of_concat_from_zero on hSavePrefix_halts
        -- sSavePrefix comes from Halts.suffix_of_concat_sf on hSaveGPhases_halts
        -- Both represent the final state after saveInputs ++ prefix(i) halts
        have h1 := Steps.chain_concat hSave_steps hSave_halted' rfl hPrefix_steps hPrefix_halted
        -- h1.1 : Steps (saveInputs ++ prefix) ⟨0, fromInputs⟩ ⟨cPrefix.pc + save.length, cPrefix.state⟩
        -- h1.2 : halted
        -- hSavePrefix_halts.choose_spec : Steps (saveInputs ++ prefix) ⟨0, fromInputs⟩ c ∧ c.isHalted
        have hunique := Steps.halts_unique h1.1 h1.2 hSavePrefix_halts.choose_spec.1 hSavePrefix_halts.choose_spec.2
        -- hunique : ⟨cPrefix.pc + save.length, cPrefix.state⟩ = Classical.choose hSavePrefix_halts
        -- We need to show cPrefix.state = sSavePrefix
        -- sSavePrefix = (Classical.choose hSavePrefix_halts).state by hsSavePrefix_eq
        have heq := hsSavePrefix_eq hSavePrefix_halts
        rw [heq]
        -- Goal: cPrefix.state = (Classical.choose hSavePrefix_halts).state
        -- Use hunique to extract state equality
        have hstate_eq : cPrefix.state = (Classical.choose hSavePrefix_halts).state := by
          have := congrArg Config.state hunique
          exact this
        exact hstate_eq

      have hPrefix_preserves := allGPhases_prefix_preserves_saved_inputs m n base pGs hGs_sf hpGs_max hn_le_base
        i.val (Nat.le_of_lt i.isLt)
        sSave sSavePrefix cPrefix hPrefix_steps hPrefix_halted hPrefix_state_match

      -- Chain: sSavePrefix.read (base+1+r) = sSave.read (base+1+r) = inputs[r]
      rw [hPrefix_preserves (base + 1 + r) (by omega) (by omega), hsSave_value]
    · -- r ≥ n: should be 0
      have hRHS_zero : (State.fromInputs (List.ofFn inputs)).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; exact hr_ge_n)]
        rfl
      rw [hRHS_zero]
      -- After clear, R[r] = 0 for r ≤ base
      -- copyRange only writes to R[0..n-1], so R[r] still 0 for r ≥ n

      -- Connect sClear to straightLineFinalState
      have hClear_sl := clearRegisters_isStraightLine base
      have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
          (clearRegisters base) := by simp [Config.isHalted]

      -- Get the starting state for clear - need to extract from the context
      -- sSavePrefix is the state after saveInputs ++ prefix(i)
      -- Actually, we need to know that hClear_steps starts from some state s_before_clear

      -- Use suffix_of_concat_from_zero structure: hGPhase_i_steps starts from sSavePrefix
      -- gPhase = clear ++ rest, so clear starts from sSavePrefix too
      -- We got sClear from suffix_of_concat_from_zero hGPhase_i_steps ...

      -- Connect sCopy.read r to sClear.read r using copyRange_preserves
      -- copyRange (base+1) 0 n writes to [0, n), so for r ≥ n, R[r] is preserved
      have hCopy_sl := copyRegisterRange_isStraightLine (base + 1) 0 n
      have hCopy_halted' : (⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ : Config).isHalted
          (copyRegisterRange (base + 1) 0 n) := by simp [Config.isHalted]
      have hsCopy_eq : sCopy = straightLineFinalState hCopy_sl sClear :=
        straightLineFinalState_eq_of_halted hCopy_sl sClear
          ⟨(copyRegisterRange (base + 1) 0 n).length, sCopy⟩ hCopy_steps hCopy_halted'

      -- r ≥ n means r is outside the write range [0, n)
      have hr_outside : r < 0 ∨ r ≥ 0 + n := Or.inr (by omega : r ≥ 0 + n)
      rw [hsCopy_eq, copyRegisterRange_preserves (base + 1) 0 n sClear r hr_outside]

      -- Now show sClear.read r = 0
      -- hClear_steps has starting state sSavePrefix (from the gPhase execution)
      -- Use straightLineFinalState_eq_of_halted to connect sClear to straightLineFinalState

      -- The starting state for clear is sSavePrefix (traced through the obtain chain)
      -- hGPhase_i_steps : Steps gPhase ⟨0, sSavePrefix⟩ _ (from hSuffix_steps starting at sSavePrefix)
      -- suffix_of_concat_from_zero preserves the starting state: clear starts from sSavePrefix

      have hsClear_eq : sClear = straightLineFinalState hClear_sl sSavePrefix :=
        straightLineFinalState_eq_of_halted hClear_sl sSavePrefix
          ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'
      rw [hsClear_eq]
      exact clearRegisters_zeros' base sSavePrefix r hr_le_base

  -- Use Halts.of_agreeing_state to conclude Halts (pGs i) (List.ofFn inputs)
  have hGi_halts : Halts (pGs i) (List.ofFn inputs) :=
    Halts.of_agreeing_state hGi_steps hGi_halted hagreeGi

  -- By hGs_spec, Halts → Dom
  exact (hGs_spec i inputs).1.mp hGi_halts

/-- If the composition halts and all gᵢ are defined, then f is defined. -/
theorem comp_general_halts_imp_f_dom
    {m n : ℕ} [NeZero m]
    {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hF_sf : pF.IsStandardForm)
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs))
    (hGs_dom : ∀ i, (gs i inputs).Dom) :
    (f (fun i => (gs i inputs).get (hGs_dom i))).Dom := by
  -- Setup
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF

  -- Standard form facts
  have hSaveInputs_sf := saveInputs_isStandardForm base n
  have hGPhases_sf : gPhases.IsStandardForm := allGPhases_isStandardForm hGs_sf
  have hFinal_sf : final.IsStandardForm := finalPhase_isStandardForm hF_sf

  -- Program structure: H = saveInputs ++ (gPhases ++ final)
  have hH_eq : Program.composeGeneral m n pF pGs = saveInputs.concat (gPhases.concat final) := rfl

  -- Rewrite as (saveInputs ++ gPhases) ++ final
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf
  rw [hH_eq, ← concat_assoc] at hHalts

  -- Extract: saveInputs ++ gPhases halts (as prefix)
  have hSaveGPhases_halts := Halts.prefix_of_concat_sf hHalts hSaveGPhases_sf

  -- Extract: suffix execution (final phase) from the combined program
  obtain ⟨sFinal_start, hSaveGPhases_halts', hsFinal_start_eq', cFinal, hFinal_steps, hFinal_halted⟩ :=
    Halts.suffix_of_concat_sf hHalts hSaveGPhases_sf

  -- final = clear ++ (transfer ++ F)
  have hClear_sf := straightLine_isStandardForm (clearRegisters_isStraightLine base)
  have hTransfer_sf := straightLine_isStandardForm (transferResultsToInputs_isStraightLine (base + n + 1) m)

  -- Split final: clear halts, then (transfer ++ F) halts
  obtain ⟨sClear, hClear_steps, ⟨cTF, hTF_steps, hTF_halted⟩⟩ :=
    suffix_of_concat_from_zero hFinal_steps hFinal_halted hClear_sf

  -- Split transfer ++ F: transfer halts, then F halts
  obtain ⟨sTransfer, hTransfer_steps, ⟨cF, hF_steps, hF_halted⟩⟩ :=
    suffix_of_concat_from_zero hTF_steps hTF_halted hTransfer_sf

  -- Now we need to show that sTransfer agrees with the g results
  -- For each i < m, sTransfer.read i = (gs i inputs).get (hGs_dom i)

  -- First, by hGs_spec, each gs i inputs has a value via the halting gi
  have hGi_halts : ∀ i, Halts (pGs i) (List.ofFn inputs) := by
    intro i
    have hdom := hGs_dom i
    exact (hGs_spec i inputs).1.mpr hdom

  have hGi_results : ∀ i, ∃ v, Result (pGs i) (List.ofFn inputs) (hGi_halts i) = v ∧
      v = (gs i inputs).get (hGs_dom i) := by
    intro i
    use (gs i inputs).get (hGs_dom i)
    constructor
    · exact (hGs_spec i inputs).2 (hGi_halts i) (hGs_dom i)
    · rfl

  -- The key is that after all gPhases, R[base+n+1+i] = result of gi
  -- And transferResultsToInputs copies these to R[i]
  -- So sTransfer.read i = result of gi for i < m

  -- For now, we show state agreement for F
  have hagreeF : ∀ r, r ≤ pF.maxRegister →
      sTransfer.read r = (State.fromInputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r := by
    intro r hr
    -- r ≤ pF.maxRegister ≤ base
    have hr_le_base : r ≤ base := Nat.le_trans hr (compositionBase_ge_F m n pF pGs)
    -- Two cases: r < m (input to F) or r ≥ m (should be 0)
    rcases Nat.lt_or_ge r m with hr_lt_m | hr_ge_m
    · -- r < m: sTransfer.read r = gs r result
      -- 1. transferResults copies R[base+n+1+r] to R[r]
      -- 2. clear preserves R[base+n+1+r] since base+n+1+r > base
      -- 3. After allGPhases, R[base+n+1+r] = result of g_r

      -- RHS value
      have hRHS : (State.fromInputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r =
          (gs ⟨r, hr_lt_m⟩ inputs).get (hGs_dom ⟨r, hr_lt_m⟩) := by
        simp only [State.fromInputs, State.read]
        rw [List.getD_eq_getElem (List.ofFn _) 0 (by simp; exact hr_lt_m), List.getElem_ofFn]

      -- Connect sClear and sTransfer to straightLineFinalState
      have hClear_sl := clearRegisters_isStraightLine base
      have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
          (clearRegisters base) := by simp [Config.isHalted]
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sFinal_start :=
        straightLineFinalState_eq_of_halted hClear_sl sFinal_start
          ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'

      have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m
      have hTransfer_halted' : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).isHalted
          (transferResultsToInputs (base + n + 1) m) := by simp [Config.isHalted]
      have hsTransfer_eq : sTransfer = straightLineFinalState hTransfer_sl sClear :=
        straightLineFinalState_eq_of_halted hTransfer_sl sClear
          ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ hTransfer_steps hTransfer_halted'

      -- Step 1: sTransfer.read r = sClear.read (base+n+1+r)
      -- Using transferResultsToInputs_state
      have hNoOverlap_transfer : m ≤ base + n + 1 := by
        have h := compositionBase_ge_m_sub_one m n pF pGs
        omega
      obtain ⟨sTransfer', hsTransfer'_eq, hTransfer_copies, _⟩ :=
        transferResultsToInputs_state (base + n + 1) m sClear hNoOverlap_transfer
      have hTransfer_r : sTransfer.read r = sClear.read (base + n + 1 + r) := by
        rw [hsTransfer_eq, hsTransfer'_eq]
        exact hTransfer_copies r hr_lt_m

      -- Step 2: sClear.read (base+n+1+r) = sFinal_start.read (base+n+1+r)
      -- clear preserves registers > base
      have hr_saved_gt_base : base < base + n + 1 + r := by omega
      have hClear_preserves : sClear.read (base + n + 1 + r) = sFinal_start.read (base + n + 1 + r) := by
        rw [hsClear_eq]
        exact clearRegisters_preserves_above' base sFinal_start (base + n + 1 + r) hr_saved_gt_base

      -- Step 3: sFinal_start.read (base+n+1+r) = result of g_r
      -- Use allGPhases_saves_result helper
      have hSavedResult : sFinal_start.read (base + n + 1 + r) =
          (gs ⟨r, hr_lt_m⟩ inputs).get (hGs_dom ⟨r, hr_lt_m⟩) := by
        -- sFinal_start is the state after saveInputs ++ gPhases halts
        -- hsFinal_start_eq' says sFinal_start = (Classical.choose hSaveGPhases_halts').state
        have h1 : sFinal_start = (Classical.choose hSaveGPhases_halts').state :=
          hsFinal_start_eq' hSaveGPhases_halts'
        -- Get the canonical witness
        have hspec := Classical.choose_spec hSaveGPhases_halts'
        let cSaveGPhases := Classical.choose hSaveGPhases_halts'
        have hSaveGPhases_steps := hspec.1
        have hSaveGPhases_halted'' := hspec.2
        -- sFinal_start = cSaveGPhases.state
        have hsFinal_start_eq : sFinal_start = cSaveGPhases.state := h1
        rw [hsFinal_start_eq]
        exact allGPhases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨r, hr_lt_m⟩
          (sSaveGPhases := cSaveGPhases.state)
          ⟨cSaveGPhases, hSaveGPhases_steps, hSaveGPhases_halted'', rfl⟩

      rw [hRHS, hTransfer_r, hClear_preserves, hSavedResult]
    · -- r ≥ m: should be 0
      have hRHS_zero : (State.fromInputs (List.ofFn (fun i => (gs i inputs).get (hGs_dom i)))).read r = 0 := by
        simp only [State.fromInputs, State.read, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; exact hr_ge_m)]
        rfl
      rw [hRHS_zero]
      -- After clear and transfer, R[r] = 0 for r ≥ m
      -- clear sets R[0..base] to 0
      -- transfer only writes to R[0..m-1]
      -- So R[r] for m ≤ r ≤ base is 0 (from clear)

      -- Connect sClear to straightLineFinalState
      have hClear_sl := clearRegisters_isStraightLine base
      have hClear_halted' : (⟨(clearRegisters base).length, sClear⟩ : Config).isHalted
          (clearRegisters base) := by simp [Config.isHalted]
      have hsClear_eq : sClear = straightLineFinalState hClear_sl sFinal_start :=
        straightLineFinalState_eq_of_halted hClear_sl sFinal_start
          ⟨(clearRegisters base).length, sClear⟩ hClear_steps hClear_halted'

      -- After clear, R[r] = 0 for r ≤ base
      have hsClear_zero : sClear.read r = 0 := by
        rw [hsClear_eq]
        exact clearRegisters_zeros' base sFinal_start r hr_le_base

      -- transfer preserves R[r] for r ≥ m
      have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m
      have hTransfer_halted' : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).isHalted
          (transferResultsToInputs (base + n + 1) m) := by simp [Config.isHalted]
      have hsTransfer_eq : sTransfer = straightLineFinalState hTransfer_sl sClear :=
        straightLineFinalState_eq_of_halted hTransfer_sl sClear
          ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ hTransfer_steps hTransfer_halted'

      rw [hsTransfer_eq, transferResultsToInputs_preserves (base + n + 1) m sClear r hr_ge_m, hsClear_zero]

  -- Use Halts.of_agreeing_state to conclude Halts pF (result inputs)
  have hF_halts : Halts pF (List.ofFn (fun i => (gs i inputs).get (hGs_dom i))) :=
    Halts.of_agreeing_state hF_steps hF_halted hagreeF

  -- By hF_spec, Halts → Dom
  exact (hF_spec (fun i => (gs i inputs).get (hGs_dom i))).1.mp hF_halts

set_option maxHeartbeats 800000 in
/-- If the composed function is defined, then the program halts. -/
theorem comp_general_dom_imp_halts
    {m n : ℕ} [NeZero m]
    {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hF_sf : pF.IsStandardForm)
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hDom : (compFunction m n f gs inputs).Dom) :
    Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs) := by
  -- Extract domain information from compFunction
  simp only [compFunction, Part.bind_dom] at hDom
  obtain ⟨hSeq_dom, hf_dom⟩ := hDom
  have hGs_dom : ∀ i, (gs i inputs).Dom := Part.sequence_dom.mp hSeq_dom

  -- Each Gi halts
  have hGi_halts : ∀ i, Halts (pGs i) (List.ofFn inputs) :=
    fun i => (hGs_spec i inputs).1.mpr (hGs_dom i)

  -- Get results
  let results : Fin m → ℕ := fun i => (gs i inputs).get (hGs_dom i)

  -- F halts on results
  have hf_dom' : (f results).Dom := by
    have h : results = (Part.sequence (fun i => gs i inputs)).get hSeq_dom := by
      funext i
      simp only [results, Part.sequence_get]
    rw [h]
    exact hf_dom
  have hF_halts := (hF_spec results).1.mpr hf_dom'

  -- Setup
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF

  -- Standard form facts
  have hSaveInputs_sf := saveInputs_isStandardForm base n
  have hGPhases_sf : gPhases.IsStandardForm := allGPhases_isStandardForm hGs_sf
  have hFinal_sf : final.IsStandardForm := finalPhase_isStandardForm hF_sf
  have hSaveGPhases_sf := hSaveInputs_sf.concat hGPhases_sf

  -- Program structure
  have hH_eq : Program.composeGeneral m n pF pGs = saveInputs.concat (gPhases.concat final) := rfl

  -- saveInputs halts (straight-line)
  have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
  have hSave_halts := straightLine_halts hSave_sl (List.ofFn inputs)
  have hSave_pc := straightLine_halts_at_length hSave_sl (List.ofFn inputs)

  -- Get state after saveInputs
  have hNoOverlap : 0 + n ≤ base + 1 := by simp; exact compositionBase_ge_n m n pF pGs
  obtain ⟨sSave, hsSave_eq, hSave_copies, hSave_preserves⟩ :=
    copyRegisterRange_state 0 (base + 1) n (State.fromInputs (List.ofFn inputs)) (Or.inl hNoOverlap)
  obtain ⟨cSave, hSave_steps, hSave_halted, hSave_pc'⟩ :=
    straightLine_halts_from_state hSave_sl (State.fromInputs (List.ofFn inputs))
  have hcSave_state : cSave.state = sSave := by
    rw [straightLineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps hSave_halted, hsSave_eq]

  -- Saved inputs after saveInputs
  have hSaved : ∀ j : ℕ, (hj : j < n) → sSave.read (base + 1 + j) = inputs ⟨j, hj⟩ := by
    intro j hj
    rw [hSave_copies j hj]
    simp only [State.fromInputs, State.read, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hj, ↓reduceDIte, Option.getD_some]

  -- allGPhases halts from sSave
  have hpGs_max : ∀ i, (pGs i).maxRegister ≤ base := fun i => compositionBase_ge_pGs_max m n pF pGs i
  have hn_le_base : n ≤ base + 1 := compositionBase_ge_n m n pF pGs
  obtain ⟨cGPhases, hGPhases_steps, hGPhases_halted⟩ :=
    allGPhases_halts_from_saved_inputs hGs_sf hpGs_max hn_le_base hGi_halts sSave hSaved

  -- Chain saveInputs with gPhases
  have hSave_halted' : (⟨saveInputs.length, sSave⟩ : Config).isHalted saveInputs := by
    simp [Config.isHalted]
  have hSave_steps' : Steps saveInputs ⟨0, State.fromInputs (List.ofFn inputs)⟩ ⟨saveInputs.length, sSave⟩ := by
    have : cSave = ⟨saveInputs.length, sSave⟩ := Config.ext hSave_pc' hcSave_state
    rw [← this]; exact hSave_steps
  have ⟨hSaveGPhases_steps, hSaveGPhases_halted⟩ := Steps.chain_concat hSave_steps' hSave_halted'
    rfl hGPhases_steps hGPhases_halted

  -- Get state after all gPhases
  have hGPhases_pc : cGPhases.pc = gPhases.length :=
    hGPhases_sf.pc_eq_length_of_halted hGPhases_steps (Nat.zero_le _) hGPhases_halted
  let sGPhases := cGPhases.state

  -- sGPhases has results at correct locations
  have hResults : ∀ j : ℕ, (hj : j < m) → sGPhases.read (base + n + 1 + j) = results ⟨j, hj⟩ := by
    intro j hj
    -- Use allGPhases_saves_result through proper extraction
    -- We have execution of saveInputs ++ gPhases that reaches cGPhases.state
    let sSaveGPhases := cGPhases.state
    have hSaveGPhases_halted' : ∃ c : Config,
        Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩ c ∧
        c.isHalted (saveInputs.concat gPhases) ∧ c.state = sSaveGPhases := by
      have hSaveGPhases_halted'' : (⟨(saveInputs.concat gPhases).length, sGPhases⟩ : Config).isHalted (saveInputs.concat gPhases) := by
        simp [Config.isHalted, Program.concat_length]
      have hchain_state_eq : sSaveGPhases = sGPhases := rfl
      refine ⟨⟨(saveInputs.concat gPhases).length, sGPhases⟩, ?_, hSaveGPhases_halted'', rfl⟩
      convert hSaveGPhases_steps using 2
      simp [Program.concat_length, hGPhases_pc, add_comm]
    have hres := allGPhases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨j, hj⟩ sSaveGPhases hSaveGPhases_halted'
    simp only [results]
    exact hres

  -- Saved inputs preserved after gPhases
  have hSaved_after_gPhases : ∀ j : ℕ, (hj : j < n) → sGPhases.read (base + 1 + j) = inputs ⟨j, hj⟩ := by
    intro j hj
    -- TODO: Need to use allGPhases_prefix_full to convert between allGPhases and allGPhases_prefix
    sorry

  -- finalPhase halts from sGPhases
  have hpF_max : pF.maxRegister ≤ base := compositionBase_ge_pF_max m n pF pGs
  have hm_le_base : m ≤ base + 1 := compositionBase_ge_m m n pF pGs
  obtain ⟨cFinal, hFinal_steps, hFinal_halted⟩ :=
    finalPhase_halts_from_results hF_sf hpF_max hm_le_base hF_halts sGPhases hResults

  -- Chain all together
  have hSaveGPhases_halted' : (⟨(saveInputs.concat gPhases).length, sGPhases⟩ : Config).isHalted (saveInputs.concat gPhases) := by
    simp [Config.isHalted]
  have hSaveGPhases_steps' : Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩
      ⟨(saveInputs.concat gPhases).length, sGPhases⟩ := by
    -- hSaveGPhases_steps goes to { pc := cGPhases.pc + saveInputs.length, state := cGPhases.state }
    -- which equals { pc := gPhases.length + saveInputs.length, state := sGPhases }
    have hpc_eq : cGPhases.pc + saveInputs.length = (saveInputs.concat gPhases).length := by
      simp only [Program.concat_length, hGPhases_pc]
      omega
    have hstate_eq : cGPhases.state = sGPhases := rfl
    have heq : (⟨cGPhases.pc + saveInputs.length, cGPhases.state⟩ : Config) =
        ⟨(saveInputs.concat gPhases).length, sGPhases⟩ := by
      ext <;> simp [hpc_eq, hstate_eq]
    rw [← heq]
    exact hSaveGPhases_steps
  have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hSaveGPhases_steps' hSaveGPhases_halted'
    rfl hFinal_steps hFinal_halted

  -- The total program is saveInputs ++ (gPhases ++ final)
  have hProg_eq : saveInputs.concat (gPhases.concat final) = (saveInputs.concat gPhases).concat final := by
    rw [concat_assoc]
  rw [hH_eq, hProg_eq]
  exact ⟨_, hTotal_steps, hTotal_halted⟩

/-- The result of the composition equals the composed function value. -/
theorem comp_general_result
    {m n : ℕ} [NeZero m]
    {pF : Program} {pGs : Fin m → Program}
    {f : (Fin m → ℕ) → Part ℕ}
    {gs : Fin m → (Fin n → ℕ) → Part ℕ}
    (hF_sf : pF.IsStandardForm)
    (hGs_sf : ∀ i, (pGs i).IsStandardForm)
    (hF_spec : ∀ inputs : Fin m → ℕ,
      (Halts pF (List.ofFn inputs) ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pF (List.ofFn inputs)) (hDom : (f inputs).Dom),
        Result pF (List.ofFn inputs) hHalts = (f inputs).get hDom)
    (hGs_spec : ∀ i, ∀ inputs : Fin n → ℕ,
      (Halts (pGs i) (List.ofFn inputs) ↔ (gs i inputs).Dom) ∧
      ∀ (hHalts : Halts (pGs i) (List.ofFn inputs)) (hDom : (gs i inputs).Dom),
        Result (pGs i) (List.ofFn inputs) hHalts = (gs i inputs).get hDom)
    (inputs : Fin n → ℕ)
    (hHalts : Halts (Program.composeGeneral m n pF pGs) (List.ofFn inputs))
    (hDom : (compFunction m n f gs inputs).Dom) :
    Result (Program.composeGeneral m n pF pGs) (List.ofFn inputs) hHalts =
      (compFunction m n f gs inputs).get hDom := by
  -- Setup
  let H := Program.composeGeneral m n pF pGs
  let base := compositionBase m n pF pGs
  let saveInputs := copyRegisterRange 0 (base + 1) n
  let gPhases := allGPhases m n base pGs
  let final := finalPhase m n base pF

  -- Extract g_i domain from hDom
  simp only [compFunction] at hDom
  have hSeq_dom : (Part.sequence fun i => gs i inputs).Dom := Part.bind_dom.mp hDom |>.1
  have hGs_dom : ∀ i, (gs i inputs).Dom := Part.sequence_dom.mp hSeq_dom

  -- Define results
  let results : Fin m → ℕ := fun i => (gs i inputs).get (hGs_dom i)

  -- f is defined on results
  have hf_dom : (f results).Dom := by
    have h := Part.bind_dom.mp hDom |>.2
    have harg_eq : (Part.sequence fun i => gs i inputs).get hSeq_dom = results := by
      funext i; exact Part.sequence_get hSeq_dom i
    rw [harg_eq] at h; exact h

  -- pF halts on results
  have hF_halts : Halts pF (List.ofFn results) := (hF_spec results).1.mpr hf_dom

  -- Get the canonical halted config for H
  let cH := Classical.choose hHalts
  have hH_spec := Classical.choose_spec hHalts
  have hH_steps : Steps H (Config.init (List.ofFn inputs)) cH := hH_spec.1
  have hH_halted : cH.isHalted H := hH_spec.2

  -- Get canonical halted config for pF on results
  let cF := Classical.choose hF_halts
  have hF_steps : Steps pF (Config.init (List.ofFn results)) cF := (Classical.choose_spec hF_halts).1
  have hF_halted : cF.isHalted pF := (Classical.choose_spec hF_halts).2
  have hF_pc : cF.pc = pF.length := hF_sf.halts_at_length (List.ofFn results) cF hF_steps hF_halted

  -- Bounds
  have hpF_max : pF.maxRegister ≤ base := compositionBase_ge_pF_max m n pF pGs
  have hpGs_max : ∀ i, (pGs i).maxRegister ≤ base := fun i => compositionBase_ge_pGs_max m n pF pGs i
  have hn_le_base : n ≤ base + 1 := compositionBase_ge_n m n pF pGs
  have hm_le_base : m ≤ base + 1 := compositionBase_ge_m m n pF pGs

  -- g_i halts for each i
  have hGi_halts : ∀ i, Halts (pGs i) (List.ofFn inputs) :=
    fun i => (hGs_spec i inputs).1.mpr (hGs_dom i)

  -- Standard form facts
  have hH_sf := composeGeneral_isStandardForm (n := n) hF_sf hGs_sf
  have hSave_sf := saveInputs_isStandardForm base n
  have hGPhases_sf := allGPhases_isStandardForm (n := n) (base := base) hGs_sf

  -- Execute saveInputs
  have hSave_sl := copyRegisterRange_isStraightLine 0 (base + 1) n
  have hSave_sf := straightLine_isStandardForm hSave_sl
  obtain ⟨cSave, hSave_steps, hSave_halted, hSave_pc'⟩ := straightLine_halts_from_state hSave_sl (State.fromInputs (List.ofFn inputs))
  have hNoOverlap' : 0 + n ≤ base + 1 := by simp; exact compositionBase_ge_n m n pF pGs
  obtain ⟨sSave, hsSave_eq, hSave_copies, hSave_preserves⟩ := copyRegisterRange_state 0 (base + 1) n (State.fromInputs (List.ofFn inputs)) (Or.inl hNoOverlap')
  have hcSave_state : cSave.state = sSave := by
    rw [straightLineFinalState_eq_of_halted hSave_sl _ cSave hSave_steps hSave_halted, hsSave_eq]

  -- Saved inputs after saveInputs
  have hSaved : ∀ j : ℕ, (hj : j < n) → sSave.read (base + 1 + j) = inputs ⟨j, hj⟩ := by
    intro j hj
    rw [hSave_copies j hj]
    simp only [State.fromInputs, State.read, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hj, ↓reduceDIte, Option.getD_some]

  -- allGPhases halts from sSave
  obtain ⟨cGPhases, hGPhases_steps, hGPhases_halted⟩ :=
    allGPhases_halts_from_saved_inputs hGs_sf hpGs_max hn_le_base hGi_halts sSave hSaved

  -- Chain saveInputs with gPhases
  have hSave_halted' : (⟨saveInputs.length, sSave⟩ : Config).isHalted saveInputs := by simp [Config.isHalted]
  have hSave_steps' : Steps saveInputs ⟨0, State.fromInputs (List.ofFn inputs)⟩ ⟨saveInputs.length, sSave⟩ := by
    have : cSave = ⟨saveInputs.length, sSave⟩ := Config.ext hSave_pc' hcSave_state
    rw [← this]; exact hSave_steps
  have ⟨hSaveGPhases_steps, hSaveGPhases_halted⟩ := Steps.chain_concat hSave_steps' hSave_halted' rfl hGPhases_steps hGPhases_halted

  -- Get state after all gPhases
  have hGPhases_pc : cGPhases.pc = gPhases.length :=
    hGPhases_sf.pc_eq_length_of_halted hGPhases_steps (Nat.zero_le _) hGPhases_halted
  let sGPhases := cGPhases.state

  -- sGPhases has results at correct locations (use allGPhases_saves_result)
  have hResults : ∀ j : ℕ, (hj : j < m) → sGPhases.read (base + n + 1 + j) = results ⟨j, hj⟩ := by
    intro j hj
    let sSaveGPhases := cGPhases.state
    have hSaveGPhases_halted' : ∃ c : Config,
        Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩ c ∧
        c.isHalted (saveInputs.concat gPhases) ∧ c.state = sSaveGPhases := by
      have hSaveGPhases_halted'' : (⟨(saveInputs.concat gPhases).length, sGPhases⟩ : Config).isHalted (saveInputs.concat gPhases) := by
        simp [Config.isHalted, Program.concat_length]
      -- TODO: Config equality proof needs fixing
      sorry
    have hres := allGPhases_saves_result (pF := pF) hGs_sf hGs_spec inputs hGs_dom ⟨j, hj⟩ sSaveGPhases hSaveGPhases_halted'
    simp only [results]; exact hres

  -- Execute finalPhase from sGPhases
  -- finalPhase = clear ++ (transfer ++ pF)
  -- After clear+transfer: R[0..m-1] = results, R[m..base] = 0, agreeing with fromInputs results

  -- State agreement for pF: after clear+transfer, agrees with List.ofFn results
  have hagree_pF : ∀ sSetup : State,
      (∀ j : ℕ, (hj : j < m) → sSetup.read j = results ⟨j, hj⟩) →
      (∀ r, m ≤ r → r ≤ base → sSetup.read r = 0) →
      sSetup.agreeOn (State.fromInputs (List.ofFn results)) 0 pF.maxRegister := by
    intro sSetup hInputs hZeros
    apply agrees_list_inputs_after_clear_transfer hpF_max
    · intro i hi
      simp only [List.length_ofFn] at hi
      rw [hInputs i hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
    · intro r hr_ge hr_le
      simp only [List.length_ofFn] at hr_ge
      exact hZeros r hr_ge hr_le

  -- Get final state after clear + transfer
  have hClear_sl := clearRegisters_isStraightLine base
  have hTransfer_sl := transferResultsToInputs_isStraightLine (base + n + 1) m

  -- Clear halts from sGPhases
  obtain ⟨cClear, hClear_steps, hClear_halted, hClear_pc, hClear_zeros, hClear_preserves⟩ :=
    clearRegisters_exec base sGPhases

  -- After clear, results still there
  have hResults_after_clear : ∀ j : ℕ, (hj : j < m) → cClear.state.read (base + n + 1 + j) = results ⟨j, hj⟩ :=
    fun j hj => by rw [hClear_preserves (base + n + 1 + j) (by omega)]; exact hResults j hj

  -- Transfer halts and sets up inputs
  have hNoOverlap : m ≤ base + n + 1 := by omega
  obtain ⟨sTransfer, hsTransfer_eq, hTransfer_correct, hTransfer_preserves⟩ :=
    transferResultsToInputs_state (base + n + 1) m cClear.state hNoOverlap

  obtain ⟨cTransfer, hTransfer_steps', hTransfer_halted', hTransfer_pc⟩ :=
    straightLine_halts_from_state hTransfer_sl cClear.state
  have hTransfer_state_eq : cTransfer.state = straightLineFinalState hTransfer_sl cClear.state :=
    straightLineFinalState_eq_of_halted hTransfer_sl cClear.state cTransfer hTransfer_steps' hTransfer_halted'
  have hTransfer_state_sTransfer : cTransfer.state = sTransfer := by rw [hTransfer_state_eq, hsTransfer_eq]

  -- After transfer, R[0..m-1] = results
  have hInputs_set : ∀ j : ℕ, (hj : j < m) → sTransfer.read j = results ⟨j, hj⟩ := by
    intro j hj; rw [hTransfer_correct j hj, hResults_after_clear j hj]

  -- R[m..base] = 0 after transfer
  have hZeros_set : ∀ r, m ≤ r → r ≤ base → sTransfer.read r = 0 := by
    intro r hr_ge hr_le
    rw [hTransfer_preserves r (by omega), hClear_zeros r (by omega)]

  -- State agrees for pF execution
  have hagree : sTransfer.agreeOn (State.fromInputs (List.ofFn results)) 0 pF.maxRegister :=
    hagree_pF sTransfer hInputs_set hZeros_set

  -- pF halts from sTransfer via agreeing execution
  let epF := Halts.executeFromAgreeingState hF_halts hF_sf hagree
  have hpF_steps' := epF.steps
  have hpF_halted' := epF.halted

  -- The output matches: epF.config.state.output = cF.state.output
  have hOutput_eq : epF.config.state.read 0 = cF.state.read 0 := by
    have h := AgreeingExecution.result_matches_original epF
    simp only [Result] at h
    have hcF_eq : Classical.choose hF_halts = cF := rfl
    rw [hcF_eq] at h
    exact h

  -- Build execution in H from start to epF final state
  -- H = saveInputs ++ (gPhases ++ final)
  -- final = clear ++ (transfer ++ pF)
  have hH_eq : H = saveInputs.concat (gPhases.concat final) := rfl

  -- Chain clear with (transfer ++ pF)
  have hTransfer_steps : Steps (transferResultsToInputs (base + n + 1) m) ⟨0, cClear.state⟩
      ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
    have : cTransfer = ⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ := by
      ext <;> simp only [hTransfer_pc, hTransfer_state_sTransfer]
    rw [← this]; exact hTransfer_steps'
  have hTransfer_halted : (⟨(transferResultsToInputs (base + n + 1) m).length, sTransfer⟩ : Config).isHalted
      (transferResultsToInputs (base + n + 1) m) := by simp [Config.isHalted]

  have ⟨hTransferF_steps, hTransferF_halted⟩ := Steps.chain_concat hTransfer_steps hTransfer_halted
    rfl hpF_steps' hpF_halted'

  have ⟨hClearTransferF_steps, hClearTransferF_halted⟩ := Steps.chain_concat hClear_steps hClear_halted
    hClear_pc hTransferF_steps hTransferF_halted

  -- Chain saveInputs ++ gPhases with final
  have hSaveGPhases_halted' : (⟨(saveInputs.concat gPhases).length, sGPhases⟩ : Config).isHalted (saveInputs.concat gPhases) := by
    simp [Config.isHalted]
  have hSaveGPhases_steps' : Steps (saveInputs.concat gPhases) ⟨0, State.fromInputs (List.ofFn inputs)⟩
      ⟨(saveInputs.concat gPhases).length, sGPhases⟩ := by
    have hpc_eq : cGPhases.pc + saveInputs.length = (saveInputs.concat gPhases).length := by
      simp only [Program.concat_length, hGPhases_pc]
      omega
    have hstate_eq : cGPhases.state = sGPhases := rfl
    have heq : (⟨cGPhases.pc + saveInputs.length, cGPhases.state⟩ : Config) =
        ⟨(saveInputs.concat gPhases).length, sGPhases⟩ := by
      ext <;> simp [hpc_eq, hstate_eq]
    rw [← heq]
    exact hSaveGPhases_steps

  have ⟨hTotal_steps, hTotal_halted⟩ := Steps.chain_concat hSaveGPhases_steps' hSaveGPhases_halted'
    rfl hClearTransferF_steps hClearTransferF_halted

  -- The total program is saveInputs ++ (gPhases ++ final)
  have hProg_eq : saveInputs.concat (gPhases.concat final) = (saveInputs.concat gPhases).concat final := by
    rw [concat_assoc]
  rw [hH_eq, hProg_eq] at hH_steps hH_halted

  -- The final state of our built execution
  let cH_built : Config := ⟨(saveInputs.concat gPhases).length + final.length + epF.config.pc - pF.length,
                            epF.config.state⟩

  -- Show cH_built equals the unique halted config
  have hcH_built_halted : cH_built.isHalted ((saveInputs.concat gPhases).concat final) := by
    -- TODO: Arithmetic simplification needs work
    sorry

  have hH_steps_built : Steps ((saveInputs.concat gPhases).concat final)
      ⟨0, State.fromInputs (List.ofFn inputs)⟩ cH_built := by
    -- TODO: Arithmetic conversion from hTotal_steps
    sorry

  have hcH_eq := Steps.halts_unique hH_steps hH_halted hH_steps_built hcH_built_halted

  -- Final calculation
  have hResult_eq : cH.state.read 0 = cF.state.read 0 := by
    calc cH.state.read 0 = cH_built.state.read 0 := by rw [hcH_eq]
      _ = epF.config.state.read 0 := rfl
      _ = cF.state.read 0 := hOutput_eq

  -- Connect to compFunction
  calc Result H (List.ofFn inputs) hHalts
      = cH.state.output := rfl
    _ = cH.state.read 0 := rfl
    _ = cF.state.read 0 := hResult_eq
    _ = Result pF (List.ofFn results) hF_halts := rfl
    _ = (f results).get hf_dom := (hF_spec results).2 hF_halts hf_dom
    _ = (compFunction m n f gs inputs).get hDom := by
        simp only [compFunction, Part.Dom.bind hSeq_dom]
        congr 2
        funext i
        exact (Part.sequence_get hSeq_dom i).symm

end Urm
