/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Simulate.StepPrimrec
import Urm.Partrec
import Mathlib.Computability.Partrec



/-! # URM Computability implies Partial Recursiveness

This file proves the main theorem: every URM-computable function is partial recursive.

## Main results

- `URMComputable1.toPartrec`: Every URM-computable unary function is `Nat.Partrec`

## Strategy

Given `URMComputable1 f`, we have a program `p` that computes `f`. We show `f` is
partial recursive by:

1. Encoding configurations as natural numbers
2. Using μ-recursion (rfind) to find the first halting step
3. Extracting the output from register 0

The key technical lemmas are:
- `encodedStep_primrec_fixed`: The step function is primitive recursive (for fixed program)
- `iterateEncodedStep_correct`: Iteration correctly simulates multi-step execution
-/

namespace Urm

/-! ## Finding the Halting Step -/

/-- Predicate: has the encoded configuration halted at exactly n steps?
    Returns true if halted at step n. -/
def isHaltedAtStep (progCode bound inputConfig : ℕ) (n : ℕ) : Bool :=
  encodedIsHalted progCode (iterateEncodedStep progCode bound n inputConfig)

/-- Extract output (register 0) from an encoded configuration. -/
def extractOutput (configCode : ℕ) : ℕ :=
  nthEncoded 0 configCode.unpair.2

/-- Partial evaluation: find the halting step and extract output.
    This is the partial recursive simulation of URM evaluation. -/
noncomputable def evalEncoded (progCode bound inputConfig : ℕ) : Part ℕ :=
  -- Use rfind to find first n where isHaltedAtStep returns true
  (Nat.rfind fun n => Part.some (isHaltedAtStep progCode bound inputConfig n)).map
    fun n => extractOutput (iterateEncodedStep progCode bound n inputConfig)

/-! ## Primitive Recursiveness of Helper Functions -/

/-- extractOutput is primitive recursive. -/
theorem extractOutput_primrec : Nat.Primrec extractOutput := by
  -- extractOutput configCode = nthEncoded 0 configCode.unpair.2
  -- = configCode.unpair.2.unpair.1
  unfold extractOutput
  simp only [nthEncoded_zero]
  exact Nat.Primrec.left.comp Nat.Primrec.right

/-! ## Correctness of Simulation -/

/-- The initial encoded configuration for a single input. -/
def encodeInput1 (bound : ℕ) (input : ℕ) : ℕ :=
  encodeConfig bound (Config.init [input])

/-- Connection between encodedIsHalted and Config.isHalted. -/
theorem encodedIsHalted_iff_isHalted (p : Program) (c : Config) :
    encodedIsHalted (encodeProgram p) (encodeConfig p.maxRegister c) ↔ c.isHalted p := by
  simp only [encodedIsHalted, encodeProgram, encodeConfig, Nat.unpair_pair, Config.isHalted]
  -- LHS: decide (p.length ≤ c.pc) = true
  -- RHS: p.length ≤ c.pc
  simp only [decide_eq_true_eq]

/-- extractOutput correctly extracts register 0. -/
theorem extractOutput_encodeConfig (bound : ℕ) (c : Config) (h : 0 ≤ bound) :
    extractOutput (encodeConfig bound c) = c.state 0 := by
  simp only [extractOutput]
  exact nthEncoded_encodeConfig_regs bound c 0 h

/-- isHaltedAtStep correctly reflects halting status. -/
theorem isHaltedAtStep_correct (p : Program) (n : ℕ) (c c' : Config)
    (hsteps : StepsN p n c c') :
    let bound := p.maxRegister
    let progCode := encodeProgram p
    let inputConfig := encodeConfig bound c
    isHaltedAtStep progCode bound inputConfig n ↔ c'.isHalted p := by
  simp only [isHaltedAtStep]
  rw [iterateEncodedStep_correct p n c c' hsteps]
  exact encodedIsHalted_iff_isHalted p c'

/-! ## Helper Lemmas for evalEncoded_correct -/

/-- If a configuration is not halted, a step exists. -/
theorem Step.of_not_halted (p : Program) (c : Config) (h : ¬c.isHalted p) :
    ∃ c', Step p c c' := by
  simp only [Config.isHalted, Nat.not_le] at h
  have hinstr : p.getInstr c.pc ≠ none := by
    simp only [Program.getInstr, ne_eq]
    intro heq
    rw [List.getElem?_eq_none_iff] at heq
    exact Nat.not_lt.mpr heq h
  obtain ⟨instr, hinstr'⟩ := Option.ne_none_iff_exists'.mp hinstr
  cases instr with
  | Z n => exact ⟨⟨c.pc + 1, c.state.write n 0⟩, Step.zero hinstr'⟩
  | S n => exact ⟨⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩, Step.succ hinstr'⟩
  | T m n => exact ⟨⟨c.pc + 1, c.state.write n (c.state.read m)⟩, Step.trans hinstr'⟩
  | J m n q =>
    by_cases heq : c.state.read m = c.state.read n
    · exact ⟨⟨q, c.state⟩, Step.jump_eq hinstr' heq⟩
    · exact ⟨⟨c.pc + 1, c.state⟩, Step.jump_ne hinstr' heq⟩

/-- If no configuration before step n is halted, we can build StepsN p n. -/
theorem stepsN_of_not_halted_before (p : Program) (input : ℕ) (n : ℕ)
    (hBefore : ∀ m < n, isHaltedAtStep (encodeProgram p) p.maxRegister
        (encodeInput1 p.maxRegister input) m = false) :
    ∃ c', StepsN p n (Config.init [input]) c' := by
  induction n with
  | zero => exact ⟨Config.init [input], StepsN.zero _⟩
  | succ n ih =>
    have hBefore' : ∀ m < n, isHaltedAtStep (encodeProgram p) p.maxRegister
        (encodeInput1 p.maxRegister input) m = false :=
      fun m hm => hBefore m (Nat.lt_trans hm (Nat.lt_succ_self n))
    obtain ⟨c_n, hstepsN⟩ := ih hBefore'
    have hn_false := hBefore n (Nat.lt_succ_self n)
    have h_not_halted : ¬c_n.isHalted p := by
      let hcorrect := isHaltedAtStep_correct p n (Config.init [input]) c_n hstepsN
      unfold encodeInput1 at hn_false
      intro hHalted
      let htrue := hcorrect.mpr hHalted
      simp only [htrue] at hn_false
      exact nomatch hn_false
    obtain ⟨c', hstep⟩ := Step.of_not_halted p c_n h_not_halted
    have h1 : StepsN p 1 c_n c' := StepsN.succ hstep (StepsN.zero _)
    exact ⟨c', StepsN.add hstepsN h1⟩

/-- If StepsN p n c c_final with c_final halted, then for m < n,
    the config at step m from c is not halted. -/
theorem stepsN_before_halted (p : Program) (n : ℕ) (c c_final : Config)
    (hStepsN : StepsN p n c c_final) (hHalted : c_final.isHalted p) :
    ∀ m < n, ∃ c_m, StepsN p m c c_m ∧ ¬c_m.isHalted p := by
  intro m hm
  induction m generalizing c n with
  | zero =>
    use c, StepsN.zero c
    intro hc_halted
    cases hStepsN with
    | zero => omega
    | succ hstep _ => exact Step.halted_no_step hc_halted hstep
  | succ m ih =>
    match hStepsN with
    | .zero _ => omega
    | .succ hstep hrest =>
      have hm' : m < _ := Nat.lt_of_succ_lt_succ hm
      obtain ⟨c_m', hstepsM', hnot_halted⟩ := ih _ _ hrest hm'
      exact ⟨c_m', StepsN.succ hstep hstepsM', hnot_halted⟩

/-- isHaltedAtStep is false for all m < n when there's StepsN p n to halted config. -/
theorem isHaltedAtStep_false_before (p : Program) (n : ℕ) (c c_final : Config)
    (hStepsN : StepsN p n c c_final) (hHalted : c_final.isHalted p) :
    ∀ m < n, isHaltedAtStep (encodeProgram p) p.maxRegister (encodeConfig p.maxRegister c) m = false := by
  intro m hm
  obtain ⟨c_m, hstepsM, hnot_halted⟩ := stepsN_before_halted p n c c_final hStepsN hHalted m hm
  have hcorrect := isHaltedAtStep_correct p m c c_m hstepsM
  by_contra h
  have h' : isHaltedAtStep (encodeProgram p) p.maxRegister (encodeConfig p.maxRegister c) m = true := by
    cases h'' : isHaltedAtStep (encodeProgram p) p.maxRegister (encodeConfig p.maxRegister c) m with
    | true => rfl
    | false => exact absurd h'' h
  exact hnot_halted (hcorrect.mp h')

/-- The output of any halted config reachable from init equals Result. -/
theorem halted_output_eq_Result (p : Program) (inputs : List ℕ) (c : Config)
    (hSteps : Steps p (Config.init inputs) c) (hHalted : c.isHalted p)
    (hHalts : Halts p inputs) :
    c.state.output = Result p inputs hHalts := by
  unfold Result
  have h_chosen := Classical.choose_spec hHalts
  obtain ⟨hSteps_chosen, hHalted_chosen⟩ := h_chosen
  have h_unique := Steps.halts_unique hSteps hHalted hSteps_chosen hHalted_chosen
  simp only [h_unique]

/-- Simulation correctness: evalEncoded computes the same result as eval. -/
theorem evalEncoded_correct (p : Program) (input : ℕ) :
    let bound := p.maxRegister
    let progCode := encodeProgram p
    let inputConfig := encodeInput1 bound input
    evalEncoded progCode bound inputConfig = eval p [input] := by
  apply Part.ext
  intro result
  constructor
  -- Forward: result ∈ evalEncoded → result ∈ eval
  · intro hmem_enc
    simp only [evalEncoded] at hmem_enc
    rw [Part.mem_map_iff] at hmem_enc
    obtain ⟨n, hn_mem, hresult_eq⟩ := hmem_enc
    rw [Nat.mem_rfind] at hn_mem
    obtain ⟨htrue_n, hfalse_before⟩ := hn_mem
    simp only [Part.mem_some_iff] at htrue_n hfalse_before
    have hBefore : ∀ m < n, isHaltedAtStep (encodeProgram p) p.maxRegister
        (encodeInput1 p.maxRegister input) m = false :=
      fun m hm => (hfalse_before hm).symm
    obtain ⟨c', hstepsN⟩ := stepsN_of_not_halted_before p input n hBefore
    have hhalted : c'.isHalted p := by
      let hcorrect := isHaltedAtStep_correct p n (Config.init [input]) c' hstepsN
      unfold encodeInput1 at htrue_n
      exact hcorrect.mp htrue_n.symm
    have hHalts : Halts p [input] := ⟨c', StepsN.toSteps hstepsN, hhalted⟩
    simp only [eval, Part.mem_mk_iff]
    use hHalts
    have h_iter := iterateEncodedStep_correct p n (Config.init [input]) c' hstepsN
    rw [← hresult_eq]
    unfold encodeInput1
    rw [h_iter]
    have h_extract := extractOutput_encodeConfig p.maxRegister c' (Nat.zero_le _)
    rw [h_extract]
    exact (halted_output_eq_Result p [input] c' (StepsN.toSteps hstepsN) hhalted hHalts).symm
  -- Backward: result ∈ eval → result ∈ evalEncoded
  · intro hmem_eval
    simp only [eval, Part.mem_mk_iff] at hmem_eval
    obtain ⟨hHalts, hresult_eq⟩ := hmem_eval
    obtain ⟨c, hSteps, hHalted⟩ := hHalts
    obtain ⟨n, hStepsN⟩ := StepsN.fromSteps hSteps
    simp only [evalEncoded]
    rw [Part.mem_map_iff]
    use n
    constructor
    · rw [Nat.mem_rfind]
      constructor
      · simp only [Part.mem_some_iff]
        have hcorrect := isHaltedAtStep_correct p n (Config.init [input]) c hStepsN
        unfold encodeInput1
        exact (hcorrect.mpr hHalted).symm
      · intro m hm
        simp only [Part.mem_some_iff]
        unfold encodeInput1
        exact (isHaltedAtStep_false_before p n (Config.init [input]) c hStepsN hHalted m hm).symm
    · have h_iter := iterateEncodedStep_correct p n (Config.init [input]) c hStepsN
      unfold encodeInput1
      rw [h_iter]
      have h_extract := extractOutput_encodeConfig p.maxRegister c (Nat.zero_le _)
      rw [h_extract]
      rw [← hresult_eq]
      have hHalts' : Halts p [input] := ⟨c, hSteps, hHalted⟩
      exact halted_output_eq_Result p [input] c hSteps hHalted hHalts'

/-! ## Main Theorem -/

/-- Every URM-computable unary function is partial recursive.

Strategy:
1. Get the program p that computes f from URMComputable1 f
2. Show evalEncoded (for fixed p) is partial recursive:
   - encodeInput1 is primitive recursive (for fixed bound)
   - isHaltedAtStep is primitive recursive (for fixed progCode, bound, inputConfig)
   - rfind on a primitive recursive predicate is partial recursive
   - extractOutput is primitive recursive
   - Composition of these is partial recursive
3. Show evalEncoded correctly computes f:
   - iterateEncodedStep correctly simulates StepsN
   - The halting step found by rfind gives the final configuration
   - extractOutput extracts register 0, matching eval's Result
-/
theorem URMComputable1.toPartrec' {f : ℕ →. ℕ} (hf : URMComputable1 f) :
    Nat.Partrec f := by
  -- Extract the program from URMComputable1
  obtain ⟨p, hp⟩ := hf
  -- Define constants for this fixed program
  let progCode := encodeProgram p
  let bound := p.maxRegister
  -- Step 1: Show eval p [n] = f n
  have heval : ∀ n, eval p [n] = f n := by
    intro n
    let hp_n := hp (fun _ => n)
    simp only [List.ofFn_const, List.replicate] at hp_n
    obtain ⟨hiff, hres⟩ := hp_n
    ext m
    simp only [eval, Part.mem_mk_iff]
    constructor
    · rintro ⟨hHalts, rfl⟩
      let hDom := hiff.mp hHalts
      let heq := hres hHalts hDom
      rw [heq]
      exact Part.get_mem hDom
    · intro hm
      let hDom : (f n).Dom := Part.dom_iff_mem.mpr ⟨m, hm⟩
      let hHalts := hiff.mpr hDom
      refine ⟨hHalts, ?_⟩
      let heq := hres hHalts hDom
      rw [heq]
      exact Part.mem_unique (Part.get_mem hDom) hm
  -- Step 2: Show evalEncoded equals eval via evalEncoded_correct
  have henc_correct : ∀ n, evalEncoded progCode bound (encodeInput1 bound n) = f n := by
    intro n
    rw [← heval n]
    exact evalEncoded_correct p n
  -- Step 3: Build Nat.Partrec for evalEncoded
  -- First, show encodeInput1 is primrec for fixed bound
  have hEnc1 : Nat.Primrec (encodeInput1 bound) := by
    -- encodeInput1 bound input = pair 0 (pair input C) where C is constant
    unfold encodeInput1 encodeConfig Config.init
    simp only [State.fromInputs]
    let C := encodeRegs (List.replicate bound 0)
    let heq : ∀ input, encodeRegs (List.ofFn fun i : Fin (bound + 1) =>
        List.getD [input] i 0) = Nat.pair input C := by
      intro input
      rw [List.ofFn_succ]
      simp only [Fin.val_zero, List.getD, List.getElem?_cons_zero, Option.getD_some,
                 encodeRegs, Fin.val_succ, List.getElem?_cons_succ]
      congr 1
      -- Show: List.ofFn (fun i => [].getElem? i.val |>.getD 0) = List.replicate bound 0
      let h_regs : (List.ofFn fun i : Fin bound => ([] : List ℕ)[i.val]?.getD 0) =
                    List.replicate bound 0 := by
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp only [List.getElem_ofFn, List.getElem_replicate, List.getElem?_nil, Option.getD_none]
      rw [h_regs]
    refine (Nat.Primrec.pair (Nat.Primrec.const 0)
            (Nat.Primrec.pair Nat.Primrec.id (Nat.Primrec.const C))).of_eq ?_
    intro input
    simp only [id_eq, heq]
  -- Step 4: The halting predicate for varying input is primrec
  have hHaltPred : Nat.Primrec (fun p =>
      let input := p.unpair.1
      let step := p.unpair.2
      let inputConfig := encodeInput1 bound input
      if isHaltedAtStep progCode bound inputConfig step then 0 else 1) := by
    let hIter : Primrec₂ (iterateEncodedStep progCode bound) :=
      iterateEncodedStep_primrec_fixed progCode bound
    let hHalted : Nat.Primrec (encodedIsHaltedNat progCode) :=
      encodedIsHaltedNat_primrec_fixed progCode
    let hEnc1' : Primrec (encodeInput1 bound) := Primrec.nat_iff.mpr hEnc1
    let hInputConfig : Primrec (fun p : ℕ => encodeInput1 bound p.unpair.1) :=
      hEnc1'.comp (Primrec.fst.comp Primrec.unpair)
    let hStep : Primrec (fun p : ℕ => p.unpair.2) := Primrec.snd.comp Primrec.unpair
    let hIterFull : Primrec (fun p : ℕ =>
        iterateEncodedStep progCode bound p.unpair.2 (encodeInput1 bound p.unpair.1)) :=
      hIter.comp hStep hInputConfig
    let hCheck : Primrec (fun p : ℕ =>
        encodedIsHaltedNat progCode (iterateEncodedStep progCode bound p.unpair.2
          (encodeInput1 bound p.unpair.1))) :=
      (Primrec.nat_iff.mpr hHalted).comp hIterFull
    let hFlip : Primrec (fun p : ℕ =>
        1 - encodedIsHaltedNat progCode (iterateEncodedStep progCode bound p.unpair.2
          (encodeInput1 bound p.unpair.1))) :=
      Primrec.nat_sub.comp (Primrec.const 1) hCheck
    refine Primrec.nat_iff.mp (hFlip.of_eq fun p => ?_)
    simp only [isHaltedAtStep, encodedIsHaltedNat]
    split_ifs with h
    · simp only [Nat.sub_self]
    · simp only [Nat.sub_zero]
  -- Step 5: Apply Partrec.rfind
  -- Use the typed version Partrec.rfind which works with Partrec₂
  -- First, we need Computable₂ (fun input step => isHaltedAtStep ...) : ℕ → ℕ → Bool
  have hHaltPred₂ : Computable₂ (fun input step =>
      isHaltedAtStep progCode bound (encodeInput1 bound input) step) := by
    -- Build Primrec₂ first, then convert to Computable₂
    let h1 : Primrec₂ (iterateEncodedStep progCode bound) :=
      iterateEncodedStep_primrec_fixed progCode bound
    let h2 : Primrec (encodeInput1 bound) := Primrec.nat_iff.mpr hEnc1
    -- Build: fun (input, step) => iterateEncodedStep step (encodeInput1 input)
    let hConfig : Primrec₂ (fun input step =>
        iterateEncodedStep progCode bound step (encodeInput1 bound input)) :=
      h1.comp Primrec.snd (h2.comp Primrec.fst)
    -- Convert to Primrec on pairs using unpaired
    let hConfigP : Primrec (fun p : ℕ × ℕ =>
        iterateEncodedStep progCode bound p.2 (encodeInput1 bound p.1)) :=
      Primrec.nat_iff.mpr (Primrec₂.unpaired'.mpr hConfig)
    -- encodedIsHalted: check if progCode.unpair.1 ≤ configCode.unpair.1
    let progLen := progCode.unpair.1
    -- Build the pc extraction
    let hPc : Primrec (fun p : ℕ × ℕ =>
        (iterateEncodedStep progCode bound p.2 (encodeInput1 bound p.1)).unpair.1) :=
      (Primrec.fst.comp Primrec.unpair).comp hConfigP
    let hLeq : Primrec (fun p : ℕ × ℕ =>
        decide (progLen ≤ (iterateEncodedStep progCode bound p.2 (encodeInput1 bound p.1)).unpair.1)) :=
      (Primrec.nat_le.comp (Primrec.const progLen) hPc).decide
    -- Show this equals isHaltedAtStep (progLen = progCode.unpair.1 by definition)
    exact hLeq.to₂.to_comp.of_eq fun ⟨input, step⟩ => rfl
  -- Convert to Partrec₂ with Part.some
  have hHaltPred₂' : Partrec₂ (fun input step =>
      Part.some (isHaltedAtStep progCode bound (encodeInput1 bound input) step)) :=
    hHaltPred₂.partrec
  -- Apply Partrec.rfind
  have hRfindSimp : Partrec (fun input => Nat.rfind fun step =>
      Part.some (isHaltedAtStep progCode bound (encodeInput1 bound input) step)) :=
    Partrec.rfind hHaltPred₂'
  -- Step 6: Compose with output extraction using Partrec.map
  have hExtract₂ : Computable₂ (fun input step =>
      extractOutput (iterateEncodedStep progCode bound step (encodeInput1 bound input))) := by
    let h1 : Primrec₂ (iterateEncodedStep progCode bound) :=
      iterateEncodedStep_primrec_fixed progCode bound
    let h2 : Primrec (encodeInput1 bound) := Primrec.nat_iff.mpr hEnc1
    let h3 : Primrec extractOutput := Primrec.nat_iff.mpr extractOutput_primrec
    let hConfig : Primrec₂ (fun input step =>
        iterateEncodedStep progCode bound step (encodeInput1 bound input)) :=
      h1.comp Primrec.snd (h2.comp Primrec.fst)
    exact (h3.comp₂ hConfig).to_comp
  -- Use Partrec.map
  have hFinal : Partrec (fun input =>
      (Nat.rfind fun step => Part.some (isHaltedAtStep progCode bound (encodeInput1 bound input) step)).map
        fun step => extractOutput (iterateEncodedStep progCode bound step (encodeInput1 bound input))) :=
    Partrec.map hRfindSimp hExtract₂
  -- Convert from Partrec to Nat.Partrec
  have hFinalNat : Nat.Partrec (fun input =>
      (Nat.rfind fun step => Part.some (isHaltedAtStep progCode bound (encodeInput1 bound input) step)).map
        fun step => extractOutput (iterateEncodedStep progCode bound step (encodeInput1 bound input))) :=
    Partrec.nat_iff.mp hFinal
  -- Show this equals evalEncoded
  have hFinalEq : (fun input =>
      (Nat.rfind fun step => Part.some (isHaltedAtStep progCode bound (encodeInput1 bound input) step)).map
        fun step => extractOutput (iterateEncodedStep progCode bound step (encodeInput1 bound input))) =
      (fun input => evalEncoded progCode bound (encodeInput1 bound input)) := by
    ext input
    simp only [evalEncoded]
  -- Conclude
  rw [← funext henc_correct]
  rw [← hFinalEq]
  exact hFinalNat

end Urm
