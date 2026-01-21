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
- `encoded_step_primrec_fixed`: The step function is primitive recursive (for fixed program)
- `iterate_encoded_step_correct`: Iteration correctly simulates multi-step execution
-/

namespace Urm

/-! ## Finding the Halting Step -/

/-- Predicate: has the encoded configuration halted at exactly n steps?
    Returns true if halted at step n. -/
def is_haltedAtStep (progCode bound inputConfig : ℕ) (n : ℕ) : Bool :=
  encoded_is_halted progCode (iterate_encoded_step progCode bound n inputConfig)

/-- Extract output (register 0) from an encoded configuration. -/
def extract_output (configCode : ℕ) : ℕ :=
  nth_encoded 0 configCode.unpair.2

/-- Partial evaluation: find the halting step and extract output.
    This is the partial recursive simulation of URM evaluation. -/
noncomputable def eval_encoded (progCode bound inputConfig : ℕ) : Part ℕ :=
  -- Use rfind to find first n where is_haltedAtStep returns true
  (Nat.rfind fun n => Part.some (is_haltedAtStep progCode bound inputConfig n)).map
    fun n => extract_output (iterate_encoded_step progCode bound n inputConfig)

/-! ## Primitive Recursiveness of Helper Functions -/

/-- extract_output is primitive recursive. -/
theorem extract_output_primrec : Nat.Primrec extract_output := by
  -- extract_output configCode = nth_encoded 0 configCode.unpair.2
  -- = configCode.unpair.2.unpair.1
  unfold extract_output
  simp only [nth_encoded_zero]
  exact Nat.Primrec.left.comp Nat.Primrec.right

/-! ## Correctness of Simulation -/

/-- The initial encoded configuration for a single input. -/
def encode_input1 (bound : ℕ) (input : ℕ) : ℕ :=
  encode_config bound (Config.init [input])

/-- Connection between encoded_is_halted and Config.is_halted. -/
theorem encoded_is_halted_iff_is_halted (p : Program) (c : Config) :
    encoded_is_halted (encode_program p) (encode_config p.max_register c) ↔ c.is_halted p := by
  simp only [encoded_is_halted, encode_program, encode_config, Nat.unpair_pair, Config.is_halted,
             decide_eq_true_eq]

/-- extract_output correctly extracts register 0. -/
theorem extract_output_encode_config (bound : ℕ) (c : Config) :
    extract_output (encode_config bound c) = c.state 0 := by
  simp only [extract_output]
  exact nth_encoded_encode_config_regs bound c 0 (Nat.zero_le _)

/-- is_haltedAtStep correctly reflects halting status. -/
theorem is_haltedAtStep_correct (p : Program) (n : ℕ) (c c' : Config)
    (hsteps : StepsN p n c c') :
    let bound := p.max_register
    let progCode := encode_program p
    let inputConfig := encode_config bound c
    is_haltedAtStep progCode bound inputConfig n ↔ c'.is_halted p := by
  simp only [is_haltedAtStep]
  rw [iterate_encoded_step_correct p n c c' hsteps]
  exact encoded_is_halted_iff_is_halted p c'

/-! ## Helper Lemmas for eval_encoded_correct -/

/-- If a configuration is not halted, a step exists. -/
theorem Step.of_not_halted (p : Program) (c : Config) (h : ¬c.is_halted p) :
    ∃ c', Step p c c' := by
  simp only [Config.is_halted, Nat.not_le] at h
  have hinstr : p[c.pc]? ≠ none := List.getElem?_eq_none_iff.not.mpr (Nat.not_le.mpr h)
  obtain ⟨instr, hinstr'⟩ := Option.ne_none_iff_exists'.mp hinstr
  match instr with
  | .Z n => exact ⟨_, Step.zero hinstr'⟩
  | .S n => exact ⟨_, Step.succ hinstr'⟩
  | .T m n => exact ⟨_, Step.trans hinstr'⟩
  | .J m n q =>
    by_cases heq : c.state.read m = c.state.read n
    · exact ⟨_, Step.jump_eq hinstr' heq⟩
    · exact ⟨_, Step.jump_ne hinstr' heq⟩

/-- If no configuration before step n is halted, we can build StepsN p n. -/
theorem stepsN_of_not_halted_before (p : Program) (input : ℕ) (n : ℕ)
    (hBefore : ∀ m < n, is_haltedAtStep (encode_program p) p.max_register
        (encode_input1 p.max_register input) m = false) :
    ∃ c', StepsN p n (Config.init [input]) c' := by
  induction n with
  | zero => exact ⟨Config.init [input], StepsN.zero _⟩
  | succ n ih =>
    have hBefore' : ∀ m < n, is_haltedAtStep (encode_program p) p.max_register
        (encode_input1 p.max_register input) m = false :=
      fun m hm => hBefore m (Nat.lt_trans hm (Nat.lt_succ_self n))
    obtain ⟨c_n, hstepsN⟩ := ih hBefore'
    have hn_false := hBefore n (Nat.lt_succ_self n)
    have h_not_halted : ¬c_n.is_halted p := by
      intro hHalted
      have hcorrect := is_haltedAtStep_correct p n (Config.init [input]) c_n hstepsN
      unfold encode_input1 at hn_false
      simp only [hcorrect.mpr hHalted] at hn_false
      exact Bool.false_ne_true hn_false.symm
    obtain ⟨c', hstep⟩ := Step.of_not_halted p c_n h_not_halted
    have h1 : StepsN p 1 c_n c' := StepsN.succ hstep (StepsN.zero _)
    exact ⟨c', StepsN.add hstepsN h1⟩

/-- If StepsN p n c c_final with c_final halted, then for m < n,
    the config at step m from c is not halted. -/
theorem stepsN_before_halted (p : Program) (n : ℕ) (c c_final : Config)
    (hStepsN : StepsN p n c c_final) (hHalted : c_final.is_halted p) :
    ∀ m < n, ∃ c_m, StepsN p m c c_m ∧ ¬c_m.is_halted p := by
  intro m hm
  induction m generalizing c n with
  | zero =>
    use c, StepsN.zero c
    intro hc_halted
    cases hStepsN with
    | zero => omega
    | succ hstep _ => exact Step.no_step_of_halted hc_halted hstep
  | succ m ih =>
    match hStepsN with
    | .zero _ => omega
    | .succ hstep hrest =>
      have hm' : m < _ := Nat.lt_of_succ_lt_succ hm
      obtain ⟨c_m', hstepsM', hnot_halted⟩ := ih _ _ hrest hm'
      exact ⟨c_m', StepsN.succ hstep hstepsM', hnot_halted⟩

/-- is_haltedAtStep is false for all m < n when there's StepsN p n to halted config. -/
theorem is_haltedAtStep_false_before (p : Program) (n : ℕ) (c c_final : Config)
    (hStepsN : StepsN p n c c_final) (hHalted : c_final.is_halted p) :
    ∀ m < n, is_haltedAtStep (encode_program p) p.max_register (encode_config p.max_register c) m = false := by
  intro m hm
  obtain ⟨c_m, hstepsM, hnot_halted⟩ := stepsN_before_halted p n c c_final hStepsN hHalted m hm
  have hcorrect := is_haltedAtStep_correct p m c c_m hstepsM
  cases h : is_haltedAtStep (encode_program p) p.max_register (encode_config p.max_register c) m
  · rfl
  · exact absurd (hcorrect.mp h) hnot_halted

/-- The output of any halted config reachable from init equals Result. -/
theorem halted_output_eq_Result (p : Program) (inputs : List ℕ) (c : Config)
    (hSteps : Steps p (Config.init inputs) c) (hHalted : c.is_halted p)
    (hHalts : Halts p inputs) :
    c.state.output = Result p inputs hHalts := by
  unfold Result
  have h_chosen := Classical.choose_spec hHalts
  obtain ⟨hSteps_chosen, hHalted_chosen⟩ := h_chosen
  have h_unique := Steps.eq_of_halts hSteps hHalted hSteps_chosen hHalted_chosen
  simp only [h_unique]

/-- Simulation correctness: eval_encoded computes the same result as eval. -/
theorem eval_encoded_correct (p : Program) (input : ℕ) :
    let bound := p.max_register
    let progCode := encode_program p
    let inputConfig := encode_input1 bound input
    eval_encoded progCode bound inputConfig = eval p [input] := by
  apply Part.ext
  intro result
  constructor
  -- Forward: result ∈ eval_encoded → result ∈ eval
  · intro hmem_enc
    simp only [eval_encoded] at hmem_enc
    rw [Part.mem_map_iff] at hmem_enc
    obtain ⟨n, hn_mem, hresult_eq⟩ := hmem_enc
    rw [Nat.mem_rfind] at hn_mem
    obtain ⟨htrue_n, hfalse_before⟩ := hn_mem
    simp only [Part.mem_some_iff] at htrue_n hfalse_before
    have hBefore : ∀ m < n, is_haltedAtStep (encode_program p) p.max_register
        (encode_input1 p.max_register input) m = false :=
      fun m hm => (hfalse_before hm).symm
    obtain ⟨c', hstepsN⟩ := stepsN_of_not_halted_before p input n hBefore
    have hhalted : c'.is_halted p := by
      let hcorrect := is_haltedAtStep_correct p n (Config.init [input]) c' hstepsN
      unfold encode_input1 at htrue_n
      exact hcorrect.mp htrue_n.symm
    have hHalts : Halts p [input] := ⟨c', StepsN.to_steps hstepsN, hhalted⟩
    simp only [eval, Part.mem_mk_iff]
    use hHalts
    have h_iter := iterate_encoded_step_correct p n (Config.init [input]) c' hstepsN
    rw [← hresult_eq]
    unfold encode_input1
    rw [h_iter, extract_output_encode_config]
    exact (halted_output_eq_Result p [input] c' (StepsN.to_steps hstepsN) hhalted hHalts).symm
  -- Backward: result ∈ eval → result ∈ eval_encoded
  · intro hmem_eval
    simp only [eval, Part.mem_mk_iff] at hmem_eval
    obtain ⟨hHalts, hresult_eq⟩ := hmem_eval
    obtain ⟨c, hSteps, hHalted⟩ := hHalts
    obtain ⟨n, hStepsN⟩ := StepsN.from_steps hSteps
    simp only [eval_encoded]
    rw [Part.mem_map_iff]
    use n
    constructor
    · rw [Nat.mem_rfind]
      constructor
      · simp only [Part.mem_some_iff]
        have hcorrect := is_haltedAtStep_correct p n (Config.init [input]) c hStepsN
        unfold encode_input1
        exact (hcorrect.mpr hHalted).symm
      · intro m hm
        simp only [Part.mem_some_iff]
        unfold encode_input1
        exact (is_haltedAtStep_false_before p n (Config.init [input]) c hStepsN hHalted m hm).symm
    · have h_iter := iterate_encoded_step_correct p n (Config.init [input]) c hStepsN
      unfold encode_input1
      rw [h_iter, extract_output_encode_config, ← hresult_eq]
      exact halted_output_eq_Result p [input] c hSteps hHalted ⟨c, hSteps, hHalted⟩

/-! ## Main Theorem -/

/-- Every URM-computable unary function is partial recursive.

Strategy:
1. Get the program p that computes f from URMComputable1 f
2. Show eval_encoded (for fixed p) is partial recursive:
   - encode_input1 is primitive recursive (for fixed bound)
   - is_haltedAtStep is primitive recursive (for fixed progCode, bound, inputConfig)
   - rfind on a primitive recursive predicate is partial recursive
   - extract_output is primitive recursive
   - Composition of these is partial recursive
3. Show eval_encoded correctly computes f:
   - iterate_encoded_step correctly simulates StepsN
   - The halting step found by rfind gives the final configuration
   - extract_output extracts register 0, matching eval's Result
-/
theorem URMComputable1.toPartrec {f : ℕ →. ℕ} (hf : URMComputable1 f) :
    Nat.Partrec f := by
  -- Extract the program from URMComputable1
  obtain ⟨p, hp⟩ := hf
  -- Define constants for this fixed program
  let progCode := encode_program p
  let bound := p.max_register
  -- Step 1: Show eval p [n] = f n
  have heval : ∀ n, eval p [n] = f n := by
    intro n
    have hp_n := hp (fun _ => n)
    simp only [List.ofFn_const, List.replicate] at hp_n
    obtain ⟨hiff, hres⟩ := hp_n
    ext m
    simp only [eval, Part.mem_mk_iff]
    constructor
    · rintro ⟨hHalts, rfl⟩
      have hDom := hiff.mp hHalts
      rw [hres hHalts hDom]
      exact Part.get_mem hDom
    · intro hm
      have hDom : (f n).Dom := Part.dom_iff_mem.mpr ⟨m, hm⟩
      have hHalts := hiff.mpr hDom
      refine ⟨hHalts, ?_⟩
      rw [hres hHalts hDom]
      exact Part.mem_unique (Part.get_mem hDom) hm
  -- Step 2: Show eval_encoded equals eval via eval_encoded_correct
  have henc_correct : ∀ n, eval_encoded progCode bound (encode_input1 bound n) = f n := by
    intro n
    rw [← heval n]
    exact eval_encoded_correct p n
  -- Step 3: Build Nat.Partrec for eval_encoded
  -- First, show encode_input1 is primrec for fixed bound
  have hEnc1 : Nat.Primrec (encode_input1 bound) := by
    -- encode_input1 bound input = pair 0 (pair input C) where C is constant
    unfold encode_input1 encode_config Config.init
    simp only [State.of_inputs]
    let C := encode_regs (List.replicate bound 0)
    let heq : ∀ input, encode_regs (List.ofFn fun i : Fin (bound + 1) =>
        List.getD [input] i 0) = Nat.pair input C := by
      intro input
      rw [List.ofFn_succ]
      simp only [Fin.val_zero, List.getD, List.getElem?_cons_zero, Option.getD_some,
                 encode_regs, Fin.val_succ, List.getElem?_cons_succ]
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
  -- Step 4: Build Computable₂ for the halting predicate
  have hHaltPred₂ : Computable₂ (fun input step =>
      is_haltedAtStep progCode bound (encode_input1 bound input) step) := by
    have h1 := iterate_encoded_step_primrec_fixed progCode bound
    have h2 : Primrec (encode_input1 bound) := Primrec.nat_iff.mpr hEnc1
    have hConfig : Primrec₂ (fun input step =>
        iterate_encoded_step progCode bound step (encode_input1 bound input)) :=
      h1.comp Primrec.snd (h2.comp Primrec.fst)
    have hConfigP : Primrec (fun p : ℕ × ℕ =>
        iterate_encoded_step progCode bound p.2 (encode_input1 bound p.1)) :=
      Primrec.nat_iff.mpr (Primrec₂.unpaired'.mpr hConfig)
    have hPc : Primrec (fun p : ℕ × ℕ =>
        (iterate_encoded_step progCode bound p.2 (encode_input1 bound p.1)).unpair.1) :=
      (Primrec.fst.comp Primrec.unpair).comp hConfigP
    have hLeq : Primrec (fun p : ℕ × ℕ =>
        decide (progCode.unpair.1 ≤ (iterate_encoded_step progCode bound p.2 (encode_input1 bound p.1)).unpair.1)) :=
      (Primrec.nat_le.comp (Primrec.const progCode.unpair.1) hPc).decide
    exact hLeq.to₂.to_comp.of_eq fun ⟨_, _⟩ => rfl
  -- Step 5: Apply Partrec.rfind
  have hRfindSimp : Partrec (fun input => Nat.rfind fun step =>
      Part.some (is_haltedAtStep progCode bound (encode_input1 bound input) step)) :=
    Partrec.rfind hHaltPred₂.partrec
  -- Step 6: Compose with output extraction
  have hExtract₂ : Computable₂ (fun input step =>
      extract_output (iterate_encoded_step progCode bound step (encode_input1 bound input))) := by
    have h1 := iterate_encoded_step_primrec_fixed progCode bound
    have h2 : Primrec (encode_input1 bound) := Primrec.nat_iff.mpr hEnc1
    have h3 : Primrec extract_output := Primrec.nat_iff.mpr extract_output_primrec
    have hConfig : Primrec₂ (fun input step =>
        iterate_encoded_step progCode bound step (encode_input1 bound input)) :=
      h1.comp Primrec.snd (h2.comp Primrec.fst)
    exact (h3.comp₂ hConfig).to_comp
  -- Step 7: Combine rfind and extraction
  have hFinal : Partrec (fun input =>
      (Nat.rfind fun step => Part.some (is_haltedAtStep progCode bound (encode_input1 bound input) step)).map
        fun step => extract_output (iterate_encoded_step progCode bound step (encode_input1 bound input))) :=
    Partrec.map hRfindSimp hExtract₂
  -- Step 8: Show this equals f
  rw [← funext henc_correct]
  exact Partrec.nat_iff.mp (hFinal.of_eq fun input => by simp only [eval_encoded])

end Urm
