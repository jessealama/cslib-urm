/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Composition.PrefixTransfer

/-! # Unary Composition Theorem

This file proves that URM-computable functions are closed under unary composition.
Given f : (Fin 1 → ℕ) → Part ℕ and g : (Fin n → ℕ) → Part ℕ, the composition
h(x) = f(g(x)) is also URM-computable.

## Main statements

- `Urm.URMComputable.comp_unary`: Unary composition closure
-/

namespace Urm

namespace URMComputable

/-- Unary composition: compose f with a single function g.
    This is a simpler case that can be proven directly.

    The composed program:
    1. Run pg (result in R[0])
    2. Clear registers R[1..k] where k = pf.maxRegister
    3. Run pf (now sees a clean state matching State.fromInputs [v])

    Proof outline:
    - Forward direction (halting → function defined):
      * If the composed program halts, then pg must have halted (first segment)
      * After pg halts, clearing runs and halts (finite program)
      * Then pf runs and halts on the cleared state
      * By `Halts.agree_halts`, pf halting on cleared state ↔ pf halting on [v]
      * So both g and f are defined

    - Backward direction (function defined → halting):
      * If g(inputs) is defined, pg halts with R[0] = v
      * Clearing always halts
      * After clearing, state agrees with fromInputs [v] on registers 0..k
      * If f([v]) is defined, pf halts on fromInputs [v]
      * By `Halts.agree_halts`, pf halts on cleared state too
      * So the composed program halts

    - Result equality:
      * Both produce the same R[0] value by `Halts.agree_halts`

    Note: We assume programs are in "standard form" (JumpsBounded), meaning all jump
    targets are within bounds. Cutland proves every program has an equivalent standard-form
    program, so this is not a restriction on computability. All basic programs (zero, succ,
    proj) are naturally in standard form. -/
theorem comp_unary {n : ℕ}
    {f : (Fin 1 → ℕ) → Part ℕ} {g : (Fin n → ℕ) → Part ℕ}
    {pf : Program} {pg : Program}
    (hpf : ∀ inputs : Fin 1 → ℕ,
      let inputList := List.ofFn inputs
      (Halts pf inputList ↔ (f inputs).Dom) ∧
      ∀ (hHalts : Halts pf inputList) (hDom : (f inputs).Dom),
        Result pf inputList hHalts = (f inputs).get hDom)
    (hpg : ∀ inputs : Fin n → ℕ,
      let inputList := List.ofFn inputs
      (Halts pg inputList ↔ (g inputs).Dom) ∧
      ∀ (hHalts : Halts pg inputList) (hDom : (g inputs).Dom),
        Result pg inputList hHalts = (g inputs).get hDom)
    (hboundedg : JumpsBounded pg)
    (hboundedf : JumpsBounded pf) :
    URMComputable n (fun inputs => (g inputs).bind (fun v => f (fun _ => v))) := by
  -- The composed program: run pg, clear non-R[0] registers, then run pf
  let k := pf.maxRegister
  use pg.seq ((clearRegsFrom1 k).seq pf)
  intro inputs
  let inputList := List.ofFn inputs

  -- First prove the iff for halting ↔ domain, then the result equality
  refine ⟨⟨?halts_imp_dom, ?dom_imp_halts⟩, ?result_eq⟩

  case halts_imp_dom =>
    -- Forward: Halts → Domain
    -- This direction requires showing that if composite halts, both g and f are defined
    intro hHalts

    -- The composed function is defined iff g is defined AND f is defined on g's output
    -- Goal: ((g inputs).bind (fun v => f (fun _ => v))).Dom
    -- Which unfolds to: ∃ hg : (g inputs).Dom, (f (fun _ => (g inputs).get hg)).Dom
    simp only [Part.bind_dom]

    -- pg.seq (inner) halts, so by seq_first_halts, pg halts
    have hpgHalts : Halts pg inputList :=
      JumpsBounded.seq_first_halts hboundedg hHalts

    -- pg halts iff g is defined
    have hgSpec := hpg inputs
    have hgDom : (g inputs).Dom := hgSpec.1.mp hpgHalts

    -- Get the value v = g(inputs)
    let v := (g inputs).get hgDom

    have hpgResult : Result pg inputList hpgHalts = v := hgSpec.2 hpgHalts hgDom

    have hclear_bounded : JumpsBounded (clearRegsFrom1 k) := clearRegsFrom1_bounded k
    refine ⟨hgDom, ?_⟩

    -- Use seq_second_halts to extract the inner execution
    let inner := (clearRegsFrom1 k).seq pf
    have hinner_bounded : JumpsBounded inner := by
      apply JumpsBounded.seq
      · exact hclear_bounded
      · exact hboundedf

    obtain ⟨σ_after_pg, hpg_steps, c_inner, hinner_steps, hinner_halted⟩ :=
      JumpsBounded.seq_second_halts hboundedg hinner_bounded hHalts

    -- Show σ_after_pg 0 = v (by halts_unique with the chosen halted config)
    have hpg_output : σ_after_pg 0 = v := by
      simp only [Result, State.output] at hpgResult
      have hpg_halted : (⟨pg.length, σ_after_pg⟩ : Config).isHalted pg := by simp [Config.isHalted]
      have hresult_config := Classical.choose_spec hpgHalts
      have hunique := Steps.halts_unique hpg_steps hpg_halted hresult_config.1 hresult_config.2
      have hstate_eq : σ_after_pg = (Classical.choose hpgHalts).state := congrArg Config.state hunique
      rw [hstate_eq]; exact hpgResult

    let σ_init := State.fromInputs [σ_after_pg 0]
    have hclear_steps_init : Steps (clearRegsFrom1 k) ⟨0, σ_init⟩ ⟨k, σ_init.clearFrom1 k⟩ :=
      clearRegsFrom1_reaches_clearFrom1 k σ_init
    have hclear_steps_pg : Steps (clearRegsFrom1 k) ⟨0, σ_after_pg⟩ ⟨k, σ_after_pg.clearFrom1 k⟩ :=
      clearRegsFrom1_reaches_clearFrom1 k σ_after_pg

    have hagree_cleared : (σ_after_pg.clearFrom1 k).agreeUpTo (σ_init.clearFrom1 k) k := by
      intro r hr
      rw [State.clearFrom1_eq_fromInputs_on_range σ_after_pg k r hr]
      rw [State.clearFrom1_eq_fromInputs_on_range σ_init k r hr]
      simp only [σ_init, State.fromInputs, List.getD, List.getElem?_cons_zero, Option.getD_some]

    -- Extract pf execution from inner
    have hclear_in_inner : Steps inner ⟨0, σ_after_pg⟩ ⟨k, σ_after_pg.clearFrom1 k⟩ :=
      Steps.clearRegsFrom1_in_seq k pf σ_after_pg
    have hpf_in_inner : Steps inner ⟨k, σ_after_pg.clearFrom1 k⟩ c_inner :=
      Steps.deterministic_continuation hclear_in_inner hinner_steps hinner_halted

    have hcfinal_in_p2 : k ≤ c_inner.pc := by
      have : inner.length ≤ c_inner.pc := hinner_halted
      simp only [inner, Program.seq_length, clearRegsFrom1_length] at this; omega

    have hpf_steps_from_pg : Steps pf ⟨0, σ_after_pg.clearFrom1 k⟩ ⟨c_inner.pc - k, c_inner.state⟩ := by
      have hpc_eq : (⟨k, σ_after_pg.clearFrom1 k⟩ : Config).pc = (clearRegsFrom1 k).length := by
        simp [clearRegsFrom1_length]
      have h := JumpsBounded.seq_steps_to_p2_steps hboundedf hpf_in_inner hpc_eq hinner_halted
      simp only [clearRegsFrom1_length] at h; exact h

    have hpf_final_halted : (⟨c_inner.pc - k, c_inner.state⟩ : Config).isHalted pf := by
      simp only [Config.isHalted] at hinner_halted ⊢
      simp only [inner, Program.seq_length, clearRegsFrom1_length] at hinner_halted; omega

    have hagree_for_pf : (σ_after_pg.clearFrom1 k).agreeUpTo (σ_init.clearFrom1 k) pf.maxRegister :=
      fun r hr => hagree_cleared r (Nat.le_trans hr (Nat.le_refl k))

    obtain ⟨c_pf', hpf_steps_init, hpc_eq, _⟩ := Steps.agree_steps hpf_steps_from_pg hagree_for_pf

    have hpf_halted' : c_pf'.isHalted pf := by
      simp only [Config.isHalted] at hpf_final_halted ⊢; simp only at hpc_eq; omega

    have hclear_in_inner_init : Steps inner ⟨0, σ_init⟩ ⟨k, σ_init.clearFrom1 k⟩ :=
      Steps.clearRegsFrom1_in_seq k pf σ_init

    -- Lift pf steps to inner from σ_init.clearFrom1 k
    have hpf_in_inner_init : Steps inner ⟨k, σ_init.clearFrom1 k⟩ ⟨k + c_pf'.pc, c_pf'.state⟩ := by
      have := Steps.seq_steps_second (p₁ := clearRegsFrom1 k) hpf_steps_init
      simp only [clearRegsFrom1_length] at this
      exact this

    -- Combine for inner execution from σ_init
    have hinner_full : Steps inner ⟨0, σ_init⟩ ⟨k + c_pf'.pc, c_pf'.state⟩ :=
      Steps.trans hclear_in_inner_init hpf_in_inner_init

    -- The final config is halted in inner
    have hinner_final_halted : (⟨k + c_pf'.pc, c_pf'.state⟩ : Config).isHalted inner := by
      simp only [Config.isHalted, inner, Program.seq_length, clearRegsFrom1_length]
      have : pf.length ≤ c_pf'.pc := hpf_halted'
      omega

    -- Now apply seq_second_halts to the inner program
    have hinner_halts : Halts inner [σ_after_pg 0] := by
      use ⟨k + c_pf'.pc, c_pf'.state⟩
      constructor
      · -- Config.init [σ_after_pg 0] = ⟨0, State.fromInputs [σ_after_pg 0]⟩ = ⟨0, σ_init⟩
        simp only [Config.init]
        exact hinner_full
      · exact hinner_final_halted

    -- From inner halting, use seq_second_halts again to get pf halting
    obtain ⟨σ_after_clear, hclear_steps'', c_pf_final, hpf_steps_final, hpf_halted_final⟩ :=
      JumpsBounded.seq_second_halts hclear_bounded hboundedf hinner_halts

    -- Determine σ_after_clear by determinism: it must be (fromInputs [σ_after_pg 0]).clearFrom1 k
    have hpf_spec := hpf (fun _ => σ_after_pg 0)
    let σ_clear_expected := (State.fromInputs [σ_after_pg 0]).clearFrom1 k
    have hclear_expected : Steps (clearRegsFrom1 k) ⟨0, State.fromInputs [σ_after_pg 0]⟩
        ⟨k, σ_clear_expected⟩ := clearRegsFrom1_reaches_clearFrom1 k (State.fromInputs [σ_after_pg 0])
    have hclear_expected_halted : (⟨k, σ_clear_expected⟩ : Config).isHalted (clearRegsFrom1 k) := by
      simp [Config.isHalted, clearRegsFrom1_length]
    have hclear_actual_halted : (⟨(clearRegsFrom1 k).length, σ_after_clear⟩ : Config).isHalted (clearRegsFrom1 k) := by
      simp [Config.isHalted]
    have hclear_steps_unfolded : Steps (clearRegsFrom1 k) ⟨0, State.fromInputs [σ_after_pg 0]⟩
        ⟨(clearRegsFrom1 k).length, σ_after_clear⟩ := by
      simp only [Config.init] at hclear_steps''
      convert hclear_steps'' using 2
    have hstate_eq : σ_after_clear = σ_clear_expected := by
      have hunique := Steps.halts_unique hclear_steps_unfolded hclear_actual_halted hclear_expected hclear_expected_halted
      simp only [clearRegsFrom1_length] at hunique
      exact congrArg Config.state hunique

    have hagree_clear : σ_after_clear.agreeUpTo (State.fromInputs [σ_after_pg 0]) k := by
      rw [hstate_eq]
      exact State.clearFrom1_agreeUpTo_fromInputs (State.fromInputs [σ_after_pg 0]) k

    have hagree_pf : σ_after_clear.agreeUpTo (State.fromInputs [σ_after_pg 0]) pf.maxRegister :=
      fun r hr => hagree_clear r (Nat.le_trans hr (Nat.le_refl k))

    -- Use agree_steps to transfer pf execution to State.fromInputs [σ_after_pg 0]
    obtain ⟨c_pf_v, hpf_steps_v, hpc_eq', _⟩ := Steps.agree_steps hpf_steps_final hagree_pf

    have hpf_halted_v : c_pf_v.isHalted pf := by
      simp only [Config.isHalted] at hpf_halted_final ⊢
      omega

    have hpf_halts_v : Halts pf [σ_after_pg 0] := by
      use c_pf_v
      constructor
      · exact hpf_steps_v
      · exact hpf_halted_v

    have hfDom : (f (fun _ => σ_after_pg 0)).Dom := hpf_spec.1.mp hpf_halts_v
    -- Convert using hpg_output: σ_after_pg 0 = v
    convert hfDom using 2
    funext _
    exact hpg_output.symm

  case dom_imp_halts =>
    intro hDom
    simp only [Part.bind_dom] at hDom
    obtain ⟨hgDom, hfDom⟩ := hDom
    let v := (g inputs).get hgDom

    -- pg halts with output v
    have hgSpec := hpg inputs
    have hpgHalts : Halts pg inputList := hgSpec.1.mpr hgDom
    have hpgResult : Result pg inputList hpgHalts = v := hgSpec.2 hpgHalts hgDom

    -- Get the halted config for pg
    let cg := Classical.choose hpgHalts
    have hcg_spec := Classical.choose_spec hpgHalts
    have hstepsg : Steps pg (Config.init inputList) cg := hcg_spec.1
    have hhaltedg : cg.isHalted pg := hcg_spec.2
    have hcg_output : cg.state.output = v := by simp only [Result, State.output] at hpgResult; exact hpgResult
    let σg := cg.state
    have hclearSteps : Steps (clearRegsFrom1 k) ⟨0, σg⟩ ⟨k, σg.clearFrom1 k⟩ :=
      clearRegsFrom1_reaches_clearFrom1 k σg

    -- Cleared state agrees with fromInputs [v] on 0..k (and hence 0..pf.maxRegister)
    have hσg_0_eq_v : σg 0 = v := by simp only [State.output] at hcg_output; exact hcg_output
    have hagree : (σg.clearFrom1 k).agreeUpTo (State.fromInputs [v]) k := by
      simpa only [hσg_0_eq_v] using State.clearFrom1_agreeUpTo_fromInputs σg k
    have hagree' : (σg.clearFrom1 k).agreeUpTo (State.fromInputs [v]) pf.maxRegister := hagree

    -- pf halts on [v] because f is defined there
    have hfSpec := hpf (fun _ => v)
    have hpfHalts' : Halts pf [v] := hfSpec.1.mpr hfDom
    obtain ⟨cf, hstepsf, hhaltedf⟩ := hpfHalts'

    -- Use agree_steps to get execution from σg.clearFrom1 k
    have hagreeInit : (State.fromInputs [v]).agreeUpTo (σg.clearFrom1 k) pf.maxRegister :=
      fun r hr => (hagree' r hr).symm
    obtain ⟨cf', hstepsf', hpceq, _⟩ := Steps.agree_steps hstepsf hagreeInit
    have hhaltedf' : cf'.isHalted pf := by simp only [Config.isHalted] at hhaltedf ⊢; omega
    have hinner_halts : Steps ((clearRegsFrom1 k).seq pf)
        ⟨0, σg⟩ ⟨k + cf'.pc, cf'.state⟩ := by
      have hphase1 := Steps.clearRegsFrom1_in_seq k pf σg
      have hphase2 : Steps ((clearRegsFrom1 k).seq pf) ⟨k, σg.clearFrom1 k⟩ ⟨k + cf'.pc, cf'.state⟩ := by
        have := Steps.seq_steps_second (p₁ := clearRegsFrom1 k) hstepsf'
        simp only [clearRegsFrom1_length] at this
        exact this
      exact Steps.trans hphase1 hphase2

    have hinner_halted : (⟨k + cf'.pc, cf'.state⟩ : Config).isHalted
        ((clearRegsFrom1 k).seq pf) := by
      simp only [Config.isHalted, Program.seq_length, clearRegsFrom1_length]
      have : pf.length ≤ cf'.pc := hhaltedf'
      omega

    -- JumpsBounded: halted configs have pc = length
    have hcg_at_length : cg.pc = pg.length :=
      JumpsBounded.halts_at_length hboundedg hstepsg hhaltedg
    have hstepsg_exact : Steps pg (Config.init inputList) ⟨pg.length, σg⟩ := by
      have heq : cg = ⟨pg.length, σg⟩ := by
        simp only [σg]
        have : cg = ⟨cg.pc, cg.state⟩ := by cases cg; rfl
        rw [this, hcg_at_length]
      rw [heq] at hstepsg
      exact hstepsg

    -- Now apply seq_halts_compose for the outer composition
    exact Steps.seq_halts_compose hstepsg_exact hinner_halts hinner_halted

  case result_eq =>
    intro hHalts hDom
    simp only [Part.bind_dom] at hDom
    obtain ⟨hgDom, hfDom_at_v⟩ := hDom
    let v := (g inputs).get hgDom
    have hfDom : (f (fun _ => v)).Dom := hfDom_at_v

    -- pg halts with output v
    have hpg_spec := hpg inputs
    have hpgHalts : Halts pg inputList := hpg_spec.1.mpr hgDom
    have hpgResult : Result pg inputList hpgHalts = v := hpg_spec.2 hpgHalts hgDom

    -- pf halts on [v] with result (f (fun _ => v)).get hfDom
    have hpf_spec := hpf (fun _ => v)
    have hpfHalts : Halts pf [v] := hpf_spec.1.mpr hfDom
    have hpfResult : Result pf [v] hpfHalts = (f (fun _ => v)).get hfDom :=
      hpf_spec.2 hpfHalts hfDom

    -- Get halted configs
    let cg := Classical.choose hpgHalts
    have hcg_spec := Classical.choose_spec hpgHalts
    have hstepsg : Steps pg (Config.init inputList) cg := hcg_spec.1
    have hhaltedg : cg.isHalted pg := hcg_spec.2
    let σg := cg.state
    have hσg_output : σg 0 = v := by simp only [Result, State.output, σg] at hpgResult ⊢; exact hpgResult

    have hcg_at_length : cg.pc = pg.length :=
      JumpsBounded.halts_at_length hboundedg hstepsg hhaltedg
    have hstepsg_exact : Steps pg (Config.init inputList) ⟨pg.length, σg⟩ := by
      have heq : cg = ⟨pg.length, σg⟩ := Config.ext hcg_at_length rfl
      rw [heq] at hstepsg; exact hstepsg

    let inner := (clearRegsFrom1 k).seq pf
    have hclearSteps : Steps (clearRegsFrom1 k) ⟨0, σg⟩ ⟨k, σg.clearFrom1 k⟩ :=
      clearRegsFrom1_reaches_clearFrom1 k σg
    have hagree_cleared : (σg.clearFrom1 k).agreeUpTo (State.fromInputs [v]) k := by
      simpa only [hσg_output] using State.clearFrom1_agreeUpTo_fromInputs σg k
    let cf := Classical.choose hpfHalts
    have hcf_spec := Classical.choose_spec hpfHalts
    have hstepsf : Steps pf (Config.init [v]) cf := hcf_spec.1
    have hhaltedf : cf.isHalted pf := hcf_spec.2

    -- Use agree_steps to transfer pf execution from [v] to cleared state
    have hagreeInit : (State.fromInputs [v]).agreeUpTo (σg.clearFrom1 k) pf.maxRegister :=
      fun r hr => (hagree_cleared r (Nat.le_trans hr (Nat.le_refl k))).symm
    obtain ⟨cf', hstepsf', hpceq, hagree_final⟩ := Steps.agree_steps hstepsf hagreeInit
    have hhaltedf' : cf'.isHalted pf := by simp only [Config.isHalted] at hhaltedf ⊢; omega
    have hresult_agree : cf'.state 0 = cf.state 0 := (hagree_final 0 (Nat.zero_le _)).symm
    have hcf_output : cf.state.output = (f (fun _ => v)).get hfDom := by
      simp only [Result, State.output, cf] at hpfResult ⊢; exact hpfResult
    have hinner_halts : Steps inner ⟨0, σg⟩ ⟨k + cf'.pc, cf'.state⟩ := by
      have hphase1 := Steps.clearRegsFrom1_in_seq k pf σg
      have hphase2 : Steps inner ⟨k, σg.clearFrom1 k⟩ ⟨k + cf'.pc, cf'.state⟩ := by
        have := Steps.seq_steps_second (p₁ := clearRegsFrom1 k) hstepsf'
        simp only [clearRegsFrom1_length] at this
        exact this
      exact Steps.trans hphase1 hphase2

    have hinner_halted : (⟨k + cf'.pc, cf'.state⟩ : Config).isHalted inner := by
      simp only [Config.isHalted, inner, Program.seq_length, clearRegsFrom1_length]
      have : pf.length ≤ cf'.pc := hhaltedf'
      omega

    have hfull_steps : Steps (pg.seq inner) (Config.init inputList)
        ⟨pg.length + k + cf'.pc, cf'.state⟩ := by
      have hsteps_pg_seq : Steps (pg.seq inner) (Config.init inputList) ⟨pg.length, σg⟩ := by
        by_cases hpg_empty : pg.length = 0
        · have hinit_halted : (Config.init inputList).isHalted pg := by simp [Config.isHalted, Config.init, hpg_empty]
          have hσg_eq : σg = (Config.init inputList).state := by
            have huniq := Steps.halts_unique hstepsg hhaltedg (Steps.refl _) hinit_halted
            simp only [σg, huniq, Config.init]
          simp only [hpg_empty, hσg_eq, Config.init]; exact Steps.refl _
        · apply Steps.seq_steps_first hstepsg_exact
          · simp [Config.init]; omega
          · exact Nat.le_refl _
      have hsteps_inner_seq : Steps (pg.seq inner) ⟨pg.length, σg⟩ ⟨pg.length + (k + cf'.pc), cf'.state⟩ := by
        have := Steps.seq_steps_second (p₁ := pg) hinner_halts
        simp only [Nat.add_zero] at this; exact this
      convert Steps.trans hsteps_pg_seq hsteps_inner_seq using 2; omega

    have hfull_halted : (⟨pg.length + k + cf'.pc, cf'.state⟩ : Config).isHalted (pg.seq inner) := by
      simp only [Config.isHalted, Program.seq_length, inner, Program.seq_length, clearRegsFrom1_length]
      have : pf.length ≤ cf'.pc := hhaltedf'
      omega

    have hfinal_result : Result (pg.seq inner) inputList hHalts = cf'.state 0 := by
      simp only [Result, State.output]
      have huniq := Steps.halts_unique (Classical.choose_spec hHalts).1
        (Classical.choose_spec hHalts).2 hfull_steps hfull_halted
      rw [huniq]

    calc Result (pg.seq inner) inputList hHalts
        = cf'.state 0 := hfinal_result
      _ = cf.state 0 := hresult_agree
      _ = cf.state.output := rfl
      _ = (f (fun _ => v)).get hfDom := hcf_output
      _ = ((g inputs).bind (fun v' => f (fun _ => v'))).get hDom := by
          symm; apply Part.get_eq_of_mem; rw [Part.mem_bind_iff]
          exact ⟨v, Part.get_mem hgDom, Part.get_mem hfDom⟩

end URMComputable

end Urm
