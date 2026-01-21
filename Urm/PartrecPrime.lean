/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Partrec
import Urm.PartSequence
import Urm.Simulate.Simulate
import Mathlib.Computability.Halting

/-! # Equivalence with Nat.Partrec' (n-ary partial recursive functions)

This file proves the equivalence between n-ary URM computability and Mathlib's n-ary
partial recursive functions (`Nat.Partrec'`).

## Main results

- `URMComputable.toPartrec'`: Every n-ary URM-computable function is n-ary partial recursive
- `Nat.Partrec'.toURMComputable`: Every n-ary partial recursive function is n-ary URM-computable
- `URMComputable_iff_Partrec'`: The equivalence between the two notions

## Strategy

We leverage the existing unary equivalence `URMComputable1 ↔ Nat.Partrec` along with
`Nat.Partrec'.part_iff : Nat.Partrec' f ↔ Partrec f` which reduces n-ary Partrec' to
unary Partrec with vector encoding.

## Type conversion

`Nat.Partrec'` uses `List.Vector ℕ n →. ℕ` while `URMComputable` uses `(Fin n → ℕ) → Part ℕ`.
These are isomorphic via:
- `List.Vector.ofFn : (Fin n → ℕ) → List.Vector ℕ n`
- `List.Vector.get : List.Vector ℕ n → Fin n → ℕ`
-/

namespace Urm

/-! ## Type conversion utilities -/

/-- Convert from (Fin n → ℕ) → Part ℕ to List.Vector ℕ n →. ℕ -/
def toVectorFun {n : ℕ} (f : (Fin n → ℕ) → Part ℕ) : List.Vector ℕ n →. ℕ :=
  fun v => f v.get

/-- Convert from List.Vector ℕ n →. ℕ to (Fin n → ℕ) → Part ℕ -/
def fromVectorFun {n : ℕ} (f : List.Vector ℕ n →. ℕ) : (Fin n → ℕ) → Part ℕ :=
  fun x => f (List.Vector.ofFn x)

/-- Round-trip: fromVectorFun ∘ toVectorFun = id -/
theorem fromVectorFun_toVectorFun {n : ℕ} (f : (Fin n → ℕ) → Part ℕ) :
    fromVectorFun (toVectorFun f) = f := by
  funext x
  simp only [fromVectorFun, toVectorFun]
  congr 1
  funext i
  exact List.Vector.get_ofFn x i

/-- Round-trip: toVectorFun ∘ fromVectorFun = id -/
theorem toVectorFun_fromVectorFun {n : ℕ} (f : List.Vector ℕ n →. ℕ) :
    toVectorFun (fromVectorFun f) = f := by
  funext v
  simp only [toVectorFun, fromVectorFun, List.Vector.ofFn_get]

/-! ## Helper lemmas for Partrec with ℕ output -/

/-- For functions with ℕ output, Part.map encode is the identity. -/
private theorem Part.map_encode_nat (x : Part ℕ) : Part.map Encodable.encode x = x := by
  ext m
  simp only [Part.mem_map_iff, Encodable.encode_nat]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact hk
  · intro hm; exact ⟨m, hm, rfl⟩

/-- For f : Vector ℕ n →. ℕ, Partrec is equivalent to Nat.Partrec on the decoded version. -/
private theorem Partrec_iff_bind {n : ℕ} (f : List.Vector ℕ n →. ℕ) :
    Partrec f ↔ Nat.Partrec (fun code =>
      (Part.ofOption (Encodable.decode₂ (List.Vector ℕ n) code)).bind f) := by
  rw [Partrec.bind_decode₂_iff]
  simp only [Part.map_encode_nat]

/-! ## Vector Encoding is URMComputable

We build the encoding of vectors using iterated pairing.
List encoding: [] ↦ 0, a :: l ↦ (Nat.pair a (encode l)) + 1
-/

/-- Encoding a list as a natural number, following the Encodable List ℕ instance. -/
def encodeList : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.pair a (encodeList l) + 1

theorem encodeList_eq_encode (l : List ℕ) : encodeList l = Encodable.encode l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encodeList, Encodable.encode_list_cons, Encodable.encode_nat, ih]

/-- The encoding function for Vector ℕ n matches our encodeList. -/
theorem encode_vector_eq (v : List.Vector ℕ n) :
    Encodable.encode v = encodeList v.toList :=
  (encodeList_eq_encode v.toList).symm

/-- Vector.ofFn produces a list that matches List.ofFn. -/
private theorem vector_ofFn_toList {n : ℕ} (f : Fin n → ℕ) :
    (List.Vector.ofFn f).toList = List.ofFn f := List.Vector.toList_ofFn f

/-- The encoding of Vector.ofFn f equals encodeList (List.ofFn f). -/
theorem encode_vector_ofFn {n : ℕ} (f : Fin n → ℕ) :
    Encodable.encode (List.Vector.ofFn f) = encodeList (List.ofFn f) := by
  rw [encode_vector_eq, vector_ofFn_toList]

/-- The successor function on ℕ as URMComputable 1. -/
private theorem succ_1_computable : URMComputable 1 (fun x => Part.some (x 0 + 1)) :=
  URMComputable.succ_computable

/-- Successor of pair is URMComputable: (a, b) ↦ Nat.pair a b + 1. -/
private theorem succPair_computable :
    URMComputable 2 (fun xy => Part.some (Nat.pair (xy 0) (xy 1) + 1)) := by
  have h := URMComputable.comp_unary_total succ_1_computable pair_computable
  convert h using 1

/-- Constant 0 is URMComputable n for any n. -/
private theorem const_zero_computable (n : ℕ) : URMComputable n (fun _ => Part.some 0) := by
  use [Instr.Z 0]
  intro inputs
  let s := State.fromInputs (List.ofFn inputs)
  let s' := s.write 0 0
  have hstep : Step [Instr.Z 0] ⟨0, s⟩ ⟨1, s'⟩ := Step.zero rfl
  have hhalted : (⟨1, s'⟩ : Config).isHalted [Instr.Z 0] := by simp
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨⟨1, s'⟩, Steps.single hstep, hhalted⟩
  · intro hHalts _
    obtain ⟨hsteps, hhalted'⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps hhalted' (Steps.single hstep) hhalted
    simp only [Result, heq, State.output, s', s, State.write,
      Function.update_self, Part.get_some]

/-- In [Z 0].concat p, stepping from pc ≥ 1 preserves pc ≥ 1.
    Jump targets in the shifted p are all ≥ 1 since they're offset by 1. -/
private theorem step_concat_Z0_preserves_pc_ge_one {p : Program} {c c' : Config}
    (hstep : Step (Program.concat [Instr.Z 0] p) c c') (hc : c.pc ≥ 1) : c'.pc ≥ 1 := by
  cases hstep with
  | zero _ => simp only; omega
  | succ _ => simp only; omega
  | trans _ => simp only; omega
  | jump_eq h _ =>
    simp only [Program.concat, List.length_singleton] at h
    rw [List.getElem?_append_right (by omega : 1 ≤ c.pc)] at h
    simp only [Program.shiftJumps, List.getElem?_map, List.length_singleton] at h
    cases hp' : p[c.pc - 1]? with
    | none => simp [hp'] at h
    | some i => cases i with
      | J m n q =>
        simp only [Instr.shiftJumps, hp', Option.map_some] at h
        simp only [Option.some.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        simp only; omega
      | _ => simp [Instr.shiftJumps, hp'] at h
  | jump_ne _ => simp only; omega

/-- All configs reachable from a config with pc ≥ 1 in [Z 0].concat p have pc ≥ 1. -/
private theorem steps_preserves_pc_ge1 {p : Program} {c c' : Config}
    (hsteps : Steps (Program.concat [Instr.Z 0] p) c c') (hc : c.pc ≥ 1) : c'.pc ≥ 1 := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact hc
  | @head a b hstep _ ih => exact ih (step_concat_Z0_preserves_pc_ge_one hstep hc)

/-- Convert steps in [Z 0].concat p (starting from pc ≥ 1) to steps in p. -/
private theorem steps_concat_to_steps_p {p : Program} {c c' : Config}
    (hsteps : Steps (Program.concat [Instr.Z 0] p) c c') (hc : c.pc ≥ 1) :
    Steps p ⟨c.pc - 1, c.state⟩ ⟨c'.pc - 1, c'.state⟩ := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep hrest' ih =>
    have ha_pc : a.pc ≥ 1 := hc
    have hb_pc : b.pc ≥ 1 := step_concat_Z0_preserves_pc_ge_one hstep ha_pc
    -- Extract that the step is within bounds
    have hlt_concat : a.pc < (Program.concat [Instr.Z 0] p).length := Step.pc_lt_length hstep
    simp only [Program.concat_length, List.length_singleton] at hlt_concat
    have hlt : a.pc - 1 < p.length := by omega
    have hstep_p : Step p ⟨a.pc - 1, a.state⟩ ⟨b.pc - 1, b.state⟩ := by
      have hinstr_concat : (Program.concat [Instr.Z 0] p)[a.pc]? =
          (p.shiftJumps 1)[a.pc - 1]? := by
        rw [Program.getElem?_concat_right]
        · simp only [List.length_singleton]
        · simp only [List.length_singleton]; omega
      have hinstr_shift : (p.shiftJumps 1)[a.pc - 1]? =
          p[a.pc - 1]?.map (Instr.shiftJumps 1) := Program.getElem?_shiftJumps 1 p _
      cases hstep with
      | zero h =>
        rw [hinstr_concat, hinstr_shift] at h
        cases hp' : p[a.pc - 1]? with
        | none => simp [hp'] at h
        | some i =>
          cases i <;> simp [Instr.shiftJumps, hp'] at h
          dsimp only -- reduce struct projections
          have hpc_eq : (a.pc + 1) - 1 = (a.pc - 1) + 1 := by omega
          rw [hpc_eq]
          exact Step.zero (by rw [hp', h])
      | succ h =>
        rw [hinstr_concat, hinstr_shift] at h
        cases hp' : p[a.pc - 1]? with
        | none => simp [hp'] at h
        | some i =>
          cases i <;> simp [Instr.shiftJumps, hp'] at h
          dsimp only -- reduce struct projections
          have hpc_eq : (a.pc + 1) - 1 = (a.pc - 1) + 1 := by omega
          rw [hpc_eq]
          exact Step.succ (by rw [hp', h])
      | trans h =>
        rw [hinstr_concat, hinstr_shift] at h
        cases hp' : p[a.pc - 1]? with
        | none => simp [hp'] at h
        | some i =>
          cases i <;> simp [Instr.shiftJumps, hp'] at h
          dsimp only -- reduce struct projections
          have hpc_eq : (a.pc + 1) - 1 = (a.pc - 1) + 1 := by omega
          rw [hpc_eq]
          obtain ⟨h1, h2⟩ := h
          exact Step.trans (by rw [hp', h1, h2])
      | jump_eq h heq =>
        rw [hinstr_concat, hinstr_shift] at h
        cases hp' : p[a.pc - 1]? with
        | none => simp [hp'] at h
        | some i =>
          cases i with
          | J m' n' q' =>
            simp [Instr.shiftJumps, hp'] at h
            obtain ⟨rfl, rfl, hq⟩ := h
            dsimp only -- reduce struct projections
            rw [← hq]
            simp only [Nat.add_sub_cancel]
            exact Step.jump_eq (by rw [hp']) heq
          | _ => simp [Instr.shiftJumps, hp'] at h
      | jump_ne h hne =>
        rw [hinstr_concat, hinstr_shift] at h
        cases hp' : p[a.pc - 1]? with
        | none => simp [hp'] at h
        | some i =>
          cases i with
          | J m' n' q' =>
            simp [Instr.shiftJumps, hp'] at h
            obtain ⟨rfl, rfl, -⟩ := h
            dsimp only -- reduce struct projections
            have hpc_eq : (a.pc + 1) - 1 = (a.pc - 1) + 1 := by omega
            rw [hpc_eq]
            exact Step.jump_ne (by rw [hp']) hne
          | _ => simp [Instr.shiftJumps, hp'] at h
    exact Relation.ReflTransGen.head hstep_p (ih hb_pc)

/-- After Z 0, the state from input [x] becomes the same as the empty input state. -/
private theorem state_after_Z0_eq_fromInputs_nil (x : ℕ) :
    (State.fromInputs [x]).write 0 0 = State.fromInputs [] := by
  funext r
  simp only [State.write, State.fromInputs, Function.update]
  split_ifs with hr
  · simp [List.getD]
  · rcases r with _ | r'
    · contradiction
    · simp [List.getD]

/-- Lift URMComputable 0 to URMComputable 1 for constant functions.
    If f : (Fin 0 → ℕ) → Part ℕ is URMComputable 0, then (fun _ => f Fin.elim0) is URMComputable 1.
    The idea is to prepend Z 0 to reset R₀, making the initial state match the 0-arity case. -/
private theorem URMComputable_zero_to_one {f : (Fin 0 → ℕ) → Part ℕ} (hf : URMComputable 0 f) :
    URMComputable 1 (fun _ => f Fin.elim0) := by
  obtain ⟨p, hp⟩ := hf
  -- Prepend Z 0 to the program using concat (which shifts jumps)
  use Program.concat [Instr.Z 0] p
  intro inputs
  let x := inputs 0
  -- The input list is just [x]
  have hinputs_eq : List.ofFn inputs = [x] := by simp [List.ofFn_succ, x]
  -- Key state equality: after Z 0 on [x], state equals State.fromInputs []
  have hstate_eq : (State.fromInputs [x]).write 0 0 = State.fromInputs [] :=
    state_after_Z0_eq_fromInputs_nil x
  -- After Z 0, R₀ = 0, same as the 0-arity initial state. Then p computes f Fin.elim0
  have h0 := hp Fin.elim0
  -- First step: Z 0 executes
  have hZ0_step : Step (Program.concat [Instr.Z 0] p) (Config.init [x])
      ⟨1, (State.fromInputs [x]).write 0 0⟩ := by
    apply Step.zero
    simp only [Program.concat, Program.shiftJumps, Config.init]
    rfl
  -- After the first step, we're at pc=1 with state = State.fromInputs []
  have hafter_Z0 : (⟨1, (State.fromInputs [x]).write 0 0⟩ : Config) = ⟨1, State.fromInputs []⟩ := by
    simp only [Config.mk.injEq, true_and]; exact hstate_eq
  -- Simplify h0 to use [] instead of List.ofFn Fin.elim0
  have hlist_eq : List.ofFn (Fin.elim0 : Fin 0 → ℕ) = [] := rfl
  simp only [hlist_eq] at h0
  simp only [hinputs_eq]
  constructor
  · -- Halts iff f Fin.elim0 is defined
    constructor
    · -- Forward: concat halts → f Fin.elim0 is defined
      intro hHalts_concat
      -- p halts on [] iff f Fin.elim0 is defined
      have hiff := h0.1
      -- concat halts → p halts (by extracting execution after Z 0)
      -- The key insight: execution in [Z 0].concat p after the first step
      -- corresponds exactly to execution in p (with shifted pcs)
      have hp_halts : Halts p [] := by
        obtain ⟨c, hsteps, hhalted⟩ := hHalts_concat
        simp only [Config.isHalted, Program.concat_length, List.length_singleton] at hhalted
        -- First step must be Z 0
        have hsteps' : Steps (Program.concat [Instr.Z 0] p) (Config.init [x]) c := hsteps
        -- Use a helper: extract the path structure
        have hpc_init : (Config.init [x]).pc = 0 := rfl
        have hpc_halted : c.pc ≥ 1 + p.length := hhalted
        -- There must be at least one step (since init.pc = 0 < 1 + p.length ≤ c.pc)
        have hne : Config.init [x] ≠ c := by
          intro heq
          subst heq
          simp only [Config.init] at hhalted
          omega
        -- Extract the first step using cases_head
        rcases Relation.ReflTransGen.cases_head hsteps' with heq | ⟨mid, hfirst, hrest⟩
        · exact absurd heq hne
        have hmid_eq := Step.deterministic hfirst hZ0_step
        -- After Z 0, we're at ⟨1, State.fromInputs []⟩
        -- Build corresponding steps in p using the helper lemma
        have hsteps_p : Steps p (Config.init []) ⟨c.pc - 1, c.state⟩ := by
          rw [hmid_eq, hafter_Z0] at hrest
          -- Use the helper lemma to convert concat steps to p steps
          exact steps_concat_to_steps_p hrest (by decide)
        exact ⟨⟨c.pc - 1, c.state⟩, hsteps_p, by simp only [Config.isHalted] at hhalted ⊢; omega⟩
      exact hiff.mp hp_halts
    · -- Backward: f Fin.elim0 is defined → concat halts
      intro hDom
      have hp_halts := h0.1.mpr hDom
      obtain ⟨c, hsteps, hhalted⟩ := hp_halts
      -- Lift steps from p to concat using Steps.concat_right
      have hsteps' := Steps.concat_right (p1 := [Instr.Z 0]) hsteps
      simp only [List.length_singleton] at hsteps'
      use ⟨c.pc + 1, c.state⟩
      constructor
      · apply Relation.ReflTransGen.head hZ0_step
        rw [hafter_Z0]
        convert hsteps' using 2
      · simp only [Config.isHalted, Program.concat_length, List.length_singleton] at hhalted ⊢
        omega
  · intro hHalts_concat hDom
    -- Result is the same as the 0-arity case
    have h2 := h0.2
    -- Get halting info for both programs
    have hp_halts : Halts p [] := h0.1.mpr hDom
    -- The result from p equals f Fin.elim0
    have hp_result := h2 hp_halts hDom
    -- Show that the concat program halts with the same state as p
    have hHalts_copy := hHalts_concat
    obtain ⟨c_concat, hsteps_concat, hhalted_concat⟩ := hHalts_concat
    have hp_halts_copy := hp_halts
    obtain ⟨c_p, hsteps_p, hhalted_p⟩ := hp_halts
    -- Lift steps from p to concat
    have hsteps_lifted := Steps.concat_right (p1 := [Instr.Z 0]) hsteps_p
    simp only [List.length_singleton] at hsteps_lifted
    have hsteps_from_1 : Steps (Program.concat [Instr.Z 0] p) ⟨1, State.fromInputs []⟩
        ⟨c_p.pc + 1, c_p.state⟩ := by convert hsteps_lifted using 2
    -- Decompose the concat execution
    have hne : Config.init [x] ≠ c_concat := by
      intro h_eq
      subst h_eq
      simp only [Config.isHalted, Program.concat_length, List.length_singleton,
        Config.init] at hhalted_concat
      omega
    rcases Relation.ReflTransGen.cases_head hsteps_concat with h_eq | ⟨mid, hfirst, hrest⟩
    · exact absurd h_eq hne
    have hmid_eq := Step.deterministic hfirst hZ0_step
    rw [hmid_eq, hafter_Z0] at hrest
    have hhalted' : c_concat.isHalted (Program.concat [Instr.Z 0] p) := hhalted_concat
    have hhalted_lifted : (⟨c_p.pc + 1, c_p.state⟩ : Config).isHalted
        (Program.concat [Instr.Z 0] p) := by
      simp only [Config.isHalted, Program.concat_length, List.length_singleton] at hhalted_p ⊢
      omega
    have hconfigs_eq := Steps.halts_unique hrest hhalted' hsteps_from_1 hhalted_lifted
    -- Show the states match: c_concat.state = c_p.state
    have hstate_eq' : c_concat.state = c_p.state := by
      have h := congrArg Config.state hconfigs_eq
      simp only at h
      exact h
    -- Now show Result for concat equals Result for p
    simp only [Result, State.output]
    -- The Classical.choose for concat halts at some c_concat'
    -- By uniqueness, c_concat'.state = c_concat.state = c_p.state = c_p'.state
    obtain ⟨hsteps_chosen, hhalted_chosen⟩ := Classical.choose_spec hHalts_copy
    have hchosen_eq := Steps.halts_unique hsteps_concat hhalted_concat hsteps_chosen hhalted_chosen
    have hstate_concat : (Classical.choose hHalts_copy).state = c_concat.state :=
      congrArg Config.state hchosen_eq.symm
    have hstate_p := Classical.choose_spec hp_halts_copy
    have hchosen_eq_p := Steps.halts_unique hsteps_p hhalted_p hstate_p.1 hstate_p.2
    -- Goal: (Classical.choose hHalts_copy).state 0 = (f Fin.elim0).get hDom
    -- hstate_concat : (Classical.choose hHalts_copy).state = c_concat.state
    -- hstate_eq' : c_concat.state = c_p.state
    -- hchosen_eq_p : c_p = Classical.choose hp_halts_copy
    -- hp_result : Result p [] hp_halts_copy = (f Fin.elim0).get hDom
    rw [hstate_concat, hstate_eq', ← congrArg Config.state hchosen_eq_p.symm]
    -- Goal is now: (Classical.choose hp_halts_copy).state 0 = (f Fin.elim0).get hDom
    exact hp_result

/-- Encoding for n=0: empty vector encodes to 0. -/
private theorem encodeVector_zero_computable :
    URMComputable 0 (fun _ => Part.some (Encodable.encode (List.Vector.nil : List.Vector ℕ 0))) := by
  convert const_zero_computable 0

/-- Project the i-th component as URMComputable n. -/
private theorem proj_n_computable (n : ℕ) (i : Fin n) :
    URMComputable n (fun x => Part.some (x i)) :=
  URMComputable.proj_computable n i

/-- Encoding vectors of length n is URMComputable n.
This is the key lemma: we build it inductively using pairing. -/
theorem encodeVector_computable (n : ℕ) :
    URMComputable n (fun x => Part.some (Encodable.encode (List.Vector.ofFn x))) := by
  induction n with
  | zero => convert encodeVector_zero_computable using 1
  | succ n ih =>
    -- For n+1, encode [x₀, x₁, ..., xₙ] = Nat.pair x₀ (encode [x₁, ..., xₙ]) + 1
    -- We need to compose succPair with (proj 0, encode ∘ tail)

    -- First, show that encoding the tail is URMComputable (n+1)
    have h_tail : URMComputable (n + 1) (fun x => Part.some (Encodable.encode
        (List.Vector.ofFn (fun i : Fin n => x i.succ)))) := by
      cases n with
      | zero =>
        -- When n = 0, the tail is empty, encoded as 0
        convert const_zero_computable 1 using 1
      | succ n' =>
        -- Use ih composed with projections for indices 1, 2, ..., n
        haveI : NeZero (n' + 1) := ⟨Nat.succ_ne_zero n'⟩
        have hgs : ∀ i : Fin (n' + 1), URMComputable (n' + 1 + 1) (fun x => Part.some (x i.succ)) :=
          fun i => proj_n_computable (n' + 2) i.succ
        have h_comp := URMComputable.comp_general ih hgs
        convert h_comp.toComputable using 1
        funext x
        simp only [compFunction, Part.sequence_some, Part.bind_some]

    -- Now compose succPair with (proj 0, tail encoding)
    have h_result := URMComputable.comp_binary_total succPair_computable
      (proj_n_computable (n + 1) 0) h_tail
    convert h_result using 1

/-! ## Nat.Partrec' → URMComputable n -/

/-- Composing URMComputable1 with URMComputable n (total) gives URMComputable n. -/
theorem URMComputable.comp_with_total {n : ℕ} {f : ℕ →. ℕ} {g : (Fin n → ℕ) → ℕ}
    (hf : URMComputable1 f) (hg : URMComputable n (fun x => Part.some (g x))) :
    URMComputable n (fun x => f (g x)) := by
  unfold URMComputable1 at hf
  let gs : Fin 1 → (Fin n → ℕ) → Part ℕ := fun _ x => Part.some (g x)
  have hgs : ∀ i, URMComputable n (gs i) := fun _ => hg
  have h := URMComputable.comp_general hf hgs
  convert h.toComputable using 1
  funext x
  simp only [compFunction, gs, Part.sequence_some, Part.bind_some]

/-- Every n-ary partial recursive function is n-ary URM-computable.

Strategy:
1. From Nat.Partrec' f, get Nat.Partrec (decode >>= f) via part_iff
2. Convert to URMComputable1 via Nat.Partrec.toURMComputable1
3. Compose with vector encoding (which is URMComputable n) -/
theorem Nat.Partrec'.toURMComputable {n : ℕ} {f : List.Vector ℕ n →. ℕ}
    (hf : Nat.Partrec' f) : URMComputable n (fromVectorFun f) := by
  -- Step 1: Get Partrec f from Nat.Partrec' f
  rw [Nat.Partrec'.part_iff] at hf

  -- Step 2: Get Nat.Partrec for the encoded function
  have h_nat_partrec : Nat.Partrec (fun code =>
      (Part.ofOption (Encodable.decode₂ (List.Vector ℕ n) code)).bind f) := by
    rw [← Partrec_iff_bind]
    exact hf

  -- Step 3: Convert to URMComputable1
  have h_urm1 : URMComputable1 (fun code =>
      (Part.ofOption (Encodable.decode₂ (List.Vector ℕ n) code)).bind f) :=
    Nat.Partrec.toURMComputable1 h_nat_partrec

  -- Step 4: Vector encoding is URMComputable n (total)
  have h_encode : URMComputable n (fun x => Part.some (Encodable.encode (List.Vector.ofFn x))) :=
    encodeVector_computable n

  -- Step 5: Compose
  have h_composed := URMComputable.comp_with_total h_urm1 h_encode

  -- Step 6: Show this equals fromVectorFun f
  convert h_composed using 1
  funext x
  simp only [fromVectorFun]
  -- Need: f (Vector.ofFn x) = decode₂ (encode (Vector.ofFn x)) >>= f
  -- By decode₂_encode: decode₂ (encode v) = some v
  rw [Encodable.decode₂_encode, Part.coe_some, Part.bind_some]

/-! ## URMComputable n → Nat.Partrec'

For the forward direction, we need to show that if f is URMComputable n, then
the function (fun code => decode₂ code >>= toVectorFun f) is Nat.Partrec.

The key insight is that vector decoding is Computable (via Primcodable), and
Partrec is closed under composition with Computable functions.
-/

/-- Get the "rest" code after removing the head from a list encoding.
    For c encoding [a, ...], returns the code for [...]. -/
private def listRestCode (c : ℕ) : ℕ := (c - 1).unpair.2

/-- Get the head element from a list encoding (0 if empty). -/
private def listHeadCode (c : ℕ) : ℕ := (c - 1).unpair.1

/-- Iterate listRestCode k times to get the code for the k-th tail. -/
private def listNthTailCode (k c : ℕ) : ℕ := Nat.iterate listRestCode k c

/-- Extract the k-th element from a list code (assuming valid). -/
private def extractListElem (k c : ℕ) : ℕ := listHeadCode (listNthTailCode k c)

/-- Predecessor as URMComputable1. -/
private theorem pred1_computable : URMComputable1 (fun c => Part.some (c - 1)) := by
  unfold URMComputable1
  convert pred_computable using 1

/-- listRestCode is URMComputable1. -/
private theorem listRestCode_computable : URMComputable1 (fun c => Part.some (listRestCode c)) := by
  -- listRestCode c = (c - 1).unpair.2
  have h := URMComputable1.comp URMComputable1.right pred1_computable
  convert h using 1
  funext c
  unfold listRestCode
  show Part.some (Nat.unpair (c - 1)).2 = (Part.some (c - 1)).bind fun n => Part.some n.unpair.2
  rw [Part.bind_some]

/-- listHeadCode is URMComputable1. -/
private theorem listHeadCode_computable : URMComputable1 (fun c => Part.some (listHeadCode c)) := by
  -- listHeadCode c = (c - 1).unpair.1
  have h := URMComputable1.comp URMComputable1.left pred1_computable
  convert h using 1
  funext c
  unfold listHeadCode
  show Part.some (Nat.unpair (c - 1)).1 = (Part.some (c - 1)).bind fun n => Part.some n.unpair.1
  rw [Part.bind_some]

/-- listNthTailCode is URMComputable1 for any fixed k.
    This iterates listRestCode k times. -/
private theorem listNthTailCode_computable (k : ℕ) :
    URMComputable1 (fun c => Part.some (listNthTailCode k c)) := by
  induction k with
  | zero =>
    -- listNthTailCode 0 c = c (identity)
    convert URMComputable.proj_computable 1 0 using 1
  | succ k ih =>
    -- listNthTailCode (k+1) c = listRestCode (listNthTailCode k c)
    have h := URMComputable1.comp listRestCode_computable ih
    convert h using 1
    funext c
    simp only [listNthTailCode, Function.iterate_succ', Function.comp_apply,
      Part.bind_eq_bind, Part.bind_some]

/-- extractListElem is URMComputable1 for any fixed k. -/
private theorem extractListElem_computable (k : ℕ) :
    URMComputable1 (fun c => Part.some (extractListElem k c)) := by
  -- extractListElem k c = listHeadCode (listNthTailCode k c)
  have h := URMComputable1.comp listHeadCode_computable (listNthTailCode_computable k)
  convert h using 1
  funext c
  simp only [extractListElem, Part.bind_eq_bind, Part.bind_some]

/-- Check if a code represents an empty list (code = 0). -/
private def isEmptyList (c : ℕ) : ℕ := if c = 0 then 1 else 0

/-- Constant 1 is URMComputable n for any n. -/
private theorem const_one_n_computable' (n : ℕ) : URMComputable n (fun _ => Part.some 1) := by
  use [Instr.Z 0, Instr.S 0]
  intro inputs
  let s0 := State.fromInputs (List.ofFn inputs)
  let s1 := s0.write 0 0
  let s2 := s1.write 0 (s1.read 0 + 1)
  have hstep1 : Step [Instr.Z 0, Instr.S 0] ⟨0, s0⟩ ⟨1, s1⟩ := Step.zero rfl
  have hstep2 : Step [Instr.Z 0, Instr.S 0] ⟨1, s1⟩ ⟨2, s2⟩ := Step.succ rfl
  have hhalted : (⟨2, s2⟩ : Config).isHalted [Instr.Z 0, Instr.S 0] := by simp
  have hsteps : Steps [Instr.Z 0, Instr.S 0] (Config.init (List.ofFn inputs)) ⟨2, s2⟩ := by aesop_steps
  constructor
  · simp only [Part.some_dom, iff_true]
    exact ⟨⟨2, s2⟩, hsteps, hhalted⟩
  · intro hHalts _
    obtain ⟨hsteps', hhalted'⟩ := Classical.choose_spec hHalts
    have heq := Steps.halts_unique hsteps' hhalted' hsteps hhalted
    simp only [Result, heq, State.output, s2, s1, s0, State.write, State.read,
      Function.update_self, Part.get_some]

/-- Constant 1 as URMComputable1. -/
private theorem const_one_1_computable' : URMComputable1 (fun _ => Part.some 1) := by
  unfold URMComputable1
  exact const_one_n_computable' 1

/-- Helper: mkPair' a b = Fin.cons a (Fin.cons b Fin.elim0) -/
private def mkPair' (a b : ℕ) : Fin 2 → ℕ := Fin.cons a (Fin.cons b Fin.elim0)

@[simp] private theorem mkPair'_zero (a b : ℕ) : mkPair' a b 0 = a := rfl
@[simp] private theorem mkPair'_one (a b : ℕ) : mkPair' a b 1 = b := rfl

/-- isEmptyList is URMComputable1.
    isEmptyList c = 1 - sign(c), where sign(0) = 0, sign(n+1) = 1. -/
private theorem isEmptyList_computable :
    URMComputable1 (fun c => Part.some (isEmptyList c)) := by
  -- isEmptyList c = 1 - sign(c)
  have h_sign : URMComputable1 (fun c => Part.some (if c = 0 then 0 else 1)) := by
    unfold URMComputable1
    convert sign_computable using 1
  -- Use sub_computable with const 1 and sign
  have h_sub : URMComputable 2 (fun xy => Part.some (xy 0 - xy 1)) := sub_computable
  -- Build composition: (fun c => sub (1, sign c))
  have h := URMComputable.comp_binary_total h_sub const_one_1_computable' h_sign
  unfold URMComputable1
  convert h using 1
  funext c
  simp only [isEmptyList]
  by_cases hc : c 0 = 0
  · simp only [hc, ↓reduceIte]
    rfl
  · simp only [hc, ↓reduceIte]
    rfl

/-- Check if listNthTailCode k c = 0 (i.e., the k-th tail is empty).
    This is true iff the list has exactly k elements. -/
private def tailIsEmpty (k c : ℕ) : ℕ := isEmptyList (listNthTailCode k c)

/-- tailIsEmpty k is URMComputable1 for fixed k. -/
private theorem tailIsEmpty_computable (k : ℕ) :
    URMComputable1 (fun c => Part.some (tailIsEmpty k c)) := by
  have h := URMComputable1.comp isEmptyList_computable (listNthTailCode_computable k)
  convert h using 1
  funext c
  simp only [tailIsEmpty, Part.bind_eq_bind, Part.bind_some]

/-- Check if the k-th tail is non-empty (i.e., list has more than k elements). -/
private def tailIsNonEmpty (k c : ℕ) : ℕ := if listNthTailCode k c = 0 then 0 else 1

/-- tailIsNonEmpty k is URMComputable1 for fixed k. -/
private theorem tailIsNonEmpty_computable (k : ℕ) :
    URMComputable1 (fun c => Part.some (tailIsNonEmpty k c)) := by
  -- tailIsNonEmpty k c = sign(listNthTailCode k c)
  have h_sign : URMComputable1 (fun c => Part.some (if c = 0 then 0 else 1)) := by
    unfold URMComputable1
    convert sign_computable using 1
  have h := URMComputable1.comp h_sign (listNthTailCode_computable k)
  convert h using 1
  funext c
  simp only [tailIsNonEmpty, Part.bind_eq_bind, Part.bind_some]

/-- A code has valid length n if:
    - The n-th tail is empty (list has at most n elements)
    - If n > 0, the (n-1)-th tail is non-empty (list has at least n elements) -/
private def hasValidLength (n c : ℕ) : Prop :=
  -- n-th tail must be empty (at most n elements)
  -- AND for i < n, the i-th tail must be non-empty (at least n elements)
  listNthTailCode n c = 0 ∧ (∀ i < n, listNthTailCode i c ≠ 0)

/-- listRestCode 0 = 0 (empty list stays empty). -/
private theorem listRestCode_zero : listRestCode 0 = 0 := by
  simp [listRestCode]

/-- If listNthTailCode i c = 0, then listNthTailCode j c = 0 for all j ≥ i.
    This is because listRestCode 0 = 0 (empty list stays empty). -/
private theorem listNthTailCode_zero_propagates (c : ℕ) (i j : ℕ) (hi : listNthTailCode i c = 0) (hj : i ≤ j) :
    listNthTailCode j c = 0 := by
  induction j with
  | zero =>
    simp only [Nat.le_zero] at hj
    rw [hj] at hi; exact hi
  | succ j' ih =>
    cases Nat.lt_or_eq_of_le hj with
    | inl hlt =>
      have hi' : i ≤ j' := Nat.lt_succ_iff.mp hlt
      have hj'_zero := ih hi'
      simp only [listNthTailCode] at hj'_zero ⊢
      simp only [Function.iterate_succ', Function.comp_apply, hj'_zero, listRestCode_zero]
    | inr heq =>
      rw [← heq]; exact hi

/-- Alternative characterization: hasValidLength n c ↔ length n tail empty ∧ (n-1) tail non-empty (for n > 0). -/
private theorem hasValidLength_alt (n c : ℕ) :
    hasValidLength n c ↔
      listNthTailCode n c = 0 ∧
      (n = 0 ∨ listNthTailCode (n - 1) c ≠ 0) := by
  constructor
  · intro ⟨htail_empty, hprev_nonempty⟩
    constructor
    · exact htail_empty
    · cases n with
      | zero => left; rfl
      | succ n' =>
        right
        exact hprev_nonempty n' (Nat.lt_succ_self n')
  · intro ⟨htail_empty, hprev⟩
    constructor
    · exact htail_empty
    · intro i hi
      cases hprev with
      | inl h0 => omega
      | inr hprev' =>
        by_contra h
        have : listNthTailCode (n - 1) c = 0 := listNthTailCode_zero_propagates c i (n - 1) h (by omega)
        exact hprev' this

/-- Numeric indicator for hasValidLength: 1 if valid, 0 otherwise. -/
private def hasValidLengthNum (n c : ℕ) : ℕ :=
  -- tailIsEmpty n c * (if n = 0 then 1 else tailIsNonEmpty (n-1) c)
  tailIsEmpty n c * (if n = 0 then 1 else tailIsNonEmpty (n - 1) c)

/-- hasValidLengthNum correctly indicates hasValidLength. -/
private theorem hasValidLengthNum_eq (n c : ℕ) :
    hasValidLengthNum n c = 1 ↔ hasValidLength n c := by
  simp only [hasValidLengthNum, tailIsEmpty, tailIsNonEmpty, isEmptyList]
  rw [hasValidLength_alt]
  constructor
  · intro h
    by_cases hn : n = 0
    · -- n = 0 case
      subst hn
      simp only [↓reduceIte, Nat.mul_one] at h
      by_cases htail : listNthTailCode 0 c = 0
      · exact ⟨htail, Or.inl rfl⟩
      · simp only [htail, ↓reduceIte] at h; omega
    · -- n ≠ 0 case
      simp only [hn, ↓reduceIte] at h
      by_cases htail : listNthTailCode n c = 0
      · simp only [htail, ↓reduceIte, Nat.one_mul] at h
        by_cases hprev : listNthTailCode (n - 1) c = 0
        · simp only [hprev, ↓reduceIte] at h; omega
        · exact ⟨htail, Or.inr hprev⟩
      · simp only [htail, ↓reduceIte, Nat.zero_mul] at h; omega
  · intro ⟨htail, hprev⟩
    simp only [htail, ↓reduceIte, Nat.one_mul]
    cases hprev with
    | inl h0 => simp [h0]
    | inr hne =>
      have hne0 : ¬n = 0 := by
        intro h0
        subst h0
        simp only [listNthTailCode] at htail
        -- When n=0, listNthTailCode 0 c = c, and htail says c = 0
        -- But hne says listNthTailCode (0-1) c ≠ 0, i.e., c ≠ 0
        -- This is a contradiction
        simp only [listNthTailCode] at hne
        exact hne htail
      simp only [hne, ↓reduceIte, hne0]

/-- hasValidLengthNum is URMComputable1 for fixed n. -/
private theorem hasValidLengthNum_computable (n : ℕ) :
    URMComputable1 (fun c => Part.some (hasValidLengthNum n c)) := by
  cases n with
  | zero =>
    -- hasValidLengthNum 0 c = tailIsEmpty 0 c * 1 = tailIsEmpty 0 c = isEmptyList c
    convert tailIsEmpty_computable 0 using 1
    funext c
    simp [hasValidLengthNum]
  | succ n' =>
    -- hasValidLengthNum (n'+1) c = tailIsEmpty (n'+1) c * tailIsNonEmpty n' c
    have h_mul := URMComputable.comp_binary_total mul_computable
      (tailIsEmpty_computable (n' + 1)) (tailIsNonEmpty_computable n')
    convert h_mul using 1

/-- Guard for validity: diverges if hasValidLengthNum n c ≠ 1, returns 0 otherwise.
    This uses minimization: rfind (fun _ => if valid then true else diverge) -/
private def guardValid (n : ℕ) (c : ℕ) : Part ℕ :=
  Nat.rfind fun _ => if hasValidLengthNum n c = 1 then Part.some true else Part.none

/-- guardValid returns 0 when valid, diverges when invalid. -/
private theorem guardValid_valid (n c : ℕ) (h : hasValidLengthNum n c = 1) :
    guardValid n c = Part.some 0 := by
  simp only [guardValid, h, ↓reduceIte]
  rw [Part.eq_some_iff, Nat.mem_rfind]
  constructor
  · simp only [Part.mem_some_iff]
  · intro m hm
    simp only [Part.mem_some_iff]
    omega

private theorem guardValid_invalid (n c : ℕ) (h : hasValidLengthNum n c ≠ 1) :
    guardValid n c = Part.none := by
  simp only [guardValid, h, ↓reduceIte]
  exact Nat.rfind_zero_none _ rfl

/-- If anything is a member of guardValid n c, it must be 0. -/
private theorem guardValid_mem_eq_zero {n c v : ℕ} (hv : v ∈ guardValid n c) : v = 0 := by
  by_cases h : hasValidLengthNum n c = 1
  · rw [guardValid_valid n c h, Part.mem_some_iff] at hv; exact hv
  · rw [guardValid_invalid n c h] at hv; exact (Part.notMem_none _ hv).elim

/-- The predicate function for guardValid's minimization. -/
private def guardValidPred (n : ℕ) : (Fin 2 → ℕ) → Part ℕ :=
  fun xy => Part.some (if hasValidLengthNum n (xy 0) = 1 then 0 else 1)

/-- guardValidPred is URMComputable 2 for fixed n. -/
private theorem guardValidPred_computable (n : ℕ) :
    URMComputable 2 (guardValidPred n) := by
  -- guardValidPred n (xy) = if hasValidLengthNum n (xy 0) = 1 then 0 else 1
  -- = 1 - (if hasValidLengthNum n (xy 0) = 1 then 1 else 0)
  -- The inner part equals hasValidLengthNum n (xy 0) when it's 0 or 1
  -- We know hasValidLengthNum only returns 0 or 1
  have h_inner : URMComputable 2 (fun xy => Part.some (hasValidLengthNum n (xy 0))) := by
    have h := URMComputable.comp_unary_total (hasValidLengthNum_computable n)
      (URMComputable.proj_computable 2 0)
    convert h using 1
  have h_const1 : URMComputable 2 (fun _ => Part.some 1) := const_one_n_computable' 2
  have h_sub := URMComputable.comp_binary_total sub_computable h_const1 h_inner
  convert h_sub using 1
  funext xy
  simp only [guardValidPred]
  -- hasValidLengthNum n c is always 0 or 1
  have h01 : hasValidLengthNum n (xy 0) = 0 ∨ hasValidLengthNum n (xy 0) = 1 := by
    simp only [hasValidLengthNum, tailIsEmpty, tailIsNonEmpty, isEmptyList]
    split_ifs <;> omega
  cases h01 with
  | inl h0 => simp [h0]
  | inr h1 => simp [h1]

/-- guardValid is URMComputable1 for fixed n. -/
private theorem guardValid_computable (n : ℕ) :
    URMComputable1 (guardValid n) := by
  unfold URMComputable1
  -- We show guardValid agrees with μFunction (guardValidPred n)
  have h_min := URMComputable.min (guardValidPred_computable n)
  have h_eq : ∀ x : Fin 1 → ℕ, guardValid n (x 0) = μFunction (guardValidPred n) x := by
    intro x
    -- Case split on validity
    by_cases hvalid : hasValidLengthNum n (x 0) = 1
    · -- Valid case: both return 0
      have hg : guardValid n (x 0) = Part.some 0 := guardValid_valid n (x 0) hvalid
      have hmu : μFunction (guardValidPred n) x = Part.some 0 := by
        simp only [μFunction, μ]
        rw [Part.eq_some_iff, Nat.mem_rfind]
        constructor
        · -- true ∈ checkZero predicate at 0
          simp only [checkZero, extendInputs, guardValidPred, Part.map_some, Part.mem_some_iff]
          -- Fin.snoc x 0 (0 : Fin 2) = x 0 because 0 < 1
          have h1 : (Fin.snoc x 0 : Fin 2 → ℕ) 0 = x 0 := by
            simp only [Fin.snoc, Fin.val_zero, Nat.zero_lt_one, ↓reduceDIte]
            rfl
          simp only [h1, hvalid, ↓reduceIte]
          decide
        · -- All k < 0 have Dom (vacuously true)
          intro k hk; omega
      rw [hg, hmu]
    · -- Invalid case: both diverge
      have hg : guardValid n (x 0) = Part.none := guardValid_invalid n (x 0) hvalid
      have hmu : μFunction (guardValidPred n) x = Part.none := by
        simp only [μFunction, μ]
        rw [Part.eq_none_iff]
        intro k
        rw [Nat.mem_rfind]
        push_neg
        intro htrue
        -- Fin.snoc x k (0 : Fin 2) = x 0 because 0 < 1
        have hsnoc : (Fin.snoc x k : Fin 2 → ℕ) 0 = x 0 := by
          simp only [Fin.snoc, Fin.val_zero, Nat.zero_lt_one, ↓reduceDIte]
          rfl
        simp only [checkZero, extendInputs, guardValidPred, Part.map_some, Part.mem_some_iff,
          hsnoc, hvalid, ↓reduceIte] at htrue
        -- htrue : true = decide (1 = 0) is a contradiction
        simp at htrue
      rw [hg, hmu]
  convert h_min.toComputable using 1
  funext x
  exact h_eq x

/-- For a non-empty list, listRestCode gives the encoding of the tail. -/
private theorem listRestCode_cons (a : ℕ) (l : List ℕ) :
    listRestCode (Encodable.encode (a :: l)) = Encodable.encode l := by
  simp only [listRestCode, Encodable.encode_list_cons]
  simp only [Nat.succ_sub_one, Nat.unpair_pair]

/-- For a non-empty list, listHeadCode gives the head element. -/
private theorem listHeadCode_cons (a : ℕ) (l : List ℕ) :
    listHeadCode (Encodable.encode (a :: l)) = a := by
  simp only [listHeadCode, Encodable.encode_list_cons, Encodable.encode_nat]
  simp only [Nat.succ_sub_one, Nat.unpair_pair]

/-- listNthTailCode on an encoded list gives the encoding of the k-th tail. -/
private theorem listNthTailCode_encode (l : List ℕ) (k : ℕ) (hk : k ≤ l.length) :
    listNthTailCode k (Encodable.encode l) = Encodable.encode (l.drop k) := by
  simp only [listNthTailCode]
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    match l with
    | [] =>
      simp only [List.length_nil] at hk
      omega
    | a :: l' =>
      simp only [Function.iterate_succ', Function.comp_apply, List.drop_succ_cons]
      have hk' : k ≤ l'.length := by simp only [List.length_cons] at hk; omega
      -- First use IH to simplify iterate^[k]
      have h1 : listRestCode^[k] (Encodable.encode (a :: l')) =
          Encodable.encode (List.drop k (a :: l')) := ih (a :: l') (by omega)
      rw [h1]
      -- Now drop k of (a :: l') for k ≤ length l' is a non-empty list
      have hdrop_ne : (List.drop k (a :: l')) ≠ [] := by
        intro hcontra
        have : (List.drop k (a :: l')).length = 0 := by rw [hcontra]; rfl
        simp only [List.length_drop, List.length_cons] at this
        omega
      match h : List.drop k (a :: l') with
      | [] => exact (hdrop_ne h).elim
      | b :: rest =>
        rw [listRestCode_cons]
        congr 1
        have hrest : List.drop 1 (b :: rest) = rest := rfl
        rw [← hrest, ← h, List.drop_drop]
        rfl

/-- Encoding a non-empty list gives a non-zero code. -/
private theorem encode_cons_ne_zero (a : ℕ) (l : List ℕ) :
    Encodable.encode (a :: l) ≠ 0 := by
  simp only [Encodable.encode_list_cons, ne_eq, Nat.succ_ne_zero, not_false_eq_true]

/-- hasValidLength holds for the encoding of any list. -/
private theorem hasValidLength_encode (l : List ℕ) :
    hasValidLength l.length (Encodable.encode l) := by
  constructor
  · -- n-th tail is empty
    rw [listNthTailCode_encode l l.length (Nat.le_refl _)]
    simp only [List.drop_length, Encodable.encode_list_nil]
  · -- all previous tails are non-empty
    intro i hi
    rw [listNthTailCode_encode l i (Nat.le_of_lt hi)]
    cases h : l.drop i with
    | nil =>
      exfalso
      have : (l.drop i).length = 0 := by rw [h]; rfl
      simp only [List.length_drop] at this
      omega
    | cons a l' =>
      exact encode_cons_ne_zero a l'

/-- Helper: listNthTailCode (n+1) c = listNthTailCode n (listRestCode c) -/
private theorem listNthTailCode_succ (n c : ℕ) :
    listNthTailCode (n + 1) c = listNthTailCode n (listRestCode c) := by
  simp only [listNthTailCode]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply] at ih ⊢
    rw [ih]

/-- If hasValidLength n c holds, then there exists a list l with length n such that encode l = c. -/
private theorem exists_list_of_hasValidLength {n c : ℕ} (hvalid : hasValidLength n c) :
    ∃ l : List ℕ, l.length = n ∧ Encodable.encode l = c := by
  induction n generalizing c with
  | zero =>
    use []
    simp only [List.length_nil, Encodable.encode_list_nil, true_and]
    -- hvalid.1 : listNthTailCode 0 c = 0, and listNthTailCode 0 c = c
    have h := hvalid.1
    simp only [listNthTailCode, Function.iterate_zero, id_eq] at h
    exact h.symm
  | succ n ih =>
    -- c ≠ 0 because the 0-th tail is non-empty
    have hc_ne : c ≠ 0 := hvalid.2 0 (Nat.zero_lt_succ n)
    -- So c = Nat.pair a rest + 1 for some a, rest
    have hc_pos : 0 < c := Nat.pos_of_ne_zero hc_ne
    let a := listHeadCode c
    let rest := listRestCode c
    -- hasValidLength n rest holds
    have hrest : hasValidLength n rest := by
      constructor
      · -- n-th tail of rest is empty
        have h := hvalid.1
        rw [listNthTailCode_succ] at h
        exact h
      · -- all previous tails of rest are non-empty
        intro i hi
        have h := hvalid.2 (i + 1) (by omega)
        rw [listNthTailCode_succ] at h
        exact h
    -- By IH, rest encodes some list l' of length n
    obtain ⟨l', hl'_len, hl'_enc⟩ := ih hrest
    -- Then c encodes a :: l'
    use a :: l'
    constructor
    · simp only [List.length_cons, hl'_len]
    · simp only [Encodable.encode_list_cons, Encodable.encode_nat]
      -- Goal: (Nat.pair a (Encodable.encode l')).succ = c
      -- We have: hl'_enc : Encodable.encode l' = rest = listRestCode c
      rw [hl'_enc]
      -- Now goal is: (Nat.pair a rest).succ = c
      -- a = listHeadCode c = (c-1).unpair.1
      -- rest = listRestCode c = (c-1).unpair.2
      simp only [a, listHeadCode, rest, listRestCode]
      rw [Nat.pair_unpair]
      omega

/-- extractListElem correctly retrieves elements from an encoded list. -/
private theorem extractListElem_encode (l : List ℕ) (k : ℕ) (hk : k < l.length) :
    extractListElem k (Encodable.encode l) = l.get ⟨k, hk⟩ := by
  simp only [extractListElem]
  rw [listNthTailCode_encode l k (Nat.le_of_lt hk)]
  cases h : l.drop k with
  | nil =>
    exfalso
    have : (l.drop k).length = 0 := by rw [h]; rfl
    simp only [List.length_drop] at this
    omega
  | cons a l' =>
    simp only [listHeadCode_cons]
    -- a is the head of l.drop k, which is l[k]
    have hdrop := List.drop_eq_getElem_cons hk
    rw [h] at hdrop
    -- hdrop : a :: l' = l[k] :: List.drop (k + 1) l
    have ha : a = l[k] := by
      have := congrArg List.head? hdrop
      simp only [List.head?_cons] at this
      exact Option.some.inj this
    rw [ha]
    rfl

/-- Decoding a valid n-element list code produces components matching extractListElem.
    This theorem establishes that hasValidLength exactly characterizes valid vector encodings,
    and that extractListElem correctly retrieves the corresponding vector elements. -/
private theorem decode_valid_extract {n : ℕ} (c : ℕ) (hvalid : hasValidLength n c) :
    ∃ v : List.Vector ℕ n, Encodable.decode₂ (List.Vector ℕ n) c = some v ∧
    ∀ i : Fin n, v.get i = extractListElem i.val c := by
  -- Use exists_list_of_hasValidLength to get the list
  obtain ⟨l, hl_len, hl_enc⟩ := exists_list_of_hasValidLength hvalid
  -- Construct the vector
  let v : List.Vector ℕ n := ⟨l, hl_len⟩
  use v
  constructor
  · -- decode₂ c = some v
    -- Since c = encode l and l.length = n, decode₂ should return some v
    rw [Encodable.decode₂_eq_some]
    -- encode v = encode v.toList = encode l = c
    show Encodable.encode v.toList = c
    exact hl_enc
  · -- ∀ i, v.get i = extractListElem i.val c
    intro i
    -- v.get i = l.get ⟨i, _⟩
    -- extractListElem i.val c = extractListElem i.val (encode l)
    -- By extractListElem_encode, this equals l.get ⟨i, _⟩
    rw [← hl_enc]
    have hi : i.val < l.length := by rw [hl_len]; exact i.isLt
    rw [extractListElem_encode l i.val hi]
    -- v.get i = l.get ⟨i, hi⟩
    simp only [List.Vector.get, v, List.get_eq_getElem]
    congr 1

/-- The function that guards validity and then applies f to extracted components. -/
private def guardAndApply {n : ℕ} (f : (Fin n → ℕ) → Part ℕ) (code : ℕ) : Part ℕ :=
  (guardValid n code).bind fun _ => f (fun i => extractListElem i.val code)

/-- guardAndApply agrees with decode₂ >>= toVectorFun f on valid codes. -/
private theorem guardAndApply_eq_decode_bind {n : ℕ} (f : (Fin n → ℕ) → Part ℕ) (code : ℕ) :
    guardAndApply f code =
    (Part.ofOption (Encodable.decode₂ (List.Vector ℕ n) code)).bind (toVectorFun f) := by
  simp only [guardAndApply]
  by_cases hvalid : hasValidLengthNum n code = 1
  · -- Code is valid
    rw [guardValid_valid n code hvalid, Part.bind_some]
    have hvalid' := (hasValidLengthNum_eq n code).mp hvalid
    obtain ⟨v, hdec, hget⟩ := decode_valid_extract code hvalid'
    simp only [hdec, Part.coe_some, Part.bind_some, toVectorFun]
    congr 1
    funext i
    exact (hget i).symm
  · -- Code is invalid
    rw [guardValid_invalid n code hvalid, Part.bind_none]
    -- Need to show decode₂ code = none (i.e., code doesn't encode a valid n-vector)
    -- By contrapositive: if decode₂ code = some v, then hasValidLength n code holds
    have hnotvalid : ¬hasValidLength n code := by
      intro hcontra
      have := (hasValidLengthNum_eq n code).mpr hcontra
      exact hvalid this
    -- Show decode₂ code = none by contrapositive
    cases hdec : Encodable.decode₂ (List.Vector ℕ n) code with
    | none => simp [Part.coe_none]
    | some v =>
      -- v : List.Vector ℕ n with decode₂ code = some v
      -- So code = encode v.toList and v.toList has length n
      exfalso
      rw [Encodable.decode₂_eq_some] at hdec
      -- hdec : encode v = code
      have hlen : v.toList.length = n := v.toList_length
      have henc : Encodable.encode v.toList = code := hdec
      have hvalid' := hasValidLength_encode v.toList
      rw [hlen, henc] at hvalid'
      exact hnotvalid hvalid'

/-- guardAndApply is URMComputable1 when f is URMComputable n. -/
private theorem guardAndApply_computable {n : ℕ} {f : (Fin n → ℕ) → Part ℕ}
    (hf : URMComputable n f) : URMComputable1 (guardAndApply f) := by
  unfold URMComputable1
  -- guardAndApply f code = guardValid n code >>= fun _ => f (fun i => extractListElem i code)
  -- = guardValid n code >>= fun _ => f (gs code)
  -- where gs code i = extractListElem i code

  -- Step 1: Build the function that extracts all n components
  -- For each i : Fin n, extractListElem i.val code is URMComputable1
  have h_extract : ∀ i : Fin n, URMComputable 1 (fun x => Part.some (extractListElem i.val (x 0))) := by
    intro i
    convert extractListElem_computable i.val using 1

  -- Step 2: Build g : ℕ → Part ℕ that computes f applied to extracted components
  -- g code = f (fun i => extractListElem i.val code)
  have h_f_extract : URMComputable 1 (fun x => f (fun i => extractListElem i.val (x 0))) := by
    by_cases hn : n = 0
    · -- When n = 0, f : (Fin 0 → ℕ) → Part ℕ is essentially a constant
      -- since there's only one function from Fin 0 to ℕ (the empty function)
      subst hn
      have heq : ∀ x : Fin 1 → ℕ, (fun i : Fin 0 => extractListElem i.val (x 0)) = Fin.elim0 := by
        intro x; funext i; exact i.elim0
      simp only [heq]
      -- f Fin.elim0 is a constant Part value, which is URMComputable 0 by hf
      -- Use the lifting lemma to convert URMComputable 0 to URMComputable 1
      exact URMComputable_zero_to_one hf
    · -- When n > 0, use comp_general
      haveI : NeZero n := ⟨hn⟩
      have hgs : ∀ i : Fin n, URMComputable 1 (fun x => Part.some (extractListElem i.val (x 0))) := h_extract
      have h := URMComputable.comp_general hf hgs
      convert h.toComputable using 1
      funext x
      simp only [compFunction, Part.sequence_some, Part.bind_some]

  -- Step 3: guardValid returns 0 when valid, so we need to sequence it with f_extract
  -- guardAndApply f code = guardValid n code >>= fun _ => f_extract code
  -- This is composition: first check validity (which returns 0 on success),
  -- then compute f on extracted components

  -- The issue is that guardValid returns 0, not the code, so we can't directly compose
  -- Instead, we use the pattern: pair the code with guardValid, then extract

  -- Alternative: use the fact that guardValid n code >>= fun _ => g code
  -- equals (fun _ => g code) 0 when valid, and Part.none when invalid

  -- We can express this as:
  -- (guardValid n code).bind (fun _ => f_extract code)
  -- = if valid then f_extract code else Part.none

  -- To make this URMComputable1, we use minimization differently
  -- Actually, we can use the following construction:
  -- Define h(code, y) = if y = 0 ∧ valid then (sign of f_extract code) else 1
  -- Then μ(h) gives us the minimization-based conditional

  -- Simpler approach: use the fact that URMComputable is closed under bind
  -- guardValid is URMComputable1, f_extract is URMComputable 1
  -- We need to show guardValid >>= (fun _ => f_extract) is URMComputable1

  -- Key insight: guardValid n code returns Part.some 0 when valid
  -- So guardValid n code >>= fun _ => g = g when valid, Part.none when invalid

  -- We can express this as:
  -- Code that: 1) checks validity, 2) if valid, computes f on extracted components
  -- The check causes divergence on invalid input

  -- Use composition with guardValid:
  -- Step A: Compute guardValid n code (returns 0 or diverges)
  -- Step B: Compute f on extracted components (ignoring the 0 from step A)

  -- Since we need both the code (to extract) and the guard result,
  -- we use pairing: pair(guardValid n code, f (extracted))
  -- Then project to second component

  -- Actually, simpler: guardValid returns 0, which we ignore
  -- The bind effectively sequences: first wait for guard, then compute f

  -- For URMComputable, we model this as:
  -- Compute guard + extract in parallel conceptually, but guard controls termination

  -- The cleanest approach: show that
  -- (fun code => guardValid n code >>= fun _ => f (extract code)) is URMComputable1

  -- This requires showing URMComputable1 is closed under bind when the
  -- second function ignores the bound value (i.e., is constant in the bound variable)

  -- Let's build: define F(code) = guardValid n code >>= fun _ => f(extract code)

  -- We use minimization. The predicate:
  -- P(code, y) = 1 if (y ≠ 0) OR (y = 0 AND f(extract code) is not defined yet)
  --            = 0 if y = 0 AND f(extract code) returns something

  -- Actually this is getting complex. Let's use a different approach:
  -- URMComputable is closed under minimization, so we can build the conditional.

  -- Cleaner construction:
  -- We compose guardValid with a constant that retrieves f(extracted)
  -- guardAndApply f code = (guardValid n code).bind (fun _ => f (fun i => extractListElem i code))

  -- The value passed to the bind (which is 0) is ignored
  -- We can model this as: pair(code, guardValid n code), then project code, then apply f_extract

  -- Use URMComputable1.comp: if h : URMComputable1 and g : URMComputable1,
  -- then (fun n => g n >>= h) : URMComputable1

  -- guardValid : URMComputable1
  -- We need (fun code => f (extract code)) : ℕ →. ℕ to be URMComputable1, which is h_f_extract

  -- But bind needs the second function to use the output of the first
  -- Here, we ignore it. So we need a different pattern.

  -- Use: guardAndApply f code
  --    = do { _ ← guardValid n code; f (fun i => extractListElem i.val code) }
  --    = guardValid n code >> f (extract code)

  -- In URMComputable terms: sequence guardValid with f_extract
  -- The trick: pair(guardValid n code, code) gives us both
  -- Then unpair.2 = code, apply f_extract

  -- Compute pair(guardValid n code, code):
  -- Step 1: Compute guardValid (gives 0 or diverges)
  -- Step 2: Pair with original input

  -- Using URMComputable1.pair:
  -- URMComputable1.pair (guardValid n) URMComputable1.id would give
  -- fun code => pair <$> guardValid n code <*> pure code
  -- = fun code => guardValid n code >>= fun g => pure (pair g code)
  -- = fun code => (guardValid n code).map (fun g => pair g code)

  -- Then compose with right projection and f_extract:
  -- fun code => (guardValid n code).map (...).bind (fun p => f_extract p.2)

  -- Actually this is still complex. Let me use a more direct approach.

  -- Direct construction using min:
  -- We want: if valid then f(extract code) else diverge
  -- f(extract code) is already URMComputable 1

  -- Build: (fun code y => if y = 0 ∧ valid then (if f(extract code) has result then 0 else 1) else 1)
  -- Then minimization finds y=0 when valid, and we extract f result

  -- This is getting complicated. Let me try a simpler lemma first.

  -- Actually, the key observation is:
  -- guardAndApply f code = (guardValid n code) >> (f (fun i => extractListElem i code))
  -- where >> is Part.seq (ignoring left result)

  -- For URMs: we can model this by running the guard program first,
  -- then running the f program on extracted inputs.
  -- If guard diverges, the whole thing diverges.
  -- If guard halts (with any value), we proceed to f.

  -- In terms of URMComputable closures:
  -- We need a "sequence" operation that runs one computation, ignores result, runs another

  -- Claim: if g : URMComputable1 and h : URMComputable1,
  -- then (fun x => g x >> h x) : URMComputable1
  -- where >> means: bind (fun _ => h x)

  -- Proof idea: Run g, when it halts (with value v), run h ignoring v.
  -- We can implement this by: computing pair(g x, h x) then projecting to second.
  -- But pair requires both to terminate for the pair to have a value.
  -- That's exactly what we want: pair(g x, h x) = some (v1, v2) iff both terminate.
  -- Then project to get v2.

  -- So: guardAndApply f code
  --   = (guardValid n code, f(extract code)) paired, then project second
  --   = (URMComputable1.pair guardValid_computable h_f_extract) >>= right

  have h_guard : URMComputable1 (guardValid n) := guardValid_computable n

  have h_paired : URMComputable1 (fun code =>
      Nat.pair <$> guardValid n code <*> f (fun i => extractListElem i.val code)) :=
    URMComputable1.pair h_guard (by unfold URMComputable1; exact h_f_extract)

  have h_proj_right : URMComputable1 (fun p => Part.some p.unpair.2) := URMComputable1.right

  have h_final := URMComputable1.comp h_proj_right h_paired

  -- h_final : URMComputable1 (fun code => (pair <$> guardValid n code <*> ...) >>= right)
  -- This equals: fun code => guardValid n code >>= fun g => f(...) >>= fun r => some (pair g r).unpair.2
  --            = fun code => guardValid n code >>= fun g => f(...) >>= fun r => some r
  --            = fun code => guardValid n code >>= fun _ => f(...)
  --            = guardAndApply f code

  -- Show the two functions are equal
  have heq : (fun code => (Nat.pair <$> guardValid n code <*> f (fun i => extractListElem i.val code))
              >>= fun p => Part.some p.unpair.2) = guardAndApply f := by
    funext code
    simp only [guardAndApply]
    -- LHS: (pair <$> guard <*> f_extract) >>= (fun p => some p.2)
    -- RHS: guard >>= (fun _ => f_extract)
    -- Both diverge when guard diverges
    -- When guard returns some g, LHS returns f_extract, RHS returns f_extract
    ext m
    constructor
    · -- LHS → RHS
      intro hm
      -- Convert >>= notation to Part.bind
      rw [Part.bind_eq_bind] at hm
      rw [Part.mem_bind_iff] at hm
      obtain ⟨p, hp, hpm⟩ := hm
      simp only [Part.mem_some_iff] at hpm
      rw [hpm]
      -- p is in (pair <$> guard <*> f_extract)
      -- Convert <*> to bind+map: pf <*> x = pf.bind (fun h => x.map h)
      rw [seq_eq_bind_map] at hp
      -- Now hp : p ∈ (Nat.pair <$> guardValid n code).bind (fun h => (f (...)).map h)
      rw [Part.bind_eq_bind, Part.mem_bind_iff] at hp
      obtain ⟨h, hh, hp'⟩ := hp
      -- h : ℕ → ℕ is in (Nat.pair <$> guardValid n code)
      -- hp' : p ∈ (f (...)).map h
      simp only [Part.map_eq_map, Part.mem_map_iff] at hh hp'
      obtain ⟨gv, hgv, hheq⟩ := hh  -- gv ∈ guardValid, h = Nat.pair gv
      obtain ⟨r, hr, hpeq⟩ := hp'   -- r ∈ f(...), h r = p
      rw [Part.mem_bind_iff]
      -- guardValid only returns 0 when it returns anything
      have hgv0 : gv = 0 := guardValid_mem_eq_zero hgv
      use 0
      constructor
      · rw [hgv0] at hgv; exact hgv
      · -- Need to show (Nat.unpair p).2 ∈ f ...
        -- We have p = h r = (Nat.pair gv) r = Nat.pair gv r
        -- So (Nat.unpair p).2 = r
        have hp_eq : p = Nat.pair gv r := by rw [← hpeq, hheq]
        rw [hp_eq, Nat.unpair_pair]
        exact hr
    · -- RHS → LHS
      intro hm
      rw [Part.mem_bind_iff] at hm
      obtain ⟨g, h0, hfm⟩ := hm
      -- g ∈ guardValid n code, so g = 0
      have hg0 : g = 0 := guardValid_mem_eq_zero h0
      -- Goal: m ∈ do { let p ← ...; Part.some ... }
      -- Convert do notation to bind
      show m ∈ (Nat.pair <$> guardValid n code <*> f (fun i => extractListElem i.val code)).bind
               (fun p => Part.some (Nat.unpair p).2)
      rw [Part.mem_bind_iff]
      use Nat.pair 0 m
      constructor
      · -- Show Nat.pair 0 m ∈ (Nat.pair <$> guard <*> f_extract)
        rw [seq_eq_bind_map, Part.bind_eq_bind, Part.mem_bind_iff]
        use Nat.pair 0  -- The partial function Nat.pair applied to 0
        constructor
        · simp only [Part.map_eq_map, Part.mem_map_iff]
          exact ⟨g, h0, by rw [hg0]⟩
        · simp only [Part.map_eq_map, Part.mem_map_iff]
          exact ⟨m, hfm, rfl⟩
      · simp only [Part.mem_some_iff, Nat.unpair_pair]
  rw [← heq]
  exact h_final

/-- Every n-ary URM-computable function is n-ary partial recursive.

The proof constructs a URMComputable1 function that:
1. Checks if the input code is a valid encoding of an n-element vector
2. If valid, extracts the n components and applies f
3. If invalid, diverges

This is achieved using guardValid (minimization-based validity check)
and extractListElem (primitive recursive component extraction). -/
theorem URMComputable.toPartrec' {n : ℕ} {f : (Fin n → ℕ) → Part ℕ}
    (hf : URMComputable n f) : Nat.Partrec' (toVectorFun f) := by
  rw [Nat.Partrec'.part_iff, Partrec_iff_bind]
  -- Need: Nat.Partrec (fun code => decode₂ code >>= toVectorFun f)
  suffices h : URMComputable1 (fun code =>
      (Part.ofOption (Encodable.decode₂ (List.Vector ℕ n) code)).bind (toVectorFun f)) by
    exact URMComputable1.toPartrec h
  -- Use guardAndApply which implements the same function
  have h_guard := guardAndApply_computable hf
  convert h_guard using 1
  funext code
  exact (guardAndApply_eq_decode_bind f code).symm

/-! ## The Equivalence -/

/-- URMComputable n is equivalent to Nat.Partrec' up to the type conversion. -/
theorem URMComputable_iff_Partrec' {n : ℕ} {f : (Fin n → ℕ) → Part ℕ} :
    URMComputable n f ↔ Nat.Partrec' (toVectorFun f) :=
  ⟨URMComputable.toPartrec', fun h => by
    have h' := Nat.Partrec'.toURMComputable h
    convert h' using 1
    exact (fromVectorFun_toVectorFun f).symm⟩

end Urm
