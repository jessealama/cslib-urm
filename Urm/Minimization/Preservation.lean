/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Urm.Minimization.StandardForm

/-! # Preservation Lemmas for Minimization

This file proves register preservation during minimization program execution.

## Main results

- pF doesn't touch counter, zero, or saved input registers
- Loop iterations preserve saved inputs
- Zero register remains zero
-/

namespace Urm

open Program

/-! ## pF Register Preservation -/

/-- pF execution preserves the counter register. -/
theorem pF_preserves_counter (n : ℕ) (pF : Program) (s s' : State)
    (hpF_max : pF.maxRegister ≤ minimizationBase n pF)
    (c' : Config) (hsteps : Steps pF ⟨0, s⟩ c') (hhalted : c'.isHalted pF)
    (hstate_eq : c'.state = s') :
    s'.read (counterReg n pF) = s.read (counterReg n pF) := by
  subst hstate_eq
  exact Steps.preserves_high_register hsteps (counterReg n pF) (by
    have h := pF_doesnt_touch_counter n pF
    omega)

/-- pF execution preserves the zero register. -/
theorem pF_preserves_zeroReg (n : ℕ) (pF : Program) (s s' : State)
    (hpF_max : pF.maxRegister ≤ minimizationBase n pF)
    (c' : Config) (hsteps : Steps pF ⟨0, s⟩ c') (hhalted : c'.isHalted pF)
    (hstate_eq : c'.state = s') :
    s'.read (zeroReg n pF) = s.read (zeroReg n pF) := by
  subst hstate_eq
  exact Steps.preserves_high_register hsteps (zeroReg n pF) (by
    have h := pF_doesnt_touch_zeroReg n pF
    omega)

/-- pF execution preserves saved input registers. -/
theorem pF_preserves_savedInputs (n : ℕ) (pF : Program) (s s' : State)
    (hpF_max : pF.maxRegister ≤ minimizationBase n pF)
    (c' : Config) (hsteps : Steps pF ⟨0, s⟩ c') (hhalted : c'.isHalted pF)
    (hstate_eq : c'.state = s') (i : Fin n) :
    s'.read (savedInputsStart n pF + i) = s.read (savedInputsStart n pF + i) := by
  subst hstate_eq
  exact Steps.preserves_high_register hsteps (savedInputsStart n pF + i) (by
    have h := pF_doesnt_touch_savedInputs n pF i
    omega)

/-! ## Setup Phase Results -/

/-- After setup phase, saved inputs contain original inputs. -/
theorem setupPhase_saves_inputs (n : ℕ) (pF : Program) (inputs : Fin n → ℕ)
    (s : State) (hs : s = State.fromInputs (List.ofFn inputs))
    (c' : Config) (hsteps : Steps (setupPhase n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (setupPhase n pF)) (i : Fin n) :
    c'.state.read (savedInputsStart n pF + i) = inputs i := by
  -- Setup phase = copyRegisterRange ++ [Z counter, Z zero]
  -- After copyRegisterRange, saved inputs contain inputs
  -- The Z instructions don't affect saved inputs
  sorry

/-- After setup phase, counter is 0. -/
theorem setupPhase_counter_zero (n : ℕ) (pF : Program) (inputs : Fin n → ℕ)
    (s : State) (hs : s = State.fromInputs (List.ofFn inputs))
    (c' : Config) (hsteps : Steps (setupPhase n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (setupPhase n pF)) :
    c'.state.read (counterReg n pF) = 0 := by
  sorry

/-- After setup phase, zero register is 0. -/
theorem setupPhase_zeroReg_zero (n : ℕ) (pF : Program) (inputs : Fin n → ℕ)
    (s : State) (hs : s = State.fromInputs (List.ofFn inputs))
    (c' : Config) (hsteps : Steps (setupPhase n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (setupPhase n pF)) :
    c'.state.read (zeroReg n pF) = 0 := by
  sorry

/-! ## Loop Prologue Results -/

/-- After loop prologue, R[0..n-1] contain saved inputs. -/
theorem loopPrologue_restores_inputs (n : ℕ) (pF : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (loopPrologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (loopPrologue n pF)) (i : Fin n) :
    c'.state.read i = s.read (savedInputsStart n pF + i) := by
  sorry

/-- After loop prologue, R[n] contains counter value. -/
theorem loopPrologue_sets_counter_input (n : ℕ) (pF : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (loopPrologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (loopPrologue n pF)) :
    c'.state.read n = s.read (counterReg n pF) := by
  sorry

/-- Loop prologue preserves counter register. -/
theorem loopPrologue_preserves_counter (n : ℕ) (pF : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (loopPrologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (loopPrologue n pF)) :
    c'.state.read (counterReg n pF) = s.read (counterReg n pF) := by
  sorry

/-- Loop prologue preserves zero register. -/
theorem loopPrologue_preserves_zeroReg (n : ℕ) (pF : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (loopPrologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (loopPrologue n pF)) :
    c'.state.read (zeroReg n pF) = s.read (zeroReg n pF) := by
  sorry

/-- Loop prologue preserves saved inputs. -/
theorem loopPrologue_preserves_savedInputs (n : ℕ) (pF : Program)
    (s : State) (c' : Config)
    (hsteps : Steps (loopPrologue n pF) ⟨0, s⟩ c')
    (hhalted : c'.isHalted (loopPrologue n pF)) (i : Fin n) :
    c'.state.read (savedInputsStart n pF + i) = s.read (savedInputsStart n pF + i) := by
  sorry

end Urm
