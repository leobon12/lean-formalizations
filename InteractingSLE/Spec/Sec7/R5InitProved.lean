/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5InitOuterClose
import InteractingSLE.Spec.Wire.T12Asm3Inputs

/-!
# Lemma R.5 on every R.7 pocket, unconditionally (universe 0)

Packet PROVE-R5-INIT. With Aux. lemma 7 at every `k > 4` (`Wire.T12Asm3.aux7`, from clearance Part A), the extremal
chain (`R5Init.r7PhaseWordRemaining_of_aux7`, `R5InitTest`) and the outer chain
(`R5Init.r7OuterRelativeCoverMRemaining_of_aux7`, `R5InitOuterClose`) have no remaining input. This leaf file
states the results in the exact binder forms of PROVE-T12-ASSEMBLE3 (`Wire.T12Asm3`):
* **`wordPhase_proved`**: Theorem 1.2's binder `hWordPhase`; **`phaseWordM_proved`** at every margin `0 ≤ c, c'`;
* **`hOuterCover_proved`**: `T12Asm3`'s variable `hOuterCover` (all margins `πχ(16/k) ≤ c`, `0 ≤ c'`);
* **`outerCont_proved`**: Theorem 1.2's binder `hOuterCont`;
* `r7R5RemainingOn_proved`, `r7OuterR5MRemainingCompOn_proved` (the component clauses).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses (`T12Asm3.aux7` is R48-clean, see its module).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE.Sec7.R5Init

/-- **Lemma R.5 on every extremal R.7 configuration** (`R5Enl.R7R5RemainingOn`, universe 0, `k > 4`, `0 ≤ c, c'`). -/
theorem r7R5RemainingOn_proved {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    R5Enl.R7R5RemainingOn.{0} k rL rR c c' :=
  r7R5RemainingOn_of_aux7 hk4 hc hc' (Wire.T12Asm3.aux7 k hk4)

/-- **R.5 up to phase on every extremal R.7 pocket test** (universe 0, every margin `0 ≤ c, c'`). -/
theorem phaseWordM_proved {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    PhaseCont.R7PhaseWordRemaining.{0} k rL rR c c' :=
  r7PhaseWordRemaining_of_aux7 hk4 hc hc' (Wire.T12Asm3.aux7 k hk4)

/-- **Theorem 1.2's binder `hWordPhase`** (the type of `Wire.T12Asm3.wordPhase_of_split`). -/
theorem wordPhase_proved : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
    PhaseCont.R7PhaseWordRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
  fun _ hk4 _ _ _ _ _ => phaseWordM_proved hk4 (Wire.T12Asm2.margin_nonneg hk4) le_rfl

/-- **Outer R.5's source component clauses on every outer R.7 configuration** (universe 0). -/
theorem r7OuterR5MRemainingCompOn_proved {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    R5Out.R7OuterR5MRemainingCompOn.{0} k rL rR c c' :=
  r7OuterR5MRemainingCompOn_of_aux7 hk4 hc hc' (Wire.T12Asm3.aux7 k hk4)

/-- **Outer R.5 in R5-OUTER's relative-cover form** (`R5Out.R7OuterRelativeCoverMRemaining`), universe 0, in the
exact type of `Wire.T12Asm3`'s variable `hOuterCover`. -/
theorem hOuterCover_proved : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
    ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Out.R7OuterRelativeCoverMRemaining.{0} k rL rR c c' :=
  fun k hk4 _ _ _ _ _ _ _ hc hc' =>
    r7OuterRelativeCoverMRemaining_of_aux7 hk4 ((Wire.T12Asm2.margin_nonneg hk4).trans hc) hc'
      (Wire.T12Asm3.aux7 k hk4)

/-- **Theorem 1.2's binder `hOuterCont`** (the type of `Wire.T12Asm3.outerCont_of_cover`). -/
theorem outerCont_proved : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
    OuterPhNext.R7OuterPhaseContRemaining.{0} k rL rR :=
  Wire.T12Asm3.outerCont_of_cover hOuterCover_proved

end InteractingSLE.Sec7.R5Init
