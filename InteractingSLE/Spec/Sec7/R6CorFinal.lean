/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CorInfInf
import InteractingSLE.Spec.Sec7.R6FcFinal

/-!
# Drop-in: R.6's mixed faces with no input (seed corner included)

Packet PROVE-R6-CORNER. The three mixed faces `R6Safe.R6FaceSMixed{,Inf,InfInf}Remaining` are PROVED for all
parameters (`r6FaceSMixedRemaining`, `r6FaceSMixedInfRemaining`, `r6FaceSMixedInfInfRemaining`, by Astra's same-time
inverse reflection, `R6CorReflect`), so the drop-ins of PROVE-R6-FACE2/FACE3 lose their non-corner inputs
(`R6Fc.R6NonCornerMixed{,Inf,InfInf}Remaining`, and FACE3's `R6Fd.R6InnerSharedHitMixed{,InfInf}Remaining`):

* `TwoOuterCornerInputs`: `R6Safe.TwoOuterFaceSInputs` without its three mixed faces of the intermediate pocket `V`;
  `twoOuterFaceSInputs_of_corner`, `twoOuterCornerInputs_of_nonCornerAll`;
* **`r7OuterPhaseSideRemaining_of_cont_corner_safe`**: the drop-in for
  `R6Fc.r7OuterPhaseSideRemaining_of_cont_nonCornerAll_safe` without `hNC`, `hNCI`, `hNCII` and with the two-outer-arm
  inputs reduced to `TwoOuterCornerInputs`.

R43/R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open QuantumZipper (chiC)
open scoped Real

namespace InteractingSLE.Sec7.R6Cor

open R6Safe R6Fc R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketMarks PocketStopWallsFin
  PocketStopSide

universe u

variable {k rL rR : ℝ}

/-- `R6Safe.TwoOuterFaceSInputs` without its three mixed faces of the intermediate pocket `V` (now proved). -/
def TwoOuterCornerInputs (k rL rR : ℝ) : Prop :=
  PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) ∧
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceQTwoRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceQTwoInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceQTwoInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0

/-- The two-outer-arm inputs with the three mixed faces of `V` supplied by `r6FaceSMixed{,Inf,InfInf}Remaining`. -/
theorem twoOuterFaceSInputs_of_corner (h : TwoOuterCornerInputs.{u} k rL rR) : TwoOuterFaceSInputs.{u} k rL rR :=
  ⟨h.1, r6FaceSMixedRemaining, r6FaceSMixedInfRemaining, r6FaceSMixedInfInfRemaining, h.2⟩

/-- The non-corner two-outer-arm inputs contain the corner ones (their three non-corner conjuncts are not needed). -/
theorem twoOuterCornerInputs_of_nonCornerAll (h : TwoOuterNonCornerAllInputs.{u} k rL rR) :
    TwoOuterCornerInputs.{u} k rL rR :=
  ⟨h.1, h.2.2.2.2⟩

/-- **Drop-in for `R6Fc.r7OuterPhaseSideRemaining_of_cont_nonCornerAll_safe`** with the three mixed faces of `C` (and
of the intermediate pocket `V` in the two-outer-arm inputs) PROVED: no non-corner landing input. -/
theorem r7OuterPhaseSideRemaining_of_cont_corner_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwoIn : k / 2 - 4 < rL → k / 2 - 4 < rR → TwoOuterCornerInputs.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_faceS_safe h411 h51 h47 h47T haux7 h44 hA hword r6FaceSMixedRemaining
    r6FaceSMixedInfRemaining r6FaceSMixedInfInfRemaining hk4 hrL hrR hcont
    fun hdL hdR => twoOuterFaceSInputs_of_corner (htwoIn hdL hdR)

end InteractingSLE.Sec7.R6Cor
