/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FcWire
import InteractingSLE.Spec.Sec7.R6FcWireInfInf
import InteractingSLE.Spec.Sec7.R6SafeMeetInf

/-!
# Drop-in: R.6's bounded mixed faces from the non-corner landing input

Packet PROVE-R6-FACE2. `R6Safe.r7OuterPhaseSideRemaining_of_cont_faceS_safe` with its bounded mixed face
`R6FaceSMixedRemaining` (for `C`, and inside the two-outer-arm inputs for the intermediate pocket `V`) replaced by the
named non-corner input `R6NonCornerMixedRemaining` (`r6FaceSMixedRemaining_of_nonCorner`):

* `TwoOuterNonCornerInputs`, `twoOuterFaceSInputs_of_nonCorner`;
* **`r7OuterPhaseSideRemaining_of_cont_nonCorner_safe`**;
* the same with all three mixed shapes (bounded, `Inf`, `InfInf`) given by their non-corner inputs:
  `TwoOuterNonCornerAllInputs`, `twoOuterFaceSInputs_of_nonCornerAll`,
  **`r7OuterPhaseSideRemaining_of_cont_nonCornerAll_safe`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open QuantumZipper (chiC)
open scoped Real

namespace InteractingSLE.Sec7.R6Fc

open R6Safe R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketMarks PocketStopWallsFin PocketStopSide

universe u

variable {k rL rR : ℝ}

/-- `R6Safe.TwoOuterFaceSInputs` with the mixed face of the intermediate pocket `V` given by the non-corner input. -/
def TwoOuterNonCornerInputs (k rL rR : ℝ) : Prop :=
  PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) ∧
    R6NonCornerMixedRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceSMixedInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceSMixedInfInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceQTwoRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceQTwoInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceQTwoInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0

theorem twoOuterFaceSInputs_of_nonCorner (h : TwoOuterNonCornerInputs.{u} k rL rR) :
    TwoOuterFaceSInputs.{u} k rL rR :=
  ⟨h.1, r6FaceSMixedRemaining_of_nonCorner h.2.1, h.2.2⟩

/-- **Drop-in for `R6Safe.r7OuterPhaseSideRemaining_of_cont_faceS_safe`** with the bounded mixed face (of `C`, and of
the intermediate pocket `V` in the two-outer-arm inputs) given by the non-corner landing input. -/
theorem r7OuterPhaseSideRemaining_of_cont_nonCorner_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hNC : R6NonCornerMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceI : R6FaceSMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceII : R6FaceSMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwoIn : k / 2 - 4 < rL → k / 2 - 4 < rR → TwoOuterNonCornerInputs.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_faceS_safe h411 h51 h47 h47T haux7 h44 hA hword
    (r6FaceSMixedRemaining_of_nonCorner hNC) hfaceI hfaceII hk4 hrL hrR hcont
    fun hdL hdR => twoOuterFaceSInputs_of_nonCorner (htwoIn hdL hdR)

/-- `R6Safe.TwoOuterFaceSInputs` with all three mixed faces of the intermediate pocket `V` given by the non-corner
inputs. -/
def TwoOuterNonCornerAllInputs (k rL rR : ℝ) : Prop :=
  PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) ∧
    R6NonCornerMixedRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6NonCornerMixedInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6NonCornerMixedInfInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceQTwoRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceQTwoInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceQTwoInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0

theorem twoOuterFaceSInputs_of_nonCornerAll (h : TwoOuterNonCornerAllInputs.{u} k rL rR) :
    TwoOuterFaceSInputs.{u} k rL rR :=
  ⟨h.1, r6FaceSMixedRemaining_of_nonCorner h.2.1, r6FaceSMixedInfRemaining_of_nonCorner h.2.2.1,
    r6FaceSMixedInfInfRemaining_of_nonCorner h.2.2.2.1, h.2.2.2.2⟩

/-- **Drop-in for `R6Safe.r7OuterPhaseSideRemaining_of_cont_faceS_safe`** with all three mixed faces (of `C`, and of
the intermediate pocket `V` in the two-outer-arm inputs) given by the non-corner landing inputs. -/
theorem r7OuterPhaseSideRemaining_of_cont_nonCornerAll_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hNC : R6NonCornerMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hNCI : R6NonCornerMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hNCII : R6NonCornerMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwoIn : k / 2 - 4 < rL → k / 2 - 4 < rR → TwoOuterNonCornerAllInputs.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_faceS_safe h411 h51 h47 h47T haux7 h44 hA hword
    (r6FaceSMixedRemaining_of_nonCorner hNC) (r6FaceSMixedInfRemaining_of_nonCorner hNCI)
    (r6FaceSMixedInfInfRemaining_of_nonCorner hNCII) hk4 hrL hrR hcont
    fun hdL hdR => twoOuterFaceSInputs_of_nonCornerAll (htwoIn hdL hdR)

end InteractingSLE.Sec7.R6Fc
