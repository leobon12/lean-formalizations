/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TnTwo
import InteractingSLE.Spec.Sec7.R6TnTwoInf
import InteractingSLE.Spec.Sec7.R6TnTwoInfInf

/-!
# Two-outer input assembly from the named landing patches

PROVE-R6-TWO. Conditional drop-ins for the original fully reduced
R.6 input and outer-phase theorem. The three mixed faces and phase
inputs retain exactly their original hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open QuantumZipper (chiC)
open scoped Real

namespace InteractingSLE.Sec7.R6Tn

open R6Safe R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketMarks PocketStopWallsFin PocketStopSide

universe u

variable {k rL rR : ℝ}

/-- The original full input with precisely its three two-outer face
conjuncts replaced by the named geometric landing-patch inputs. -/
def TwoOuterLandingPatchInputs (k rL rR : ℝ) : Prop :=
  PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) ∧
    R6FaceQMixedRemaining.{u} k rL (k / 2 - 4) (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceQMixedInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceQMixedInfInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6LandingPatchTwoRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6LandingPatchTwoInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6LandingPatchTwoInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0

/-- The three two-outer face statements follow from the geometric
landing patches, including their original common-point clauses. -/
theorem twoOuterFaceQFullInputs_of_landingPatch (h : TwoOuterLandingPatchInputs.{u} k rL rR) :
    TwoOuterFaceQFullInputs.{u} k rL rR :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    r6FaceQTwoRemaining_of_landingPatch h.2.2.2.2.2.1,
    r6FaceQTwoInfRemaining_of_landingPatch h.2.2.2.2.2.2.1,
    r6FaceQTwoInfInfRemaining_of_landingPatch h.2.2.2.2.2.2.2⟩

/-- Conditional drop-in for the outer-phase theorem with the three
two-outer faces replaced by their named physical landing patches. -/
theorem r7OuterPhaseSideRemaining_of_cont_landingPatch_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hface : R6FaceQMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceI : R6FaceQMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceII : R6FaceQMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwoIn : k / 2 - 4 < rL → k / 2 - 4 < rR → TwoOuterLandingPatchInputs.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_faceQFull_safe h411 h51 h47 h47T haux7 h44 hA hword
    hface hfaceI hfaceII hk4 hrL hrR hcont
    fun hdL hdR => twoOuterFaceQFullInputs_of_landingPatch (htwoIn hdL hdR)

end InteractingSLE.Sec7.R6Tn
