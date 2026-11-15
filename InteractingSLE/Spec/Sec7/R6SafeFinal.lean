/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeTwoWire
import InteractingSLE.Spec.Sec7.R6SafeFaceWire

/-!
# The outer phase input of Theorem 1.2's R.7 from R.5 and R.6's face descriptions

PROVE-R6-SAFE. The final drop-in for `R6Fin.r7OuterPhaseSideRemaining_of_cont_core` (PROVE-R6-CERT2): neither the strip
system `hstrip` nor the two-outer-arm certificates `htwo` are inputs, and the geometry enters only through the face
descriptions `R6FaceMixed{,Inf,InfInf}Remaining` / `R6FaceTwo{,Inf,InfInf}Remaining` (the source's Lemma R.6
hypotheses, supplement p. 476):

* `TwoOuterFaceInputs`, `twoOuterInputs_of_face`;
* **`r7OuterPhaseSideRemaining_of_cont_face_safe`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Safe

open R6Fin R7Outer R7Leaves R6Nest R6Rel

variable {k rL rR : ℝ}

/-- **The named inputs of R.6's two-outer-arm case in face form** (`TwoOuterInputs` with the six geometry cores
replaced by the face descriptions). -/
def TwoOuterFaceInputs (k rL rR : ℝ) : Prop :=
  PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) ∧
    R6FaceMixedRemaining.{u} k rL (k / 2 - 4) (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceMixedInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceMixedInfInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceTwoRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceTwoInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceTwoInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0

/-- The face form of the two-outer-arm inputs gives `TwoOuterInputs`. -/
theorem twoOuterInputs_of_face (h : TwoOuterFaceInputs.{u} k rL rR) : TwoOuterInputs.{u} k rL rR :=
  ⟨h.1, r6GeomCoreMixedRemaining_of_face h.2.1, r6GeomCoreMixedInfRemaining_of_face h.2.2.1,
    r6GeomCoreMixedInfInfRemaining_of_face h.2.2.2.1, h.2.2.2.2.1, r6GeomCoreTwoRemaining_of_face h.2.2.2.2.2.1,
    r6GeomCoreTwoInfRemaining_of_face h.2.2.2.2.2.2.1, r6GeomCoreTwoInfInfRemaining_of_face h.2.2.2.2.2.2.2⟩

/-- **The outer phase input from R.5 and R.6's face descriptions** (drop-in for
`R6Fin.r7OuterPhaseSideRemaining_of_cont_core`, without `hstrip` and `htwo`): the landed R.7 inputs, R.5 with
continuity (`hcont`), the mixed-case inner R.5 word (`hword`), the three mixed-case face descriptions, and, only for two
outer arms, `TwoOuterFaceInputs`. -/
theorem r7OuterPhaseSideRemaining_of_cont_face_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hface : R6FaceMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceI : R6FaceMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceII : R6FaceMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwoIn : k / 2 - 4 < rL → k / 2 - 4 < rR → TwoOuterFaceInputs.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_core_two_safe h411 h51 h47 h47T haux7 h44 hA hword
    (r6GeomCoreMixedRemaining_of_face hface) (r6GeomCoreMixedInfRemaining_of_face hfaceI)
    (r6GeomCoreMixedInfInfRemaining_of_face hfaceII) hk4 hrL hrR hcont
    fun hdL hdR => twoOuterInputs_of_face (htwoIn hdL hdR)

end InteractingSLE.Sec7.R6Safe
