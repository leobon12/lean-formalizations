/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceWire
import InteractingSLE.Spec.Wire.PartAClearanceRegularity
import InteractingSLE.Spec.Sec5.CfAvoidLeftQFree
import InteractingSLE.Spec.Sec5.CfFirstContactQ
import InteractingSLE.Spec.Sec5.Prop51GQ
import InteractingSLE.Spec.Sec5.Prop51GQExit
import InteractingSLE.Spec.Sec5.Prop51HQNoContact
import InteractingSLE.Spec.Sec5.Prop51HQPost
import InteractingSLE.Spec.Sec5.Prop51IQEast

/-! # Part A clearance variants: forward

Packet PROVE-WIRE-PARTA. The source proofs use only Aux. lemma 7 from Part A.
These variants replace the two-crosscut input by protected-ray clearance, using
the existing clearance and inverse-boundary API. All other hypotheses and conclusions
are those of the original consumers; the original declarations are unchanged.
-/

set_option autoImplicit false

section

/- Clearance variants of `Sec5/CfAvoidLeftQFree`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

open scoped NNReal ENNReal Real

open QuantumZipper (H chiC fwdHull fwdMap)

open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CfAvoidLeftQ

open WangWu hiding ratPt exists_ratPt_dist_lt

open LawUnique Cond44Ref Prop51Q

variable {W : ℝ → ℝ} {γ : ℝ → ℂ}

/-- Clearance variant of `prop51QStatement_of_partA_of_cfFirstContact`; only Aux. lemma 7 is used from Part A. -/
theorem prop51QStatement_of_partA_of_cfFirstContact_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hfirst : CfFirstContactQStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_cfFirstContact (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA) hfirst

end InteractingSLE.Sec5.CfAvoidLeftQ

end

end

section

/- Clearance variants of `Sec5/CfFirstContactQ`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric

open scoped NNReal ENNReal Real

open QuantumZipper (H chiC fwdHull fwdMap)

open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CfFirstContactQ

open WangWu hiding ratPt exists_ratPt_dist_lt

open LawUnique Cond44Ref Prop51Q CfAvoidLeftQ

section Core

variable {c : ℝ → ℂ}

end Core

/-- Clearance variant of `prop51QStatement_of_partA_of_return`; only Aux. lemma 7 is used from Part A. -/
theorem prop51QStatement_of_partA_of_return_of_clearance (hA : PartAInputsSixteenDivOfClearance) (hnew : CfExitNewStatement.{u})
    (hret : CfReturnStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_return (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA) hnew hret

/-- Clearance variant of `prop51QStatement_of_partA_of_exit`; only Aux. lemma 7 is used from Part A. -/
theorem prop51QStatement_of_partA_of_exit_of_clearance (hA : PartAInputsSixteenDivOfClearance) (hnew : CfExitNewStatement.{u})
    (hold : CfExitOldStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_exit (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA) hnew hold

end InteractingSLE.Sec5.CfFirstContactQ

end

end

section

/- Clearance variants of `Sec5/Prop51GQ`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

open scoped NNReal ENNReal Real

open QuantumZipper (H chiC fwdHull fwdMap)

open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.Prop51G

open WangWu hiding ratPt exists_ratPt_dist_lt

open LawUnique Cond44Ref Prop51Q CfAvoidLeftQ

section Params

variable {κ : ℝ}

end Params

section Defs

end Defs

section Setting

end Setting

section Inputs

end Inputs

section Wiring

/-- Clearance variant of `prop51QStatement_of_partA_of_fwd`; only Aux. lemma 7 is used from Part A. -/
theorem prop51QStatement_of_partA_of_fwd_of_clearance (hA : PartAInputsSixteenDivOfClearance) (htopo : FwdNoWrapQStatement)
    (h0 : FwdFirstExitQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂)
    (hpost : FwdPostContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂)
    (hnc : FwdNoContactQStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_regimes (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA) htopo
    (fwdFirstContactNotEastQOn_of_split h0 hpost) hnc

end Wiring

end InteractingSLE.Sec5.Prop51G

end

end

section

/- Clearance variants of `Sec5/Prop51GQExit`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)

open LQGMetric (DistOn TestOn)

open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop51G

open WangWu hiding ratPt exists_ratPt_dist_lt

open WangWu.ImgWord CrossCond CrossCond.Word49 CrossCond.Theta MartChar.RealFlow LawUnique Cond44Ref Prop411Q
  CfRegQ Prop49Exit

open Sec7.Lemma71C (capClock)

section Weights

variable {nL nR : ℕ}

end Weights

section Exit

end Exit

section Det

end Det

section Main

/-- Clearance variant of `prop51QStatement_of_partA_of_fwd_post`; only Aux. lemma 7 is used from Part A. -/
theorem prop51QStatement_of_partA_of_fwd_post_of_clearance (hA : PartAInputsSixteenDivOfClearance) (htopo : FwdNoWrapQStatement)
    (hpost : FwdPostContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂)
    (hnc : FwdNoContactQStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_partA_of_fwd_of_clearance hA htopo
    (fwdFirstExitQOn_smallGap (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA)) hpost hnc

/-- Clearance variant of `cfFirstContactQStatement_of_partA_of_fwd_post`; only Aux. lemma 7 is used from Part A. -/
theorem cfFirstContactQStatement_of_partA_of_fwd_post_of_clearance (hA : PartAInputsSixteenDivOfClearance) (htopo : FwdNoWrapQStatement)
    (hpost : FwdPostContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂)
    (hnc : FwdNoContactQStatement.{u}) : CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA)
    (prop51QStatement_of_partA_of_fwd_post_of_clearance hA htopo hpost hnc)

end Main

end InteractingSLE.Sec5.Prop51G

end

end

section

/- Clearance variants of `Sec5/Prop51HQNoContact`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)

open LQGMetric (DistOn TestOn)

open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop51H

open WangWu hiding ratPt exists_ratPt_dist_lt

open WangWu.ImgWord CrossCond CrossCond.Word49 CrossCond.Theta MartChar.RealFlow LawUnique Cond44Ref Prop411Q
  CfRegQ Prop49Exit Prop51G

open Sec7.Lemma71C (capClock)

section Killed

variable {γ : ℝ → ℂ} {P : Set ℝ}

end Killed

section Det

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {η : ℝ → ℂ} {s : ℝ}

end Det

section Glued

end Glued

section NoContact

/-- Clearance variant of `prop51QOn_largeGap_of_partA`; only Aux. lemma 7 is used from Part A. -/
theorem prop51QOn_largeGap_of_partA_of_clearance (hA : PartAInputsSixteenDivOfClearance) : Prop51QOn.{u} IsLargeGap :=
  prop51QOn_largeGap_of_reg (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA)

/-- Clearance variant of `prop51QStatement_of_partA_of_post`; only Aux. lemma 7 is used from Part A. -/
theorem prop51QStatement_of_partA_of_post_of_clearance (hA : PartAInputsSixteenDivOfClearance) (htopo : FwdNoWrapQStatement)
    (hpost : FwdPostContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) : Prop51QStatement.{u} :=
  prop51QStatement_of_partA_of_fwd_post_of_clearance hA htopo hpost fwdNoContactQStatement

/-- Clearance variant of `cfFirstContactQStatement_of_partA_of_post`; only Aux. lemma 7 is used from Part A. -/
theorem cfFirstContactQStatement_of_partA_of_post_of_clearance (hA : PartAInputsSixteenDivOfClearance) (htopo : FwdNoWrapQStatement)
    (hpost : FwdPostContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  cfFirstContactQStatement_of_partA_of_fwd_post_of_clearance hA htopo hpost fwdNoContactQStatement

end NoContact

end InteractingSLE.Sec5.Prop51H

end

end

section

/- Clearance variants of `Sec5/Prop51HQPost`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)

open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop51H

open WangWu hiding ratPt exists_ratPt_dist_lt

open WangWu.ImgWord CrossCond CrossCond.Word49 MartChar.RealFlow LawUnique Cond44Ref Prop411Q Prop49Exit Prop51G

section Bdry

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ}

end Bdry

section Excl

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} {η : ℝ → ℂ}

end Excl

section Residual

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} {η : ℝ → ℂ}

/-- Clearance variant of `prop51QStatement_of_partA_of_east`; only Aux. lemma 7 is used from Part A. -/
theorem prop51QStatement_of_partA_of_east_of_clearance (hA : PartAInputsSixteenDivOfClearance) (htopo : FwdNoWrapQStatement)
    (hres : FwdPostContactEastQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) : Prop51QStatement.{u} :=
  prop51QStatement_of_partA_of_post_of_clearance hA htopo
    (fwdPostContactQOn_of_residual (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA) hres)

/-- Clearance variant of `cfFirstContactQStatement_of_partA_of_east`; only Aux. lemma 7 is used from Part A. -/
theorem cfFirstContactQStatement_of_partA_of_east_of_clearance (hA : PartAInputsSixteenDivOfClearance) (htopo : FwdNoWrapQStatement)
    (hres : FwdPostContactEastQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  cfFirstContactQStatement_of_partA_of_post_of_clearance hA htopo
    (fwdPostContactQOn_of_residual (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA) hres)

end Residual

end InteractingSLE.Sec5.Prop51H

end

end

section

/- Clearance variants of `Sec5/Prop51IQEast`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)

open LQGMetric (DistOn TestOn)

open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop51I

open WangWu hiding ratPt exists_ratPt_dist_lt

open WangWu.ImgWord CrossCond CrossCond.Word49 CrossCond.Theta MartChar.RealFlow LawUnique Cond44Ref Prop411Q
  CfRegQ Prop49Exit Prop51G Prop51H

section Hit

end Hit

section Far

variable {w : ℝ → ℝ}

end Far

section Residual

/-- Clearance variant of `prop51QStatement_of_partA_of_eastSide`; only Aux. lemma 7 is used from Part A. -/
theorem prop51QStatement_of_partA_of_eastSide_of_clearance (hA : PartAInputsSixteenDivOfClearance) (htopo : FwdNoWrapQStatement)
    (hside : FwdPostContactEastSideQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) : Prop51QStatement.{u} :=
  prop51QStatement_of_partA_of_east_of_clearance hA htopo
    (fwdPostContactEastQOn_of_side (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA) hside)

/-- Clearance variant of `cfFirstContactQStatement_of_partA_of_eastSide`; only Aux. lemma 7 is used from Part A. -/
theorem cfFirstContactQStatement_of_partA_of_eastSide_of_clearance (hA : PartAInputsSixteenDivOfClearance) (htopo : FwdNoWrapQStatement)
    (hside : FwdPostContactEastSideQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  cfFirstContactQStatement_of_partA_of_east_of_clearance hA htopo
    (fwdPostContactEastQOn_of_side (CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA) hside)

end Residual

end InteractingSLE.Sec5.Prop51I

end

end
