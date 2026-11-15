/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceWire
import InteractingSLE.Spec.Wire.PartAClearanceRegularity
import InteractingSLE.Spec.Wire.PartAClearanceForward
import InteractingSLE.Spec.Wire.Thm12Inputs6
import InteractingSLE.Spec.Wire.Thm12Inputs7
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRouteWire

/-! # Part A clearance variants: theorems

Packet PROVE-WIRE-PARTA. The source proofs use only Aux. lemma 7 from Part A.
These variants replace the two-crosscut input by protected-ray clearance, using
the existing clearance and inverse-boundary API. All other hypotheses and conclusions
are those of the original consumers; the original declarations are unchanged.
-/

set_option autoImplicit false

section

/- Clearance variants of `Wire/Thm12Inputs6`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- Clearance variant of `twoSeedGraphInput_of_open6`; only Aux. lemma 7 is used from Part A. -/
theorem twoSeedGraphInput_of_open6_of_clearance
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h49 : Sec5.Prop411Q.Prop49QExitStatement.{u})
    (hfirst : Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u})
    (hoff : Sec7.Lemma71P.MidRealOffStatement)
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) : LP.TwoSeedGraphInput.{u} κ := by
  have h411 : Sec5.Cond44Ref.Prop411QStatement.{u} :=
    Sec5.Prop411Q.prop411QStatement_of_lemma47Q_of_prop49Q Sec5.CfRegQ.cfRegQStatement h47 h49
  have h51 : Sec5.Cond44Ref.Prop51QStatement.{u} :=
    Sec5.CfAvoidLeftQ.prop51QStatement_of_partA_of_cfFirstContact_of_clearance hA hfirst
  have href : Sec7.Lemma71H.Cond44ReferenceStatement.{u} :=
    Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  have h55 : Sec7.Lemma71H.Prop55HalfPlaneStatement.{u} :=
    Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hMD : Sec7.Lemma71I.Lemma613ContactStatement.{u} :=
    Sec7.Lemma613.lemma613ContactStatement_of_prop55 href h55
  have hJ : Sec7.Lemma72.Lemma71JointStatement.{u} :=
    Sec7.Lemma71R.lemma71JointStatement_of_midRealOff href h55 hMD hoff
  rcases lt_trichotomy κ 4 with hκ4 | rfl | hκ4
  · exact twoSeedGraphInput_of_lt_four3 hJ h50_of_open4 hκ hκ4
  · exact WangWu.Chamber4.twoSeedGraphInput_four_of_joint hC4
  · exact twoSeedGraphInput_of_four_lt3 hR7 h50R_of_open4
      (lemma725DeterminationStatement_of_open4 hPW href725) hPW hκ4

/-- Clearance variant of `exists_measurable_lifetime_trace_eq_comp_field_of_open6`; only Aux. lemma 7 is used from Part A. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_open6_of_clearance
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h49 : Sec5.Prop411Q.Prop49QExitStatement.{u})
    (hfirst : Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u})
    (hoff : Sec7.Lemma71P.MidRealOffStatement)
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by assumption) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  exists_measurable_lifetime_trace_eq_comp_field_of_inputs2
    (fun _ hκ' => twoSeedGraphInput_of_open6_of_clearance hA h47 h49 hfirst hoff hC4 hR7 hPW href725 hκ')
    (fun _ hκ' => LocalExt.stoppedSeedExtensionStatement hκ')
    (fun _ hκ' => LocalExt.restartSeedCouplingStatement hκ') hκ hF hcoup

/-- Clearance variant of `theorem12Statement_of_open6`; only Aux. lemma 7 is used from Part A. -/
theorem theorem12Statement_of_open6_of_clearance
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h49 : Sec5.Prop411Q.Prop49QExitStatement.{u})
    (hfirst : Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u})
    (hoff : Sec7.Lemma71P.MidRealOffStatement)
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u}) : Exist.Theorem12Statement.{u} := by
  intro _ hκ _ _ _ _ _ _ hF _ _ _ _ _ _ _ _ _ _ _ hcoup
  exact exists_measurable_lifetime_trace_eq_comp_field_of_open6_of_clearance hA h47 h49 hfirst hoff hC4 hR7 hPW href725
    hκ hF hcoup

end Wire

end InteractingSLE

end

end

section

/- Clearance variants of `Wire/Thm12Inputs7`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire

/-- Clearance variant of `twoSeedGraphInput_of_open7`; only Aux. lemma 7 is used from Part A. -/
theorem twoSeedGraphInput_of_open7_of_clearance
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h49 : Sec5.Prop411Q.Prop49QExitStatement.{u})
    (hfirst : Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) : LP.TwoSeedGraphInput.{u} κ := by
  have h411 : Sec5.Cond44Ref.Prop411QStatement.{u} :=
    Sec5.Prop411Q.prop411QStatement_of_lemma47Q_of_prop49Q Sec5.CfRegQ.cfRegQStatement h47 h49
  have h51 : Sec5.Cond44Ref.Prop51QStatement.{u} :=
    Sec5.CfAvoidLeftQ.prop51QStatement_of_partA_of_cfFirstContact_of_clearance hA hfirst
  have href : Sec7.Lemma71H.Cond44ReferenceStatement.{u} :=
    Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  have h55 : Sec7.Lemma71H.Prop55HalfPlaneStatement.{u} :=
    Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hMD : Sec7.Lemma71I.Lemma613ContactStatement.{u} :=
    Sec7.Lemma613.lemma613ContactStatement_of_prop55 href h55
  have hJ : Sec7.Lemma72.Lemma71JointStatement.{u} := Sec7.Lemma71T.lemma71JointStatement href h55 hMD
  rcases lt_trichotomy κ 4 with hκ4 | rfl | hκ4
  · exact twoSeedGraphInput_of_lt_four3 hJ h50_of_open4 hκ hκ4
  · exact WangWu.Chamber4.twoSeedGraphInput_four_of_joint hC4
  · exact twoSeedGraphInput_of_four_lt3 hR7 h50R_of_open4
      (lemma725DeterminationStatement_of_open4 hPW href725) hPW hκ4

/-- Clearance variant of `exists_measurable_lifetime_trace_eq_comp_field_of_open7`; only Aux. lemma 7 is used from Part A. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_open7_of_clearance
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h49 : Sec5.Prop411Q.Prop49QExitStatement.{u})
    (hfirst : Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by assumption) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  exists_measurable_lifetime_trace_eq_comp_field_of_inputs2
    (fun _ hκ' => twoSeedGraphInput_of_open7_of_clearance hA h47 h49 hfirst hC4 hR7 hPW href725 hκ')
    (fun _ hκ' => LocalExt.stoppedSeedExtensionStatement hκ')
    (fun _ hκ' => LocalExt.restartSeedCouplingStatement hκ') hκ hF hcoup

/-- Clearance variant of `theorem12Statement_of_open7`; only Aux. lemma 7 is used from Part A. -/
theorem theorem12Statement_of_open7_of_clearance
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h49 : Sec5.Prop411Q.Prop49QExitStatement.{u})
    (hfirst : Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u}) : Exist.Theorem12Statement.{u} := by
  intro _ hκ _ _ _ _ _ _ hF _ _ _ _ _ _ _ _ _ _ _ hcoup
  exact exists_measurable_lifetime_trace_eq_comp_field_of_open7_of_clearance hA h47 h49 hfirst hC4 hR7 hPW href725
    hκ hF hcoup

end InteractingSLE.Wire

end

end

section

/- Clearance variants of `Supplement/CounterflowNoReturnRouteWire`. -/

noncomputable section

universe u

namespace InteractingSLE.Wire

/-- Clearance variant of `theorem12Statement_of_open7_partA`; only Aux. lemma 7 is used from Part A. -/
theorem theorem12Statement_of_open7_partA_of_clearance
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (hfirst : Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u}) : Exist.Theorem12Statement.{u} :=
  theorem12Statement_of_open7_of_clearance hA h47 (Sec5.Prop49Exit.prop49QExitStatement_of_partA_of_clearance hA) hfirst hC4 hR7 hPW href725

/-- Clearance variant of `theorem13Statement_of_open7_partA`; only Aux. lemma 7 is used from Part A. -/
theorem theorem13Statement_of_open7_partA_of_clearance
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ) : Exist.Theorem13Statement.{u} :=
  theorem13Statement_of_open7 (Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 hA) h51 hC4 hR7 hPW
    hA2 hA2'

end InteractingSLE.Wire

end

end
