/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfPhysical
import InteractingSLE.Spec.Supplement.GW2SfCanonical
import InteractingSLE.Spec.Supplement.GW2RdSafeGood

/-!
# The threshold clause of GW2's relative safe law

Packet PROVE-GW2-SAFE. Physical collision exclusion proves the continuation
threshold bound for every announced GW2 version and every type of its raised
word, under exactly the corresponding conditioned canonical law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Sf

open Restart Exist.StagedLaw Sec7.PocketTraversal Restart.FCDet
  Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop GW2Rd GW2TipSystem

/-- The continuation-threshold clause of `GW2RdSafeStatement`, proved from
physical bad-boundary avoidance before contact and before the flow lifetime. -/
theorem ae_canonStp_le_thr_gw2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {h h' Hc : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ))
      (chiC (16 / κ)) (h ω) (h' ω))
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hadm : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      0 (flowLineXL b J 0) (flowLineXR b J 0))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0) (hHcm : Measurable Hc)
    (c' : BoundaryWord) (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsGW2RelVersion s P W Wα ζ ζα γ α R V) (w : WordType) :
    ∀ᵐ y ∂((P.map fun ω => (gb6Rec s W ζ ω,
        relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))[|
          typeEvent κ w (gw2Word κ θ c') (gb6TS s)]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv
        (fun y => typedXL κ w (gw2Word κ θ c' y.1))
        (fun y => typedXR κ w (gw2Word κ θ c' y.1)) y := by
  obtain ⟨GT, hGT, -, hGTrec⟩ := exists_goodSet_gw2 hκ hfl hα hadm hcf hγ hζ s
  have hGTae : ∀ᵐ ω ∂P, γ ω s ∈ H → ω ∈ GT := by
    filter_upwards [hGTrec, ae_gb6RecGood hcf hγ s, hζ] with ω hgr hrec hz hsH
    exact hgr.2 ((mem_gb6TS_iff hrec).1 ⟨by rw [hz]; exact ENNReal.coe_lt_top, hsH⟩)
  have hn := ae_no_threshold_gw2_of_goodSet hκ hκ4 hb hG hb' hT hfl hα hcf hζ s c' hc'J hc'b hver hGT hGTae
  obtain ⟨⟨⟨⟨hRm, hRc, hR0, -, hVm, -, -⟩, -⟩, -⟩, -⟩ := hver
  apply ae_canonStp_le_thr_gw2_of_driver_bound hcf hγ s hHcm c' hRm hRc hR0 hVm w
  filter_upwards [hn] with ω hnω hsH htype
  refine (le_thr_iff_no_threshold hRc _ _ V ω).2 fun u hu => ?_
  have hnt := not_threshold_images_of_isFlowType (isFlowType_typed htype)
    (D := fun v : ℝ => R v.toNNReal ω) (u := u)
    (by simpa only [Real.toNNReal_coe] using hnω hsH u hu)
  convert hnt using 1
  simp only [Real.toNNReal_coe]
  rfl

end InteractingSLE.Theorem14.GW2Sf
