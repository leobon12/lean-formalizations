/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GChoice16Recorded
import InteractingSLE.Spec.Sec5.Aux61GStepPhysical
import InteractingSLE.Spec.Sec5.Aux61SlitWCaptureFields
import InteractingSLE.Spec.Sec4.Prop412

/-! # The actual source own reference has the canonical seed germ

Force-point separation follows from the given source coupling. The
landed physical seed theorem then identifies the singular reference germ
using the actual chart normalization. No separate force-separation,
reflection, derivative, or relative-phase premise is supplied.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GChoice16
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61Restart Aux61FibData
open LawUnique GlueCond
universe u

/-- All actual force points are separated from the source driver at every
positive time, by the existing noncollision theorem under condition (4.4). -/
theorem ae_source_force_separation (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    ∀ t : ℝ≥0, 0 < t →
      (∀ j, S.own.VL j t p.1 < S.own.W t p.1) ∧
      ∀ j, S.own.W t p.1 < S.own.VR j t p.1 := by
  have hsep := Sec4.ae_simple_trace_of_cond44 S.κ_pos S.κ_lt_four
    (Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data S.a S.b) {0} 0)
    S.cond44 S.own.coupling.1
  exact (WangWu.ae_glue_fst (μ := S.P) S.kernel S.measCounterField hsep).mono
    fun _ hp => hp.2.1

/-- At zero the actual own reference mean, with the inherited physical
lift, agrees with the reference word. All analytic seed inputs are proved
from source chart geometry and the coupling's force separation. -/
theorem source_own_seed_germ (S : SourceSetting.{u})
    (F : SourceRestartData S.Ω S.nL S.nR)
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι) (q : ℚ) (hq : F.start i = rationalTime q)
    (hleft : PiecewiseConstantBoundaryData.leftLim (F.data i).bR 0 = -sleLambda (F.data i).κ)
    (hright : PiecewiseConstantBoundaryData.rightLim (F.data i).bR 0 = sleLambda (F.data i).κ)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) :
    ∀ᵐ p ∂S.μ, p ∈ F.event i → Tendsto
      (fun z => sourceReferenceMean S (.inl q) p (((S.marksData F).chart i p).2.1 z) +
        (S.marksData F).scale + (S.marksData F).constant *
          ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
        Aux61GlueK.refMean0 (F.data i) z) (𝓝[H] 0) (𝓝 0) := by
  filter_upwards [S.physical_path, ae_source_force_separation S, hgeometry]
    with p hp hsep hg he
  have hW := hp.1.continuous_rpath
  have hW0 : (fun t : ℝ => S.own.W t.toNNReal p.1) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hp.1.2.1
  have hc := (hR.spec i).conf p he
  have hgeo := hg he
  have hsub : (((S.marksData F).chart i p).dom : Set ℂ) ⊆
      H \ fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i) := by
    rw [WangWu.fwdHull_eq_image_Ioc hp.2.1 hp.2.2 (F.start i).coe_nonneg]
    intro z hz
    exact ⟨(hgeo.retained hz).1, fun hP => (hgeo.retained hz).2
      (Or.inr (image_mono Ioc_subset_Icc_self hP))⟩
  have hB := isHPHull_stripTargetHull ((S.marksData F).chart i p).dom.isOpen
    hgeo.simply hc.dom_subset hgeo.target
  obtain ⟨a, ξ, -, hscale⟩ := hgeo.scale hW hW0 hp.2.1 hp.2.2 hc
  have hs := hsep (F.start i) hgeo.start_pos
  have ht := Aux61GStep.tendsto_charted_couplingMean_sub_refMean0_seed (F.data i)
    (Ito.weightWord S.ρL S.ρR)
    (fun j => S.own.VL j (F.start i) p.1 - S.own.W (F.start i) p.1)
    (fun j => S.own.VR j (F.start i) p.1 - S.own.W (F.start i) p.1)
    (fun j => Or.inl (sub_neg.2 (hs.1 j)))
    (fun j => Or.inl (sub_pos.2 (hs.2 j))) hleft hright hW hW0 hp.2.1
    (NNReal.coe_pos.2 hgeo.start_pos) (hp.2.2.inj.mono Icc_subset_Ici_self)
    (fun t ht => hp.2.2.mem_H t ht.1) hc hsub hB hscale hgeo.collar hgeo.current hgeo.lift
  rw [hR.kappa i] at ht
  change Tendsto (fun z =>
    couplingMean S.κ (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime q)
      (sourcePatchExtension S.own.W S.own.VL S.own.VR S.κ S.ρL S.ρR q p.1)
      (((S.marksData F).chart i p).2.1 z) + 0 + chiC S.κ *
      ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
      Aux61GlueK.refMean0 (F.data i) z) (𝓝[H] 0) (𝓝 0)
  have heq : Ito.rpath (fun t => S.own.W t p.1) = (fun t : ℝ => S.own.W t.toNNReal p.1) := rfl
  rw [heq] at ht
  simpa only [sourcePatchExtension, ← hq, add_zero,
    SourceSetting.marksData, sourceMarksData] using ht

end InteractingSLE.Sec5.Aux61GChoice16
