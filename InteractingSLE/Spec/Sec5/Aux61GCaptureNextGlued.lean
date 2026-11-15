/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextPhysical

/-! # Positive-time source slit facts without any capture hypothesis

The physical source, its explicit word, and the actual source chart imply
the slit facts required by MARKS independently of the event to be covered.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GCaptureNext
open Aux61SlitW Aux61SlitW.SourceSetting Aux61Marks Aux61Asm Aux61ChLoc Aux61ULoc
open Aux61FibData Aux61GInst LawUnique GlueCond WangWu Cond44Ref CrossCond.Theta Coupling
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ)
  (hgeo : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (F.start i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
  (hpath : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ v : ℝ≥0, 0 < v →
    (v : ℝ≥0∞) < F.contact i p → F.path i p v = S.path p.1 (F.start i + v))

include hR hgeo hpath

/-- The actual selected-access code, physical trace and explicit comparison
means satisfy the positive-time clause of `MarksFacts`. -/
theorem glued_facts : let D := S.marksData F;
    ∀ i (q : ℝ≥0), 0 < q → ∀ᵐ p ∂S.μ, D.Z i p ∈ D.B i → (q : ℝ≥0∞) < (D.code i p).life →
      GluedSlitFacts (D.data i).κ (D.code i p) q (D.physicalDriver i q p) (D.physicalPath i q p)
        (D.start i q p) (D.duration i q p) (D.chart i p) (D.domain i q p) (D.chartPath i q p) (D.chartLife i q p)
        (fun j => D.time j i q p) (fun j => D.patches j i q p) (D.baseSets i q p)
        (fun j => D.mean j i q p) (fun j => D.physicalMean j i q p) := by
  intro D i q hq0
  filter_upwards [S.physical_path, hgeo i, hpath i, S.geometric_patch_mean]
    with p hp hg hv hb hB hq
  have hx := mem_exitEv_of_lt_accessLife hq
  have hbefore : ∀ u : ℝ≥0,
      u < exitNN (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (F.path i) (F.contact i) (F.data i).V p → (u : ℝ≥0∞) < F.contact i p :=
    fun u hu => (ENNReal.coe_lt_coe.2 hu).trans_le
      (IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le p)
  have hgl := source_isGluedSlit F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField
    hR hq hq0 hp.1.continuous_rpath hp.1.2.1 hp.2.1 hp.2.2 (hg hx.1.1)
    (fun u hu hue => hv hx.1.1 u hu (hbefore u hue))
  have hgeo := sourceSets_geometry F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField
    hR.spec i q p ⟨hB, hq⟩
  have hclosed := sourceSets_closed F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField
    hR.spec i q p
  have hword := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data S.a S.b) {0} 0
  have hf := gluedSlitFacts_of_bhe hgl hclosed.1 (inter_domain_subset_trace hgl hgeo)
    hword.2.1 hword.2.2.2 hb
  have hpatch : (fun j : ℚ => D.patches j i q p) =
      fun j => fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime j) := by
    funext j
    exact Aux50Hit.regHull_stopHistory_cstop hp.1 (rationalTime j)
  rw [← hpatch] at hf
  change GluedSlitFacts (F.data i).κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hR.kappa i]
  exact hf


end InteractingSLE.Sec5.Aux61GCaptureNext
