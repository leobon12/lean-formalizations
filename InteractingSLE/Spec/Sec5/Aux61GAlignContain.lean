/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GAlignGauss

/-! # Initial union containment from the retained source component

At zero capacity the physical stop is the initial own time. The proper-arc
hull is exactly its initial trace segment. Thus retained-domain exclusion
already proves containment; no positive-time path reading is needed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GAlign
open Aux61SlitW Aux61SlitW.SourceSetting Aux61Marks Aux61ChLoc
open Aux61ULoc Aux61GInst LawUnique GlueCond Coupling WangWu
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
    (μ := S.μ) S.κ)
include hR

/-- The retained component excludes the initial counterflow hull and own
prefix; this proves the precise regular-union input at zero capacity. -/
theorem source_initial_contains (i : F.ι)
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ))) :
    ∀ᵐ p ∂S.μ, unionAt (fun p => cfHullQ (rationalTime S.s) p.2)
      (fun t p => Sec7.PocketStopWallsFin.regHull S.own.W S.life t p.1)
      (fun p => capacityRule (F.chart i) (F.start i) 0
        (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) p ⊆
        (S.marksData F).baseSets i 0 p := by
  have hreg := ae_glue_fst (μ := S.P) S.kernel S.measCounterField
    (Sec7.PocketStopWallsFin.ae_regHull_eq S.own.coupling S.own_infinite)
  filter_upwards [S.physical_path, hreg, hretained] with p hp hr hd
  simp only [capacityRule_zero, unionAt, ENNReal.coe_lt_top, ↓reduceIte, ENNReal.toNNReal_coe, hr]
  change _ ⊆ sourceSets F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField i 0 p
  by_cases hl : p ∈ liveEv
      (sourceHistory F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      (sourceHistoryEvent F i)
      (sourceCode F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField i) 0
  · have hxE : p ∈ F.event i := (mem_exitEv_of_lt_accessLife hl.2).1.1
    have hc := (hR.spec i).conf p hxE
    rw [sourceSets, liveSet_of_mem hl, Aux61OldB.chartHull_zero]
    intro z hz
    refine ⟨hz.1, ?_⟩
    rintro ⟨w, hw, he⟩
    have hzdom : z ∈ ((S.marksData F).chart i p).dom := he ▸ hc.inv_mem_dom hw.1
    apply (hd hxE hzdom).2
    rcases hz.2 with hcf | hown
    · exact Or.inl hcf
    · rw [WangWu.fwdHull_eq_image_Ioc hp.2.1 hp.2.2 (F.start i).coe_nonneg] at hown
      exact Or.inr (image_mono Ioc_subset_Icc_self hown)
  · rw [sourceSets, liveSet_of_notMem hl]
    exact inter_subset_left

/-- The concrete initial Gaussian law needs only MARKS's initial set
measurability and the physical retained-component exclusion. -/
theorem exists_source_initialGauss_of_retained (i : F.ι)
    (hsets : Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      ((S.marksData F).baseSets i 0))
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ))) :
    ∃ g : S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      @IsChartGaussAt (S.Ω × HistorySpace 0 0) _
        ((S.marksData F).β i) ((S.marksData F).mβ i)
        S.μ ((S.marksData F).Z i) ((S.marksData F).B i)
        ((S.marksData F).code i) 0 ((S.marksData F).sigma i 0) g :=
  exists_source_initialGauss S F hR i hsets (source_initial_contains S F hR i hretained)

end InteractingSLE.Sec5.Aux61GAlign
