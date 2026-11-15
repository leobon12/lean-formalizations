/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceBasic

/-! # Physical source containment and the actual positive-time slit -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC fwdHull fwdMapInv)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61Fib Aux61FibData Aux61GInst Aux61ChLoc Aux61ULoc LawUnique GlueCond
open Aux61UnionK Aux61Conf2
universe u

/-- The original-target R1 chart geometry retained by the restart worker. -/
structure SourceChartGeometry (Wph : ℝ → ℝ) (η : ℝ → ℂ) (K : Set ℂ) (r : ℝ≥0) (c : Chart) : Prop where
  start_pos : 0 < r
  retained : (c.dom : Set ℂ) ⊆ H \ (K ∪ η '' Icc 0 r)
  simply : IsSimplyConnected (c.dom : Set ℂ)
  target : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ (c.dom : Set ℂ)
  infty : Tendsto (fun z : ℂ => ‖c.1 (z + 1)‖) (𝓝[H] 0) atTop
  lift : ∀ z ∈ (c.dom : Set ℂ),
    c.2.2 z = (Aux61Restart.physicalRestartLog (Aux61Restart.stripTargetHull c.dom) z).im
  collar : ∃ δ > 0, MapsTo (fwdMapInv Wph r) (ball 0 δ ∩ H) (c.dom : Set ℂ)
  current : Tendsto (fun z => c.1 (fwdMapInv Wph r z)) (𝓝[H] 0) (𝓝 0)

variable {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ}
  (F : SourceRestartData Ω nL nR) (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
  (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
  (κ : ℝ) (h : Ω → DistOn upperHalfPlaneOpens)
  {μ : Measure (Ω × HistorySpace 0 0)} (hF : SourceRestartFacts F s W VL VR ζ (μ := μ) κ)
  {η : Ω → ℝ≥0 → ℂ}
include hF

/-- The original-target chart facts and the physical trace construct the
glued slit with the concrete chart interval used in `sourceMarksData`. -/
theorem source_isGluedSlit {i : F.ι} {p : Ω × HistorySpace 0 0} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < (sourceCode F s W VL VR ζ κ h i p).life) (hq0 : 0 < q)
    (hW : Continuous (fun t : ℝ => W t.toNNReal p.1)) (hW0 : W 0 p.1 = 0)
    (hη : IsLoewnerTrace (fun t : ℝ => W t.toNNReal p.1) (fun t => η p.1 t.toNNReal))
    (harc : WangWu.IsProperArc (fun t : ℝ => η p.1 t.toNNReal))
    (hg : SourceChartGeometry (fun t : ℝ => W t.toNNReal p.1) (fun t => η p.1 t.toNNReal)
      (cfHullQ s p.2) (F.start i) (sourceChart F s W VL VR ζ i p))
    (hpath : ∀ u : ℝ≥0, 0 < u →
      u < exitNN (F.event i) (sourceChart F s W VL VR ζ i) (F.path i) (F.contact i) (F.data i).V p →
      F.path i p u = η p.1 (F.start i + u)) :
    IsGluedSlit (fun t : ℝ => W t.toNNReal p.1) (fun t => η p.1 t.toNNReal) (F.start i)
      (accessTime (E := F.event i) (c := sourceChart F s W VL VR ζ i) (ρ := F.path i)
        (T := F.contact i) (V := (F.data i).V) p q)
      (sourceChart F s W VL VR ζ i p) (sourceChart F s W VL VR ζ i p).dom
      (fun t : ℝ => (sourceCode F s W VL VR ζ κ h i p).driver t.toNNReal)
      (fun t : ℝ => (sourceCode F s W VL VR ζ κ h i p).trace t.toNNReal)
      (codeSpan (sourceCode F s W VL VR ζ κ h i p) q) q := by
  have hx := mem_exitEv_of_lt_accessLife hq
  have hsub : ((sourceChart F s W VL VR ζ i p).dom : Set ℂ) ⊆
      H \ fwdHull (fun t : ℝ => W t.toNNReal p.1) (F.start i) := by
    rw [WangWu.fwdHull_eq_image_Ioc hη harc (F.start i).coe_nonneg]
    intro z hz
    refine ⟨(hg.retained hz).1, ?_⟩
    rintro ⟨u, hu, he⟩
    exact (hg.retained hz).2 (Or.inr ⟨u, ⟨hu.1.le, hu.2⟩, he⟩)
  obtain ⟨Tc, hTc⟩ := exists_isGluedSlit_accessExitCode (hF.spec i) (hF.open_window i)
    (hF.zero_window i) (hF.landing i) (hF.injective_path i) (F.data i) rfl (hF.clearance i) hq hq0
    hW (by simpa only [Real.toNNReal_zero] using hW0) hη (NNReal.coe_pos.2 hg.start_pos)
    (harc.inj.mono fun _ ht => ht.1) (fun t ht => harc.mem_H t ht.1)
    (fun u hu hue => by simpa only [← NNReal.coe_add, Real.toNNReal_coe] using hpath u hu hue)
    rfl hsub hg.simply hg.target hg.infty hg.lift hg.collar hg.current
  have hp := pathGood_accessExitCode (hF.spec i) (hF.open_window i) (hF.zero_window i)
    (hF.landing i) (hF.injective_path i) (a := 0) (k := chiC κ) (h := fun p => h p.1)
    (F.data i) rfl (hF.clearance i) hx
  have hspan := codeSpan_spec hp.1 hp.2.2.2.2.2 hp.2.2.2.2.1 hq
  exact { hTc with ctrace := hspan.2.1, t_lt := hspan.1 }

/-- The physical union is contained in the explicitly constructed source
set. The sole reading input is the actual restart's own-record identity. -/
theorem source_union_subset {i : F.ι} {p : Ω × HistorySpace 0 0} {q : ℝ≥0}
    (hη : IsLoewnerTrace (fun t : ℝ => W t.toNNReal p.1) (fun t => η p.1 t.toNNReal))
    (harc : WangWu.IsProperArc (fun t : ℝ => η p.1 t.toNNReal))
    (hg : SourceChartGeometry (fun t : ℝ => W t.toNNReal p.1) (fun t => η p.1 t.toNNReal)
      (cfHullQ s p.2) (F.start i) (sourceChart F s W VL VR ζ i p))
    (hread : ∀ u : ℝ≥0, 0 < u →
      u < exitNN (F.event i) (sourceChart F s W VL VR ζ i) (F.path i) (F.contact i) (F.data i).V p →
      F.path i p u = Restart.FlowStopIdentG.histTrace 0 (killedHistory W VL VR ζ p.1) (F.start i + u))
    (hpath : ∀ u : ℝ≥0, 0 < u →
      u < exitNN (F.event i) (sourceChart F s W VL VR ζ i) (F.path i) (F.contact i) (F.data i).V p →
      F.path i p u = η p.1 (F.start i + u)) :
    unionAt (fun p => cfHullQ s p.2) (fun v p => fwdHull (fun t : ℝ => W t.toNNReal p.1) v)
      (fun p => capacityRule (F.chart i) (F.start i) q
        (stopRec s p.2, killedHistory W VL VR ζ p.1)) p ⊆ sourceSets F s W VL VR ζ κ h i q p := by
  by_cases hp : p ∈ liveEv (sourceHistory F s W VL VR ζ i) (sourceHistoryEvent F i)
      (sourceCode F s W VL VR ζ κ h i) q
  · rw [sourceSets, liveSet_of_mem hp]
    have htime : capacityRule (F.chart i) (F.start i) q
        (stopRec s p.2, killedHistory W VL VR ζ p.1) =
        ((F.start i + accessTime (E := F.event i) (c := sourceChart F s W VL VR ζ i)
          (ρ := F.path i) (T := F.contact i) (V := (F.data i).V) p q : ℝ≥0) : ℝ≥0∞) := by
      by_cases hq : q = 0
      · subst q
        rw [capacityRule_zero, accessTime_zero (hF.spec i) (hF.open_window i) (hF.zero_window i)
          (hF.landing i) (hF.injective_path i) hp.2, add_zero]
      · exact capacityRule_eq_accessTime (hF.spec i) (hF.open_window i) (hF.zero_window i)
          (hF.landing i) (hF.injective_path i) (c := F.chart i) (r := F.start i)
          (a := 0) (k := chiC κ) (h := fun p => h p.1)
          rfl hread (pos_iff_ne_zero.2 hq) hp.2
    have hτ := (accessTime_spec (hF.spec i) (hF.open_window i) (hF.zero_window i)
      (hF.landing i) (hF.injective_path i) (a := 0) (k := chiC κ) (h := fun p => h p.1) hp.2).1
    apply unionAt_subset_chartSet (x := p) (A₂ := fun p : Ω × HistorySpace 0 0 => cfHullQ s p.2)
      ((hF.spec i).conf p (mem_exitEv_of_lt_accessLife hp.2).1.1)
      (htime ▸ ENNReal.coe_lt_top)
      (fun z hz hzd => (hg.retained hzd).2 (Or.inl hz))
    rw [htime, ENNReal.toNNReal_coe]
    apply fwdHull_mapsTo_chartHull_of_access (hF.spec i) (hF.open_window i) (hF.zero_window i)
      (hF.landing i) (hF.injective_path i) (F.data i) rfl (hF.clearance i) hp.2 hη harc
    · intro u hu hue
      simpa only [← NNReal.coe_add, Real.toNNReal_coe] using hpath u hu (hue.trans_lt hτ)
    · intro u hu hdom
      exact (hg.retained hdom).2 (Or.inr ⟨u, hu, rfl⟩)
  · rw [sourceSets, liveSet_of_notMem hp]
    by_cases hT : capacityRule (F.chart i) (F.start i) q (stopRec s p.2, killedHistory W VL VR ζ p.1) < ⊤
    · simp only [unionAt, hT, ↓reduceIte]; exact inter_subset_left
    · simp only [unionAt, hT, ↓reduceIte, subset_refl]

end InteractingSLE.Sec5.Aux61SlitW
