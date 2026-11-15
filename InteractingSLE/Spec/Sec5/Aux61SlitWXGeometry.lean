/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXRead
import InteractingSLE.Spec.Sec5.Aux61SlitWRetainedFields

/-! # Normalized physical chart geometry from the selected R1 configuration -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWX
open Aux61SlitW Aux61Asm2 Aux61Restart Aux61FibData Aux61Marks Aux61ULoc LawUnique
open Restart.FlowStopIdentG

/-- Current incidence supplies the fresh segment, so the full geometry
does not depend on an already assembled restart specification. -/
theorem geometry_of_incidence {W : ℝ → ℝ} {η : ℝ → ℂ} {K : Set ℂ} {r : ℝ≥0} {b : ℂ} {c : Chart}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (harc : WangWu.IsProperArc η)
    (hr : 0 < r) (hKo : IsOpen (H \ K))
    (hKu : ∀ z ∈ LocalSets.lowerUnion K,
      ¬ Bornology.IsBounded (connectedComponentIn (LocalSets.lowerUnion K) z))
    (hb : b ∈ retainedDomain K η r) (hdom : (c.dom : Set ℂ) = restartComponent K η r b)
    (hprotected : (1 : ℂ) ∉ closure K) (hmark : (1 : ℂ) ∈ closure (c.dom : Set ℂ))
    (hclear : 0 < infDist (η r) K)
    (hfreq : ∃ᶠ w in 𝓝[H] 0, fwdMapInv W r w ∈ restartComponent K η r b)
    (hinfty : Tendsto (fun z : ℂ => ‖c.1 (z + 1)‖) (𝓝[H] 0) atTop)
    (hlift : ∀ z ∈ (c.dom : Set ℂ), c.2.2 z = (physicalRestartLog (stripTargetHull c.dom) z).im)
    (hcurrent : Tendsto (fun z => c.1 (fwdMapInv W r z)) (𝓝[H] 0) (𝓝 0)) :
    SourceChartGeometry W η K r c := by
  obtain ⟨t, hrt, -, -, hnew⟩ := exists_fresh_segment_in_incident_component
    hW hW0 hη r.coe_nonneg (lt_add_one (r : ℝ))
    (harc.inj.mono Icc_subset_Ici_self) (fun t ht => harc.mem_H t ht.1)
    (harc.mem_H r (NNReal.coe_pos.2 hr)) hKo hclear hfreq
  apply sourceChartGeometry_of_retained hW hW0 hη harc hr hKo hKu hb hdom hprotected hmark hclear
    ⟨t, hrt, ?_⟩ hinfty hlift hcurrent
  rwa [hdom]

universe u
variable {S : SourceSetting.{u}} {D : R1Restart S} (R : ReaderFacts D) (h : D.HasChart)
include R

/-- Every physical chart-geometry field follows from the full R1 choice
and the selected initial-record configuration. No restart or landing
specification is assumed. -/
theorem ReaderFacts.ae_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (GlueCond.cfHullQ (rationalTime S.s) p.2) (rationalTime (D.q i))
      (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
  intro i
  filter_upwards [S.physical_path, S.counterflow_retained_geometry, ae_trace_eq_and_continuous S,
    R.ae_inverse_eq h, ae_mem_goodCfSet S] with p hp hcf htr hinv hgood he
  let y := sourceRecord (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p
  have hy : y ∈ D.selected i := he
  have hq : (rationalTime (D.q i) : ℝ) = (D.q i : ℝ) := Real.coe_toNNReal _ (R.q_pos i).le
  have hK : historyHull (rationalTime S.s) (D.Y i) y = GlueCond.cfHullQ (rationalTime S.s) p.2 := by
    have heq : historyHull (rationalTime S.s) (D.Y i) y =
        historyHull (rationalTime S.s) Prod.fst y := by
      simp only [historyHull, R.counterflow i y hy]
    rw [heq]
    exact historyHull_stopRec_eq_cfHullQ hgood _
  have hη : EqOn (D.η i y) (fun t : ℝ => S.path p.1 t.toNNReal) (Icc (0 : ℝ) (D.q i)) := by
    intro t ht
    rw [(R.path i y hy) ht]
    change histTrace 0 (stopRec (rationalTime (D.q i))
      (killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) t.toNNReal = _
    rw [histTrace_stopRec_of_le (by rw [Real.toNNReal_le_iff_le_coe, hq]; exact ht.2), htr.1]
  have hret : retainedDomain (historyHull (rationalTime S.s) (D.Y i) y) (D.η i y) (D.q i) =
      retainedDomain (GlueCond.cfHullQ (rationalTime S.s) p.2)
        (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (D.q i)) := by
    rw [hK, retainedDomain, retainedDomain, hη.image_eq, hq]
  have hc := chart_spec D h i
  have hd := hc.domain y
  change ((chart D h i y).dom : Set ℂ) = connectedComponentIn _ _ at hd
  rw [hret] at hd
  have hm := hc.target y
  have hmark := hm
  rw [hd] at hmark
  have hH : MapsTo (fun t : ℝ => S.path p.1 t.toNNReal) (Ioc 0 (rationalTime (D.q i) : ℝ)) H :=
    fun t ht => hp.2.2.mem_H t ht.1
  have hcollars := fun b hb => exists_original_right_target_component_collar
    (hp.2.2.cont.mono Icc_subset_Ici_self) hp.2.2.zero hH
      (hcf (rationalTime S.s)).2.2.2 (b := b) hb
  have hinc := (R.configuration i hy).2.2
  change ∃ b : ℂ, (1 : ℂ) ∈ closure (connectedComponentIn _ b) ∧
    ∃ᶠ w in 𝓝[H] 0, (ownHistoryChart (D.U i) (D.r i) y).2.1 w ∈ connectedComponentIn _ b at hinc
  rw [hret] at hinc
  have hfreqU := (original_target_access_iff_selected_component hcollars hmark).1 hinc
  have hfreq : ∃ᶠ w in 𝓝[H] 0, fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1)
      (rationalTime (D.q i)) w ∈ connectedComponentIn
        (retainedDomain (GlueCond.cfHullQ (rationalTime S.s) p.2)
          (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (D.q i))) (base D h i y) := by
    refine (hfreqU.and_eventually self_mem_nhdsWithin).mono fun w hw => ?_
    rw [← hinv i he hw.2]
    exact hw.1
  have hclear := (R.configuration i hy).1.2.2
  rw [hK, hη ⟨(R.q_pos i).le, le_rfl⟩] at hclear
  have hcurrent : Tendsto (fun w => (chart D h i y).1
      (fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime (D.q i)) w)) (𝓝[H] 0) (𝓝 0) :=
    (hc.current y).congr' ((show ∀ᶠ w : ℂ in 𝓝[H] 0, w ∈ H from self_mem_nhdsWithin).mono
      fun w hw => congrArg (chart D h i y).1 (hinv i he hw))
  change SourceChartGeometry _ _ _ _ (chart D h i y)
  apply geometry_of_incidence hp.1.continuous_rpath
    (by simpa only [Ito.rpath, Real.toNNReal_zero] using hp.1.2.1) hp.2.1 hp.2.2
    (Real.toNNReal_pos.2 (R.q_pos i)) (hcf (rationalTime S.s)).2.1
    (hcf (rationalTime S.s)).2.2.1 (hret ▸ hc.base_mem y) hd
    (hcf (rationalTime S.s)).2.2.2 hm _ hfreq (hc.infty y) (hc.lift y) hcurrent
  simpa only [Real.toNNReal_coe] using hclear

end InteractingSLE.Sec5.Aux61SlitWX
