/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWAccessFields
import InteractingSLE.Spec.Sec5.Aux61RestartGeoIncident

/-! # Source chart geometry from the retained component construction -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Restart Aux61FibData Aux61GInst

/-- The actual retained component and the normalized R1 chart give all
source geometry fields. The whole current collar follows from physical
clearance and incidence of a fresh continuation, rather than being assumed. -/
theorem sourceChartGeometry_of_retained {W : ℝ → ℝ} {η : ℝ → ℂ}
    {K : Set ℂ} {r : ℝ≥0} {b : ℂ} {c : Chart}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η)
    (harc : WangWu.IsProperArc η) (hr : 0 < r)
    (hKo : IsOpen (H \ K))
    (hKu : ∀ z ∈ LocalSets.lowerUnion K,
      ¬ Bornology.IsBounded (connectedComponentIn (LocalSets.lowerUnion K) z))
    (hb : b ∈ retainedDomain K η r)
    (hdom : (c.dom : Set ℂ) = restartComponent K η r b)
    (hprotected : (1 : ℂ) ∉ closure K) (hmark : (1 : ℂ) ∈ closure (c.dom : Set ℂ))
    (hclear : 0 < infDist (η r) K)
    (hnew : ∃ t : ℝ, (r : ℝ) < t ∧ MapsTo η (Ioc (r : ℝ) t) (c.dom : Set ℂ))
    (hinfty : Tendsto (fun z : ℂ => ‖c.1 (z + 1)‖) (𝓝[H] 0) atTop)
    (hlift : ∀ z ∈ (c.dom : Set ℂ),
      c.2.2 z = (physicalRestartLog (stripTargetHull c.dom) z).im)
    (hcurrent : Tendsto (fun z => c.1 (fwdMapInv W r z)) (𝓝[H] 0) (𝓝 0)) :
    SourceChartGeometry W η K r c := by
  have hc := harc.cont.mono (show Icc (0 : ℝ) r ⊆ Ici 0 from fun _ ht => ht.1)
  have hH : MapsTo η (Ioc (0 : ℝ) r) H := fun t ht => harc.mem_H t ht.1
  have hprops := restartComponent_properties r.coe_nonneg hKo hKu hc harc.zero hb
  have hret : (c.dom : Set ℂ) ⊆ retainedDomain K η r := by
    rw [hdom]
    exact connectedComponentIn_subset _ _
  have hown : (c.dom : Set ℂ) ⊆ H \ fwdHull W r := by
    rw [WangWu.fwdHull_eq_image_Ioc hη harc r.coe_nonneg]
    intro z hz
    exact ⟨(hret hz).1, fun hzP => (hret hz).2
      (Or.inr (image_mono Ioc_subset_Icc_self hzP))⟩
  obtain ⟨δ, hδ, _, hcollar⟩ := exists_restart_halfDisk_collar_of_pos_infDist
    hW hW0 r.coe_nonneg hη hKo (harc.mem_H r (NNReal.coe_pos.2 hr)) hclear
  obtain ⟨t, hrt, ht⟩ := hnew
  have hfreq := frequent_current_access_of_fresh_continuation hW hW0 hη r.coe_nonneg hrt hown ht
  have hwhole : ∃ δ > 0, MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) (c.dom : Set ℂ) := by
    rw [hdom] at hfreq ⊢
    exact exists_current_collar_of_frequent_component ⟨δ, hδ, hcollar⟩ hfreq
  refine ⟨hr, hret, ?_, ?_, hinfty, hlift, hwhole, hcurrent⟩
  · rw [hdom]
    exact hprops.2.2.1
  · rw [hdom] at hmark ⊢
    exact exists_original_right_target_component_collar hc harc.zero hH hprotected hmark

/-- A positive physical contact and the actual continuation version supply
the fresh segment needed by the retained-chart collar theorem. -/
theorem exists_fresh_segment_of_restart {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E) (hpos : 0 < T x)
    {η : ℝ → ℂ} {r : ℝ≥0}
    (hversion : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = η (r + (u : ℝ))) :
    ∃ t : ℝ, (r : ℝ) < t ∧ MapsTo η (Ioc (r : ℝ) t) ((c x).dom : Set ℂ) := by
  obtain ⟨ε, hε, hεT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (ENNReal.coe_lt_coe.1 hε)
  refine ⟨r + (ε : ℝ), lt_add_of_pos_right _ hε0, ?_⟩
  intro t ht
  have ht0 : 0 < t - r := sub_pos.2 ht.1
  have htle : (t - r).toNNReal ≤ ε := Real.toNNReal_le_iff_le_coe.2 (by linarith only [ht.2])
  have hbefore : ((t - r).toNNReal : ℝ≥0∞) < T x := (ENNReal.coe_le_coe.2 htle).trans_lt hεT
  have he : r + ((t - r).toNNReal : ℝ) = t := by rw [Real.coe_toNNReal _ ht0.le]; ring
  rw [← he, ← hversion _ (Real.toNNReal_pos.2 ht0) hbefore]
  exact hs.inside x hx _ (Real.toNNReal_pos.2 ht0) hbefore

end InteractingSLE.Sec5.Aux61SlitW
