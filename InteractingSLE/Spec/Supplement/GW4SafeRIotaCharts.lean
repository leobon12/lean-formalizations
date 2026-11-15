/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaAccess
import InteractingSLE.Spec.Sec7.R5LiftSeed

/-! # GW4: actual local curves and physical current charts -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Rel Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal
open Sec7.Lemma71C

/-- The initial chart with its two source inversions has precisely the
physical component as its domain. -/
theorem component_base_domain {R L C : Set ℂ} {c : Chart}
    (hch : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H) :
    (((infinitySourceChart.trans c).trans infinitySourceChart).dom : Set ℂ) = relDom C := by
  have hc := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hch hCo hCH)).trans Chart.isConformal_infinitySourceChart
  rw [hc.coe_dom]
  change relInvC c '' H = relDom C
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    exact relInvC_mem hch hy
  · intro z hz
    exact ⟨relMapC c z, relMapC_mem_H hch hz, relInvC_relMapC hch hz⟩

/-- The physical current domain follows directly from the actual hull
identity, independently of any time change or choice of phase. -/
theorem componentAmbientChart_domain_of_hull {R L C : Set ℂ} {c : Chart}
    (hch : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {w : ℝ≥0 → ℝ} {q t : ℝ≥0}
    (hHull : fwdHull W q = relHullFam c C w t) :
    ((componentAmbientChart c W q).dom : Set ℂ) =
      relDom C ∩ (H \ fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  have hc := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hch hCo hCH)).trans Chart.isConformal_infinitySourceChart
  have hHull' : fwdHull W q = relMapC c ''
      (fwdHull (fun s : ℝ => w s.toNNReal) t ∩ relDom C) := hHull
  rw [componentAmbientChart, dom_own_stage_as_initial_inverse_image hc hW hW0 q.coe_nonneg,
    hHull', GW4Reg.H_diff_relHull_eq hch]
  change relInvC c '' (relMapC c '' (relDom C \ fwdHull (fun s : ℝ => w s.toNNReal) t)) = _
  rw [image_image]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change relInvC c (relMapC c y) ∈ _
    rw [relInvC_relMapC hch hy.1]
    exact ⟨hy.1, relDom_subset_H hCH hy.1, hy.2⟩
  · rintro ⟨hzC, _, hzK⟩
    exact ⟨z, ⟨hzC, hzK⟩, relInvC_relMapC hch hzC⟩

/-- The actual hull-version driver gives the same full chart as the
landed local driven curve, at every capacity below both lifetimes. -/
theorem Frame.relChart_eq_componentAmbientChart {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} {T : ℝ≥0} (hLoc : F.IsLoc w T)
    (hR : Continuous R) (hR0 : R 0 = 0) {V : ℝ≥0∞}
    (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (F.curve w T)) (hqV : (q : ℝ≥0∞) < V) :
    relChart (fun _ : Unit => (infinitySourceChart.trans F.c).trans infinitySourceChart)
      (fun _ : Unit => F.curve w T) q () =
      componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q := by
  obtain ⟨q', hqq', hq'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min hq hqV)
  refine loewner_congr _ q.coe_nonneg (by exact_mod_cast hqq') ?_
  intro r hr
  exact (Frame.eq_segDrv_of_version hF hLoc hR hR0 hVer
    ((ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans_lt
      (lt_min_iff.1 hq').1)
    ((ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans
      (lt_min_iff.1 hq').2.le)).symm

/-- Every physical time at or after entry and before exit lies below a
local driven-curve horizon, at exactly its physical relative capacity. -/
theorem Frame.exists_local_curve_at {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {t : ℝ≥0}
    (htEnt : F.ent w ≤ t) (htExit : (t : ℝ≥0∞) < F.exit w) :
    ∃ T : ℝ≥0, F.IsLoc w T ∧
      (ENNReal.ofReal (F.rcap w t)) < capLife (F.curve w T) := by
  obtain ⟨T, htT, hLoc⟩ := Frame.exists_isLoc_gt hF hw htExit
  exact ⟨T, hLoc, Frame.ofReal_rcap_lt_capLife hF hLoc htEnt htT⟩

end InteractingSLE.Theorem14.GW4Fix
