/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaCover
import InteractingSLE.Spec.Supplement.GW3LawEvery
import InteractingSLE.Spec.Sec7.R5LiftAccess

/-! # GW4: the actual component references in the ambient counterflow chart

The relative hull version agrees with the physical-time hull on a live
line. Pulling its chart back by the two source inversions therefore gives
exactly the full ambient hull complement inside the inverted component.
This supplies the domain equality required by R.5's reflection machinery.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Rel Sec7.PocketStopSide MartChar

/-- The inherited relative chart, read on the original ambient
counterflow domain using the two prescribed inversions. -/
def componentAmbientChart (c : Chart) (R : ℝ → ℝ) (q : ℝ) : Chart :=
  ((infinitySourceChart.trans c).trans infinitySourceChart).loewner R q

/-- On every live physical line the version's hull is the actual relative
hull at that physical time, including lines before entry. -/
theorem component_fwdHull_eq_hullAt {Ω : Type*} {F : Frame} (hF : F.IsOk)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) {ω : Ω} (hω : ω ∈ GT)
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0)
    (hver : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω →
      ∃ u, fwdHull (wpath R ω) q = F.hullAt (fun r => Wd r ω) u)
    {t : ℝ≥0} (hLive : lineClock F Wd GT V t ω < V ω) :
    fwdHull (wpath R ω) (lineClock F Wd GT V t ω).toNNReal =
      F.hullAt (fun r => Wd r ω) t := by
  have hw := hGT ω hω
  have hex := CLoc.lt_exit_of_lineClock_lt hF hGT hω hRc hR0 hver hLive
  have hP : F.physClockG Wd GT t ω < V ω := by
    by_contra hnot
    exact (lt_irrefl _) (hLive.trans_le (le_min (not_lt.1 hnot) le_rfl))
  have hq : (↑(lineClock F Wd GT V t ω).toNNReal : ℝ) = F.rcap (fun r => Wd r ω) t := by
    rw [ENNReal.coe_toNNReal_eq_toReal, lineClock, min_eq_left hP.le]
    rw [Frame.physClockG_eq_rcap hF hGT hω hex,
      ENNReal.toReal_ofReal (Frame.rcap_nonneg hF hw hex)]
  have hW : Continuous (wpath R ω) := hRc.comp continuous_real_toNNReal
  have hW0 : wpath R ω 0 = 0 := by simpa only [wpath, Real.toNNReal_zero] using hR0
  by_cases hte : t ≤ F.ent (fun r => Wd r ω)
  · have hq0 : (lineClock F Wd GT V t ω).toNNReal = 0 := by
      apply NNReal.coe_injective
      rw [hq, Frame.rcap_eq_zero_of_le hF hw hte, NNReal.coe_zero]
    rw [hq0, NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hW,
      Frame.hullAt_eq_empty_of_le hF hw hte]
  · obtain ⟨u, hu⟩ := hver (lineClock F Wd GT V t ω).toNNReal (by
      rw [ENNReal.coe_toNNReal (hLive.trans_le le_top).ne]
      exact hLive)
    exact Frame.fwdHull_eq_hullAt_of_version hF hw hW hW0 hu (not_le.1 hte).le hex hq

/-- The physical reference really has the full complement domain used in
R.5, rather than only an inclusion in the ambient complement. -/
theorem componentAmbientChart_domain {Ω : Type*} {F : Frame} (hF : F.IsOk)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) {ω : Ω} (hω : ω ∈ GT)
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0)
    (hver : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω →
      ∃ u, fwdHull (wpath R ω) q = F.hullAt (fun r => Wd r ω) u)
    {t : ℝ≥0} (hLive : lineClock F Wd GT V t ω < V ω) :
    ((componentAmbientChart F.c (wpath R ω)
      (lineClock F Wd GT V t ω).toNNReal).dom : Set ℂ) =
      relDom F.C ∩ (H \ fwdHull (wpath Wd ω) t) := by
  have hw := hGT ω hω
  have hCH : F.C ⊆ H := subset_H_of_mem_betweenComponents hF.2.1
  have hc := GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 (Frame.isOpen_C hF hw) hCH
  have hBase := (Chart.isConformal_infinitySourceChart.trans hc).trans
    Chart.isConformal_infinitySourceChart
  have hW : Continuous (wpath R ω) := hRc.comp continuous_real_toNNReal
  have hW0 : wpath R ω 0 = 0 := by simpa only [wpath, Real.toNNReal_zero] using hR0
  have hHull : fwdHull (wpath R ω) (lineClock F Wd GT V t ω).toNNReal =
      relMapC F.c '' (fwdHull (wpath Wd ω) t ∩ relDom F.C) :=
    component_fwdHull_eq_hullAt hF hGT hω hRc hR0 hver hLive
  rw [componentAmbientChart, dom_own_stage_as_initial_inverse_image hBase hW hW0
    (lineClock F Wd GT V t ω).toNNReal.coe_nonneg, hHull,
    GW4Reg.H_diff_relHull_eq hF.2.2.2.1]
  change relInvC F.c '' (relMapC F.c '' (relDom F.C \ fwdHull (wpath Wd ω) t)) = _
  rw [image_image]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change relInvC F.c (relMapC F.c y) ∈ _
    rw [relInvC_relMapC hF.2.2.2.1 hy.1]
    exact ⟨hy.1, relDom_subset_H hCH hy.1, hy.2⟩
  · rintro ⟨hzD, _, hzK⟩
    exact ⟨z, ⟨hzD, hzK⟩, relInvC_relMapC hF.2.2.2.1 hzD⟩

end InteractingSLE.Theorem14.GW4Fix
