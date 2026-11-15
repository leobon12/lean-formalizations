/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaVisits
import InteractingSLE.Spec.Supplement.GW4CLocGeom

/-!
# GW4: the actual rational physical-reference cover

Every nonzero coordinate at a positive live component line has an incident
half-disc in an earlier component chart at a rational physical interior
visit. The old/current inherited lift tends to zero on that access. The
cover includes exposed coordinates and does not discard landing fibers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar

/-- The actual traversal's rational interior visits supply the own-stage
collars at every nonzero current relative coordinate. -/
theorem exists_rat_visit_own_collar {F : Frame} (hF : F.IsOk) {w : ℝ≥0 → ℝ}
    (hw : F.IsPathOk w) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < F.exit w) (hq : 0 < F.rcap w t)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ s : ℚ, (F.ent w : ℝ) < s ∧ (s : ℝ) < t ∧
      trc w (s : ℝ).toNNReal ≠ 0 ∧ -(trc w (s : ℝ).toNNReal)⁻¹ ∈ F.C ∧
      0 < F.rcap w (s : ℝ).toNNReal ∧ F.rcap w (s : ℝ).toNNReal < F.rcap w t ∧
      ∃ x r : ℝ, 0 < r ∧
        (Chart.id.loewner W (F.rcap w (s : ℝ).toNNReal)).2.1 ''
          (H ∩ ball (x : ℂ) r) ⊆ ((Chart.id.loewner W (F.rcap w t)).dom : Set ℂ) ∧
        Tendsto (fun z => (Chart.id.loewner W (F.rcap w (s : ℝ).toNNReal)).1
            ((Chart.id.loewner W (F.rcap w t)).2.1 z))
          (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (fun z => (Chart.id.loewner W (F.rcap w t)).2.2
              ((Chart.id.loewner W (F.rcap w t)).2.1 z) -
            (Chart.id.loewner W (F.rcap w (s : ℝ).toNNReal)).2.2
              ((Chart.id.loewner W (F.rcap w t)).2.1 z))
          (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨δ, hδ, hδq, hCol⟩ := exists_recent_own_collars hW hW0 hq hξ
  obtain ⟨s, hsEnt, hst, hs0, hsC, hsCap, hsLt⟩ :=
    Frame.exists_rat_interior_visit_recent_capacity hF hw ht hq hδ
  refine ⟨s, hsEnt, hst, hs0, hsC, ?_, hsLt, hCol _ ⟨hsCap, hsLt⟩⟩
  linarith only [hsCap, hδq]

/-- At every positive live line, a rational physical interior visit gives
an earlier actual component line with an incident collar and zero lift.
No boundary-limit or reference-cover assumption is imposed. -/
theorem exists_component_rat_reference {Ω : Type*} {F : Frame} (hF : F.IsOk)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun u => Wd u ω)) {ω : Ω} (hω : ω ∈ GT)
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0)
    (hver : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω →
      ∃ t, QuantumZipper.fwdHull (wpath R ω) q = F.hullAt (fun u => Wd u ω) t)
    {t : ℝ≥0} (hlt : lineClock F Wd GT V t ω < V ω)
    (hq : 0 < (lineClock F Wd GT V t ω).toNNReal) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ s : ℚ, (F.ent (fun u => Wd u ω) : ℝ) < s ∧ (s : ℝ) < t ∧
      trc (fun u => Wd u ω) (s : ℝ).toNNReal ≠ 0 ∧
      -(trc (fun u => Wd u ω) (s : ℝ).toNNReal)⁻¹ ∈ F.C ∧
      lineClock F Wd GT V (s : ℝ).toNNReal ω < lineClock F Wd GT V t ω ∧
      ∃ x r : ℝ, 0 < r ∧
        (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).2.1 ''
          (H ∩ ball (x : ℂ) r) ⊆ ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) ∧
        Tendsto (fun z => (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).1
            ((componentLineChart F Wd GT R V t ω).2.1 z))
          (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (fun z => (componentLineChart F Wd GT R V t ω).2.2
              ((componentLineChart F Wd GT R V t ω).2.1 z) -
            (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).2.2
              ((componentLineChart F Wd GT R V t ω).2.1 z))
          (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have hw := hGT ω hω
  have hex := CLoc.lt_exit_of_lineClock_lt hF hGT hω hRc hR0 hver hlt
  have hP : F.physClockG Wd GT t ω < V ω := by
    by_contra hnot
    exact (lt_irrefl _) (hlt.trans_le (le_min (not_lt.1 hnot) le_rfl))
  have hClock : ∀ u : ℝ≥0, u ≤ t →
      ((lineClock F Wd GT V u ω).toNNReal : ℝ) = F.rcap (fun v => Wd v ω) u := by
    intro u hut
    have hPu := (Frame.monotone_physClockG hF hGT ω hut).trans_lt hP
    have hue := (ENNReal.coe_le_coe.2 hut).trans_lt hex
    rw [ENNReal.coe_toNNReal_eq_toReal, lineClock, min_eq_left hPu.le]
    change (F.physClockG Wd GT u ω).toReal = _
    rw [Frame.physClockG_eq_rcap hF hGT hω hue,
      ENNReal.toReal_ofReal (Frame.rcap_nonneg hF hw hue)]
  have hW : Continuous (wpath R ω) := hRc.comp continuous_real_toNNReal
  have hW0 : wpath R ω 0 = 0 := by simpa only [wpath, Real.toNNReal_zero] using hR0
  obtain ⟨s, hsEnt, hst, hs0, hsC, hsCap0, hsCapLt, x, r, hr, hCol, hTr, hLift⟩ :=
    exists_rat_visit_own_collar hF hw hW hW0 hex
      (by rw [← hClock t le_rfl]; exact NNReal.coe_pos.2 hq) hξ
  have hsn : (s : ℝ).toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hst.le
  have hChart : ∀ u : ℝ≥0, u ≤ t → componentLineChart F Wd GT R V u ω =
      Chart.id.loewner (wpath R ω) (F.rcap (fun v => Wd v ω) u) := by
    intro u hut
    unfold componentLineChart
    rw [hClock u hut]
  refine ⟨s, hsEnt, hst, hs0, hsC, ?_, x, r, hr, ?_⟩
  · have hOldFin : lineClock F Wd GT V (s : ℝ).toNNReal ω ≠ ⊤ :=
      ne_top_of_le_ne_top (((Frame.monotone_physClockG hF hGT ω hsn).trans_lt hP).trans_le le_top).ne
        (min_le_left _ _)
    rw [← ENNReal.coe_toNNReal (hlt.trans_le le_top).ne,
      ← ENNReal.coe_toNNReal hOldFin]
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hClock _ hsn, hClock t le_rfl]
    exact hsCapLt
  · rw [hChart _ hsn, hChart t le_rfl]
    exact ⟨hCol, hTr, hLift⟩

end InteractingSLE.Theorem14.GW4Fix
