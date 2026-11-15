/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaSeedCover

/-! # GW4: an exposed rational physical-reference cover -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar RealFlow

/-- At every positive live physical line, a nonzero exposed access has a
rational interior-visit reference whose own boundary coordinate is also
exposed. This supplies the seed condition needed by the phase comparison. -/
theorem exists_component_rat_seed_reference {Ω : Type*} {F : Frame} (hF : F.IsOk)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun u => Wd u ω)) {ω : Ω} (hω : ω ∈ GT)
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0)
    (hver : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω →
      ∃ t, QuantumZipper.fwdHull (wpath R ω) q = F.hullAt (fun u => Wd u ω) t)
    {t : ℝ≥0} (hlt : lineClock F Wd GT V t ω < V ω)
    (hq : 0 < (lineClock F Wd GT V t ω).toNNReal) {ξ : ℝ} (hξ : ξ ≠ 0)
    (hξSeed : ξ ∈ Ioo
      (-rightImg (fun u => -wpath R ω u) 0 (lineClock F Wd GT V t ω).toNNReal -
        R (lineClock F Wd GT V t ω).toNNReal ω)
      (rightImg (wpath R ω) 0 (lineClock F Wd GT V t ω).toNNReal -
        R (lineClock F Wd GT V t ω).toNNReal ω)) :
    ∃ s : ℚ, (F.ent (fun u => Wd u ω) : ℝ) < s ∧ (s : ℝ) < t ∧
      trc (fun u => Wd u ω) (s : ℝ).toNNReal ≠ 0 ∧
      -(trc (fun u => Wd u ω) (s : ℝ).toNNReal)⁻¹ ∈ F.C ∧
      lineClock F Wd GT V (s : ℝ).toNNReal ω < lineClock F Wd GT V t ω ∧
      ∃ x r : ℝ, x ∈ Ioo
        (-rightImg (fun u => -wpath R ω u) 0
          (lineClock F Wd GT V (s : ℝ).toNNReal ω).toNNReal -
          R (lineClock F Wd GT V (s : ℝ).toNNReal ω).toNNReal ω)
        (rightImg (wpath R ω) 0 (lineClock F Wd GT V (s : ℝ).toNNReal ω).toNNReal -
          R (lineClock F Wd GT V (s : ℝ).toNNReal ω).toNNReal ω) ∧ 0 < r ∧
        (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).2.1 ''
          (H ∩ ball (x : ℂ) r) ⊆ ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) ∧
        Tendsto (fun z => (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).1
          ((componentLineChart F Wd GT R V t ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (fun z => (componentLineChart F Wd GT R V t ω).2.2
            ((componentLineChart F Wd GT R V t ω).2.1 z) -
          (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).2.2
            ((componentLineChart F Wd GT R V t ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
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
  have hWclock : ∀ u : ℝ≥0, u ≤ t → R (lineClock F Wd GT V u ω).toNNReal ω =
      wpath R ω (F.rcap (fun v => Wd v ω) u) := by
    intro u hu
    rw [← hClock u hu]
    simp only [wpath, Real.toNNReal_coe]
  obtain ⟨s, hsEnt, hst, hs0, hsC, hsCap0, hsCapLt, x, r, hx, hr, hCol, hTr, hLift⟩ :=
    exists_rat_visit_own_seed_collar hF hw hW hW0 hex
      (by rw [← hClock t le_rfl]; exact NNReal.coe_pos.2 hq) hξ
      (by simpa only [hClock t le_rfl, hWclock t le_rfl] using hξSeed)
  have hsn : (s : ℝ).toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hst.le
  have hChart : ∀ u : ℝ≥0, u ≤ t → componentLineChart F Wd GT R V u ω =
      Chart.id.loewner (wpath R ω) (F.rcap (fun v => Wd v ω) u) := by
    intro u hut
    unfold componentLineChart
    rw [hClock u hut]
  refine ⟨s, hsEnt, hst, hs0, hsC, ?_, x, r, ?_, hr, ?_⟩
  · have hOldFin : lineClock F Wd GT V (s : ℝ).toNNReal ω ≠ ⊤ :=
      ne_top_of_le_ne_top (((Frame.monotone_physClockG hF hGT ω hsn).trans_lt hP).trans_le le_top).ne
        (min_le_left _ _)
    rw [← ENNReal.coe_toNNReal (hlt.trans_le le_top).ne, ← ENNReal.coe_toNNReal hOldFin]
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hClock _ hsn, hClock t le_rfl]
    exact hsCapLt
  · simpa only [hClock _ hsn, hWclock _ hsn] using hx
  · rw [hChart _ hsn, hChart t le_rfl]
    exact ⟨hCol, hTr, hLift⟩

end InteractingSLE.Theorem14.GW4Fix
