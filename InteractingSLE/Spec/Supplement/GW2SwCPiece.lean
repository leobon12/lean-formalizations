/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SwCJoin
import InteractingSLE.Spec.Supplement.GW2FbConfig

/-!
# Trace-generating extensions of live pieces

Packet PROVE-GW2-SWITCH (round 3). A regular piece with a generating trace before its lifetime, run
for an own time strictly before that lifetime (the live condition `GW2Schedule.AllSucc`), has a
trace-generating extension (`HasPieceExt`): FABLE's frozen extension
(`GW2Fb.exists_frozen_generatingTrace`) agrees with the driver beyond the stop, and the stopped
driver is the driver there.

* `hasPieceExt_of_trace`;
* **`exists_isGeneratingTrace_joinDrv_of_allSucc`**: for a live schedule whose pieces are regular with
  generating traces, the joined driver generates a trace up to its total time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.SwC

open GW2Schedule Exist Staged StagedLaw Swc

variable {Δ : ℕ → ℝ≥0∞} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- A regular piece with a generating trace, stopped strictly before its lifetime, has a
trace-generating extension. -/
theorem hasPieceExt_of_trace {j : ℕ} (he : IsRegularDriver (D j)) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (D j).1 (D j).2 α) (hΔ : Δ j < (D j).2) : HasPieceExt Δ D j := by
  have hΔt : Δ j ≠ ⊤ := ne_top_of_lt hΔ
  have hmin : min (Δ j) (D j).2 = Δ j := min_eq_left hΔ.le
  have ht₁ : (((Δ j).toNNReal : ℝ≥0) : ℝ≥0∞) < (D j).2 := by rwa [ENNReal.coe_toNNReal hΔt]
  obtain ⟨w, α', t₂, h12, -, hwc, hw0, hα', hag, -⟩ :=
    GW2Fb.exists_frozen_generatingTrace hα he.1 he.2.1 ht₁
  refine ⟨w, α', hwc, hw0, hα', fun u hu => ?_⟩
  have hu' : u ≤ (Δ j).toNNReal := by
    have h' : (u : ℝ) ≤ ((Δ j).toNNReal : ℝ) := by simpa only [stopTime, hmin] using hu
    exact_mod_cast h'
  have huΔ : (u : ℝ≥0∞) ≤ Δ j := by
    calc (u : ℝ≥0∞) ≤ ((Δ j).toNNReal : ℝ≥0∞) := ENNReal.coe_le_coe.2 hu'
      _ = Δ j := ENNReal.coe_toNNReal hΔt
  have hs : stopDrv (Δ j) (D j) u = (D j).1 u := by
    simp only [stopDrv, retOf, Real.toNNReal_coe, hmin, min_eq_left huΔ, ENNReal.toNNReal_coe]
  rw [hs]
  exact hag u (hu'.trans h12.le)

/-- **The joined driver of a live schedule of regular pieces generates a trace up to its total
time.** -/
theorem exists_isGeneratingTrace_joinDrv_of_allSucc (n : ℕ) (hs : AllSucc Δ D (n + 1))
    (he : ∀ j < n + 1, IsRegularDriver (D j))
    (hα : ∀ j < n + 1, ∃ α : ℝ≥0 → ℂ, IsGeneratingTrace (D j).1 (D j).2 α) :
    ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t : ℝ≥0 => joinDrv Δ D (n + 1) t)
      ((joinTime Δ D (n + 1)).toNNReal : ℝ≥0∞) γ :=
  exists_isGeneratingTrace_joinDrv n fun j hj =>
    let ⟨_, hαj⟩ := hα j hj
    hasPieceExt_of_trace (he j hj) hαj (hs j hj)

end InteractingSLE.Theorem14.GW2TipSystem.SwC
