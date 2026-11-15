/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaCharts

/-! # GW4: centered images of shrinking hull increments -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.Theorem14.GW4Fix

/-- Every choice of a point in a shrinking future hull increment approaches
the centered driver after mapping out the present hull. -/
theorem tendsto_fwdMap_of_shrinking_increment {W : ℝ → ℝ} (hW : Continuous W)
    {t : ℝ} (ht : 0 ≤ t) {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 t))
    (htu : ∀ n, t ≤ u n) {z : ℕ → ℂ}
    (hz : ∀ n, z n ∈ fwdHull W (u n) \ fwdHull W t) :
    Tendsto (fun n => fwdMap W t (z n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hd, hdW⟩ := Metric.continuous_iff.1 hW t (ε / 8) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hu (min d ((ε / 8) ^ 2)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hδn := hN n hn
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (htu n))] at hδn
  have hM : ∀ s ∈ Icc (0 : ℝ) (u n - t), |W (t + s) - W t| ≤ ε / 8 := by
    intro s hs
    apply le_of_lt (hdW _ ?_)
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 (lt_of_lt_of_le hδn (min_le_left _ _))
  have hgrow := QuantumZipper.CoreArc.norm_fwdMap_le_of_mem_diff hW ht
    (sub_nonneg.2 (htu n)) hM (by simpa only [add_sub_cancel] using (hz n).1) (hz n).2
  have hsq : Real.sqrt (u n - t) < ε / 8 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact lt_of_lt_of_le hδn (min_le_right _ _)
  rw [dist_zero_right]
  calc ‖fwdMap W t (z n)‖ ≤ 4 * (ε / 8 + Real.sqrt (u n - t)) := hgrow
    _ < ε := by linarith

end InteractingSLE.Theorem14.GW4Fix
