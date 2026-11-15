/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaSeeds
import InteractingSLE.Spec.Supplement.GW4SafeRZetaCover

/-! # GW4: exposed accesses have exposed earlier reference coordinates -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.PocketStopSide MartChar RealFlow

/-- The recent own collars of an exposed current access can always be
chosen at exposed old coordinates. Seed membership follows from the force
image flow property of the surviving real characteristic. -/
theorem exists_recent_own_seed_collars {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t ξ : ℝ} (ht : 0 < t) (hξ : ξ ≠ 0)
    (hξSeed : ξ ∈ Ioo (-rightImg (fun s => -W s) 0 t - W t) (rightImg W 0 t - W t)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < t ∧ ∀ s ∈ Ioo (t - δ) t, ∃ x r : ℝ,
      x ∈ Ioo (-rightImg (fun u => -W u) 0 s - W s) (rightImg W 0 s - W s) ∧ 0 < r ∧
      (Chart.id.loewner W s).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
        ((Chart.id.loewner W t).dom : Set ℂ) ∧
      Tendsto (fun z => (Chart.id.loewner W s).1 ((Chart.id.loewner W t).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (fun z => (Chart.id.loewner W t).2.2 ((Chart.id.loewner W t).2.1 z) -
        (Chart.id.loewner W s).2.2 ((Chart.id.loewner W t).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨δ, hδ, hδt, hSeeds⟩ := exists_recent_restart_seeds hW ht (abs_pos.2 hξ)
  refine ⟨δ, hδ, hδt, fun s hs => ?_⟩
  have hs0 : 0 ≤ s := by linarith only [hs.1, hδt]
  have hV : Continuous (shiftDrive W s) :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hV0 : shiftDrive W s 0 = 0 := by simp only [shiftDrive, add_zero, sub_self]
  have hSides : ξ < -rightImg (fun u => -shiftDrive W s u) 0 (t - s) - shiftDrive W s (t - s) ∨
      rightImg (shiftDrive W s) 0 (t - s) - shiftDrive W s (t - s) < ξ := by
    rcases lt_or_gt_of_ne hξ with hNeg | hPos
    · left
      simpa only [abs_of_neg hNeg, neg_neg] using (hSeeds s hs).1
    · right
      simpa only [abs_of_pos hPos] using (hSeeds s hs).2
  obtain ⟨x, a, ha, hAt⟩ := exists_surviving_real_outside_seed_interval hV hV0 (sub_nonneg.2 hs.2.le) hSides
  obtain ⟨r, hr, hCol, hTr, hLift⟩ := exists_own_collar_of_restart_surviving_real hW hW0 hs0 hs.2.le ha
  have hx := mem_seed_interval_of_restart_terminal hW hW0 hs0 hs.2.le ha (hAt ▸ hξSeed)
  rw [hAt] at hTr hLift
  exact ⟨x, r, hx, hr, hCol, hTr, hLift⟩

/-- Rational physical interior visits cover every nonzero exposed own
access with a seed coordinate in the earlier chart. -/
theorem exists_rat_visit_own_seed_collar {F : Frame} (hF : F.IsOk) {w : ℝ≥0 → ℝ}
    (hw : F.IsPathOk w) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < F.exit w) (hq : 0 < F.rcap w t)
    {ξ : ℝ} (hξ : ξ ≠ 0)
    (hξSeed : ξ ∈ Ioo (-rightImg (fun s => -W s) 0 (F.rcap w t) - W (F.rcap w t))
      (rightImg W 0 (F.rcap w t) - W (F.rcap w t))) :
    ∃ s : ℚ, (F.ent w : ℝ) < s ∧ (s : ℝ) < t ∧
      trc w (s : ℝ).toNNReal ≠ 0 ∧ -(trc w (s : ℝ).toNNReal)⁻¹ ∈ F.C ∧
      0 < F.rcap w (s : ℝ).toNNReal ∧ F.rcap w (s : ℝ).toNNReal < F.rcap w t ∧
      ∃ x r : ℝ, x ∈ Ioo
        (-rightImg (fun u => -W u) 0 (F.rcap w (s : ℝ).toNNReal) - W (F.rcap w (s : ℝ).toNNReal))
        (rightImg W 0 (F.rcap w (s : ℝ).toNNReal) - W (F.rcap w (s : ℝ).toNNReal)) ∧ 0 < r ∧
        (Chart.id.loewner W (F.rcap w (s : ℝ).toNNReal)).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
          ((Chart.id.loewner W (F.rcap w t)).dom : Set ℂ) ∧
        Tendsto (fun z => (Chart.id.loewner W (F.rcap w (s : ℝ).toNNReal)).1
          ((Chart.id.loewner W (F.rcap w t)).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (fun z => (Chart.id.loewner W (F.rcap w t)).2.2
            ((Chart.id.loewner W (F.rcap w t)).2.1 z) -
          (Chart.id.loewner W (F.rcap w (s : ℝ).toNNReal)).2.2
            ((Chart.id.loewner W (F.rcap w t)).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨δ, hδ, hδq, hCol⟩ := exists_recent_own_seed_collars hW hW0 hq hξ hξSeed
  obtain ⟨s, hsEnt, hst, hs0, hsC, hsCap, hsLt⟩ :=
    Frame.exists_rat_interior_visit_recent_capacity hF hw ht hq hδ
  exact ⟨s, hsEnt, hst, hs0, hsC, by linarith only [hsCap, hδq], hsLt, hCol _ ⟨hsCap, hsLt⟩⟩

end InteractingSLE.Theorem14.GW4Fix
