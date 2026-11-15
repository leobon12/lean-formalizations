/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaSeeds
import InteractingSLE.Spec.Supplement.GW4SafeREpsilonCover
import InteractingSLE.Spec.Sec5.MarkovFlow

/-!
# GW4: recent own references at every nonzero current coordinate

A real characteristic of the restarted increment gives an old inverse
half-disc in the current domain. The flow property identifies its transition
with the literal old/current charts. The canonical inherited lift is zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.PocketStopSide

/-- A surviving real characteristic of an actual increment constructs its
old collar and the exact zero inherited lift in the original own charts. -/
theorem exists_own_collar_of_restart_surviving_real {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {s t x : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {a : ℝ → ℂ} (ha : QuantumZipper.IsForwardSol (shiftDrive W s) x (t - s) a) :
    ∃ r : ℝ, 0 < r ∧
      (Chart.id.loewner W s).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
        ((Chart.id.loewner W t).dom : Set ℂ) ∧
      Tendsto (fun z => (Chart.id.loewner W s).1 ((Chart.id.loewner W t).2.1 z))
        (𝓝[H] ((a (t - s)).re : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (fun z => (Chart.id.loewner W t).2.2 ((Chart.id.loewner W t).2.1 z) -
          (Chart.id.loewner W s).2.2 ((Chart.id.loewner W t).2.1 z))
        (𝓝[H] ((a (t - s)).re : ℂ)) (𝓝 0) := by
  have hΔ : 0 ≤ t - s := sub_nonneg.2 hst
  have hV : Continuous (shiftDrive W s) :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hV0 : shiftDrive W s 0 = 0 := by simp only [shiftDrive, add_zero, sub_self]
  have hNear := ZhanGT4.eventually_not_mem_fwdHull hV hΔ ha
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhdsWithin_iff.1 hNear
  have hDom : ((Chart.id.loewner W t).dom : Set ℂ) = H \ fwdHull W t := by
    rw [(Chart.isConformal_id.loewner hW hW0 (hs.trans hst)).coe_dom]
    exact QuantumZipper.RS.image_fwdMapInv_H hW hW0 (hs.trans hst)
  have hCol : (Chart.id.loewner W s).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
      ((Chart.id.loewner W t).dom : Set ℂ) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hDom]
    have hMem := mem_image_of_mem (fwdMapInv W s) (hBall ⟨hz.2, hz.1⟩)
    change fwdMapInv W s z ∈ fwdMapInv W s ''
      (H \ fwdHull (fun u => W (s + u) - W s) (t - s)) at hMem
    rw [Sec5.Markov.image_fwdMapInv_diff_fwdHull hW hW0 hs hΔ, add_sub_cancel] at hMem
    exact hMem
  have hEq : ∀ z ∈ H, (Chart.id.loewner W s).1 ((Chart.id.loewner W t).2.1 z) =
      fwdMapInv (shiftDrive W s) (t - s) z := by
    intro z hz
    change fwdMap W s (fwdMapInv W t z) = _
    have hFlow := QuantumZipper.RS.fwdMapInv_add_shift hW hW0 hs hΔ hz
    rw [show s + (t - s) = t by ring] at hFlow
    rw [hFlow]
    exact QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hs
      (QuantumZipper.RS.fwdMapInv_mem_H hV hV0 hΔ hz)
  have hTr : Tendsto (fun z => (Chart.id.loewner W s).1 ((Chart.id.loewner W t).2.1 z))
      (𝓝[H] ((a (t - s)).re : ℂ)) (𝓝 (x : ℂ)) :=
    ((tendsto_inverse_of_surviving_real hV hV0 hΔ ha).mono_right nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun z hz => (hEq z hz).symm)
  exact ⟨r, hr, hCol, hTr,
    tendsto_own_stage_lift_sub_zero Chart.isConformal_id hW hW0 hs hst hr hCol hTr⟩

/-- Every sufficiently recent own stage supplies an incident old half-disc
at the given nonzero current coordinate, with zero inherited lift. -/
theorem exists_recent_own_collars {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t ξ : ℝ} (ht : 0 < t) (hξ : ξ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ < t ∧ ∀ s ∈ Ioo (t - δ) t, ∃ x r : ℝ, 0 < r ∧
      (Chart.id.loewner W s).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
        ((Chart.id.loewner W t).dom : Set ℂ) ∧
      Tendsto (fun z => (Chart.id.loewner W s).1 ((Chart.id.loewner W t).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (fun z => (Chart.id.loewner W t).2.2 ((Chart.id.loewner W t).2.1 z) -
          (Chart.id.loewner W s).2.2 ((Chart.id.loewner W t).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨δ, hδ, hδt, hSeeds⟩ := exists_recent_restart_seeds hW ht (abs_pos.2 hξ)
  refine ⟨δ, hδ, hδt, ?_⟩
  intro s hs
  have hs0 : 0 ≤ s := by linarith only [hs.1, hδt]
  have hV : Continuous (shiftDrive W s) :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hV0 : shiftDrive W s 0 = 0 := by simp only [shiftDrive, add_zero, sub_self]
  have hSides : ξ < -MartChar.RealFlow.rightImg (fun u => -shiftDrive W s u) 0 (t - s) -
        shiftDrive W s (t - s) ∨
      MartChar.RealFlow.rightImg (shiftDrive W s) 0 (t - s) - shiftDrive W s (t - s) < ξ := by
    rcases lt_or_gt_of_ne hξ with hNeg | hPos
    · left
      simpa only [abs_of_neg hNeg, neg_neg] using (hSeeds s hs).1
    · right
      simpa only [abs_of_pos hPos] using (hSeeds s hs).2
  obtain ⟨x, a, ha, hAt⟩ := exists_surviving_real_outside_seed_interval hV hV0
    (sub_nonneg.2 hs.2.le) hSides
  obtain ⟨r, hr, hCol, hTr, hLift⟩ :=
    exists_own_collar_of_restart_surviving_real hW hW0 hs0 hs.2.le ha
  rw [hAt] at hTr hLift
  exact ⟨x, r, hr, hCol, hTr, hLift⟩

end InteractingSLE.Theorem14.GW4Fix
