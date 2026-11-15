/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaSeeds
import InteractingSLE.Spec.ZhanGT4.A1GoodHull

/-! # GW4: one old seed collar persists across a current time neighborhood -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H IsForwardSol)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar.RealFlow

/-- Every positive-time seed interval contains a nonzero coordinate. -/
theorem exists_ne_zero_mem_seed_interval {W : ℝ → ℝ} (hW : Continuous W)
    {q : ℝ} (hq : 0 < q) :
    ∃ ξ : ℝ, ξ ∈ Ioo (-rightImg (fun r => -W r) 0 q - W q) (rightImg W 0 q - W q) ∧ ξ ≠ 0 := by
  have hwidth := rightImg_add_rightImg_neg_ge hW 0 0 hq.le
  have hpos : 0 < 4 * Real.sqrt q := mul_pos (by norm_num) (Real.sqrt_pos.2 hq)
  have hab : -rightImg (fun r => -W r) 0 q - W q < rightImg W 0 q - W q := by
    linarith only [hwidth, hpos]
  obtain ⟨ξ, hξL, hξR⟩ := exists_between hab
  by_cases hξ : ξ = 0
  · subst ξ
    refine ⟨(rightImg W 0 q - W q) / 2, ⟨hξL.trans (half_pos hξR), half_lt_self hξR⟩,
      (half_pos hξR).ne'⟩
  · exact ⟨ξ, ⟨hξL, hξR⟩, hξ⟩

/-- An old seed coordinate can be kept alive past the current capacity.
Its evolving coordinate stays in the current seed interval on a full
time neighborhood. Thus the same old collar can compare neighboring
current winding integers. -/
theorem exists_persistent_seed_characteristic {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {q : ℝ} (hq : 0 < q) :
    ∃ (p x T : ℝ) (a : ℝ → ℂ), 0 < p ∧ p < q ∧
      x ∈ Ioo (-rightImg (fun r => -W r) 0 p - W p) (rightImg W 0 p - W p) ∧
      q - p < T ∧ IsForwardSol (shiftDrive W p) x T a ∧
      ∀ᶠ u : ℝ in 𝓝 q, p < u ∧ u - p < T ∧
        (a (u - p)).re ∈ Ioo (-rightImg (fun r => -W r) 0 u - W u) (rightImg W 0 u - W u) := by
  obtain ⟨ξ, hξI, hξ0⟩ := exists_ne_zero_mem_seed_interval hW hq
  obtain ⟨δ, hδ, hδq, hSeeds⟩ := exists_recent_restart_seeds hW hq (abs_pos.2 hξ0)
  let p := q - δ / 2
  have hp : 0 < p := by dsimp only [p]; linarith only [hδq, hδ, hq]
  have hpq : p < q := by dsimp only [p]; linarith only [hδ]
  have hpNear : p ∈ Ioo (q - δ) q := ⟨by dsimp only [p]; linarith only [hδ], hpq⟩
  have hV : Continuous (shiftDrive W p) := (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hV0 : shiftDrive W p 0 = 0 := by simp only [shiftDrive, add_zero, sub_self]
  have hSides : ξ < -rightImg (fun u => -shiftDrive W p u) 0 (q - p) - shiftDrive W p (q - p) ∨
      rightImg (shiftDrive W p) 0 (q - p) - shiftDrive W p (q - p) < ξ := by
    rcases lt_or_gt_of_ne hξ0 with hNeg | hPos
    · left
      simpa only [abs_of_neg hNeg, neg_neg] using (hSeeds p hpNear).1
    · right
      simpa only [abs_of_pos hPos] using (hSeeds p hpNear).2
  obtain ⟨x, b, hb, hbξ⟩ := exists_surviving_real_outside_seed_interval hV hV0 (sub_nonneg.2 hpq.le) hSides
  have hxI := mem_seed_interval_of_restart_terminal hW hW0 hp.le hpq.le hb (hbξ ▸ hξI)
  obtain ⟨T, hT, a, ha⟩ := ZhanGT4.A1Good.exists_isForwardSol_real_gt hV (sub_nonneg.2 hpq.le) hb
  have haξ : (a (q - p)).re = ξ := by
    rw [← fwdMap_eq_of_isForwardSol hV ha ⟨sub_nonneg.2 hpq.le, hT.le⟩,
      fwdMap_eq_of_isForwardSol hV hb ⟨sub_nonneg.2 hpq.le, le_rfl⟩]
    exact hbξ
  have hAc : ContinuousAt (fun u : ℝ => (a (u - p)).re) q := by
    have hc : ContinuousAt a (q - p) := ha.1.continuousAt
      (Icc_mem_nhds (sub_pos.2 hpq) hT)
    have hcomp : ContinuousAt (fun u : ℝ => a (u - p)) q :=
      hc.comp (f := fun u : ℝ => u - p) (x := q) (continuousAt_id.sub continuousAt_const)
    exact continuous_re.continuousAt.comp hcomp
  have hLc : ContinuousAt (fun u : ℝ => -rightImg (fun r => -W r) 0 u - W u) q :=
    (((continuousOn_rightImg hW.neg 0).continuousAt (Ici_mem_nhds hq)).neg).sub hW.continuousAt
  have hRc : ContinuousAt (fun u : ℝ => rightImg W 0 u - W u) q :=
    ((continuousOn_rightImg hW 0).continuousAt (Ici_mem_nhds hq)).sub hW.continuousAt
  have hAtI : (a (q - p)).re ∈ Ioo (-rightImg (fun r => -W r) 0 q - W q) (rightImg W 0 q - W q) :=
    haξ ▸ hξI
  refine ⟨p, x, T, a, hp, hpq, hxI, hT, ha, ?_⟩
  filter_upwards [Ioo_mem_nhds hpq (show q < p + T by linarith only [hT]),
    (hAc.sub hLc).eventually (Ioi_mem_nhds (sub_pos.2 hAtI.1)),
    (hRc.sub hAc).eventually (Ioi_mem_nhds (sub_pos.2 hAtI.2))] with u hu hL hR
  exact ⟨hu.1, by linarith only [hu.2], sub_pos.1 hL, sub_pos.1 hR⟩

end InteractingSLE.Theorem14.GW4Fix
